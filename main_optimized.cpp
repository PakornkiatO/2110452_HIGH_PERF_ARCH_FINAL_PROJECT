#include <bits/stdc++.h>
using namespace std;

// ─────────────────────────────────────────────
//  Global graph data (read-only after init)
// ─────────────────────────────────────────────
static int N;                          // number of nodes

// For each node: bitmask of itself + all neighbours ("coverage mask")
// We use dynamic bitsets via vector<uint64_t> words.
// covered_by[v] = set of nodes that get powered if v has a plant
static vector<vector<uint64_t>> covered_by;   // [node][word]
static int WORDS;                              // ceil(N/64)

// ─────────────────────────────────────────────
//  Shared best solution (protected by mutex)
// ─────────────────────────────────────────────
static atomic<int>       best_count;
static mutex             best_mutex;
static vector<int>       best_state_global;   // 1 = plant, 0 = no plant

// ─────────────────────────────────────────────
//  Inline bitset helpers
// ─────────────────────────────────────────────
// Returns index of lowest set bit across words[], or -1 if all zero.
static inline int first_set(const vector<uint64_t>& words)
{
    for (int w = 0; w < WORDS; w++)
        if (words[w]) return w * 64 + __builtin_ctzll(words[w]);
    return -1;
}

// popcount across all words
static inline int popcount_all(const vector<uint64_t>& words)
{
    int c = 0;
    for (int w = 0; w < WORDS; w++) c += __builtin_popcountll(words[w]);
    return c;
}

// ─────────────────────────────────────────────
//  Greedy warm-start
//  Repeatedly pick the node whose coverage mask
//  covers the most still-uncovered nodes.
// ─────────────────────────────────────────────
static int greedy_solution(vector<int>& out_state)
{
    // uncovered = bitmask of nodes not yet powered
    vector<uint64_t> uncovered(WORDS, ~0ULL);
    // mask off bits beyond N
    if (N % 64) uncovered[WORDS-1] = (1ULL << (N % 64)) - 1;

    out_state.assign(N, 0);
    int count = 0;

    while (true) {
        // find uncovered node with index = first_set(uncovered)
        int any = first_set(uncovered);
        if (any == -1) break;           // all covered

        // pick candidate among (any) and its neighbourhood that covers most
        // We score every node in covered_by[any] (those that can cover `any`)
        // Actually: any uncovered node MUST be covered by itself or a neighbour.
        // The best branch is the one whose coverage_mask has largest overlap
        // with uncovered.  We look at covered_by[any] set = {any}∪neighbours(any).

        // Build list of candidates: any node c such that bit `any` is set in covered_by[c]
        // = c == any  OR  any is neighbour of c  = covered_by[any] membership
        // We just iterate covered_by[any] bitmask.
        int best_cand = -1, best_score = -1;
        vector<uint64_t> tmp_mask = covered_by[any]; // nodes that can cover `any`

        // iterate set bits of tmp_mask
        for (int w = 0; w < WORDS; w++) {
            uint64_t word = tmp_mask[w];
            while (word) {
                int bit = __builtin_ctzll(word);
                int cand = w * 64 + bit;
                word &= word - 1;
                // score = how many uncovered nodes cand would cover
                int score = 0;
                for (int ww = 0; ww < WORDS; ww++)
                    score += __builtin_popcountll(covered_by[cand][ww] & uncovered[ww]);
                if (score > best_score) { best_score = score; best_cand = cand; }
            }
        }

        // place plant at best_cand
        out_state[best_cand] = 1;
        count++;
        // remove all nodes covered by best_cand from uncovered
        for (int w = 0; w < WORDS; w++)
            uncovered[w] &= ~covered_by[best_cand][w];
    }
    return count;
}

// ─────────────────────────────────────────────
//  Lower bound:
//  Find a greedy independent set of uncovered nodes
//  such that no two share a coverage candidate.
//  Each such node needs at least one distinct plant → LB.
// ─────────────────────────────────────────────
static inline int lower_bound(const vector<uint64_t>& uncovered)
{
    // We scan uncovered nodes; for each, "remove" all nodes reachable by
    // a single plant placement (i.e. covered_by[node] expanded one hop).
    // This gives a greedy independent domination LB.
    vector<uint64_t> remaining = uncovered;
    int lb = 0;
    while (true) {
        int v = first_set(remaining);
        if (v == -1) break;
        lb++;
        // remove all nodes that share a coverage candidate with v
        // = union of covered_by[c] for all c in covered_by[v]
        // That is: any node reachable within distance 2 from v
        vector<uint64_t> tmp_candidates = covered_by[v]; // nodes that cover v
        for (int w = 0; w < WORDS; w++) {
            uint64_t word = tmp_candidates[w];
            while (word) {
                int bit = __builtin_ctzll(word);
                int cand = w * 64 + bit;
                word &= word - 1;
                for (int ww = 0; ww < WORDS; ww++)
                    remaining[ww] &= ~covered_by[cand][ww];
            }
        }
    }
    return lb;
}

// ─────────────────────────────────────────────
//  Branch & Bound
//  state_bits  : bitmask of nodes WITH a plant
//  covered     : bitmask of nodes currently powered
//  uncovered   : complement (for fast access)
//  count       : plants placed so far
//  placement   : the actual node→{0,1} assignment for reconstruction
// ─────────────────────────────────────────────
static void BNB(
    vector<uint64_t>& state_bits,
    vector<uint64_t>& uncovered,
    int count,
    vector<int>& placement)
{
    // ── Prune 1: count already not better ──
    if (count >= best_count.load(memory_order_relaxed)) return;

    // ── Prune 2: lower bound ──
    if (count + lower_bound(uncovered) >= best_count.load(memory_order_relaxed)) return;

    // ── Find most-constrained uncovered node ──
    // = uncovered node with smallest |covered_by[v] ∩ (unplanted nodes)|
    // (fewest ways to cover it → branch factor minimised)
    int chosen = -1, chosen_score = INT_MAX;
    {
        vector<uint64_t> remaining = uncovered;
        // iterate uncovered nodes
        for (int w = 0; w < WORDS && chosen_score > 1; w++) {
            uint64_t word = remaining[w];
            while (word && chosen_score > 1) {
                int bit = __builtin_ctzll(word);
                int v = w * 64 + bit;
                word &= word - 1;
                // count candidate plants that could cover v
                // = nodes in covered_by[v] that are NOT yet a plant
                int score = 0;
                for (int ww = 0; ww < WORDS; ww++)
                    score += __builtin_popcountll(covered_by[v][ww] & ~state_bits[ww]);
                if (score < chosen_score) { chosen_score = score; chosen = v; }
            }
        }
    }

    // ── All covered → update best ──
    if (chosen == -1) {
        int cur = best_count.load(memory_order_relaxed);
        while (count < cur &&
               !best_count.compare_exchange_weak(cur, count, memory_order_relaxed));
        if (count <= best_count.load(memory_order_relaxed)) {
            lock_guard<mutex> lk(best_mutex);
            if (count < (int)best_state_global.size() ||
                count <= best_count.load(memory_order_relaxed)) {
                best_state_global = placement;
                best_count.store(count, memory_order_relaxed);
            }
        }
        return;
    }

    // ── Branch: try each candidate plant for `chosen` ──
    // Candidates = nodes in covered_by[chosen] not already planted
    vector<uint64_t> candidates = covered_by[chosen];

    // Sort candidates by descending coverage of remaining uncovered nodes
    // (place the most-promising branch first for faster pruning)
    vector<pair<int,int>> cand_list; // (score, node)
    for (int w = 0; w < WORDS; w++) {
        uint64_t word = candidates[w];
        while (word) {
            int bit = __builtin_ctzll(word);
            int cand = w * 64 + bit;
            word &= word - 1;
            if (state_bits[cand / 64] & (1ULL << (cand % 64))) continue; // already planted
            int score = 0;
            for (int ww = 0; ww < WORDS; ww++)
                score += __builtin_popcountll(covered_by[cand][ww] & uncovered[ww]);
            cand_list.push_back({score, cand});
        }
    }
    sort(cand_list.rbegin(), cand_list.rend()); // descending score

    for (auto& [score, cand] : cand_list) {
        if (count + 1 >= best_count.load(memory_order_relaxed)) break; // prune early

        // Place plant at cand
        state_bits[cand / 64] |= (1ULL << (cand % 64));
        placement[cand] = 1;

        // Update uncovered
        vector<uint64_t> new_uncovered(WORDS);
        for (int w = 0; w < WORDS; w++)
            new_uncovered[w] = uncovered[w] & ~covered_by[cand][w];

        BNB(state_bits, new_uncovered, count + 1, placement);

        // Undo
        state_bits[cand / 64] &= ~(1ULL << (cand % 64));
        placement[cand] = 0;
    }
}

// ─────────────────────────────────────────────
//  Thread worker: explores one top-level branch
// ─────────────────────────────────────────────
struct Task {
    int plant_node;                 // the node forced to have a plant
    vector<uint64_t> state_bits;
    vector<uint64_t> uncovered;
    vector<int>      placement;
};

static void thread_worker(Task task)
{
    // place the forced plant
    int c = task.plant_node;
    task.state_bits[c / 64] |= (1ULL << (c % 64));
    task.placement[c] = 1;
    for (int w = 0; w < WORDS; w++)
        task.uncovered[w] &= ~covered_by[c][w];

    BNB(task.state_bits, task.uncovered, 1, task.placement);
}

// ─────────────────────────────────────────────
//  main
// ─────────────────────────────────────────────
int main(int argc, char* argv[])
{
    ios::sync_with_stdio(false);

    ifstream fin(argv[1]);
    ofstream fout(argv[2]);

    int M;
    fin >> N >> M;

    WORDS = (N + 63) / 64;
    covered_by.assign(N, vector<uint64_t>(WORDS, 0ULL));

    // covered_by[v] = {v} ∪ neighbours(v)
    for (int v = 0; v < N; v++)
        covered_by[v][v / 64] |= (1ULL << (v % 64));

    vector<vector<int>> adj(N);
    for (int i = 0; i < M; i++) {
        int u, v; fin >> u >> v;
        adj[u].push_back(v);
        adj[v].push_back(u);
        covered_by[u][v / 64] |= (1ULL << (v % 64));
        covered_by[v][u / 64] |= (1ULL << (u % 64));
    }

    // ── Greedy warm start ──
    vector<int> greedy_state;
    int greedy_val = greedy_solution(greedy_state);
    best_count.store(greedy_val, memory_order_relaxed);
    best_state_global = greedy_state;

    // ── Build initial uncovered (all nodes) ──
    vector<uint64_t> init_uncovered(WORDS, ~0ULL);
    if (N % 64) init_uncovered[WORDS-1] = (1ULL << (N % 64)) - 1;

    // ── Enumerate top-level candidates for the first uncovered node ──
    // = covered_by[first uncovered node]
    // Dispatch each as a separate thread task.
    int root = first_set(init_uncovered); // node 0 in a full graph

    vector<Task> tasks;
    {
        vector<uint64_t> cands = covered_by[root];
        for (int w = 0; w < WORDS; w++) {
            uint64_t word = cands[w];
            while (word) {
                int bit = __builtin_ctzll(word);
                int cand = w * 64 + bit;
                word &= word - 1;
                Task t;
                t.plant_node  = cand;
                t.state_bits  = vector<uint64_t>(WORDS, 0ULL);
                t.uncovered   = init_uncovered;
                t.placement   = vector<int>(N, 0);
                tasks.push_back(move(t));
            }
        }
    }

    // Sort tasks: highest-coverage candidate first
    sort(tasks.begin(), tasks.end(), [](const Task& a, const Task& b){
        int sa = 0, sb = 0;
        for (int w = 0; w < WORDS; w++) {
            sa += __builtin_popcountll(covered_by[a.plant_node][w]);
            sb += __builtin_popcountll(covered_by[b.plant_node][w]);
        }
        return sa > sb;
    });

    // ── Thread pool: use up to 12 threads ──
    const int MAX_THREADS = min((int)tasks.size(), 12);
    vector<thread> threads;
    atomic<int> next_task(0);

    auto worker = [&]() {
        while (true) {
            int idx = next_task.fetch_add(1, memory_order_relaxed);
            if (idx >= (int)tasks.size()) break;
            thread_worker(move(tasks[idx]));
        }
    };

    for (int t = 0; t < MAX_THREADS; t++)
        threads.emplace_back(worker);
    for (auto& t : threads)
        t.join();

    // ── Output ──
    cout << "Minimum powerplant is: " << best_count.load() << "\n";
    for (int i = 0; i < N; i++) {
        cout << best_state_global[i];
        fout << best_state_global[i];
    }

    return 0;
}