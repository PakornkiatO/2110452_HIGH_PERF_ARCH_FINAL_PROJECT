#include <bits/stdc++.h>
using namespace std;

// ═══════════════════════════════════════════════════════════════
//  GLOBAL GRAPH DATA
// ═══════════════════════════════════════════════════════════════
static int N, M;
static constexpr int INF = 1e9;
static vector<vector<int>> adj;

// covered_by[v] = bitmask of {v} ∪ neighbours(v)
static vector<vector<uint64_t>> covered_by;
static int WORDS;

// ═══════════════════════════════════════════════════════════════
//  BITSET HELPERS
// ═══════════════════════════════════════════════════════════════
static inline int  first_set (const vector<uint64_t>& w) {
    for(int i=0;i<WORDS;i++) if(w[i]) return i*64+__builtin_ctzll(w[i]); return -1;
}
static inline bool bit_test  (const vector<uint64_t>& w,int v){return(w[v>>6]>>(v&63))&1;}
static inline void bit_set   (vector<uint64_t>& w,int v){w[v>>6]|= (1ULL<<(v&63));}
static inline void bit_clear (vector<uint64_t>& w,int v){w[v>>6]&=~(1ULL<<(v&63));}

// ═══════════════════════════════════════════════════════════════
//  GRAPH TYPE DETECTION
// ═══════════════════════════════════════════════════════════════
static bool is_forest() {
    if(M>=N) return false;
    vector<int> col(N,0);
    for(int s=0;s<N;s++){
        if(col[s]) continue;
        stack<pair<int,int>> st; st.push({s,-1});
        while(!st.empty()){
            auto[u,p]=st.top(); st.pop();
            if(col[u]==2) continue;
            if(col[u]==1){col[u]=2;continue;}
            col[u]=1; st.push({u,p});
            for(int v:adj[u]){
                if(v==p) continue;
                if(col[v]==1) return false;
                if(!col[v]) st.push({v,u});
            }
        }
    }
    return true;
}

// ═══════════════════════════════════════════════════════════════
//  SOLVER 1 — TREE DP  (exact O(n))
//
//  State for node u in a rooted tree:
//    0 = u HAS a plant
//    1 = u has NO plant, IS covered by a child
//    2 = u has NO plant, NOT covered yet  (parent will cover it)
//
//  Leaf base: dp = {1, INF, 0}
//
//  Merge child v into u:
//    dp'[0] = dp[u][0] + min(dp[v][0], dp[v][1], dp[v][2])
//    dp'[1] = min( dp[u][1] + min(dp[v][0],dp[v][1]),   // u already covered
//                  dp[u][2] + dp[v][0] )                  // v's plant now covers u
//    dp'[2] = dp[u][2] + min(dp[v][0], dp[v][1])         // v must cover itself
//
//  Root: state 2 invalid → pick min(dp[r][0], dp[r][1])
// ═══════════════════════════════════════════════════════════════
static vector<int> solve_tree() {
    vector<int> result(N,0);
    vector<int> par(N,-1);
    vector<bool> vis(N,false);
    vector<array<int,3>> dp(N);
    vector<vector<int>> ch(N);

    for(int root=0;root<N;root++){
        if(vis[root]) continue;

        vector<int> order;
        {
            stack<int> st; st.push(root); par[root]=-1;
            while(!st.empty()){
                int u=st.top(); st.pop();
                if(vis[u]) continue;
                vis[u]=true; order.push_back(u);
                for(int v:adj[u]) if(!vis[v]){par[v]=u;st.push(v);}
            }
        }
        reverse(order.begin(),order.end()); // leaves first

        for(int u:order){ ch[u].clear(); for(int v:adj[u]) if(v!=par[u]) ch[u].push_back(v); }

        // bottom-up DP
        for(int u:order){
            dp[u]={1,INF,0};
            for(int v:ch[u]){
                array<int,3> nd;
                int any =min({dp[v][0],dp[v][1],dp[v][2]});
                int self=min( dp[v][0], dp[v][1]);
                nd[0]=dp[u][0]+any;
                nd[1]=min(dp[u][1]<INF?dp[u][1]+self:INF,
                          dp[u][2]<INF?dp[u][2]+dp[v][0]:INF);
                nd[2]=dp[u][2]<INF?dp[u][2]+self:INF;
                dp[u]=nd;
            }
        }

        // top-down reconstruction
        vector<int> nst(N,-1);
        nst[root]=(dp[root][0]<=dp[root][1])?0:1;

        reverse(order.begin(),order.end()); // root first
        for(int u:order){
            int su=nst[u];
            if(su==0) result[u]=1;

            if(su==0){
                for(int v:ch[u]){
                    int best=min({dp[v][0],dp[v][1],dp[v][2]});
                    if     (dp[v][2]==best) nst[v]=2;
                    else if(dp[v][1]==best) nst[v]=1;
                    else                   nst[v]=0;
                }
            } else if(su==1){
                // Find the ONE child that covers u (must be in state 0).
                // That child is the one where switching it to state 0 achieves dp[u][1].
                // Compute total_self = sum of min(dp[v][0],dp[v][1]) for all children.
                int total_self=0; bool ov=false;
                for(int v:ch[u]){int s=min(dp[v][0],dp[v][1]);if(s>=INF){ov=true;break;}total_self+=s;}
                int covering=-1;
                if(!ov){
                    for(int v:ch[u]){
                        int self_v=min(dp[v][0],dp[v][1]);
                        int cost=total_self-self_v+dp[v][0];
                        if(cost==dp[u][1]){covering=v;break;}
                    }
                }
                if(covering==-1&&!ch[u].empty()) covering=ch[u][0]; // fallback
                for(int v:ch[u]){
                    if(v==covering) nst[v]=0;
                    else nst[v]=(dp[v][1]<=dp[v][0])?1:0;
                }
            } else { // su==2
                for(int v:ch[u]) nst[v]=(dp[v][1]<=dp[v][0])?1:0;
            }
        }
    }
    return result;
}

// ═══════════════════════════════════════════════════════════════
//  SOLVER 2 — BITMASK  (exact, n ≤ 25)
// ═══════════════════════════════════════════════════════════════
static vector<int> solve_bitmask(){
    vector<uint32_t> cov(N);
    for(int v=0;v<N;v++){cov[v]=1u<<v;for(int u:adj[v])cov[v]|=1u<<u;}
    uint32_t all=(N==32)?0xFFFFFFFFu:((1u<<N)-1);
    int bc=N+1; uint32_t bm=all;
    for(uint32_t S=0;S<=all;S++){
        int cnt=__builtin_popcount(S); if(cnt>=bc) continue;
        uint32_t cov2=0;
        for(uint32_t T=S;T;T&=T-1) cov2|=cov[__builtin_ctz(T)];
        if(cov2==all){bc=cnt;bm=S;}
    }
    vector<int> r(N,0); for(int v=0;v<N;v++) if((bm>>v)&1) r[v]=1;
    return r;
}

// ═══════════════════════════════════════════════════════════════
//  SOLVER 3 — OPTIMIZED BRANCH & BOUND
// ═══════════════════════════════════════════════════════════════
static atomic<int>  bnb_best;
static mutex        bnb_mutex;
static vector<int>  bnb_result;

static int greedy_solution(vector<int>& out){
    vector<uint64_t> unc(WORDS,~0ULL);
    if(N%64) unc[WORDS-1]=(1ULL<<(N%64))-1;
    out.assign(N,0); int cnt=0;
    while(true){
        int any=first_set(unc); if(any==-1) break;
        int bc=-1,bs=-1;
        for(int w=0;w<WORDS;w++){uint64_t word=covered_by[any][w];
            while(word){int bit=__builtin_ctzll(word);word&=word-1;
                int c=w*64+bit,s=0;
                for(int ww=0;ww<WORDS;ww++) s+=__builtin_popcountll(covered_by[c][ww]&unc[ww]);
                if(s>bs){bs=s;bc=c;}
            }
        }
        out[bc]=1; cnt++;
        for(int w=0;w<WORDS;w++) unc[w]&=~covered_by[bc][w];
    }
    return cnt;
}

static inline int lower_bound(const vector<uint64_t>& unc){
    vector<uint64_t> rem=unc; int lb=0;
    while(true){
        int v=first_set(rem); if(v==-1) break; lb++;
        for(int w=0;w<WORDS;w++){uint64_t word=covered_by[v][w];
            while(word){int bit=__builtin_ctzll(word);word&=word-1;
                int c=w*64+bit;
                for(int ww=0;ww<WORDS;ww++) rem[ww]&=~covered_by[c][ww];
            }
        }
    }
    return lb;
}

static void BNB(vector<uint64_t>& sb,vector<uint64_t>& unc,int cnt,vector<int>& pl){
    if(cnt>=bnb_best.load(memory_order_relaxed)) return;
    if(cnt+lower_bound(unc)>=bnb_best.load(memory_order_relaxed)) return;

    int chosen=-1,cscore=INT_MAX;
    for(int w=0;w<WORDS&&cscore>1;w++){uint64_t word=unc[w];
        while(word&&cscore>1){int bit=__builtin_ctzll(word);word&=word-1;
            int v=w*64+bit,s=0;
            for(int ww=0;ww<WORDS;ww++) s+=__builtin_popcountll(covered_by[v][ww]&~sb[ww]);
            if(s<cscore){cscore=s;chosen=v;}
        }
    }

    if(chosen==-1){
        int cur=bnb_best.load(memory_order_relaxed);
        while(cnt<cur&&!bnb_best.compare_exchange_weak(cur,cnt,memory_order_relaxed));
        if(cnt<=bnb_best.load(memory_order_relaxed)){
            lock_guard<mutex> lk(bnb_mutex);
            if(cnt<=bnb_best.load(memory_order_relaxed)){bnb_result=pl;bnb_best.store(cnt,memory_order_relaxed);}
        }
        return;
    }

    vector<pair<int,int>> cands;
    for(int w=0;w<WORDS;w++){uint64_t word=covered_by[chosen][w];
        while(word){int bit=__builtin_ctzll(word);word&=word-1;
            int c=w*64+bit; if(bit_test(sb,c)) continue;
            int s=0;
            for(int ww=0;ww<WORDS;ww++) s+=__builtin_popcountll(covered_by[c][ww]&unc[ww]);
            cands.push_back({s,c});
        }
    }
    sort(cands.rbegin(),cands.rend());

    for(auto&[s,c]:cands){
        if(cnt+1>=bnb_best.load(memory_order_relaxed)) break;
        bit_set(sb,c); pl[c]=1;
        vector<uint64_t> nu(WORDS);
        for(int w=0;w<WORDS;w++) nu[w]=unc[w]&~covered_by[c][w];
        BNB(sb,nu,cnt+1,pl);
        bit_clear(sb,c); pl[c]=0;
    }
}

struct Task{int pn;vector<uint64_t> sb,unc;vector<int> pl;};
static void thread_worker(Task t){
    int c=t.pn; bit_set(t.sb,c); t.pl[c]=1;
    for(int w=0;w<WORDS;w++) t.unc[w]&=~covered_by[c][w];
    BNB(t.sb,t.unc,1,t.pl);
}

static vector<int> solve_bnb(){
    vector<int> gs; int gv=greedy_solution(gs);
    bnb_best.store(gv,memory_order_relaxed); bnb_result=gs;

    vector<uint64_t> init_unc(WORDS,~0ULL);
    if(N%64) init_unc[WORDS-1]=(1ULL<<(N%64))-1;

    int root=first_set(init_unc);
    vector<Task> tasks;
    for(int w=0;w<WORDS;w++){uint64_t word=covered_by[root][w];
        while(word){int bit=__builtin_ctzll(word);word&=word-1;
            Task t; t.pn=w*64+bit;
            t.sb=vector<uint64_t>(WORDS,0ULL);
            t.unc=init_unc; t.pl=vector<int>(N,0);
            tasks.push_back(move(t));
        }
    }
    sort(tasks.begin(),tasks.end(),[](const Task&a,const Task&b){
        int sa=0,sb=0;
        for(int w=0;w<WORDS;w++){sa+=__builtin_popcountll(covered_by[a.pn][w]);sb+=__builtin_popcountll(covered_by[b.pn][w]);}
        return sa>sb;
    });

    const int MAX_T=min((int)tasks.size(),12);
    atomic<int> nxt(0); vector<thread> threads;
    auto worker=[&](){while(true){int i=nxt.fetch_add(1,memory_order_relaxed);if(i>=(int)tasks.size())break;thread_worker(move(tasks[i]));}};
    for(int t=0;t<MAX_T;t++) threads.emplace_back(worker);
    for(auto&t:threads) t.join();
    return bnb_result;
}

// ═══════════════════════════════════════════════════════════════
//  MAIN
// ═══════════════════════════════════════════════════════════════
int main(int argc,char* argv[]){
    ios::sync_with_stdio(false);
    ifstream fin(argv[1]); ofstream fout(argv[2]);
    fin>>N>>M;
    adj.assign(N,{}); WORDS=(N+63)/64;
    covered_by.assign(N,vector<uint64_t>(WORDS,0ULL));
    for(int v=0;v<N;v++) bit_set(covered_by[v],v);
    for(int i=0;i<M;i++){
        int u,v; fin>>u>>v;
        adj[u].push_back(v); adj[v].push_back(u);
        bit_set(covered_by[u],v); bit_set(covered_by[v],u);
    }

    vector<int> result; string method;

    if(is_forest()){
        method="Tree DP O(n)"; result=solve_tree();
    } else if(N<=25){
        method="Bitmask DP O(2^n)"; result=solve_bitmask();
    } else {
        method="Branch & Bound (multithreaded)"; result=solve_bnb();
    }

    // Safety: fix any uncovered node left by solver bugs
    vector<bool> powered(N,false);
    for(int v=0;v<N;v++) if(result[v]){powered[v]=true;for(int u:adj[v])powered[u]=true;}
    for(int v=0;v<N;v++) if(!powered[v]){result[v]=1;for(int u:adj[v])powered[u]=true;}

    int cnt=0; for(int v=0;v<N;v++) cnt+=result[v];

    cout<<"Minimum powerplant is: "<<cnt<<" ["<<method<<"]\n";
    fout<<"Minimum powerplant is: "<<cnt<<"\n";
    for(int v=0;v<N;v++){cout<<result[v];fout<<result[v];}
    cout<<"\n"; fout<<"\n";
    return 0;
}