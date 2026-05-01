#include <bits/stdc++.h>
using namespace std;

// ═══════════════════════════════════════════════════════════════
//  GLOBAL GRAPH DATA
// ═══════════════════════════════════════════════════════════════
static int N, M;
static constexpr int INF = 1e9;
static vector<vector<int>> adj;

static vector<vector<uint64_t>> covered_by;
static int WORDS;

// 🔥 NEW
static vector<int> color;
static bool is_bip;

// ═══════════════════════════════════════════════════════════════
//  BITSET HELPERS
// ═══════════════════════════════════════════════════════════════
static inline int first_set(const vector<uint64_t>& w){
    for(int i=0;i<WORDS;i++) if(w[i]) return i*64+__builtin_ctzll(w[i]);
    return -1;
}
static inline bool bit_test(const vector<uint64_t>& w,int v){return(w[v>>6]>>(v&63))&1;}
static inline void bit_set(vector<uint64_t>& w,int v){w[v>>6]|=(1ULL<<(v&63));}
static inline void bit_clear(vector<uint64_t>& w,int v){w[v>>6]&=~(1ULL<<(v&63));}

// ═══════════════════════════════════════════════════════════════
//  BIPARTITE DETECTION
// ═══════════════════════════════════════════════════════════════
static bool detect_bipartite(){
    color.assign(N,-1);
    for(int i=0;i<N;i++){
        if(color[i]!=-1) continue;
        queue<int> q;
        q.push(i);
        color[i]=0;
        while(!q.empty()){
            int u=q.front(); q.pop();
            for(int v:adj[u]){
                if(color[v]==-1){
                    color[v]=color[u]^1;
                    q.push(v);
                }else if(color[v]==color[u]){
                    return false;
                }
            }
        }
    }
    return true;
}

// ═══════════════════════════════════════════════════════════════
//  GREEDY
// ═══════════════════════════════════════════════════════════════
static int greedy_solution(vector<int>& out){
    vector<uint64_t> unc(WORDS,~0ULL);
    if(N%64) unc[WORDS-1] &= (1ULL<<(N%64))-1;

    out.assign(N,0);
    int cnt=0;

    while(true){
        int any=first_set(unc);
        if(any==-1) break;

        int best=-1,score=-1;
        for(int w=0;w<WORDS;w++){
            uint64_t word=covered_by[any][w];
            while(word){
                int bit=__builtin_ctzll(word);
                word&=word-1;
                int c=w*64+bit;

                int s=0;
                for(int ww=0;ww<WORDS;ww++)
                    s+=__builtin_popcountll(covered_by[c][ww]&unc[ww]);

                if(s>score){score=s;best=c;}
            }
        }

        out[best]=1;
        cnt++;
        for(int w=0;w<WORDS;w++)
            unc[w]&=~covered_by[best][w];
    }
    return cnt;
}

// ═══════════════════════════════════════════════════════════════
//  LOWER BOUND
// ═══════════════════════════════════════════════════════════════
static int lower_bound(const vector<uint64_t>& unc){
    vector<uint64_t> rem=unc;
    int lb=0;

    while(true){
        int v=first_set(rem);
        if(v==-1) break;
        lb++;

        for(int w=0;w<WORDS;w++){
            uint64_t word=covered_by[v][w];
            while(word){
                int bit=__builtin_ctzll(word);
                word&=word-1;
                int c=w*64+bit;

                for(int ww=0;ww<WORDS;ww++)
                    rem[ww]&=~covered_by[c][ww];
            }
        }
    }
    return lb;
}

// ═══════════════════════════════════════════════════════════════
//  BNB
// ═══════════════════════════════════════════════════════════════
static atomic<int> bnb_best;
static mutex bnb_mutex;
static vector<int> bnb_result;

static void BNB(vector<uint64_t>& sb,vector<uint64_t>& unc,int cnt,vector<int>& pl){
    if(cnt>=bnb_best.load()) return;
    if(cnt+lower_bound(unc)>=bnb_best.load()) return;

    int chosen=-1,score=INT_MAX;
    for(int w=0;w<WORDS && score>1;w++){
        uint64_t word=unc[w];
        while(word){
            int bit=__builtin_ctzll(word);
            word&=word-1;
            int v=w*64+bit;

            int s=0;
            for(int ww=0;ww<WORDS;ww++)
                s+=__builtin_popcountll(covered_by[v][ww]&~sb[ww]);

            if(s<score){score=s;chosen=v;}
        }
    }

    if(chosen==-1){
        int cur=bnb_best.load();
        if(cnt<cur){
            lock_guard<mutex> lk(bnb_mutex);
            if(cnt<bnb_best){
                bnb_best=cnt;
                bnb_result=pl;
            }
        }
        return;
    }

    // 🔥 High-degree shortcut
    if(is_bip && adj[chosen].size()>60){
        bit_set(sb,chosen);
        pl[chosen]=1;

        vector<uint64_t> nu(WORDS);
        for(int w=0;w<WORDS;w++)
            nu[w]=unc[w]&~covered_by[chosen][w];

        BNB(sb,nu,cnt+1,pl);

        bit_clear(sb,chosen);
        pl[chosen]=0;
        return;
    }

    vector<pair<int,int>> cands;

    for(int w=0;w<WORDS;w++){
        uint64_t word=covered_by[chosen][w];

        while(word){
            int bit=__builtin_ctzll(word);
            word&=word-1;

            int c=w*64+bit;
            if(bit_test(sb,c)) continue;

            // 🔥 Bipartite pruning
            if(is_bip){
                if(c!=chosen && color[c]==color[chosen]) continue;
            }

            int s=0;
            for(int ww=0;ww<WORDS;ww++)
                s+=__builtin_popcountll(covered_by[c][ww]&unc[ww]);

            cands.push_back({s,c});
        }
    }

    sort(cands.rbegin(),cands.rend());

    for(auto&[s,c]:cands){
        if(cnt+1>=bnb_best.load()) break;

        bit_set(sb,c);
        pl[c]=1;

        vector<uint64_t> nu(WORDS);
        for(int w=0;w<WORDS;w++)
            nu[w]=unc[w]&~covered_by[c][w];

        BNB(sb,nu,cnt+1,pl);

        bit_clear(sb,c);
        pl[c]=0;
    }
}

// ═══════════════════════════════════════════════════════════════
//  SOLVE BNB
// ═══════════════════════════════════════════════════════════════
static vector<int> solve_bnb(){
    vector<int> gs;
    int gv=greedy_solution(gs);

    bnb_best=gv;
    bnb_result=gs;

    vector<uint64_t> unc(WORDS,~0ULL);
    if(N%64) unc[WORDS-1] &= (1ULL<<(N%64))-1;

    vector<uint64_t> sb(WORDS,0ULL);
    vector<int> pl(N,0);

    BNB(sb,unc,0,pl);

    return bnb_result;
}

// ═══════════════════════════════════════════════════════════════
//  MAIN
// ═══════════════════════════════════════════════════════════════
int main(int argc,char* argv[]){
    ios::sync_with_stdio(false);

    ifstream fin(argv[1]);
    ofstream fout(argv[2]);

    fin>>N>>M;

    adj.assign(N,{});
    WORDS=(N+63)/64;
    covered_by.assign(N,vector<uint64_t>(WORDS,0ULL));

    for(int v=0;v<N;v++)
        bit_set(covered_by[v],v);

    for(int i=0;i<M;i++){
        int u,v; fin>>u>>v;
        adj[u].push_back(v);
        adj[v].push_back(u);
        bit_set(covered_by[u],v);
        bit_set(covered_by[v],u);
    }

    // 🔥 detect bipartite
    is_bip = detect_bipartite();

    vector<int> result = solve_bnb();

    int cnt=0;
    for(int v=0;v<N;v++) cnt+=result[v];

    cout<<"Minimum powerplant is: "<<cnt<<"\n";
    // fout<<"Minimum powerplant is: "<<cnt<<"\n";

    for(int v=0;v<N;v++){
        cout<<result[v];
        fout<<result[v];
    }
    cout<<"\n"; fout<<"\n";

    return 0;
}