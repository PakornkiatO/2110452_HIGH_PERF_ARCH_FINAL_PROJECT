#include<bits/stdc++.h>

using namespace std;

int n, best;
vector<int> best_state;

bool hasPower(int node, vector<int>& state, vector<vector<int>>& adj){
	if(state[node] == 1) return true;
	for(int adj_node: adj[node]){
		if(state[adj_node] == 1) return true;
	}
	return false;
}

void BNB(int count, vector<int>& state, vector<vector<int>>& adj){
	if(count >= best) return;

	int unpower_node = -1;
	for(int i = 0;i < n;i++){
		if(!hasPower(i, state, adj)){
			unpower_node = i;
			break;
		}
	}

	if(unpower_node == -1){
		if(count < best){
			best = count;
			best_state = state;
		}
		return;
	}

	state[unpower_node] = 1;
	BNB(count+1, state, adj);
	state[unpower_node] = -1;

	for(int adj_node: adj[unpower_node]){
		if(state[adj_node] == -1){
			state[adj_node] = 1;
			BNB(count+1, state, adj);
			state[adj_node] = -1;
		}
	}
}

int main(){
	int m;
	cin >> n >> m;
	best = n;

	vector<int>         state(n, -1);
	vector<vector<int>> adj(n);

	for(int i = 0;i < m;i++){
		int u, v; cin >> u >> v;
		adj[u].push_back(v);
		adj[v].push_back(u);
	}

	BNB(0, state, adj);

	cout << "Minimum popwerplant is: " << best << endl;
	for(int i: best_state) cout << i << " ";

//	for(int i = 0;i < n;i++){
//		cout << "Node " << i << " neighbors: ";
//		for(auto a: adj[i]){
//			cout << a << " "; 
//		}
//		cout << endl;
//	}
}
