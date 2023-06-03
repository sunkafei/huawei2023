//Author: ËïÃ÷Ö¾ Áºê»å¹ ÁÖ÷è
#define NDEBUG
#include <cstdio>
#include <cstring>
#include <algorithm>
#include <vector>
#include <queue>
#include <bitset>
#include <climits>
#include <map>
#include <tuple>
#include <cassert>
#include <iostream>
#include <ctime>
#include <random>
#include <set>
#include <unordered_set>
#include <chrono>
#include <list>
using namespace std;
#ifndef NDEBUG
const long long TIME_LIMIT = 115 * 1000;
#else
const long long TIME_LIMIT = 118 * 1000;
#endif
const int MAXN = 5005;
const int MAXM = 5005;
const int MAXT = 10005;
const int MAXP = 83;
const int INF = 0x3F3F3F3F;
const long long SEARCH_TIME = 0.6 * TIME_LIMIT;
const auto start_time = std::chrono::steady_clock::now();
int N, M, T, P, D;
vector<tuple<int, int, int>> graph;
vector<pair<int, int>> business;
#ifndef NDEBUG
template<typename T> void print(const T& sth) {
	cerr << "\033[1;31m" << sth << "\033[0m" << endl;
}
template<typename A, typename ...T> void print(const A& sth, const T& ...args) {
	cerr << "\033[1;31m" << sth << " \033[0m";
	print(args...);
}
template<typename T> void print(const vector<T>& vec) {
	cerr << "\033[1;31m[";
	for (auto x : vec)
		cerr << x << ' ';
	cerr << "]\033[0m\n";
}
#endif
template<typename T> class fast_queue {
private:
	static const int MAXSIZE = MAXP * (MAXN + MAXM);
	T* data;
	int from;
	int to;
public:
	fast_queue() {
		data = new T[MAXSIZE];
	}
	inline void push(T value) {
		data[to++] = value;
		assert(to <= MAXSIZE);
	}
	inline void pop() {
		++from;
		assert(from <= to);
	}
	inline T front() const {
		return data[from];
	}
	inline int size() const {
		return to - from;
	}
	inline bool empty() const {
		return to - from == 0;
	}
	inline void clear() {
		from = to = 0;
	}
	inline T* begin() {
		return data + from;
	}
	inline T* end() {
		return data + to;
	}
};
template<typename T> class fast_deque {
private:
	static const int MAXSIZE = MAXP * (MAXN + MAXM);
	T* data;
	int from;
	int to;
public:
	fast_deque() {
		data = new T[MAXSIZE * 2];
		data += MAXSIZE;
	}
	inline void push_back(T value) {
		data[to++] = value;
		assert(to < MAXSIZE);
	}
	inline void push_front(T value) {
		data[--from] = value;
		assert(from > -MAXSIZE);
	}
	inline void pop_back() {
		to -= 1;
		assert(from <= to);
	}
	inline void pop_front() {
		from += 1;
		assert(from <= to);
	}
	inline T front() const {
		return data[from];
	}
	inline T back() const {
		return data[to - 1];
	}
	inline int size() const {
		return to - from;
	}
	inline bool empty() const {
		return to - from == 0;
	}
	inline void clear() {
		from = to = 0;
	}
};
template<typename T> class darray {
private:
	T* data;
	int sz;
	int maxsize;
public:
	darray(const darray&) = delete;
	const darray& operator= (const darray&) = delete;
	darray() : data(nullptr), sz(0), maxsize(0) {}
	inline void init(const vector<T>& vec) {
		data = new T[vec.size()];
		maxsize = sz = vec.size();
	}
	inline void reserve(int upperbound) {
		if (upperbound > maxsize) {
			this->maxsize = upperbound;
			auto tmp = new T[maxsize];
			std::copy(data, data + sz, tmp);
			swap(tmp, data);
			delete[] tmp;
		}
	}
	inline int size() const {
		return sz;
	}
	inline void resize(int new_size) {
		sz = new_size;
		assert(sz <= maxsize);
	}
	inline void clear() {
		sz = 0;
	}
	inline void add(T val) {
		assert(sz < maxsize);
		data[sz++] = val;
	}
	inline void erase(T val) {
		int pos = -1;
		for (int i = 0; i < sz; ++i) {
			if (data[i] == val) {
				pos = i;
				break;
			}
		}
		assert(pos != -1);
		for (int i = pos + 1; i < sz; ++i) {
			data[i - 1] = data[i];
		}
		sz -= 1;
	}
	inline void copy(const vector<T>& vec) {
		sz = vec.size();
		std::copy(vec.begin(), vec.end(), data);
	}
	inline T& operator[] (int index) {
		return data[index];
	}
	inline const T& operator[] (int index) const {
		return data[index];
	}
	inline T* begin() {
		return data;
	}
	inline const T* begin() const {
		return data;
	}
	inline T* end() {
		return data + sz;
	}
	inline const T* end() const {
		return data + sz;
	}
};
inline auto runtime() {
	auto now = std::chrono::steady_clock::now();
	auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(now - start_time);
	return duration.count();
}
class bridger_t {
private:
	int N, M, P;
	vector<tuple<int, int, int>> graph;
	vector<pair<int, int>> business;
private:
	map<pair<int, int>, int> width, weight, aim;
	vector<int> G[MAXN];
	int pre[MAXN], low[MAXN], dfs_clock;
	set<pair<int, int>> bridges;
	int vis[MAXN];
public:
	vector<int> run(int N, int M, int P, vector<tuple<int, int, int>> graph, vector<pair<int, int>> business) {
		this->N = N;
		this->M = M;
		this->P = P;
		this->graph = graph;
		this->business = business;
		width.clear();
		for (int i = 0; i < N; ++i) {
			G[i].clear();
			pre[i] = low[i] = 0;
		}
		dfs_clock = 0;
		bridges.clear();
		for (int i = 0; i < graph.size(); ++i) {
			auto [s, t, d] = graph[i];
			if (s > t) swap(s, t);
			auto pr = make_pair(s, t);
			width[pr] += P;
			if (!weight.count(pr) || weight[pr] > d) {
				weight[pr] = d;
				aim[pr] = i;
			}
			G[s].push_back(t);
			G[t].push_back(s);
		}
		dfs(0, -1);
		for (auto [s, t] : business) {
			for (int i = 0; i < N; ++i)
				vis[i] = false;
			search(s, -1, t);
		}
		vector<int> ret;
		for (auto [pr, cover] : width) {
			if (cover < 0) {
				int e = aim[make_pair(pr.first, pr.second)];
				int times = (-cover - 1) / P + 1;
				for (int i = 0; i < times; ++i) {
					ret.emplace_back(e);
				}
			}
		}
		return ret;
	}
	int dfs(int u, int fa) {
		int lowu = pre[u] = ++dfs_clock;
		for (auto v : G[u]) {
			if (!pre[v]) {
				int lowv = dfs(v, u);
				lowu = min(lowu, lowv);
				if (lowv > pre[u]) {
					bridges.insert(make_pair(u, v));
					bridges.insert(make_pair(v, u));
				}
			}
			else if (pre[v] < pre[u] && v != fa) {
				lowu = min(lowu, pre[v]);
			}
		}
		low[u] = lowu;
		return lowu;
	}
	int search(int x, int fa, int t) {
		vis[x] = true;
		if (x == t) {
			return true;
		}
		for (auto y : G[x]) if (y != fa && !vis[y]) {
			if (search(y, x, t)) {
				if (x > y) swap(x, y);
				auto pr = make_pair(x, y);
				if (bridges.count(pr)) {
					width[pr] -= 1;
				}
				return true;
			}
		}
		return false;
	}
} bridger;
class cover_t {
private:
	darray<int> data[MAXP][MAXM];
public:
	inline void build(const vector<pair<int, vector<int>>>& paths) {
		for (int i = 0; i < P; ++i) {
			for (int j = 0; j < M; ++j) {
				data[i][j].clear();
			}
		}
		for (int i = 0; i < paths.size(); ++i) {
			const auto& [channel, path] = paths[i];
			for (auto e : path) {
				assert(e < M);
				data[channel][e].add(i);
			}
		}
	}
	inline void add(int channel, const vector<int>& path, int val) {
		for (auto x : path)
			data[channel][x].add(val);
	}
	inline void add(const pair<int, vector<int>>& pr, int val) {
		add(pr.first, pr.second, val);
	}
	inline void erase(int channel, const vector<int>& path, int val) {
		for (auto x : path)
			data[channel][x].erase(val);
	}
	inline void erase(const pair<int, vector<int>>& pr, int val) {
		erase(pr.first, pr.second, val);
	}
	inline auto operator[] (int index) {
		return data[index];
	}
};
class solver_t {
private:
	struct edge_t {
		int from;
		int to;
		int weight;
		vector<int> cap;
	};
	vector<edge_t> edges;
	vector<int> bridges;
	vector<pair<int, int>> G[MAXN];
	darray<pair<int, int>> E[MAXP][MAXN];
	int flow[MAXP][MAXM];
	int baseline[MAXN][MAXN];
	int component[MAXP][MAXN], changed[MAXP], component_index;
	cover_t cover;
	mt19937 engine;
public:
	solver_t() : engine(20140920) {}
	inline void preprocess() {
		static fast_queue<int> Q;
		for (int i = 0; i < N; ++i)
			G[i].clear();
		for (int i = 0; i < M; ++i) {
			auto [s, t, d] = graph[i];
			G[s].emplace_back(t, i);
			G[t].emplace_back(s, i);
		}
		for (int start = 0; start < N; ++start) {
			Q.clear();
			for (int i = 0; i < N; ++i) {
				baseline[start][i] = INF;
			}
			baseline[start][start] = 0;
			Q.push(start);
			while (Q.size()) {
				auto x = Q.front(); Q.pop();
				for (auto [y, e] : G[x]) {
					if (baseline[start][y] == INF) {
						baseline[start][y] = baseline[start][x] + 1;
						Q.push(y);
					}
				}
			}
		}
		for (int c = 0; c < P; ++c) {
			for (int i = 0; i < N; ++i) {
				E[c][i].init(G[i]);
			}
		}
		for (int c = 0; c < P; ++c) {
			for (int i = 0; i < M; ++i) {
				cover[c][i].reserve(2);
			}
		}
	}
	inline void init() {
		for (int i = 0; i < N; ++i)
			G[i].clear();
		memset(flow, 0, sizeof(flow));
		edges.resize(M);
		for (int i = 0; i < M; ++i) {
			auto [s, t, d] = graph[i];
			G[s].emplace_back(t, i);
			G[t].emplace_back(s, i);
			edges[i].from = s;
			edges[i].to = t;
			edges[i].weight = d;
			edges[i].cap = vector<int>(1, i);
		}
		for (int c = 0; c < P; ++c) {
			for (int i = 0; i < N; ++i) {
				E[c][i].copy(G[i]);
			}
		}
	}
	double congestion() const {
		double total = 0, occupy = 0;
		for (int c = 0; c < P; ++c) {
			for (int e = 0; e < M; ++e) {
				occupy += flow[c][e];
				total += edges[e].cap.size();
			}
		}
		return occupy / total;
	}
	inline void copy_edge(int e) {
		int ne = edges.size();
		edges[e].cap.push_back(ne);
		auto new_edge = edges[e];
		new_edge.cap.resize(1);
		edges.push_back(new_edge);
		const int size = edges[e].cap.size();
		for (int c = 0; c < P; ++c) {
			cover[c][e].reserve(size); //todo: ³¬ÄÚ´æ£¿
		}
	}
	inline void transform(vector<pair<int, vector<int>>>& paths) {
		memset(flow, 0, sizeof(flow));
		for (auto& [channel, path] : paths) {
			for (auto& e : path) {
				assert(e < M);
				int& f = flow[channel][e];
				e = edges[e].cap[f];
				f += 1;
			}
		}
	}
	inline void increase(int c, int e) {
		if (flow[c][e] == edges[e].cap.size()) {
			int from = edges[e].from;
			int to = edges[e].to;
			E[c][from].erase({ to, e });
			E[c][to].erase({ from, e });
		}
	}
	inline void decrease(int c, int e) {
		if (flow[c][e] + 1 == edges[e].cap.size()) {
			int from = edges[e].from;
			int to = edges[e].to;
			E[c][from].add({ to, e });
			E[c][to].add({ from, e });
		}
	}
	inline void undo(int channel, const vector<int>& path, int e = INF) {
		for (auto x : path) {
			assert(flow[channel][x] >= 1 && flow[channel][x] <= edges[x].cap.size() + (x == e));
			flow[channel][x] -= 1;
			decrease(channel, x);
		}
	}
	inline void undo(const pair<int, vector<int>>& pr, int e = INF) {
		undo(pr.first, pr.second, e);
	}
	inline void apply(int channel, const vector<int>& path, int e = INF) {
		for (auto x : path) {
			flow[channel][x] += 1;
			assert(flow[channel][x] >= 1 && flow[channel][x] <= edges[x].cap.size() + (x == e));
			increase(channel, x);
		}
	}
	inline void apply(const pair<int, vector<int>>& pr, int e = INF) {
		apply(pr.first, pr.second, e);
	}
	inline void build_residual_network() {
		for (int c = 0; c < P; ++c) {
			for (int x = 0; x < N; ++x) {
				E[c][x].copy(G[x]);
			}
		}
		for (int c = 0; c < P; ++c) {
			for (int x = 0; x < N; ++x) {
				int pos = 0;
				auto& vec = E[c][x];
				for (int i = 0; i < vec.size(); ++i) {
					int e = vec[i].second;
					assert(e >= 0 && e < M);
					if (flow[c][e] < edges[e].cap.size()) {
						vec[pos++] = vec[i];
					}
				}
				vec.resize(pos);
			}
		}
	}
	inline void check_residual_network() const {
		/*for (int c = 0; c < P; ++c) {
			for (int x = 0; x < N; ++x) {
				const auto &vec = E[c][x];
				vector<pair<int, int>> A(vec.begin(), vec.end());
				vector<pair<int, int>> B;
				for (auto [y, e] : G[x]) {
					assert(flow[c][e] <= edges[e].cap.size() + 1);
					if (flow[c][e] < edges[e].cap.size()) {
						B.push_back({ y, e });
					}
				}
				sort(A.begin(), A.end());
				sort(B.begin(), B.end());
				assert(A == B);
			}
		}*/
	}
	inline void simulate(const vector<pair<int, vector<int>>>& paths) {
		for (int i = 0; i < P; ++i) {
			for (int j = 0; j < M; ++j) {
				flow[i][j] = 0;
			}
		}
		for (int i = 0; i < paths.size(); ++i) {
			const auto& [channel, path] = paths[i];
			for (auto e : path) {
				flow[channel][e] += 1;
				assert(flow[channel][e] >= 1 && flow[channel][e] <= edges[e].cap.size() + 1);
			}
		}
		build_residual_network();
	}
	inline void shuffle_edges() {
		for (int i = 0; i < N; ++i)
			shuffle(G[i].begin(), G[i].end(), engine);
		build_residual_network();
	}
	inline void rebuild_component(int channel, int vertex, int id) {
		static fast_queue<int> Q; Q.clear();
		Q.push(vertex);
		component[channel][vertex] = id;
		while (!Q.empty()) {
			auto x = Q.front(); Q.pop();
			for (auto [y, e] : E[channel][x]) {
				if (component[channel][y] != id) {
					component[channel][y] = id;
					Q.push(y);
				}
			}
		}
	}
	inline void rebuild_component(int channel, const vector<int>& path, int start) {
		vector<int> vertices;
		vertices.reserve(path.size() + 1);
		int x = start;
		vertices.push_back(x);
		for (auto e : path) {
			assert(x == edges[e].from || x == edges[e].to);
			x = (x == edges[e].from ? edges[e].to : edges[e].from);
			vertices.push_back(x);
			component[channel][x] = -1;
		}
		for (auto x : vertices) {
			if (component[channel][x] == -1) {
				rebuild_component(channel, x, component_index++);
			}
		}
	}
	inline void rebuild_component(int channel, const vector<int>& path1, const vector<int>& path2, int start) {
		vector<int> vertices;
		vertices.reserve(path1.size() + path2.size() + 1);
		int x = start;
		vertices.push_back(x);
		for (auto e : path1) {
			assert(x == edges[e].from || x == edges[e].to);
			x = (x == edges[e].from ? edges[e].to : edges[e].from);
			vertices.push_back(x);
			component[channel][x] = -1;
		}
		x = start;
		for (auto e : path2) {
			assert(x == edges[e].from || x == edges[e].to);
			x = (x == edges[e].from ? edges[e].to : edges[e].from);
			vertices.push_back(x);
			component[channel][x] = -1;
		}
		for (auto x : vertices) {
			if (component[channel][x] == -1) {
				rebuild_component(channel, x, component_index++);
			}
		}
	}
	inline void rebuild_component(int channel) {
		for (int x = 0; x < N; ++x) {
			component[channel][x] = -1;
		}
		for (int x = 0; x < N; ++x) {
			if (component[channel][x] == -1) {
				rebuild_component(channel, x, component_index++);
			}
		}
		changed[channel] = false;
	}
	inline void build_components() {
		component_index = 0;
		for (int c = 0; c < P; ++c) {
			for (int x = 0; x < N; ++x) {
				component[c][x] = -1;
			}
		}
		for (int c = 0; c < P; ++c) {
			for (int x = 0; x < N; ++x) {
				if (component[c][x] == -1) {
					rebuild_component(c, x, component_index++);
				}
			}
		}
		for (int i = 0; i < P; ++i)
			changed[i] = false;
	}
	pair<int, vector<int>> dijkstra(int start, int terminate) {
		static double dist[MAXP][MAXN];
		static pair<int, int> parent[MAXP][MAXN];
		for (int i = 0; i < P; ++i) {
			for (int j = 0; j < N; ++j) {
				dist[i][j] = 1e100;
			}
		}
		using node = pair<double, int>;
		priority_queue<node, vector<node>, greater<node>> Q;
		for (int i = 0; i < P; ++i) {
			dist[i][start] = 0;
			Q.push({ dist[i][start], (start << 8) + i });
		}
		int channel = -1;
		while (!Q.empty()) {
			auto [distance, state] = Q.top(); Q.pop();
			int c = state & 0xFF, x = state >> 8;
			if (distance != dist[c][x])
				continue;
			if (x == terminate) {
				channel = c;
				break;
			}
			for (auto [y, e] : G[x]) {
				double w = (double)edges[e].weight / D * 100 + 1 + 1e6 * (flow[c][e] >= edges[e].cap.size());
				if (dist[c][y] > dist[c][x] + w) {
					dist[c][y] = dist[c][x] + w;
					Q.push({ dist[c][y], (y << 8) + c });
					parent[c][y] = { x, e };
				}
			}
		}
		assert(channel >= 0);
		vector<int> path;
		int x = terminate;
		while (x != start) {
			int e = parent[channel][x].second;
			path.push_back(e);
			x = parent[channel][x].first;
		}
		reverse(path.begin(), path.end());
		return { channel, path };
	}
	pair<int, vector<int>> bfs(int start, int terminate) {
		static int dist[MAXP][MAXN];
		static pair<int, int> parent[MAXP][MAXN];
		static fast_queue<pair<int, int>> A, B, C; A.clear(); B.clear(); C.clear();
		for (int i = 0; i < P; ++i) {
			for (int j = 0; j < N; ++j) {
				dist[i][j] = INF;
			}
		}
		for (int i = 0; i < P; ++i) {
			dist[i][start] = 0;
			A.push({ dist[i][start], (start << 8) + i });
		}
		for (;;) {
			if (A.empty() && C.empty()) {
				swap(A, B);
			}
			int distance, state;
			if (C.empty() || (!A.empty() && A.front().first < C.front().first)) {
				tie(distance, state) = A.front();
				A.pop();
			}
			else {
				tie(distance, state) = C.front();
				C.pop();
			}
			int c = state & 0xFF, x = state >> 8;
			if (distance != dist[c][x])
				continue;
			if (x == terminate) {
				break;
			}
			for (auto [y, e] : G[x]) {
				int w = (flow[c][e] >= edges[e].cap.size()) * (MAXT + MAXM) + 1;
				assert(w > 0);
				if (dist[c][y] > dist[c][x] + w) {
					dist[c][y] = dist[c][x] + w;
					parent[c][y] = { x, e };
					if (w == 1) {
						C.push({ dist[c][y], (y << 8) + c });
					}
					else {
						B.push({ dist[c][y], (y << 8) + c });
					}
				}
			}
		}
		int channel = 0;
		for (int i = 0; i < P; ++i) {
			if (dist[i][terminate] < dist[channel][terminate]) {
				channel = i;
			}
		}
		vector<int> path;
		int x = terminate;
		while (x != start) {
			int e = parent[channel][x].second;
			path.push_back(e);
			x = parent[channel][x].first;
		}
		reverse(path.begin(), path.end());
		return { channel, path };
	}
	pair<int, vector<int>> bidirectional_bfs(int start, int terminate) {
		static int dist1[MAXP][MAXN], dist2[MAXP][MAXN];
		static int vis1[MAXP][MAXN], vis2[MAXP][MAXN];
		static int timestamp[MAXP][MAXN], id = 1; id += 1;
		static pair<int, int> parent1[MAXP][MAXN], parent2[MAXP][MAXN];
		static fast_queue<pair<int, int>> A1, B1, C1, A2, B2, C2;
		A1.clear(); B1.clear(); C1.clear(); A2.clear(); B2.clear(); C2.clear();
		int channel = -1, middle = -1;
		for (int i = 0; i < P; ++i) {
			dist1[i][start] = 0;
			dist2[i][start] = INF;
			vis1[i][start] = false;
			vis2[i][start] = false;
			timestamp[i][start] = id;
			A1.push({ 0, (start << 8) + i });

			dist1[i][terminate] = INF;
			dist2[i][terminate] = 0;
			vis1[i][terminate] = false;
			vis2[i][terminate] = false;
			timestamp[i][terminate] = id;
			A2.push({ 0, (terminate << 8) + i });
		}
		for (;;) {
			if (A1.empty() && C1.empty()) {
				if (B1.empty())
					break;
				swap(A1, B1);
			}
			if (A2.empty() && C2.empty()) {
				if (B2.empty())
					break;
				swap(A2, B2);
			}
			fast_queue<pair<int, int>>* Q1, * Q2;
			if (C1.empty() || (!A1.empty() && A1.front().first < C1.front().first)) {
				Q1 = &A1;
			}
			else {
				Q1 = &C1;
			}
			if (C2.empty() || (!A2.empty() && A2.front().first < C2.front().first)) {
				Q2 = &A2;
			}
			else {
				Q2 = &C2;
			}
			if (Q1->front() < Q2->front()) {
				fast_queue<pair<int, int>>& Q = *Q1;
				auto [distance, state] = Q.front(); Q.pop();
				int c = state & 0xFF, x = state >> 8;
				if (distance != dist1[c][x])
					continue;
				vis1[c][x] = true;
				if (vis2[c][x]) {
					channel = c;
					middle = x;
					while (A1.size()) {
						auto [_, state] = A1.front(); A1.pop();
						int c = state & 0xFF, x = state >> 8;
						auto delta = dist1[c][x] + dist2[c][x] - (dist1[channel][middle] + dist2[channel][middle]);
						if (delta > 0)
							continue;
						if (delta < 0 || c < channel) {
							channel = c;
							middle = x;
						}
					}
					while (C1.size()) {
						auto [_, state] = C1.front(); C1.pop();
						int c = state & 0xFF, x = state >> 8;
						auto delta = dist1[c][x] + dist2[c][x] - (dist1[channel][middle] + dist2[channel][middle]);
						if (delta > 0)
							continue;
						if (delta < 0 || c < channel) {
							channel = c;
							middle = x;
						}
					}
					break;
				}
				for (auto [y, e] : G[x]) {
					int w = (flow[c][e] >= edges[e].cap.size()) * (MAXT + MAXM) + 1;
					assert(w > 0);
					if (timestamp[c][y] != id) {
						timestamp[c][y] = id;
						dist1[c][y] = dist2[c][y] = INF;
						vis1[c][y] = vis2[c][y] = false;
					}
					if (dist1[c][y] > dist1[c][x] + w) {
						dist1[c][y] = dist1[c][x] + w;
						parent1[c][y] = { x, e };
						if (w == 1) {
							C1.push({ dist1[c][y], (y << 8) + c });
						}
						else {
							B1.push({ dist1[c][y], (y << 8) + c });
						}
					}
				}
			}
			else {
				fast_queue<pair<int, int>>& Q = *Q2;
				auto [distance, state] = Q.front(); Q.pop();
				int c = state & 0xFF, x = state >> 8;
				if (distance != dist2[c][x])
					continue;
				vis2[c][x] = true;
				if (vis1[c][x]) {
					channel = c;
					middle = x;
					while (A2.size()) {
						auto [_, state] = A2.front(); A2.pop();
						int c = state & 0xFF, x = state >> 8;
						auto delta = dist1[c][x] + dist2[c][x] - (dist1[channel][middle] + dist2[channel][middle]);
						if (delta > 0)
							continue;
						if (delta < 0 || c < channel) {
							channel = c;
							middle = x;
						}
					}
					while (C2.size()) {
						auto [_, state] = C2.front(); C2.pop();
						int c = state & 0xFF, x = state >> 8;
						auto delta = dist1[c][x] + dist2[c][x] - (dist1[channel][middle] + dist2[channel][middle]);
						if (delta > 0)
							continue;
						if (delta < 0 || c < channel) {
							channel = c;
							middle = x;
						}
					}
					break;
				}
				for (auto [y, e] : G[x]) {
					int w = (flow[c][e] >= edges[e].cap.size()) * (MAXT + MAXM) + 1;
					assert(w > 0);
					assert(w > 0);
					if (timestamp[c][y] != id) {
						timestamp[c][y] = id;
						dist1[c][y] = dist2[c][y] = INF;
						vis1[c][y] = vis2[c][y] = false;
					}
					if (dist2[c][y] > dist2[c][x] + w) {
						dist2[c][y] = dist2[c][x] + w;
						parent2[c][y] = { x, e };
						if (w == 1) {
							C2.push({ dist2[c][y], (y << 8) + c });
						}
						else {
							B2.push({ dist2[c][y], (y << 8) + c });
						}
					}
				}
			}
		}
		assert(channel != -1);
		vector<int> path;
		int x = middle;
		while (x != start) {
			int e = parent1[channel][x].second;
			path.push_back(e);
			x = parent1[channel][x].first;
		}
		reverse(path.begin(), path.end());
		x = middle;
		while (x != terminate) {
			int e = parent2[channel][x].second;
			path.push_back(e);
			x = parent2[channel][x].first;
		}
#ifndef NDEBUG
		x = start;
		for (auto e : path) {
			assert(x == edges[e].from || x == edges[e].to);
			if (x == edges[e].from)
				x = edges[e].to;
			else
				x = edges[e].from;
		}
		assert(x == terminate);
#endif
		return { channel, path };
	}
	pair<int, vector<int>> connectivity(int start, int terminate, int direction = 0, int limit = INF) {
		static int timestamp[MAXP][MAXN], id = 1; id += 1;
		static pair<int, int> parent[MAXP][MAXN];
		static fast_queue<pair<int, int>> Q1, Q2; Q1.clear(); Q2.clear();
		if (direction == 0) {
			for (int i = 0; i < P; ++i) {
				timestamp[i][start] = id;
				Q1.push({ i, start });
			}
		}
		else {
			for (int i = P - 1; i >= 0; --i) {
				timestamp[i][start] = id;
				Q1.push({ i, start });
			}
		}
		int channel = -1, distance = 0;
		for (;;) {
			while (Q1.size()) {
				auto [c, x] = Q1.front(); Q1.pop();
				for (auto [y, e] : E[c][x]) {
					assert(flow[c][e] < edges[e].cap.size());
					if (timestamp[c][y] != id) {
						timestamp[c][y] = id;
						if (1 + distance + baseline[y][terminate] <= limit) {
							parent[c][y] = { x, e };
							if (y == terminate) {
								channel = c;
								goto finish;
							}
							else {
								Q2.push({ c, y });
							}
						}
					}
				}
			}
			if (Q2.empty()) {
				break;
			}
			else {
				swap(Q1, Q2);
				distance += 1;
			}
		}
	finish:
		if (channel == -1) {
			return { -1, vector<int>() };
		}
		const int length = distance + 1;
		vector<int> path(length);
		int x = terminate, index = length - 1;
		while (x != start) {
			int e = parent[channel][x].second;
			path[index--] = e;
			x = parent[channel][x].first;
		}
		assert(index == -1);
		return { channel, path };
	}
	pair<int, vector<int>> fast_connectivity(int start, int terminate, int direction = 0, int limit = INF) {
		static int timestamp[MAXP][MAXN], id = 1; id += 1;
		static pair<int, int> parent[MAXP][MAXN];
		static fast_queue<pair<int, int>> Q1, Q2; Q1.clear(); Q2.clear();
		if (direction == 0) {
			for (int i = 0; i < P; ++i) if (changed[i] || component[i][start] == component[i][terminate]) {
				timestamp[i][start] = id;
				Q1.push({ i, start });
			}
		}
		else {
			for (int i = P - 1; i >= 0; --i) if (changed[i] || component[i][start] == component[i][terminate]) {
				timestamp[i][start] = id;
				Q1.push({ i, start });
			}
		}
		int channel = -1, distance = 0;
		for (;;) {
			while (Q1.size()) {
				auto [c, x] = Q1.front(); Q1.pop();
				for (auto [y, e] : E[c][x]) {
					assert(flow[c][e] < edges[e].cap.size());
					if (timestamp[c][y] != id) {
						timestamp[c][y] = id;
						if (1 + distance + baseline[y][terminate] <= limit) {
							parent[c][y] = { x, e };
							if (y == terminate) {
								channel = c;
								goto finish;
							}
							else {
								Q2.push({ c, y });
							}
						}
					}
				}
			}
			if (Q2.empty()) {
				break;
			}
			else {
				swap(Q1, Q2);
				distance += 1;
			}
		}
	finish:
		if (channel == -1) {
			return { -1, vector<int>() };
		}
		const int length = distance + 1;
		vector<int> path(length);
		int x = terminate, index = length - 1;
		while (x != start) {
			int e = parent[channel][x].second;
			path[index--] = e;
			x = parent[channel][x].first;
		}
		assert(index == -1);
		return { channel, path };
	}
	pair<int, vector<int>> Astar(int start, int terminate, int direction = 0, int limit = INF) {
		static int dist[MAXP][MAXN], timestamp[MAXP][MAXN], id = 1; id += 1;
		static pair<int, int> parent[MAXP][MAXN];
		static fast_deque<pair<int, int>> A, B1, B2, C; A.clear(); B1.clear(); B2.clear(); C.clear();
		if (direction == 0) {
			for (int i = 0; i < P; ++i) {
				dist[i][start] = 0;
				timestamp[i][start] = id;
				A.push_front({ start | (i << 20), dist[i][start] });
			}
		}
		else {
			for (int i = 0; i < P; ++i) {
				dist[i][start] = 0;
				timestamp[i][start] = id;
				A.push_back({ start | (i << 20), dist[i][start] });
			}
		}
		int channel = -1;
		while (A.size() || B1.size() || B2.size() || C.size()) {
			while (A.empty()) {
				A.clear();
				if (direction == 0) {
					while (B1.size() && B2.size()) {
						if (B1.front() < B2.front()) {
							A.push_front(B1.front());
							B1.pop_front();
						}
						else {
							A.push_front(B2.front());
							B2.pop_front();
						}
					}
				}
				else {
					while (B1.size() && B2.size()) {
						if (B1.front() > B2.front()) {
							A.push_front(B1.front());
							B1.pop_front();
						}
						else {
							A.push_front(B2.front());
							B2.pop_front();
						}
					}
				}
				while (B1.size()) {
					A.push_front(B1.front());
					B1.pop_front();
				}
				while (B2.size()) {
					A.push_front(B2.front());
					B2.pop_front();
				}
				B1.clear();
				B2.clear();
				swap(B2, C);
			}
			auto [state, distance] = A.back(); A.pop_back();
			int c = state >> 20, x = state & 0xFFFFF;
			if (distance != dist[c][x]) {
				continue;
			}
			if (x == terminate) {
				channel = c;
				break;
			}
			int base = dist[c][x] + baseline[x][terminate];
			for (auto [y, e] : G[x]) if (flow[c][e] < edges[e].cap.size()) {
				//assert(flow[c][e] < edges[e].cap.size());
				if (timestamp[c][y] != id) {
					timestamp[c][y] = id;
					dist[c][y] = INF;
				}
				if (dist[c][y] > dist[c][x] + 1) {
					dist[c][y] = dist[c][x] + 1;
					parent[c][y] = { x, e };
					int estimate = dist[c][y] + baseline[y][terminate];
					if (estimate > limit)
						continue;
					if (estimate == base) {
						A.push_back({ y | (c << 20), dist[c][y] });
					}
					else if (estimate == base + 1) {
						B1.push_back({ y | (c << 20), dist[c][y] });
					}
					else {
						assert(estimate == base + 2);
						C.push_back({ y | (c << 20), dist[c][y] });
					}
				}
			}
		}
		if (channel == -1) {
			return { -1, vector<int>() };
		}
		const int length = dist[channel][terminate];
		vector<int> path(length);
		int x = terminate, index = length - 1;
		while (x != start) {
			int e = parent[channel][x].second;
			path[index--] = e;
			x = parent[channel][x].first;
		}
		assert(index == -1);
		return { channel, path };
	}
	long long calculate(vector<pair<int, vector<int>>> paths, bool output = false) {
		int Y = edges.size() - M;
		if (output) {
			transform(paths);
			printf("%d\n", Y);
			for (int i = M; i < edges.size(); ++i) {
				printf("%d %d\n", edges[i].from, edges[i].to);
			}
		}
		long long answer = Y * 1e6;
		for (int i = 0; i < T; ++i) {
			const auto& [channel, path] = paths[i];
			vector<int> amplifier, nodes;
			int sum = 0, x = business[i].first;
			nodes.push_back(x);
			for (auto e : path) {
				if (sum + edges[e].weight > D) {
					amplifier.push_back(x);
					sum = 0;
				}
				sum += edges[e].weight;
				assert(x == edges[e].from || x == edges[e].to);
				x = (x == edges[e].from ? edges[e].to : edges[e].from);
				nodes.push_back(x);
			}
			assert(x == business[i].second);
			if (output) {
				printf("%d %d %d", channel, (int)path.size(), (int)amplifier.size());
				for (auto e : path) {
					printf(" %d", e);
				}
				for (auto a : amplifier) {
					printf(" %d", a);
				}
				printf("\n");
			}
			answer += path.size() + (amplifier.size() * 100) * output;
#ifndef NDEBUG
			//print(channel);
			//print(nodes);
#endif
		}
		return answer;
	}
	int shrink(vector<pair<int, vector<int>>>& paths, int direction = 0, int time_limit = SEARCH_TIME) {
		if (runtime() >= time_limit)
			return 0;
		simulate(paths);
#ifndef NDEBUG
		check_residual_network();
#endif
		cover.build(paths);
		vector<int> removed(edges.size());
		vector<int> new_edges;
		for (int i = M + bridges.size(); i < edges.size(); ++i) {
			int e = edges[i].cap.front();
			if (i == edges[e].cap.back()) {
				new_edges.push_back(i);
			}
		}
		shuffle(new_edges.begin(), new_edges.end(), engine);
		build_components(); //todo
		for (auto i : new_edges) {
			if (runtime() >= time_limit)
				break;
			int from = edges[i].from, to = edges[i].to;
			int e = edges[i].cap.front();
			assert(i == edges[e].cap.back());
			edges[e].cap.pop_back();
			bool ok = true;
			vector<pair<int, pair<int, vector<int>>>> operations;
			for (int j = 0; j < P; ++j) {
				increase(j, e);
				changed[j] = 0;
			}
#ifndef NDEBUG
			check_residual_network();
#endif
			for (int j = 0; j < P; ++j) {
				if (cover[j][e].size() > edges[e].cap.size()) {
					assert(cover[j][e].size() == edges[e].cap.size() + 1);
					bool flag = false;
					for (auto q : cover[j][e]) {
						if (runtime() >= time_limit)
							break;
						const auto& path = paths[q];
						undo(path, e);
						changed[path.first] += 1;
#ifndef NDEBUG
						check_residual_network();
#endif
						auto [s, t] = business[q];
						auto new_path = fast_connectivity(s, t, direction);
#ifndef NDEBUG
						//auto tmp = connectivity(s, t, direction);
						//assert(tmp == new_path);
#endif
						if (new_path.first == -1) {
							apply(path, e);
							changed[path.first] -= 1;
						}
						else {
							apply(new_path);
#ifndef NDEBUG
							check_residual_network();
#endif
							operations.emplace_back(q, move(new_path));
							flag = true;
							break;
						}
					}
					ok &= flag;
				}
				if (!ok) {
					while (operations.size()) {
						const auto& [q, new_path] = operations.back();
						undo(new_path);
						apply(paths[q], e);
						operations.pop_back();
#ifndef NDEBUG
						check_residual_network();
#endif
					}
					break;
				}
			}
			if (ok) {
				removed[i] = true;
				int vis[MAXP] = {};
				for (int j = 0; j < operations.size(); ++j) {
					const auto& [q, new_path] = operations[j];
					const auto& [channel, path] = paths[q];
					const auto& [channel2, path2] = new_path;
					cover.erase(channel, path, q);
					cover.add(channel2, path2, q);
					paths[q] = new_path;
					vis[channel] = vis[channel2] = true;
				}
				for (int c = 0; c < P; ++c) if (vis[c] || flow[c][e] >= edges[e].cap.size())
					rebuild_component(c);
			}
			else {
				edges[e].cap.push_back(i);
				for (int j = 0; j < P; ++j) {
					decrease(j, e);
				}
#ifndef NDEBUG
				check_residual_network();
#endif
			}
		}
		int pos = 0;
		for (int i = 0; i < edges.size(); ++i) {
			if (!removed[i]) {
				edges[pos++] = edges[i];
			}
		}
		edges.resize(pos);
		vector<int> sum(removed.size());
		for (int i = 1; i < removed.size(); ++i)
			sum[i] = sum[i - 1] + removed[i];
		for (auto& edge : edges) {
			for (auto& e : edge.cap) {
				assert(!removed[e]);
				e -= sum[e];
			}
		}
		return sum.back();
	}
	int pile(vector<pair<int, vector<int>>>& paths, int direction = 0, bool random_shuffle = false, int time_limit = SEARCH_TIME) {
		if (random_shuffle) {
			shuffle_edges();
		}
		else {
			build_residual_network();
		}
		vector<int> indices(business.size());
		for (int i = 0; i < business.size(); ++i) {
			indices[i] = i;
		}
		shuffle(indices.begin(), indices.end(), engine);
		build_components(); //todo: move to flip
		for (auto i : indices) if (paths[i].second.size()) {
			if (runtime() >= time_limit)
				return false;
			const auto& [channel, path] = paths[i];
			undo(channel, path);
			changed[channel] = true;
			auto [s, t] = business[i];
			auto [channel2, path2] = fast_connectivity(s, t, direction, path.size());
			assert(channel2 != -1);
#ifndef NDEBUG
			//auto [A, B] = connectivity(s, t, direction, path.size());
			//assert(A == channel2 && B == path2);
#endif
			apply(channel2, path2);
			changed[channel] = false;
			if (channel != channel2) {
				rebuild_component(channel, path, business[i].first);
				rebuild_component(channel2, path2, business[i].first);
			}
			else if (path != path2) {
				rebuild_component(channel, path, path2, business[i].first);
			}
			paths[i] = make_pair(channel2, move(path2));
#ifndef NDEBUG
			check_residual_network();
#endif
		}
		return shrink(paths, direction, time_limit);
	}
	void flip(vector<pair<int, vector<int>>>& paths, int time_limit = SEARCH_TIME) {
		int direction = 0;
		int last = 0;
		simulate(paths);
		for (int t = 0; ;++t) {
			if (runtime() >= time_limit)
				break;
			direction ^= 1;
			int removed = pile(paths, direction, true, time_limit);
			if (removed) {
				last = t;
			}
			if (t - last > 10) {
				break;
			}
		}
	}
	vector<int> find_conflicts(int start, int terminate) {
		static int mark[MAXT];
		static int timestamp[MAXP][MAXN];
		static int id = 1; id += 1;
		static fast_queue<pair<int, int>> Q; Q.clear();
		vector<int> conflicts;
		for (int i = 0; i < P; ++i) {
			timestamp[i][start] = id;
			Q.push({ i, start });
		}
		while (Q.size()) {
			auto [c, x] = Q.front(); Q.pop();
			for (auto [y, e] : G[x]) {
				if (timestamp[c][y] != id) {
					if (flow[c][e] < edges[e].cap.size()) {
						timestamp[c][y] = id;
						Q.push({ c, y });
					}
					else {
						for (auto q : cover[c][e]) {
							mark[q] = id;
						}
					}
				}
			}
		}
		for (int i = 0; i < P; ++i) {
			if (timestamp[i][terminate] == id) {
				return vector<int>(1, -1);
			}
		}
		assert(Q.empty());
		for (int i = 0; i < P; ++i) {
			timestamp[i][terminate] = id;
			Q.push({ i, terminate });
		}
		while (Q.size()) {
			auto [c, x] = Q.front(); Q.pop();
			for (auto [y, e] : G[x]) {
				if (timestamp[c][y] != id) {
					if (flow[c][e] < edges[e].cap.size()) {
						timestamp[c][y] = id;
						Q.push({ c, y });
					}
					else {
						for (auto q : cover[c][e]) if (mark[q] == id) {
							conflicts.push_back(q);
							mark[q] = 0;
						}
					}
				}
			}
		}
		return conflicts;
	}
	void squeeze(vector<pair<int, vector<int>>>& backup, int time_limit = SEARCH_TIME) {
		vector<int> count(M);
		vector<int> all_edges(M);
		for (int i = 0; i < M; ++i)
			all_edges[i] = i;
		shuffle(all_edges.begin(), all_edges.end(), engine);
		int direction = 0;
		while (runtime() < time_limit) {
			for (auto e : all_edges) if (edges[e].cap.size() > 1) {
				direction ^= 1;
				simulate(backup);
				pile(backup, direction, true, time_limit);
				if (edges[e].cap.size() <= 1)
					continue;
				auto paths = backup;
				int direction = 0, last = 0;
				int i = edges[e].cap.back();
				list<int> indices;
				vector<int> others;
				if (runtime() >= time_limit)
					goto ret;
				edges[e].cap.pop_back();
				simulate(paths);
				build_components();
				others.reserve(paths.size());
				for (int j = 0; j < paths.size(); ++j) {
					if (runtime() >= time_limit)
						goto finish;
					const auto& [channel, path] = paths[j];
					for (auto x : path) {
						if (x == e && flow[channel][e] > edges[e].cap.size()) {
							indices.push_back(j);
							undo(channel, path, e);
							rebuild_component(channel, path, business[j].first);
							paths[j] = { -1, vector<int>() };
							goto end;
						}
					}
					others.push_back(j);
				end:;
				}
				for (auto iter = indices.begin(); iter != indices.end(); ) {
					if (runtime() >= time_limit)
						goto finish;
					int k = *iter;
					auto start = business[k].first, terminate = business[k].second;
					auto [c, p] = fast_connectivity(start, terminate);
					if (c != -1) {
						apply(c, p);
						rebuild_component(c, p, start);
						others.push_back(k);
						paths[k] = make_pair(c, move(p));
						iter = indices.erase(iter);
					}
					else {
						++iter;
					}
				}
				for (int t = 0; t < 30 && indices.size(); ++t) {
					shuffle_edges();
					shuffle(others.begin(), others.end(), engine);
					direction ^= 1;
					for (auto j : others) {
						if (runtime() >= time_limit)
							goto finish;
						if (indices.empty())
							break;
						int channel = paths[j].first;
						const auto& path = paths[j].second;
						undo(channel, path);
						changed[channel] = true;
						auto [channel2, path2] = fast_connectivity(business[j].first, business[j].second, direction, path.size());
						assert(channel2 != -1);
						apply(channel2, path2);
						changed[channel] = false;
						bool ok = true;
						if (channel != channel2) {
							rebuild_component(channel, path, business[j].first);
							rebuild_component(channel2, path2, business[j].first);
						}
						else if (path != path2) {
							rebuild_component(channel, path, path2, business[j].first);
						}
						else {
							ok = false;
						}
						if (!ok)
							continue;
						paths[j] = make_pair(channel2, move(path2));
						for (auto iter = indices.begin(); iter != indices.end(); ) {
							int k = *iter;
							auto start = business[k].first, terminate = business[k].second;
							if (component[channel][start] == component[channel][terminate]) {
								if (runtime() >= time_limit)
									goto finish;
								auto [c, p] = fast_connectivity(start, terminate);
								assert(c == channel);
								apply(c, p);
								rebuild_component(c, p, start);
								others.push_back(k);
								paths[k] = make_pair(c, move(p));
								iter = indices.erase(iter);
								last = t;
							}
							else {
								++iter;
							}
						}
#ifndef NDEBUG
						assert(others.size() + indices.size() == paths.size());
						/*for (auto k : indices) {
							for (int c = 0; c < P; ++c) {
								if (component[c][business[k].first] == component[c][business[k].second]) {
									print(channel, channel2, c);
									print(business[k].first, business[k].second, component[c][business[k].first], component[c][business[k].second]);
									abort();
								}
							}
						}*/
#endif
					}
					cover.build(paths);
					for (auto iter = indices.begin(); iter != indices.end(); ) {
						int k = *iter;
						int ex = k;
						bool ok = false;
						auto conflicts = find_conflicts(business[k].first, business[k].second);
						for (auto q : conflicts) {
							if (q == -1) {
								auto [c, p] = fast_connectivity(business[k].first, business[k].second);
								assert(c != -1);
								apply(c, p);
								rebuild_component(c, p, business[k].first);
								cover.add(c, p, k);
								others.push_back(k);
								paths[k] = make_pair(c, move(p));
								iter = indices.erase(iter);
								ok = true;
								goto next;
							}
							undo(paths[q]);
							changed[paths[q].first] = true;
							auto new_path = fast_connectivity(business[k].first, business[k].second);
							assert(new_path.first != -1);
							apply(new_path);
							auto replaced_path = fast_connectivity(business[q].first, business[q].second);
							changed[paths[q].first] = false;
							if (replaced_path.first != -1) {
								cover.erase(paths[q], q);
								cover.add(replaced_path, q);
								cover.add(new_path, k);
								apply(replaced_path);
								rebuild_component(paths[q].first, paths[q].second, business[q].first);
								rebuild_component(new_path.first, new_path.second, business[k].first);
								rebuild_component(replaced_path.first, replaced_path.second, business[q].first);
								others.push_back(k);
								paths[k] = move(new_path);
								paths[q] = move(replaced_path);
								iter = indices.erase(iter);
								last = t;
								ok = true;
								goto next;
							}
							else {
								undo(new_path);
								apply(paths[q]);
								if (baseline[business[q].first][business[q].second] < baseline[business[ex].first][business[ex].second])
									ex = q;
							}
						}
					next:
						if (!ok) {
							if (ex != k) {
								undo(paths[ex]);
								rebuild_component(paths[ex].first, paths[ex].second, business[ex].first);
								auto new_path = fast_connectivity(business[k].first, business[k].second);
								assert(new_path.first != -1);
								apply(new_path);
								rebuild_component(new_path.first, new_path.second, business[k].first);
								cover.erase(paths[ex], ex);
								cover.add(new_path, k);
								paths[k] = move(new_path);
								paths[ex] = { -1, vector<int>() };
								*iter = ex;
								auto tmp = find(others.begin(), others.end(), ex);
								assert(tmp != others.end());
								*tmp = k;
							}
							++iter;
						}
					}
					for (auto iter = indices.begin(); iter != indices.end(); ) {
						int k = *iter;
						auto start = business[k].first, terminate = business[k].second;
						for (int c = 0; c < P; ++c) {
							if (component[c][start] == component[c][terminate]) {
								auto new_path = fast_connectivity(start, terminate);
								assert(new_path.first != -1);
								apply(new_path);
								rebuild_component(new_path.first, new_path.second, start);
								others.push_back(k);
								paths[k] = move(new_path);
								iter = indices.erase(iter);
								last = t;
								goto next_loop;
							}
						}
						++iter;
					next_loop:;
					}
					if (t - last >= 2 && indices.size() >= 4 || t >= 10 && indices.size() >= 3 || t >= 20 && indices.size() > 1)
						break;
				}
				count[e] = indices.size();
				if (indices.empty()) {
					for (auto& edge : edges) {
						for (auto& x : edge.cap) {
							x -= (x > i);
						}
					}
					edges.erase(edges.begin() + i);
					backup = paths;
					continue;
				}
				if (indices.size() == 1) {
					auto index = indices.front();
					auto [channel, path] = bidirectional_bfs(business[index].first, business[index].second);
					vector<int> addition;
					for (auto x : path) if (flow[channel][x] == edges[x].cap.size())
						addition.push_back(x);
					if (addition.size() == 1) {
						for (auto& edge : edges) {
							for (auto& x : edge.cap) {
								x -= (x > i);
							}
						}
						edges.erase(edges.begin() + i);
						copy_edge(addition.front());
						paths[index] = make_pair(channel, move(path));
						backup = paths;
						continue;
					}
				}
			finish:
				edges[e].cap.push_back(i);
			}
			sort(all_edges.begin(), all_edges.end(), [&count](int x, int y) {
				return count[x] < count[y];
				});
		}
	ret:;
	}
	void optimize(vector<pair<int, vector<int>>>& paths, vector<int> indices) {
		simulate(paths);
		for (auto i : indices) {
			if (runtime() >= TIME_LIMIT)
				break;
			auto [channel, path] = paths[i];
			for (auto e : path) {
				assert(flow[channel][e] >= 1 && flow[channel][e] <= edges[e].cap.size());
				flow[channel][e] -= 1;
			}
			auto [s, t] = business[i];
			tie(channel, path) = dijkstra(s, t);
			for (auto e : path) {
				int& f = flow[channel][e];
				assert(f < edges[e].cap.size());
				f += 1;
			}
			paths[i] = make_pair(channel, path);
		}
	}
	void check(vector<pair<int, vector<int>>> paths) {
		set<pair<int, int>> S;
		transform(paths);
		for (auto [channel, path] : paths) {
			for (auto e : path) {
				auto pr = make_pair(channel, e);
				assert(!S.count(pr));
				S.emplace(pr);
			}
		}
	}
	void run_dijkstra(vector<int> new_edges) {
		long long answer = LLONG_MAX;
		vector<pair<int, vector<int>>> ans_paths;
		vector<edge_t> ans_edges;
		while (runtime() < TIME_LIMIT) {
			init();
			vector<pair<int, vector<int>>> paths(business.size());
			vector<int> indices;
			for (int i = 0; i < business.size(); ++i) {
				indices.push_back(i);
			}
			shuffle(indices.begin(), indices.end(), engine);
			for (auto e : new_edges) {
				copy_edge(e);
			}
			for (auto i : indices) {
				if (runtime() >= TIME_LIMIT)
					goto finish;
				auto [s, t] = business[i];
				auto [channel, path] = dijkstra(s, t);
				for (auto& e : path) {
					int& f = flow[channel][e];
					if (f >= edges[e].cap.size()) {
						copy_edge(e);
					}
					f += 1;
				}
				paths[i] = make_pair(channel, path);
			}
			long long now = calculate(paths);
			if (now < answer) {
				answer = now;
				ans_paths = paths;
				ans_edges = edges;
			}
		}
	finish:
		this->edges = ans_edges;
		long long value = calculate(ans_paths, true);
		assert(value == answer);
#ifndef NDEBUG
		check(ans_paths);
		print(answer);
#endif
	}
	int run(const vector<int>& new_edges) {
		static int vis[MAXT];
		this->bridges = new_edges;
		long long answer = LLONG_MAX;
		vector<pair<int, vector<int>>> ans_paths;
		vector<edge_t> ans_edges;
		vector<int> ans_indices;
		vector<int> indices;
		int iteration = 0;
		preprocess();
		for (int i = 0; i < business.size(); ++i) {
			indices.push_back(i);
		}
		while (runtime() < SEARCH_TIME || ans_paths.empty()) {
			for (int i = 0; i < T; ++i)
				vis[i] = false;
			init();
			vector<pair<int, vector<int>>> paths(business.size());
			for (auto e : bridges) {
				copy_edge(e);
			}
			double sum = 0;
			for (auto i : indices) {
				if (runtime() >= SEARCH_TIME && ans_paths.size())
					goto finish;
				auto [s, t] = business[i];
				auto [channel, path] = Astar(s, t);
				if (channel == -1) {
					tie(channel, path) = bidirectional_bfs(s, t);
					vis[i] = true;
				}
				bool flag = false;
				for (auto& e : path) {
					assert(e < M);
					int& f = flow[channel][e];
					if (f >= edges[e].cap.size()) {
						copy_edge(e);
						flag = true;
					}
					f += 1;
				}
				paths[i] = make_pair(channel, path);
				if (flag && runtime() < SEARCH_TIME) {
					sum += 200;
					if (sum >= 0) {
						double start = runtime();
						pile(paths, 1);
						pile(paths, 0);
						double end = runtime();
						sum -= end - start;
					}
				}
			}
			shrink(paths);
#ifndef NDEBUG
			if (answer == LLONG_MAX)
				print("Time baseline: ", runtime() / 1000.0);
#endif
			flip(paths);
			stable_partition(indices.begin(), indices.end(), [](int i) {
				return vis[i];
				});
			long long now = calculate(paths);
			if (now < answer) {
				answer = now;
				ans_paths = paths;
				ans_edges = edges;
				ans_indices = indices;
			}
			iteration += 1;
		}
	finish:
		this->edges = ans_edges;
#ifndef NDEBUG
		simulate(ans_paths);
		print("Answer: ", calculate(ans_paths));
		print("Congestion: ", congestion());
#endif
		squeeze(ans_paths, TIME_LIMIT * 0.96);
#ifndef NDEBUG
		print("Answer(squeezed): ", calculate(ans_paths)); //65033546
		print("Congestion(squeezed): ", congestion());
#endif
		optimize(ans_paths, ans_indices);
		answer = calculate(ans_paths, true);
#ifndef NDEBUG
		check(ans_paths);
		print(answer);
#endif
		return iteration;
	}
} solver;
int main() { //112017630        3042        91        [27742355,1074080813]
#ifndef NDEBUG
	freopen("in3.txt", "r", stdin);
	freopen("out.txt", "w", stdout);
#endif
	scanf("%d %d %d %d %d", &N, &M, &T, &P, &D);
	for (int i = 0; i < M; ++i) {
		int s, t, d;
		scanf("%d %d %d", &s, &t, &d);
		graph.emplace_back(s, t, d);
	}
	for (int i = 0; i < T; ++i) {
		int s, t;
		scanf("%d %d", &s, &t);
		business.emplace_back(s, t);
	}
	auto bridges = bridger.run(N, M, P, graph, business);
	int iteration = solver.run(bridges);
#ifndef NDEBUG
	print("Runtime: ", runtime() / 1000.0);
	print("Iteration: ", iteration);
#endif
	return 0;
}