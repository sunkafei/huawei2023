//Author: 孙明志 梁昊骞 林麒
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
#include <string>
using namespace std;
#ifndef NDEBUG
const long long TIME_LIMIT = 2 * 1000;
#else
const long long TIME_LIMIT = 115 * 1000;
#endif
const long long SEARCH_TIME = TIME_LIMIT;
const int MAXN = 6005;
const int MAXM = 20005;
const int MAXT = 42005;
const int MAXP = 123;
const int INF = 0x3F3F3F3F;
const auto start_time = std::chrono::steady_clock::now();
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
template<typename T> class fast_queue {
private:
	static const int MAXSIZE = MAXP * MAXN;
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
};
inline auto runtime() {
	auto now = std::chrono::steady_clock::now();
	auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(now - start_time);
	return duration.count();
}
int N, M, T, R, P, D, H;
vector<tuple<int, int, int, int>> graph;
vector<pair<int, int>> business;
vector<int> group[MAXT];
class result_t { // modify
public:
	int index;
	int channel;
	vector<int> path;
public:
	result_t() : index(-1), channel(-1) {}
	result_t(int index, int channel, const vector<int> &path) : index(index), channel(channel), path(path) {}
	inline auto &operator[] (int i) {
		return path[i];
	}
	inline int size() const {
		return path.size();
	}
	inline auto begin() {
		return path.begin();
	}
	inline auto end() {
		return path.end();
	}
	inline auto begin() const {
		return path.begin();
	}
	inline auto end() const {
		return path.end();
	}
};
class solver_t {
private:
	struct edge_t {
		int from;
		int to;
		int weight;
		int cost;
		int index;
	};
	int baseline[MAXN][MAXN];
	vector<edge_t> edges;
	vector<pair<int, int>> G[MAXN];
	mt19937 engine;
private:
	int cover[MAXP][MAXM];
	int visit[MAXM], cur;
public:
	inline bool idle(int c, int e) {
		return cover[c][e] == -1 && visit[e] != cur;
	}
	inline void apply(const result_t &result) {
		const int index = result.index, channel = result.channel;
		for (auto e : result) {
			assert(cover[channel][e] == -1);
			cover[channel][e] = index;
		}
	}
	inline void apply(const vector<result_t> &results) {
		for (const auto &result : results) {
			apply(result);
		}
	}
	inline void undo(const result_t &result) {
		const int index = result.index, channel = result.channel;
		for (auto e : result) {
			assert(cover[channel][e] == index);
			cover[channel][e] = -1;
		}
	}
	inline void undo(const vector<result_t> &results) {
		for (const auto &result : results) {
			undo(result);
		}
	}
	inline void check(const vector<result_t> &results) {
		set<pair<int, int>> S;
		for (auto result : results) {
			for (auto e : result) {
				pair<int, int> pr(result.channel, e);
				assert(!S.count(pr));
				S.insert(pr);
			}
		}
	}
	inline void compatible(const vector<result_t> &results) {
		int counter = 0;
		for (const auto& result : results) {
			for (auto e : result) {
				assert(cover[result.channel][e] == result.index);
				counter += 1;
			}
		}
		for (int channel = 0; channel < P; ++channel) {
			for (int e = 0; e < edges.size(); ++e) {
				counter -= (cover[channel][e] != -1);
			}
		}
		assert(counter == 0);
	}
	inline result_t solve(vector<result_t> &results, int index, bool trial=false) {
		cur += 1;
		int last = -1;
		for (auto i : group[index]) {
			for (auto e : results[i]) {
				visit[e] = cur;
			}
			if (results[i].channel != -1)
				last = results[i].channel;
		}
		const auto [s, t] = business[index];
		auto [c, path] = astar(s, t, group[index].size() == 1 ? last : -1);
		if (c == -1) {
			if (trial) {
				return result_t();
			}
			else {
				//tie(c, path) = bidirectional_bfs(s, t, last);
				tie(c, path) = bidirectional_bfs(s, t, group[index].size() == 1 ? last : -1);
			}
		}
		for (int i = 0; i < path.size(); ++i) {
			int &e = path[i];
			if (!idle(c, e)) {
				e = copy_edge(edges[e]);
			}
			assert(c < P && e < MAXM && cover[c][e] == -1);
			cover[c][e] = index;
			visit[e] = cur;
		}
		return result_t(index, c, path);
	}
	inline long long calculate(const result_t &result, bool output) {
		const auto [s, t] = business[result.index];
		const int channel = result.channel;
		vector<int> amplifier, nodes;
		int sum = 0, sum2 = 0, x = s;
		nodes.push_back(x);
		for (auto e : result) {
			if (sum + edges[e].weight > D || sum2 + edges[e].cost > H) {
				amplifier.push_back(x);
				sum = 0;
				sum2 = 0;
			}
			sum += edges[e].weight;
			sum2 += edges[e].cost;
			assert(x == edges[e].from || x == edges[e].to);
			x = (x == edges[e].from ? edges[e].to : edges[e].from);
			nodes.push_back(x);
		}
		assert(x == t);
		if (output) {
			printf("%d %d %d", channel, result.size(), (int)amplifier.size());
			for (auto e : result) {
				printf(" %d", e);
			}
			for (auto a : amplifier) {
				printf(" %d", a);
			}
			printf("\n");
#ifndef NDEBUG
			//print(channel);
			//print(nodes);
#endif
		}
		long long cost = result.size() + amplifier.size() * 100;
		return cost;
	}
public:
	solver_t() : engine(20140920) {}
	inline void preprocess() {
		static fast_queue<int> Q;
		for (int i = 0; i < N; ++i)
			G[i].clear();
		for (int i = 0; i < M; ++i) {
			auto [s, t, d, h] = graph[i];
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
	}
	inline void init() {
		memset(cover, -1, sizeof(cover));
		memset(visit, 0, sizeof(visit));
		cur = 1;
		for (int i = 0; i < N; ++i)
			G[i].clear();
		edges.resize(M);
		for (int i = 0; i < M; ++i) {
			auto [s, t, d, h] = graph[i];
			G[s].emplace_back(t, i);
			G[t].emplace_back(s, i);
			edges[i].from = s;
			edges[i].to = t;
			edges[i].weight = d;
			edges[i].cost = h;
			edges[i].index = i;
		}
	}
	inline void remove_edge(int e) {
		int from = edges[e].from, to = edges[e].to;
		auto iter = find(G[from].begin(), G[from].end(), make_pair(to, e));
		assert(iter != G[from].end());
		G[from].erase(iter);
		iter = find(G[to].begin(), G[to].end(), make_pair(from, e));
		assert(iter != G[to].end());
		G[to].erase(iter);
	}
	inline void add_edge(int e) {
		int from = edges[e].from, to = edges[e].to;
		G[from].emplace_back(to, e);
		G[to].emplace_back(from, e);
	}
	inline int copy_edge(edge_t edge) {
		int ne = edges.size();
		edges.push_back(edge);
		add_edge(ne);
		return ne;
	}
	inline void shuffle_edges() {
		for (int i = 0; i < N; ++i)
			shuffle(G[i].begin(), G[i].end(), engine);
	}
	inline void simulate(const vector<result_t> &results) {
		for (int i = 0; i < P; ++i) {
			for (int j = 0; j <= edges.size(); ++j) {
				cover[i][j] = -1;
			}
		}
		for (const auto &result : results) {
			apply(result);
		}
	}
	inline auto save(const vector<result_t> &results) {
		return make_pair(edges, results);
	}
	inline auto resume(const pair<vector<edge_t>, vector<result_t>> &backup) {
		this->edges = move(backup.first);
		simulate(backup.second);
		return backup.second;
	}
	int shrink(vector<result_t>& results) {
		if (runtime() >= SEARCH_TIME)
			return 0;
		vector<int> removed(edges.size());
		vector<pair<int, int>> pairs(edges.size() - M);
		for (int e = M; e < edges.size(); ++e)
			pairs[e - M].second = e;
		for (int c = 0; c < P; ++c) {
			for (int e = M; e < edges.size(); ++e) {
				if (cover[c][e] != -1) {
					pairs[e - M].first += 1;
				}
			}
		}
		sort(pairs.begin(), pairs.end());
		for (auto [_, e] : pairs) {
			if (runtime() >= SEARCH_TIME)
				break;
			vector<result_t> operations;
			bool ok = true;
			remove_edge(e);
			for (int c = 0; c < P; ++c) {
				int q = cover[c][e];
				if (q != -1) {
					if (runtime() >= SEARCH_TIME) {
						ok = false;
					}
					else {
						undo(results[q]);
						auto new_result = solve(results, q, true);
						if (new_result.index == -1) {
							apply(results[q]);
							ok = false;
						}
						else {
							operations.push_back(results[q]);
							results[q] = move(new_result);
						}
					}
				}
				if (!ok) {
					while (operations.size()) {
						auto &operation = operations.back();
						undo(results[operation.index]);
						results[operation.index] = move(operation);
						apply(results[operation.index]);
						operations.pop_back();
					}
					break;
				}
			}
			if (ok) {
				removed[e] = true;
			}
			else {
				add_edge(e);
			}
#ifndef NDEBUG
			compatible(results);
#endif
		}
#ifndef NDEBUG
		compatible(results);
#endif
		undo(results);
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
		for (auto &result : results) {
			for (auto& e : result) {
				assert(!removed[e]);
				e -= sum[e];
			}
		}
		for (int x = 0; x < N; ++x) {
			for (auto &[_, e] : G[x]) {
				assert(!removed[e]);
				e -= sum[e];
			}
		}
		apply(results);
#ifndef NDEBUG
		compatible(results);
#endif
		return sum.back();
	}
	long long calculate(const vector<result_t> &results, bool output=false) {
		/*if (output) {
			for (int i = 0; i < 20000; ++i)
				copy_edge(edges[0]);
		}*/
		int Y = edges.size() - M;
		if (output) {
			printf("%d\n", Y);
			for (int i = M; i < edges.size(); ++i) {
				printf("%d\n", edges[i].index);
			}
		}
		long long answer = Y * 1e6;
		for (int i = 0; i < business.size(); ++i) {
			answer += calculate(results[i], output);
		}
		return answer;
	}
	pair<int, vector<int>> astar(int start, int terminate, int chan = -1) {
		static int dist[MAXP][MAXN], timestamp[MAXP][MAXN], id = 1; id += 1;
		static pair<int, int> parent[MAXP][MAXN];
		static fast_deque<pair<int, int>> A, B1, B2, C; A.clear(); B1.clear(); B2.clear(); C.clear();
		for (int i = 0; i < P; ++i) if (chan == i || chan == -1) {
			dist[i][start] = 0;
			timestamp[i][start] = id;
			A.push_front({ start | (i << 20), dist[i][start] });
		}
		int channel = -1;
		while (A.size() || B1.size() || B2.size() || C.size()) {
			while (A.empty()) {
				A.clear();
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
			const auto [state, distance] = A.back(); A.pop_back();
			const int c = state >> 20, x = state & 0xFFFFF;
			if (distance != dist[c][x]) {
				continue;
			}
			if (x == terminate) {
				channel = c;
				break;
			}
			const int base = baseline[x][terminate];
			for (auto [y, e] : G[x]) if (idle(c, e)) {
				if (timestamp[c][y] != id || dist[c][y] > dist[c][x] + 1) {
					timestamp[c][y] = id;
					dist[c][y] = dist[c][x] + 1;
					parent[c][y] = { x, e };
					const int delta = baseline[y][terminate] - base + 1;
					if (delta == 0) {
						A.push_back({ y | (c << 20), dist[c][y] });
					}
					else if (delta == 1) {
						B1.push_back({ y | (c << 20), dist[c][y] });
					}
					else {
						assert(delta == 2);
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
	pair<int, vector<int>> bidirectional_bfs(int start, int terminate, int chan = -1) {
		static int dist1[MAXP][MAXN], dist2[MAXP][MAXN];
		static int vis1[MAXP][MAXN], vis2[MAXP][MAXN];
		static int timestamp[MAXP][MAXN], id = 1; id += 1;
		static pair<int, int> parent1[MAXP][MAXN], parent2[MAXP][MAXN];
		static fast_queue<pair<int, int>> A1, B1, C1, A2, B2, C2;
		A1.clear(); B1.clear(); C1.clear(); A2.clear(); B2.clear(); C2.clear();
		int channel = -1, middle = -1;
		for (int i = 0; i < P; ++i) if (chan == i || chan == -1) {
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
					int w = (!idle(c, e)) * (MAXT + MAXM) + 1;
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
					int w = (!idle(c, e)) * (MAXT + MAXM) + 1;
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
	int pile(vector<result_t>& results, int direction, int time_limit=SEARCH_TIME) {
		shuffle_edges();
		vector<int> indices(business.size());
		for (int i = 0; i < business.size(); ++i) {
			indices[i] = i;
		}
		shuffle(indices.begin(), indices.end(), engine);
		for (auto &result : results) {
			result.channel = P - result.channel - 1;
		}
		simulate(results);
		for (auto i : indices) {
			if (runtime() >= time_limit)
				return false;
			undo(results[i]);
			auto new_result = solve(results, i, true);
			assert(new_result.index != -1);
			results[i] = move(new_result);
		}
		return shrink(results);
	}
	void flip(vector<result_t>& results) {
		int direction = 0;
		int last = 0;
		for (int t = 0; ;++t) {
			if (runtime() >= SEARCH_TIME)
				break;
			direction ^= 1;
			int removed = pile(results, direction);
			if (removed) {
				last = t;
			}
			if (t - last > 10) {
				break;
			}
		}
	}
	int run() {
		long long answer = LLONG_MAX;
		pair<vector<edge_t>, vector<result_t>> backup;
		vector<edge_t> inherit;
		int iteration = 0;
		preprocess();
		while (runtime() < SEARCH_TIME || iteration == 0) {
			init();
			vector<result_t> results(business.size());
			for (auto edge : inherit) {
				copy_edge(edge);
			}
			inherit.clear();
			
			vector<int> indices, seq;
			for (int i = 0; i < business.size(); ++i)
				seq.push_back(i);
			while (seq.size()) {
				sort(seq.begin(), seq.end(), [](int x, int y) {
					return business[x] < business[y];
				});
				vector<int> now, rest;
				for (int i = 0; i < seq.size(); ++i) {
					if (i == 0 || business[seq[i]] != business[seq[i - 1]]) {
						now.push_back(seq[i]);
					}
					else {
						rest.push_back(seq[i]);
					}
				}
				shuffle(now.begin(), now.end(), engine);
				for (auto index : now)
					indices.push_back(index);
				seq = move(rest);
			}
			
			for (auto i : indices) {
				if (runtime() >= SEARCH_TIME && iteration > 0)
					goto finish;
				results[i] = solve(results, i, false);
			}
#ifndef NDEBUG
			if (answer == LLONG_MAX)
				print("Time baseline: ", runtime() / 1000.0);
#endif
			shrink(results);
			flip(results);
			for (int i = M; i < edges.size(); ++i) {
				inherit.push_back(edges[i]);
			}
			long long now = calculate(results);
			if (now < answer) {
				answer = now;
				backup = save(results);
			}
			iteration += 1;
		}
	finish:
		auto results = resume(backup);
#ifndef NDEBUG
		compatible(results);
#endif
		answer = calculate(results, true);
#ifndef NDEBUG
		check(results);
		print(answer);
#endif
		return iteration;
	}
} solver;
int main() { //679
#ifndef NDEBUG
	freopen("in1.txt", "r", stdin);
	freopen("out1.txt", "w", stdout);
#endif
	scanf("%d %d %d %d %d %d %d", &N, &M, &T, &R, &P, &D, &H);
	for (int i = 0; i < M; ++i) {
		int s, t, d, h;
		scanf("%d %d %d %d", &s, &t, &d, &h);
		graph.emplace_back(s, t, d, h);
	}
	for (int i = 0; i < T; ++i) {
		int s, t, k;
		scanf("%d %d %d", &s, &t, &k);
		int L = business.size();
		for (int j = 0; j < k; ++j) {
			business.emplace_back(s, t);
		}
		int R = business.size() - 1;
		for (int x = L; x <= R; ++x) {
			for (int y = L; y <= R; ++y) {
				if (x != y) {
					group[x].push_back(y);
				}
			}
		}
	}
	int iteration = solver.run();
#ifndef NDEBUG
	print("Runtime: ", runtime() / 1000.0);
	print("Iteration: ", iteration);
#endif
	return 0;
}