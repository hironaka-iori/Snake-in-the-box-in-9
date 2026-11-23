#include <algorithm>
#include <array>
#include <iostream>
#include <sstream>
#include <vector>
using Path = std::vector<int>;
struct Solver {
  std::array<std::array<int, 9>, 512> nb;
  std::array<bool, 512> live{};
  std::array<int, 512> num{}, low{}, color{};
  std::array<Path, 512> subs;
  std::vector<Path> blocks;
  std::vector<std::pair<int, int>> stack;
  Path p, answer;
  int tick = 0, nodes = 0, cap, goal;
  Solver() {
    for (int v = 0; v < 512; v++) {
      color[v] = __builtin_parity(unsigned(v));
      for (int d = 0; d < 9; d++)
        nb[v][d] = v ^ (1 << d);
    }
  }
  void dfs(int v, int par) {
    num[v] = low[v] = ++tick;
    for (int w : nb[v])
      if (live[w] && w != par) {
        if (!num[w]) {
          stack.emplace_back(v, w);
          dfs(w, v);
          low[v] = std::min(low[v], low[w]);
          if (low[w] >= num[v]) {
            Path block;
            std::pair<int, int> z;
            do {
              z = stack.back();
              stack.pop_back();
              block.push_back(z.first);
              block.push_back(z.second);
            } while (z != std::make_pair(v, w));
            std::sort(block.begin(), block.end());
            block.erase(std::unique(block.begin(), block.end()), block.end());
            subs[v].push_back(blocks.size());
            blocks.push_back(std::move(block));
          }
        } else if (num[w] < num[v]) {
          stack.emplace_back(v, w);
          low[v] = std::min(low[v], num[w]);
        }
      }
  }
  // A path from the tip follows a single branch in the block-cut tree.
  int bound(int v, int even, int odd, int rootcolor) {
    int best = 1;
    for (int id : subs[v]) {
      int a = even, b = odd;
      for (int w : blocks[id])
        if (w != v) {
          if (color[w])
            b++;
          else
            a++;
        }
      best = std::max(best, rootcolor ? std::min(2 * b, 2 * a + 1)
                                      : std::min(2 * a, 2 * b + 1));
      for (int w : blocks[id])
        if (w != v && !subs[w].empty())
          best = std::max(best, bound(w, a, b, rootcolor));
    }
    return best;
  }
  void enumerate_small(int pos, unsigned blocked, int depth,
                       const std::array<unsigned, 14> &adj,
                       std::array<int, 14> &distance) {
    distance[pos] = std::max(distance[pos], depth);
    unsigned options = adj[pos] & ~blocked;
    while (options) {
      int next = __builtin_ctz(options);
      options &= options - 1;
      enumerate_small(next, blocked | adj[pos] | (1u << pos), depth + 1, adj,
                      distance);
    }
  }
  // Sum edge bounds for induced traversals of consecutive blocks. Each shared
  // articulation is an endpoint of both traversals.
  int block_bound(int entry) {
    int upper = 0;
    for (int id : subs[entry]) {
      auto &b = blocks[id];
      int count = b.size();
      if (count <= 14) {
        std::array<unsigned, 14> adj{};
        std::array<int, 14> distance{};
        int root = 0;
        for (int j = 0; j < count; j++) {
          if (b[j] == entry)
            root = j;
          for (int i = 0; i < j; i++)
            if (__builtin_popcount(b[i] ^ b[j]) == 1) {
              adj[j] |= 1 << i;
              adj[i] |= 1 << j;
            }
        }
        enumerate_small(root, 0, 0, adj, distance);
        for (int j = 0; j < count; j++)
          if (j != root)
            upper = std::max(upper, distance[j] + block_bound(b[j]));
      } else {
        std::array<bool, 512> available{};
        int same = 0, stars = 0;
        for (int v : b) {
          available[v] = true;
          same += color[v] == color[entry];
        }
        // Four vertices forming a degree-three star cannot all be selected.
        for (int v : b)
          if (available[v]) {
            int k = 0;
            std::array<int, 3> chosen;
            for (int w : nb[v])
              if (available[w]) {
                chosen[k++] = w;
                if (k == 3)
                  break;
              }
            if (k == 3) {
              stars++;
              available[v] = false;
              for (int w : chosen)
                available[w] = false;
            }
          }
        for (int v : b)
          if (v != entry) {
            int segment = (color[v] == color[entry])
                              ? 2 * std::min(same - 1, count - same)
                              : 2 * std::min(same, count - same) - 1;
            segment = std::min(segment, count - stars - 1);
            if (__builtin_popcount(v ^ entry) == 1)
              segment = 1;
            upper = std::max(upper, segment + block_bound(v));
          }
      }
    }
    return upper;
  }
  bool visit() {
    if (p.size() == goal + 1) {
      answer = p;
      return true;
    }
    if (nodes >= cap)
      return false;
    ++nodes;
    int v = p.back();
    num.fill(0);
    for (auto &x : subs)
      x.clear();
    blocks.clear();
    stack.clear();
    tick = 0;
    dfs(v, -1);
    int need = goal + 2 - int(p.size());
    if (tick < need || bound(v, !color[v], color[v], color[v]) < need ||
        block_bound(v) + 1 < need)
      return false;
    Path opts;
    for (int w : nb[v])
      if (live[w])
        opts.push_back(w);
    live[v] = false;
    for (int w : opts)
      live[w] = false;
    for (int w : opts) {
      live[w] = true;
      p.push_back(w);
      if (visit())
        return true;
      p.pop_back();
      live[w] = false;
      if (nodes >= cap)
        break;
    }
    live[v] = true;
    for (int w : opts)
      live[w] = true;
    return false;
  }
  void run(const Path &arm) {
    p = arm;
    answer.clear();
    nodes = 0;
    live.fill(true);
    for (int i = 0; i + 1 < p.size(); i++) {
      live[p[i]] = false;
      for (int w : nb[p[i]])
        live[w] = false;
    }
    live[p.back()] = true;
    visit();
  }
};
bool valid(const Path &p) {
  for (int i = 0; i < p.size(); i++) {
    if (p[i] < 0 || p[i] >= 512)
      return false;
    for (int j = 0; j < i; j++) {
      int d = __builtin_popcount(p[i] ^ p[j]);
      if (!d || ((i == j + 1) != (d == 1)))
        return false;
    }
  }
  return true;
}
int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  Solver s;
  s.goal = std::stoi(argv[1]);
  s.cap = std::stoi(argv[2]);
  std::string line;
  while (getline(std::cin, line)) {
    std::istringstream r(line);
    Path arm;
    int v;
    while (r >> v)
      arm.push_back(v);
    if (arm.empty() || !valid(arm) || arm.size() > s.goal + 1)
      return 3;
    s.run(arm);
    if (!s.answer.empty()) {
      if (!valid(s.answer))
        return 4;
      std::cout << "FOUND";
      for (int x : s.answer)
        std::cout << " " << x;
      std::cout << std::endl;
      return 0;
    }
    std::cout << (s.nodes >= s.cap ? "UNKNOWN" : "EXHAUSTED") << " " << s.nodes
              << '\n';
  }
}
