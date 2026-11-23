// Read an ordered induced cycle on stdin. Keep all but exactly k original
// vertices and look for an induced path with the requested number of edges.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <vector>
using Path = std::vector<int>;
struct Search {
  int d, k, edges, n, add, vertices;
  Path cycle, extra, chosen;
  std::vector<Path> outside_neighbors;
  std::array<int, 512> touched{}, index{}, blocked{}, degree{};
  std::array<bool, 512> selected{};
  std::array<uint64_t, 8> eligible{};
  uint64_t cuts = 0, enough = 0, filled = 0;
  void mark(int v, bool value) {
    if (value)
      eligible[v / 64] |= 1ull << (v % 64);
    else
      eligible[v / 64] &= ~(1ull << (v % 64));
  }
  void remove_corner(int i, int change) {
    int x = cycle[i];
    selected[x] = (change < 0);
    for (int a = 0; a < d; a++)
      degree[x ^ (1 << a)] -= change;
    for (int u : {(i + n - 1) % n, i, (i + 1) % n}) {
      int before = touched[u];
      touched[u] += change;
      if (before && touched[u])
        continue;
      for (int v : outside_neighbors[u]) {
        blocked[v] -= change;
        if (blocked[v] == 0 || blocked[v] + change == 0)
          mark(v, blocked[v] == 0);
      }
    }
  }
  bool collect = false;
  std::unordered_set<std::string> classes;
  std::string shape(const Path &p) {
    std::string word;
    for (size_t i = 1; i < p.size(); i++)
      word.push_back(std::countr_zero(unsigned(p[i] ^ p[i - 1])));
    auto normalize = [](std::string s) {
      std::array<int, 9> axes;
      axes.fill(-1);
      int n = 0;
      for (char &ch : s) {
        int &j = axes[int(ch)];
        if (j < 0)
          j = n++;
        ch = j;
      }
      return s;
    };
    auto forward = normalize(word);
    std::reverse(word.begin(), word.end());
    return std::min(forward, normalize(word));
  }
  bool verify_path() {
    ++filled;
    int first = -1, ends = 0;
    for (int x = 0; x < vertices; x++)
      if (selected[x]) {
        if (degree[x] == 1) {
          first = x;
          ++ends;
        } else if (degree[x] != 2)
          return false;
      }
    if (ends != 2)
      return false;
    Path p;
    int prev = -1;
    while (first >= 0) {
      p.push_back(first);
      int next = -1;
      for (int a = 0; a < d; a++) {
        int w = first ^ (1 << a);
        if (w != prev && selected[w])
          next = w;
      }
      prev = first;
      first = next;
    }
    if (int(p.size()) != edges + 1)
      return false;
    if (collect && !classes.insert(shape(p)).second)
      return false;
    for (int i = 0; i < p.size(); i++)
      for (int j = 0; j < i; j++) {
        int h = std::popcount(unsigned(p[i] ^ p[j]));
        if (!h || ((i == j + 1) != (h == 1)))
          std::abort();
      }
    std::cout << (collect ? "PATH" : "FOUND");
    for (int x : p)
      std::cout << " " << x;
    std::cout << std::endl;
    return !collect;
  }
  bool fill(int pos, int left) {
    if (!left)
      return verify_path();
    for (int i = pos; i + left <= extra.size(); i++) {
      int x = extra[i];
      if (degree[x] > 2)
        continue;
      bool ok = true;
      for (int a = 0; a < d; a++) {
        int w = x ^ (1 << a);
        if (selected[w] && degree[w] >= 2) {
          ok = false;
          break;
        }
      }
      if (!ok)
        continue;
      selected[x] = true;
      for (int a = 0; a < d; a++)
        degree[x ^ (1 << a)]++;
      if (fill(i + 1, left - 1))
        return true;
      selected[x] = false;
      for (int a = 0; a < d; a++)
        degree[x ^ (1 << a)]--;
    }
    return false;
  }
  bool cut(int pos, int left) {
    if (left) {
      for (int i = pos; i + left <= n; i++) {
        remove_corner(i, 1);
        if (cut(i + 1, left - 1))
          return true;
        remove_corner(i, -1);
      }
      return false;
    }
    cuts++;
    int avail = 0;
    for (auto w : eligible)
      avail += std::popcount(w);
    if (avail < add)
      return false;
    extra.clear();
    for (int b = 0; b < 8; b++) {
      uint64_t w = eligible[b];
      while (w) {
        int x = 64 * b + std::countr_zero(w);
        if (degree[x] <= 2)
          extra.push_back(x);
        w &= w - 1;
      }
    }
    if (extra.size() < add)
      return false;
    ++enough;
    return fill(0, add);
  }
  // Enumerate circular runs of removed vertices. Use the lowest numbered run
  // start as origin; the last run may wrap around vertex zero.
  bool runs(int origin, int at, int remaining, int count, bool first) {
    if (!count)
      return remaining == 0 && cut(0, 0);
    int maxstart = n - remaining - count;
    for (int start = at; start <= (first ? 0 : maxstart); start++) {
      if (!first && (origin + start) % n <= origin)
        continue;
      int largest = remaining - count + 1;
      for (int length = 1; length <= largest; length++) {
        remove_corner((origin + start + length - 1) % n, 1);
        if ((count > 1 || length == remaining) &&
            runs(origin, start + length + 1, remaining - length, count - 1,
                 false))
          return true;
      }
      for (int length = largest; length >= 1; length--)
        remove_corner((origin + start + length - 1) % n, -1);
    }
    return false;
  }
  bool init() {
    vertices = 1 << d;
    n = cycle.size();
    add = edges + 1 - (n - k);
    if (add < 0 || k > n || n < 4 || k < 0)
      return false;
    index.fill(-1);
    outside_neighbors.resize(n);
    for (int i = 0; i < n; i++) {
      int x = cycle[i];
      if (x < 0 || x >= vertices || index[x] != -1)
        return false;
      index[x] = i;
      selected[x] = true;
    }
    for (int i = 0; i < n; i++) {
      int x = cycle[i];
      if (std::popcount(unsigned(x ^ cycle[(i + 1) % n])) != 1)
        return false;
      for (int a = 0; a < d; a++) {
        int w = x ^ (1 << a);
        degree[w]++;
        if (index[w] < 0) {
          outside_neighbors[i].push_back(w);
          blocked[w]++;
        }
      }
    }
    for (int x : cycle)
      if (degree[x] != 2)
        return false;
    for (int x = 0; x < vertices; x++)
      if (index[x] < 0 && !blocked[x])
        mark(x, true);
    return true;
  }
};
int main(int argc, char **argv) {
  if (argc > 4 && std::string(argv[argc - 1]) == "--collect")
    --argc;
  bool collect = argv[argc] != nullptr;
  if (argc != 4 && argc != 5)
    return 2;
  Search s;
  s.collect = collect;
  s.d = std::stoi(argv[1]);
  s.k = std::stoi(argv[2]);
  s.edges = std::stoi(argv[3]);
  if (s.d < 2 || s.d > 9)
    return 2;
  int x;
  while (std::cin >> x)
    s.cycle.push_back(x);
  if (!s.init())
    return 3;
  bool yes = false;
  if (argc == 5) {
    int r = std::stoi(argv[4]);
    if (r < 1 || r > s.k || r > s.n - s.k)
      return 2;
    for (int first = 0; first < s.n && !yes; first++)
      yes = s.runs(first, 0, s.k, r, true);
  } else
    yes = s.cut(0, s.k);
  std::cout << (yes ? "hit" : "exhausted") << " removed " << s.k << " added "
            << s.add << " cuts " << s.cuts << " eligible " << s.enough
            << " degree_ok " << s.filled << std::endl;
}
