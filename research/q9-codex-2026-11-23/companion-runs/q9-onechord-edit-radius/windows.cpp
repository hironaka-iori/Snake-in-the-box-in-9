// Enumerate exact symmetric differences from each distinct controlled image S.
// Output counts only changed crossing-edge sets from a valid input path/cycle.
// Arguments: target edges, maximum deletions (0..4), exclusive end row,
// first row, optional excluded canonical transition-word file.
// Within each control-bit layer, the original induced graph is unchanged.
// Across the two layers an image vertex can gain at most one neighbor,
// so its degree is at most three. Every degree-three vertex must be
// deleted or lose a neighbor; one deletion can resolve at most four.
// At a degree-feasible leaf all added vertices come from the complement
// of the original image. The final graph must be one induced path.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <unordered_set>
#include <vector>
using namespace std;
using Mask = array<uint64_t, 8>;
int nb[512][9], degree[512], delta[512], target, K;
bool old[512], active[512];
vector<int> vertices, additions, opts, foundPath;
long long inputs = 0, trials = 0, changed = 0, images = 0, legalLeaves = 0,
          models = 0, starsPruned = 0;
set<Mask> seen;
vector<int> over;
vector<int> chosen;
unordered_set<uint64_t> tried;
set<string> excluded;
long long knownHits = 0, disconnected = 0;
bool atLeast = false;
string shape(const vector<int> &p) {
  string s;
  for (int i = 1; i < p.size(); i++)
    s.push_back(char(countr_zero(unsigned(p[i] ^ p[i - 1]))));
  auto norm = [](string t) {
    array<int, 9> labels;
    labels.fill(-1);
    int n = 0;
    for (char &c : t) {
      if (labels[int(c)] < 0)
        labels[int(c)] = n++;
      c = char('0' + labels[int(c)]);
    }
    return t;
  };
  auto fw = norm(s);
  reverse(s.begin(), s.end());
  return min(fw, norm(s));
}
bool selected(int x) { return active[x]; }
void mark(int x, int d) {
  for (int y : nb[x])
    delta[y] += d;
  active[x] = d > 0;
}
int deg(int x) { return degree[x] + delta[x]; }
bool walk() {
  vector<int> tips;
  for (int x = 0; x < 512; x++)
    if (selected(x)) {
      int n = deg(x);
      if (n == 1)
        tips.push_back(x);
      else if (n != 2)
        return false;
    }
  if (tips.size() != 2)
    return false;
  int x = tips[0], prior = -1;
  vector<int> p;
  while (x >= 0) {
    p.push_back(x);
    int y = -1;
    for (int v : nb[x])
      if (v != prior && selected(v)) {
        y = v;
        break;
      }
    prior = x;
    x = y;
  }
  if (p.size() != vertices.size() - chosen.size() + additions.size() ||
      (atLeast ? int(p.size()) < target + 1 : int(p.size()) != target + 1))
    return false;
  for (int i = 0; i < p.size(); i++)
    for (int j = 0; j < i; j++)
      if (p[i] == p[j] ||
          ((popcount(unsigned(p[i] ^ p[j])) == 1) != (j + 1 == i)))
        exit(7);
  if (!excluded.empty() && excluded.count(shape(p))) {
    ++knownHits;
    return false;
  }
  foundPath = p;
  return true;
}
bool add(int start, int n) {
  if (n == 0) {
    ++models;
    return walk();
  }
  for (int i = start; i + n <= opts.size(); i++) {
    int v = opts[i];
    if (deg(v) > 2)
      continue;
    bool ok = true;
    for (int w : nb[v])
      if (active[w] && deg(w) >= 2) {
        ok = false;
        break;
      }
    if (!ok)
      continue;
    mark(v, 1);
    additions.push_back(v);
    if (add(i + 1, n - 1))
      return true;
    additions.pop_back();
    mark(v, -1);
  }
  return false;
}
bool finish() {
  int n = target + 1 - (int(vertices.size()) - int(chosen.size()));
  if (n < 0)
    return false;
  ++legalLeaves;
  int tips = 0;
  for (int x : vertices)
    if (active[x]) {
      int d = deg(x);
      if (d > 2)
        return false;
      tips += 2 - d;
    }
  if (!atLeast && tips > 2 + 2 * n)
    return false;
  opts.clear();
  for (int x = 0; x < 512; x++)
    if (!old[x] && deg(x) <= 2) {
      bool ok = true;
      for (int y : nb[x])
        if (active[y] && deg(y) >= 2) {
          ok = false;
          break;
        }
      if (ok)
        opts.push_back(x);
    }
  if (!atLeast)
    return add(0, n);
  array<bool, 512> live{}, reach{};
  for (int x : vertices)
    if (active[x])
      live[x] = true;
  for (int x : opts)
    live[x] = true;
  int root = -1;
  for (int x : vertices)
    if (active[x]) {
      root = x;
      break;
    }
  vector<int> queue{root};
  reach[root] = true;
  for (size_t j = 0; j < queue.size(); ++j)
    for (int y : nb[queue[j]])
      if (live[y] && !reach[y]) {
        reach[y] = true;
        queue.push_back(y);
      }
  for (int x : vertices)
    if (active[x] && !reach[x]) {
      ++disconnected;
      return false;
    }
  opts.erase(
      remove_if(opts.begin(), opts.end(), [&](int x) { return !reach[x]; }),
      opts.end());
  for (int count = max(n, (tips - 1) / 2); count <= int(opts.size()); ++count)
    if (add(0, count))
      return true;
  return false;
}
bool eraseSearch(int k) {
  array<int, 4> ordered{};
  copy(chosen.begin(), chosen.end(), ordered.begin());
  sort(ordered.begin(), ordered.begin() + chosen.size());
  uint64_t key = 0;
  for (unsigned i = 0; i < chosen.size(); i++)
    key = (key << 10) | (ordered[i] + 1);
  if (!tried.insert(key).second)
    return false;
  int bad = -1;
  for (int x : over)
    if (active[x] && deg(x) > 2) {
      bad = x;
      break;
    }
  if (bad < 0 && finish())
    return true;
  if (chosen.size() == k)
    return false;
  vector<int> branch;
  if (bad >= 0) {
    branch.push_back(bad);
    for (int y : nb[bad])
      if (active[y])
        branch.push_back(y);
  } else
    branch = vertices;
  for (int v : branch)
    if (active[v]) {
      chosen.push_back(v);
      mark(v, -1);
      if (eraseSearch(k))
        return true;
      mark(v, 1);
      chosen.pop_back();
    }
  return false;
}

vector<int> pool;
bool window(int start, int remaining) {
  if (!remaining)
    return finish();
  for (int i = start; i + remaining <= pool.size(); i++) {
    int v = pool[i];
    mark(v, -1);
    chosen.push_back(v);
    if (window(i + 1, remaining - 1))
      return true;
    chosen.pop_back();
    mark(v, 1);
  }
  return false;
}
int main(int argc, char **argv) {
 bool honestcap=argc==7&&string(argv[6])=="--unbounded-additions";atLeast=honestcap;
  if (argc != 5 && argc != 6 && !honestcap)
    return 2;
  K = stoi(argv[1]);
  int start = stoi(argv[2]), stop = stoi(argv[3]);
  target = stoi(argv[4]);
  if (K > 12 || K < 1)
    return 2;
  for (int x = 0; x < 512; x++)
    for (int j = 0; j < 9; j++)
      nb[x][j] = x ^ (1 << j);
  string row;
  int id = -1;
  set<Mask> shapes;
  while (getline(cin, row)) {
    ++id;
    if (id < start || id >= stop)
      continue;
    istringstream in(row);
    vertices.clear();
    int x;
    Mask m{};
    while (in >> x) {
      if (x < 0 || x >= 512)
        return 4;
      vertices.push_back(x);
      m[x / 64] |= 1ull << (x % 64);
    }
    shapes.insert(m); // The same set can have a different traversal and search window.
    ++inputs;
    fill(old, old + 512, false);
    fill(active, active + 512, false);
    fill(degree, degree + 512, 0);
    fill(delta, delta + 512, 0);
    for (int v : vertices) {
      if (old[v])
        return 4;
      old[v] = active[v] = true;
      for (int n : nb[v])
        degree[n]++;
    }
    int chords = 0, ca = -1, cb = -1;
    for (int i = 0; i < vertices.size(); i++)
      for (int j = 0; j < i; j++)
        if (popcount(unsigned(vertices[i] ^ vertices[j])) == 1) {
          if (i > j + 1) {
            ++chords;
            ca = i;
            cb = j;
          }
        } else if (i == j + 1)
          return 5;
    if (chords != 1)
      return 6;
    over.clear();
    for (int v : vertices)
      if (degree[v] > 2)
        over.push_back(v);
    chosen.clear();
    tried.clear();
    additions.clear();
    set<int> idx;
    for (int center : {0, ca, cb, int(vertices.size()) - 1})
      for (int i = max(0, center - K);
           i <= min(int(vertices.size()) - 1, center + K); ++i)
        idx.insert(i);
    pool.clear();
    for (int i : idx)
      pool.push_back(vertices[i]);
    bool solved = window(0, argc >= 6 ? stoi(argv[5]) : 6);
    if (solved) {
      cout << "FOUND " << id << " " << chosen.size() << " " << additions.size();
      for (int v : foundPath)
        cout << " " << v;
      cout << endl;
      return 0;
    }
  }
  cout << "NO unique_rows " << inputs << " feasible_deletions " << legalLeaves
       << " completed_additions " << models << endl;
}