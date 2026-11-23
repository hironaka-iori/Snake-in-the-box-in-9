// Five ordered pieces: two independently remapped dictionary words on either
// side of a fixed central word. Input files: known paths for the dictionary,
// then a seed bank whose central fragments are checked directly.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Path = vector<int>;
using Mask = array<uint64_t, 8>;
int nb[512][9];
string word(const Path &p, int start, int d, int n) {
  array<int, 9> names;
  names.fill(-1);
  int k = 0;
  string r;
  for (int i = 0; i < n; i++) {
    int a = countr_zero(unsigned(p[start + d * i] ^ p[start + d * (i + 1)]));
    if (names[a] < 0)
      names[a] = k++;
    r.push_back(char(names[a]));
  }
  return r;
}
bool valid(const Path &p) {
  for (int i = 0; i < p.size(); i++)
    for (int j = 0; j < i; j++)
      if (p[i] == p[j] ||
          ((popcount(unsigned(p[i] ^ p[j])) == 1) != (i == j + 1)))
        return false;
  return true;
}
struct Node {
  array<int, 9> links{};
  int active = 0;
};
struct Trie {
  vector<Node> n{1};
  int segments = 0;
  void insert(const string &w) {
    int pos = 0;
    for (unsigned char x : w) {
      int k = n[pos].links[x];
      if (!k) {
        k = n.size();
        n[pos].links[x] = k;
        n[pos].active |= (1 << x);
        n.emplace_back();
      }
      pos = k;
    }
    if (!n[pos].active)
      segments++;
    n[pos].active |= 512;
  }
};
struct Arm {
  Path nodes;
  Mask occ{}, closed{};
};
struct Side {
  vector<Trie *> words;
  vector<int> len;
  Path chain, core;
  int block[512]{};
  vector<Arm> arms;
  uint64_t visits = 0, limit;
  int cap, tip;
  bool complete = true;
  array<int, 9> bitOrder;
  void mark(int x, int z) {
    block[x] += 2 * z;
    for (int y : nb[x])
      block[y] += z;
  }
  void save() {
    Arm a;
    a.nodes = chain;
    for (int x : chain) {
      a.occ[x / 64] |= 1ull << (x % 64);
      a.closed[x / 64] |= 1ull << (x % 64);
      for (int y : nb[x])
        a.closed[y / 64] |= 1ull << (y % 64);
    }
    arms.push_back(std::move(a));
  }
  void grow(int s, int node, int depth, int used, array<int, 9> &map) {
    if (!complete)
      return;
    if (++visits > limit || arms.size() >= cap) {
      complete = false;
      return;
    }
    if (depth == len[s]) {
      if (s + 1 == words.size())
        save();
      else {
        array<int, 9> fresh{};
        grow(s + 1, 0, 0, 0, fresh);
      }
      return;
    }
    auto &t = *words[s];
    int x = chain.empty() ? tip : chain.back();
    // Each canonical word has exactly one image for a chosen sequence of flips,
    // even if some of the nine dimensions do not appear.
    for (int act = t.n[node].active & 511; act; act &= act - 1) {
      int a = countr_zero(unsigned(act)), next = t.n[node].links[a],
          save = map[a];
      for (int d : bitOrder) {
        int b = 1 << d;
        if (save ? save != b : (used & b) != 0)
          continue;
        int y = x ^ b;
        if (block[y] != 1)
          continue;
        map[a] = b;
        chain.push_back(y);
        mark(y, 1);
        grow(s, next, depth + 1, used | b, map);
        mark(y, -1);
        chain.pop_back();
        map[a] = save;
        if (!complete)
          return;
      }
    }
  }
  void run(const Path &center, bool left, mt19937 &rng) {
    core = center;
    tip = left ? center.front() : center.back();
    for (int x : center)
      mark(x, 1);
    iota(bitOrder.begin(), bitOrder.end(), 0);
    shuffle(bitOrder.begin(), bitOrder.end(), rng);
    array<int, 9> m{};
    grow(0, 0, 0, 0, m);
  }
};
vector<Path> read(string path) {
  ifstream f(path);
  if (!f)
    exit(2);
  string line;
  vector<Path> v;
  while (getline(f, line)) {
    if (line.empty())
      continue;
    Path p;
    istringstream s(line);
    int x;
    while (s >> x) {
      if (x < 0 || x >= 512)
        exit(3);
      p.push_back(x);
    }
    if (p.size() < 2)
      exit(3);
    for (int i = 1; i < p.size(); i++)
      if (popcount(unsigned(p[i] ^ p[i - 1])) != 1)
        exit(3);
    v.push_back(p);
  }
  return v;
}
int main(int argc, char **argv) {
  if (argc != 13 && argc != 14 && argc != 15 && argc != 16)
    return 2;
  bool seven = argc >= 15;
  bool outsideKnown =
      (argc == 14 || argc == 16) && string(argv[argc - 1]) == "--outside-known";
  if ((argc == 14 || argc == 16) && !outsideKnown)
    return 2;
  string bank = argv[1], seeds = argv[2];
  int c = stoi(argv[3]), a = stoi(argv[4]), b = stoi(argv[5]),
      d = stoi(argv[6]), e = stoi(argv[7]);
  int stride = stoi(argv[8]), maxCases = stoi(argv[9]),
      armLimit = stoi(argv[10]);
  uint64_t visits = stoull(argv[11]);
  mt19937 rng(stoul(argv[12]));
  for (int x = 0; x < 512; x++)
    for (int i = 0; i < 9; i++)
      nb[x][i] = x ^ (1 << i);
  auto known = read(bank), raw = read(seeds);
  set<string> knownShapes;

  if (outsideKnown) {

    for (auto &p : known) {
      if (p.size() != 192)
        continue;
      knownShapes.insert(min(word(p, 0, 1, 191), word(p, 191, -1, 191)));
    }
  }
  long long excluded = 0;
  vector<int> lens{a, b, d, e};
  if (seven) {
    lens.push_back(stoi(argv[13]));
    lens.push_back(stoi(argv[14]));
  }
  sort(lens.begin(), lens.end());
  lens.erase(unique(lens.begin(), lens.end()), lens.end());
  vector<Trie> tries(lens.size());
  auto tr = [&](int n) -> Trie * {
    return &tries[find(lens.begin(), lens.end(), n) - lens.begin()];
  };
  for (const Path &p : known) {
    if (!valid(p))
      return 4;
    for (int h : lens)
      for (int i = 0; i + h < p.size(); i++)
        for (int s : {1, -1})
          tr(h)->insert(word(p, s == 1 ? i : i + h, s, h));
  }
  set<string> ident;
  vector<Path> centers;
  for (const auto &p : raw)
    for (int i = 0; i + c < p.size(); i += stride) {
      string w = word(p, i, 1, c), r = word(p, i + c, -1, c);
      // Keep both orientations if the arm-length templates are asymmetric.
      for (int dir : {1, -1}) {
        string k = dir == 1 ? w : r;
        if (a == d && b == e && (!seven || stoi(argv[13]) == stoi(argv[14])))
          k = min(w, r);
        if (ident.count(k))
          continue;
        Path q(p.begin() + i, p.begin() + i + c + 1);
        if (dir < 0)
          reverse(q.begin(), q.end());
        if (!valid(q))
          continue;
        ident.insert(k);
        centers.push_back(std::move(q));
      }
    }
  shuffle(centers.begin(), centers.end(), rng);
  cout << "DICT";
  for (int h : lens)
    cout << " " << h << "=" << tr(h)->segments;
  cout << " centers_total " << centers.size() << endl;
  uint64_t work = 0, pairs = 0, totalLeft = 0, totalRight = 0;
  int solved = 0, complete = 0, skipped = 0, both = 0;
  for (auto &mid : centers) {
    if (solved >= maxCases)
      break;
    ++solved;
    Side l, r;
    l.words = {tr(a), tr(b)};
    r.words = {tr(d), tr(e)};
    l.len = {a, b};
    r.len = {d, e};
    if (seven) {
      int x = stoi(argv[13]), y = stoi(argv[14]);
      l.words.push_back(tr(x));
      r.words.push_back(tr(y));
      l.len.push_back(x);
      r.len.push_back(y);
    }
    l.cap = r.cap = armLimit;
    l.limit = r.limit = visits;
    l.run(mid, true, rng);
    totalLeft += l.arms.size();
    if (l.arms.empty() && l.complete) {
      ++complete;
      ++skipped;
      work += l.visits;
      continue;
    }
    r.run(mid, false, rng);
    totalRight += r.arms.size();
    work += l.visits + r.visits;
    if ((r.complete && r.arms.empty()) || (l.complete && r.complete))
      ++complete;
    if (!l.arms.empty() && !r.arms.empty())
      ++both;
    for (const Arm &x : l.arms)
      for (const Arm &y : r.arms) {
        ++pairs;
        bool good = true;
        for (int j = 0; j < 8; j++)
          if (x.closed[j] & y.occ[j]) {
            good = false;
            break;
          }
        if (!good)
          continue;
        Path q(x.nodes.rbegin(), x.nodes.rend());
        q.insert(q.end(), mid.begin(), mid.end());
        q.insert(q.end(), y.nodes.begin(), y.nodes.end());
        if (!valid(q) ||
            q.size() != a + b + c + d + e + 1 +
                            (seven ? stoi(argv[13]) + stoi(argv[14]) : 0))
          return 6;
        if (outsideKnown &&
            knownShapes.count(min(word(q, 0, 1, q.size() - 1),
                                  word(q, q.size() - 1, -1, q.size() - 1)))) {
          ++excluded;
          continue;
        }
        cout << "FOUND";
        for (int z : q)
          cout << " " << z;
        cout << endl;
        return 0;
      }
  }
  cout << "NO cases " << solved << " complete " << complete << " no_left "
       << skipped << " both_nonempty " << both << " nodes " << work
       << " left_arms " << totalLeft << " right_arms " << totalRight
       << " tested_pairs " << pairs << " excluded_known " << excluded << endl;
}
