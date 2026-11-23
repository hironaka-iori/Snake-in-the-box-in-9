#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
// Input: one space-separated Q9 vertex path per line.
// Arguments: left edges, free bridge edges, right edges, left window
// stride, maximum left forms, right window stride. Set right edges to
// zero to search unrestricted extensions of each fixed left arm.
using namespace std;
using Path = vector<int>;
struct Node {
  array<int, 9> child{};
  int active = 0;
};
vector<Node> trie(1);
array<int, 512> blocked{};
int lenA, lenB, lenBridge, target, maxLeft;
long long states = 0, bridges = 0, goodAnchors = 0, anchors = 0;
Path p;
array<int, 9> labels{};
void mark(int v, int val) {
  blocked[v] += val * 2;
  for (int d = 0; d < 9; ++d)
    blocked[v ^ (1 << d)] += val;
}
bool valid(const Path &q) {
  if (set<int>(q.begin(), q.end()).size() != q.size())
    return false;
  for (int i = 0; i < (int)q.size(); ++i)
    for (int j = 0; j < i; ++j)
      if ((__builtin_popcount(q[i] ^ q[j]) == 1) != (i == j + 1))
        return false;
  return true;
}
void (*onPair)() = nullptr;
void found() {
  if(onPair) {onPair();return;}
  if (!valid(p) || int(p.size()) != target + 1)
    exit(4);
  cout << "FOUND";
  for (int v : p)
    cout << " " << v;
  cout << endl;
  exit(0);
}
void readRight(int id, int depth, int free) {
  ++states;
  if (depth == lenB) { found(); return; }
  for (int active = trie[id].active; active; active &= active - 1) {
    int symbol = __builtin_ctz(active);
    int child = trie[id].child[symbol];
    int options = labels[symbol] ? labels[symbol] : free;
    for (int bits = options; bits; bits &= bits - 1) {
      int bit = bits & -bits;
      int next = p.back() ^ bit;
      // The right path already excludes its own chords. At depth 0
      // the join may only touch the last vertex of the left-plus-bridge path.
      if (blocked[next] != (depth == 0 ? 1 : 0))
        continue;
      int saved = labels[symbol];
      labels[symbol] = bit;
      p.push_back(next);
      readRight(child, depth + 1, free & ~bit);
      p.pop_back();
      labels[symbol] = saved;
    }
  }
}
void bridge(int n) {
  if (!n) {
    ++bridges;
    readRight(0, 0, 511);
    return;
  }
  for (int d = 0; d < 9; ++d) {
    int next = p.back() ^ (1 << d);
    if (blocked[next] != 1)
      continue;
    mark(next, 1);
    p.push_back(next);
    bridge(n - 1);
    p.pop_back();
    mark(next, -1);
  }
}
Path word(const Path &s, int a, int dir, int n) {
  Path w;
  array<int, 9> m{};
  int k = 0;
  for (int j = 0; j < n; ++j) {
    int d = __builtin_ctz(s[a + dir * j] ^ s[a + dir * (j + 1)]);
    if (!m[d])
      m[d] = ++k;
    w.push_back(m[d] - 1);
  }
  return w;
}
#ifndef Q9_FREE_BRIDGE_JOIN_NO_MAIN
int main(int argc, char **argv) {
  if (argc != 7)
    return 1;
  lenA = stoi(argv[1]);
  lenBridge = stoi(argv[2]);
  lenB = stoi(argv[3]);
  int stride = stoi(argv[4]);
  maxLeft = stoi(argv[5]);
  int rightStride = stoi(argv[6]);
  target = lenA + lenBridge + lenB;
  if (lenA < 0 || lenBridge < 0 || lenB < 0 || target > 511 || stride < 1 ||
      rightStride < 1 || maxLeft < 1)
    return 1;
  vector<Path> left;
  set<Path> aset, bset;
  string row;
  while (getline(cin, row)) {
    Path s;
    istringstream rowStream(row);
    int x;
    while (rowStream >> x) {
      if (x < 0 || x > 511)
        return 2;
      s.push_back(x);
    }
    if (!rowStream.eof() || s.empty())
      return 2;
    if (!valid(s))
      return 3;
    for (int dir : {1, -1}) {
      if (dir == -1)
        reverse(s.begin(), s.end());
      // Coordinate order is canonicalized starting from the bridge interface.
      for (int a = 0; a + lenA < s.size(); a += stride) {
        auto w = word(s, a + lenA, -1, lenA);
        if (aset.insert(w).second) {
          Path arm(s.begin() + a, s.begin() + a + lenA + 1);
          left.push_back(arm);
        }
      }
      for (int a = 0; a + lenB < s.size(); a += rightStride)
        bset.insert(word(s, a, 1, lenB));
    }
  }
  for (auto &w : bset) {
    int id = 0;
    for (int z : w) {
      int k = trie[id].child[z];
      if (!k) {
        k = trie.size();
        trie[id].child[z] = k;
        trie[id].active |= 1 << z;
        trie.emplace_back();
      }
      id = k;
    }
  }
  cerr << "lefts " << left.size() << " rights " << bset.size() << " trie "
       << trie.size() << " target " << target << endl;
  for (auto &arm : left) {
    if (anchors >= maxLeft)
      break;
    p = arm;
    blocked.fill(0);
    for (int v : p)
      mark(v, 1);
    auto old = bridges;
    bridge(lenBridge);
    goodAnchors += old != bridges;
    ++anchors;
    if (anchors % 500 == 0)
      cerr << "processed " << anchors << " bridges " << bridges
           << " trie_states " << states << endl;
  }
  if (!onPair) cout << "NO_JOIN anchors " << anchors << " extendible_anchors " << goodAnchors
       << " bridges " << bridges << " right_forms " << bset.size()
       << " trie_states " << states << endl;
  return 0;
}
#endif
