#include <chrono>
#include <map>
#include <unordered_set>
// CPU snakepit annealing with whole-proposal rollback and optional DCV bias.
// Based on Orland et al., arXiv:2607.15270v3, Algorithms 2 and 3.
#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <vector>
using namespace std;
using Path = vector<int>;
uint64_t randomState;
uint32_t nextU() {
  randomState ^= randomState << 13;
  randomState ^= randomState >> 7;
  randomState ^= randomState << 17;
  return randomState >> 32;
}
int pick(int n) { return (uint64_t(nextU()) * n) >> 32; }
double uniform() { return (nextU() + 0.5) / 4294967296.; }
int other(int x, int prev, uint16_t mask) {
  int m = mask;
  if (prev >= 0)
    m ^= x ^ prev;
  return m ? x ^ (m & -m) : -1;
}
set<string> known;
string key(const Path &p) {
  string w;
  for (int i = 1; i < p.size(); i++)
    w += char(countr_zero(unsigned(p[i] ^ p[i - 1])));
  auto norm = [](string s) {
    int map[8] = {}, n = 0;
    for (char &c : s) {
      int d = c;
      if (!map[d])
        map[d] = ++n;
      c = char(map[d] + '0' - 1);
    }
    return s;
  };
  string a = norm(w);
  reverse(w.begin(), w.end());
  return min(a, norm(w));
}
bool valid(const Path &p) {
  if (p.empty())
    return false;
  for (int i = 0; i < p.size(); i++)
    for (int j = 0; j < i; j++)
      if (p[i] == p[j] ||
          ((popcount(unsigned(p[i] ^ p[j])) == 1) != (j + 1 == i)))
        return false;
  return true;
}
struct Pit {
  uint16_t nb[256]{};
  uint8_t live[256]{};
  int nv = 0, cc = 0;
  array<int, 8> axes{};
  Path chain(int x) const {
    Path p;
    int prev = -1;
    while (x >= 0) {
      p.push_back(x);
      int z = other(x, prev, nb[x]);
      prev = x;
      x = z;
      if (p.size() > 256)
        abort();
    }
    return p;
  }
  bool legal(int x) const {
    if (live[x])
      return false;
    int m = nb[x], d = popcount(unsigned(m));
    if (d > 2)
      return false;
    for (int z = m; z; z &= z - 1)
      if (popcount(unsigned(nb[x ^ (z & -z)])) >= 2)
        return false;
    if (d < 2)
      return true;
    int a = x ^ (m & -m), b = x ^ (m & (m - 1)), prev = -1;
    while (a >= 0) {
      if (a == b)
        return false;
      int n = other(a, prev, nb[a]);
      prev = a;
      a = n;
    }
    return true;
  }
  void set(int x, bool value) {
    int s = value ? 1 : -1;
    int m = nb[x];
    live[x] = value;
    nv += s;
    cc += (1 - popcount(unsigned(m))) * s;
    for (int d = 0; d < 8; d++) {
      int b = 1 << d;
      nb[x ^ b] ^= b;
      if (m & b)
        axes[d] += s;
    }
  }
  void audit() const {
    int v = 0, e = 0;
    array<int, 8> a{};
    bool seen[256]{};
    int components = 0;
    for (int x = 0; x < 256; x++) {
      int mask = 0;
      for (int d = 0; d < 8; d++)
        if (live[x ^ (1 << d)])
          mask |= 1 << d;
      if (nb[x] != mask)
        abort();
      if (!live[x])
        continue;
      ++v;
      int deg = popcount(unsigned(mask));
      if (deg > 2)
        abort();
      e += deg;
      for (int d = 0; d < 8; d++)
        if (mask >> d & 1)
          ++a[d];
      if (seen[x] || deg > 1)
        continue;
      auto q = chain(x);
      ++components;
      for (int y : q) {
        if (seen[y])
          abort();
        seen[y] = true;
      }
    }
    for (int x = 0; x < 256; x++)
      if (live[x] != seen[x])
        abort();
    if (v != nv || e / 2 != nv - cc || components != cc)
      abort();
    for (int d = 0; d < 8; d++)
      if (a[d] != 2 * axes[d])
        abort();
  }
};
array<int, 32> faces[256];
int faceN[256];
vector<int> masks[6];
struct Trial {
  Pit &p;
  int xs[256];
  int count = 0;
  void set(int x, bool val) {
    if (count == 256)
      abort();
    xs[count++] = x;
    p.set(x, val);
  }
  void revert() {
    while (count) {
      int x = xs[--count];
      p.set(x, !p.live[x]);
    }
  }
};
void surgery(Trial &t) {
  int dim = 2 + pick(4), m = masks[dim][pick(masks[dim].size())],
      base = pick(256) & ~m, n = faceN[m];
  auto cell = faces[m];
  for (int i = 0; i < n; i++) {
    cell[i] |= base;
    if (t.p.live[cell[i]])
      t.set(cell[i], false);
  }
  for (;;) {
    int before = t.count;
    for (int phase = 0; phase < 2; phase++) {
      for (int i = n - 1; i > 0; i--)
        swap(cell[i], cell[pick(i + 1)]);
      for (int i = 0; i < n; i++) {
        int x = cell[i];
        if ((phase || t.p.nb[x]) && t.p.legal(x))
          t.set(x, true);
      }
    }
    if (before == t.count)
      break;
  }
}

using M = array<uint64_t, 4>;
using Arms = array<Path, 2>;
M mask(const Pit &p) {
  M bits{};
  for (int i = 0; i < 256; i++)
    if (p.live[i])
      bits[i / 64] |= 1ull << (i % 64);
  return bits;
}
Arms getArms(const Pit &p) {
  Arms w;
  int k = 0;
  array<bool, 256> seen{};
  for (int i = 0; i < 256; i++)
    if (p.live[i] && !seen[i] && popcount(unsigned(p.nb[i])) <= 1) {
      if (k == 2)
        abort();
      w[k] = p.chain(i);
      for (int x : w[k])
        seen[x] = true;
      k++;
    }
  if (k != 2 || w[0].size() + w[1].size() != p.nv)
    abort();
  return w;
}
void endpoint(Trial &t) {
  int x = pick(256);
  for (int j = 0; j < 48 && (!t.p.live[x] || popcount(unsigned(t.p.nb[x])) > 1);
       j++)
    x = pick(256);
  if (!t.p.live[x] || popcount(unsigned(t.p.nb[x])) > 1)
    return;
  auto p = t.p.chain(x);
  if (p.size() < 3)
    return;
  int k = min(int(p.size()) - 2, 1 + pick(13));
  for (int j = 0; j < k; j++)
    t.set(p[j], false);
  x = p[k];
  int maxSteps = k + 2 + pick(5);
  for (int j = 0; j < maxSteps; j++) {
    int d = pick(8), odd = 1 + 2 * pick(4);
    bool ok = false;
    for (int n = 0; n < 8; n++, d = (d + odd) & 7) {
      int y = x ^ (1 << d);
      if (!t.p.live[y] && popcount(unsigned(t.p.nb[y])) == 1 && t.p.legal(y)) {
        t.set(y, true);
        x = y;
        ok = true;
        break;
      }
    }
    if (!ok)
      break;
  }
}
string signature(Arms arms) {
  string best;
  for (int sw = 0; sw < 2; sw++) {
    if (sw)
      swap(arms[0], arms[1]);
    for (int dir = 0; dir < 4; dir++) {
      string k;
      int labels[8]{};
      int ct = 0;
      for (int j = 0; j < 2; j++) {
        auto &a = arms[j];
        for (int t = 1; t < a.size(); t++) {
          int idx = (dir >> j) & 1 ? int(a.size()) - t : t;
          int bit = countr_zero(unsigned(a[idx] ^ a[idx - 1]));
          if (!labels[bit])
            labels[bit] = ++ct;
          k += char(labels[bit]);
        }
        k += ':';
      }
      unsigned rel = arms[0][dir & 1 ? arms[0].size() - 1 : 0] ^
                     arms[1][dir & 2 ? arms[1].size() - 1 : 0];
      int abs = 0, other = 0;
      for (int j = 0; j < 8; j++)
        if (rel >> j & 1) {
          if (labels[j])
            abs |= 1 << (labels[j] - 1);
          else
            other++;
        }
      k += char(abs);
      k += char(other);
      if (best.empty() || k < best)
        best = k;
    }
  }
  return best;
}
int main(int argc, char **argv) {
  if (argc != 7)
    return 1;
  string file = argv[1];
  int secs = stoi(argv[2]);
  randomState = stoull(argv[3]);
  double temp = stod(argv[4]);
  int reset = stoi(argv[5]), policy = stoi(argv[6]);
  for (int m = 1; m < 256; m++) {
    int d = popcount(unsigned(m));
    if (d < 2 || d > 5)
      continue;
    masks[d].push_back(m);
    int n = 0;
    for (int z = m;; z = (z - 1) & m) {
      faces[m][n++] = z;
      if (!z)
        break;
    }
    faceN[m] = n;
  }
  Pit initial;
  ifstream in(file);
  int n;
  while (in >> n) {
    int v;
    for (int i = 0; i < n; i++) {
      if (!(in >> v) || !initial.legal(v))
        return 3;
      initial.set(v, true);
    }
  }
  initial.audit();
  if (initial.cc < 1 || initial.cc > 8)
    return 4;
  Pit p = initial;
  map<int, vector<Pit>> bank;
  set<M> seen;
  set<string> shapes;
  map<int, int> kept;
  int best = 0;
  long long checks = 0, accepted = 0, trials = 0;
  auto save = [&]() {
    if (p.nv < 100 || p.cc != 2)
      return;
    auto bits = mask(p);
    if (!seen.insert(bits).second)
      return;
    auto q = getArms(p);
    if (!shapes.insert(signature(q)).second)
      return;
    int shortLen = min(q[0].size(), q[1].size());
    if (kept[shortLen] >= 70 && p.nv <= best)
      return;
    p.audit();
    if (!valid(q[0]) || !valid(q[1]))
      abort();
    for (int a : q[0])
      for (int b : q[1])
        if (popcount(unsigned(a ^ b)) < 2)
          abort();
    ++kept[shortLen];
    best = max(best, p.nv);
    int base = q[0][0];
    for (const auto &a : q) {
      cout << a.size();
      for (int v : a)
        cout << " " << (v ^ base);
      cout << " ";
    }
    cout << endl;
    auto &list = bank[shortLen];
    if (list.size() < 100)
      list.push_back(p);
    else
      list[pick(list.size())] = p;
  };
  int aim=policy;
  double weight=.43;
  auto orig=getArms(initial); int shortOld=min(orig[0].size(),orig[1].size());
  map<int,vector<Pit>> front;map<int,int> heights;
  save();
  auto begin = chrono::steady_clock::now();
  for (;;) {
    ++trials;
    if ((trials & 65535) == 0 &&
        chrono::duration<double>(chrono::steady_clock::now() - begin).count() >=
            secs)
      break;
    if (trials % reset == 0) {
       if (pick(4)==0 || front.empty()) p=initial;
       else {auto k=front.begin();advance(k,pick(front.size()));p=k->second[pick(k->second.size())];}
       auto now=getArms(p);shortOld=min(now[0].size(),now[1].size());
    }
    int old = p.nv, oldcc = p.cc;
    Trial t{p};
    int coin = pick(100);
    if (coin < 4) {
      surgery(t);
      surgery(t);
    } else if (coin < 57)
      surgery(t);
    else if (coin < 81)
      endpoint(t);
    else {
      int x = pick(256);
      if (p.live[x])
        t.set(x, false);
      else if (p.legal(x))
        t.set(x, true);
    }
    if (!t.count)
      continue;
    int cand=shortOld;
    bool ok=p.cc==2 && p.nv>=88;
    if(ok){
      int root=-1;
      for(int x=0;x<256;x++) if(p.live[x]&&popcount(unsigned(p.nb[x]))<2){root=x;break;}
      int now=root,prev=-1,n=0;
      while(now>=0){++n;int v=other(now,prev,p.nb[now]);prev=now;now=v;}
      cand=min(n,p.nv-n);
    }
    double advantage = p.nv-old-weight*(abs(cand-aim)-abs(shortOld-aim));
    if (ok && advantage < 0)
      ok = uniform() <
           exp(advantage /
               max(.04, temp * (1. - double(trials % reset) / reset)));
    if (ok) {
      ++accepted;shortOld=cand;
      if(p.nv>=96 && p.nv>=heights[cand] && (trials%157==0 || heights[cand]<p.nv)){
         if(heights[cand]<p.nv){front[cand].clear();heights[cand]=p.nv;}
         auto &f=front[cand];if(f.size()<14)f.push_back(p);else f[pick(f.size())]=p;
      }
      if (p.cc == 2 && p.nv >= 100) {
        ++checks;
        save();
      }
    } else
      t.revert();
  }
  cerr << "proposals " << trials << " accepted " << accepted << " good_states "
       << checks << " count_shapes " << shapes.size() << " best " << best
       << " bins";
  for (auto &[k, n] : kept)
    cerr << " " << k << ":" << n;
  cerr << " heights";for(auto [x,n]:heights)if(n>=98)cerr<<" "<<x<<":"<<n;cerr<<endl;
}
