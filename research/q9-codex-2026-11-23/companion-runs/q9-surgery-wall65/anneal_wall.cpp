// CPU snakepit annealing with whole-proposal rollback and optional DCV bias.
// Based on Orland et al., arXiv:2607.15270v3, Algorithms 2 and 3.
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <filesystem>
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
    int map[9] = {}, n = 0;
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
  uint16_t nb[512]{};
  uint8_t live[512]{};
  int nv = 0, cc = 0;
  array<int, 9> axes{};
  Path chain(int x) const {
    Path p;
    int prev = -1;
    while (x >= 0) {
      p.push_back(x);
      int z = other(x, prev, nb[x]);
      prev = x;
      x = z;
      if (p.size() > 512)
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
    for (int d = 0; d < 9; d++) {
      int b = 1 << d;
      nb[x ^ b] ^= b;
      if (m & b)
        axes[d] += s;
    }
  }
  void audit() const {
    int v = 0, e = 0;
    array<int, 9> a{};
    bool seen[512]{};
    int components = 0;
    for (int x = 0; x < 512; x++) {
      int mask = 0;
      for (int d = 0; d < 9; d++)
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
      for (int d = 0; d < 9; d++)
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
    for (int x = 0; x < 512; x++)
      if (live[x] != seen[x])
        abort();
    if (v != nv || e / 2 != nv - cc || components != cc)
      abort();
    for (int d = 0; d < 9; d++)
      if (a[d] != 2 * axes[d])
        abort();
  }
};
array<int, 16> faces[512];
int faceN[512];
vector<int> masks[5];
struct Trial {
  Pit &p;
  int xs[64];
  int count = 0;
  void set(int x, bool val) {
    if (count == 64)
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
  int dim = 2 + pick(3), m = masks[dim][pick(masks[dim].size())],
      base = pick(512) & ~m, n = faceN[m];
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
double reward(const Pit &p, double bias) {
  int d = *max_element(p.axes.begin(), p.axes.end());
  double distance = max(0, max(45 - d, d - 51));
  double strength = min(1., max(0., (p.nv - p.cc - 145) / 35.));
  return p.nv - 3.2 * abs(p.cc - 1) - bias * strength * min(distance, 12.);
}
int main(int argc, char **argv) {
  if (argc != 12)
    return 2;
  string input = argv[1], bankfile = argv[2];
  long long steps = stoll(argv[3]), period = stoll(argv[4]);
  randomState = stoull(argv[5]);
  double bias = stod(argv[6]), T0 = stod(argv[7]);
  bool tabu = stoi(argv[8]);
  string cp = argv[9];
  int seconds = stoi(argv[10]), interval = stoi(argv[11]);
  if (seconds < 1 || interval < 1)
    return 2;
  auto startTime = chrono::steady_clock::now();
  auto nowSeconds = [&]() {
    return chrono::duration<double>(chrono::steady_clock::now() - startTime)
        .count();
  };
  double elapsedBase = 0, nextSave = interval;
  long long previousStep = 0, actual = 0;
  if (!randomState || period <= 0)
    return 2;
  for (int m = 1; m < 512; m++) {
    int d = popcount(unsigned(m));
    if (d < 2 || d > 4)
      continue;
    masks[d].push_back(m);
    int n = 0;
    for (int b = m;; b = (b - 1) & m) {
      faces[m][n++] = b;
      if (!b)
        break;
    }
    faceN[m] = n;
  }
  ifstream bank(bankfile);
  string s;
  while (bank >> s)
    known.insert(s);
  if (known.size() != 131)
    return 3;
  Pit p;
  int allBest = -1, gapBest = -1;
  long long accepted = 0, surgeries = 0, tabuHits = 0, updates = 0;
  if (input != "-") {
    ifstream in(input);
    if (!in)
      return 4;
    int x;
    while (in >> x) {
      if (x < 0 || x >= 512 || !p.legal(x))
        return 4;
      p.set(x, true);
    }
  }
  if (filesystem::exists(cp)) {
    ifstream in(cp);
    string ver;
    int count;
    in >> ver >> previousStep >> randomState >> elapsedBase >> allBest >>
        gapBest >> accepted >> surgeries >> tabuHits >> updates >> count;
    if (!in || ver != "Q9S1" || count < 0 || count > 512)
      return 8;
    p = Pit{};
    int v;
    for (int j = 0; j < count; j++) {
      if (!(in >> v) || v < 0 || v > 511 || !p.legal(v))
        return 8;
      p.set(v, true);
    }
    nextSave = (floor(elapsedBase / interval) + 1) * interval;
  }
  auto checkpoint = [&](long long step) {
    p.audit();
    string tmp = cp + ".tmp";
    ofstream f(tmp);
    f.precision(15);
    f << "Q9S1 " << step << " " << randomState << " "
      << elapsedBase + nowSeconds() << " " << allBest << " " << gapBest << " "
      << accepted << " " << surgeries << " " << tabuHits << " " << updates
      << " " << p.nv;
    for (int x = 0; x < 512; x++)
      if (p.live[x])
        f << " " << x;
    f << endl;
    f.close();
    if (!f || rename(tmp.c_str(), cp.c_str()))
      abort();
  };
  p.audit();
  cout << "START " << p.nv << " " << p.cc << "\n";
  auto emit = [&](long long step) {
    if (p.cc != 1 || !p.nv)
      return;
    int length = p.nv - 1;
    int hi = *max_element(p.axes.begin(), p.axes.end());
    bool gap = hi >= 45 && hi <= 51;
    if (length <= allBest && (!gap || length <= gapBest))
      return;
    int endpoint = 0;
    while (endpoint < 512 &&
           (!p.live[endpoint] || popcount(unsigned(p.nb[endpoint])) > 1))
      ++endpoint;
    auto q = p.chain(endpoint);
    if (q.size() != p.nv || !valid(q))
      abort();
    bool in = length == 191 && known.count(key(q));
    if (length > allBest || (gap && length > gapBest)) {
      cout << "SNAKE " << step << " " << length << " " << hi << " " << in;
      for (int v : q)
        cout << " " << v;
      cout << endl;
      ++updates;
    }
    allBest = max(allBest, length);
    if (gap)
      gapBest = max(gapBest, length);
  };
  emit(previousStep);
  checkpoint(previousStep);
  for (long long i = previousStep + 1; i <= steps; i++) {
    if ((i & 65535) == 0) {
      double elapsed = elapsedBase + nowSeconds();
      if (elapsed >= seconds) {
        actual = i - 1;
        break;
      }
      if (elapsed >= nextSave) {
        checkpoint(i - 1);
        nextSave += interval;
      }
    }
    actual = i;
    double old = reward(p, bias);
    Trial t{p};
    int z = pick(10000);
    if (z < 3500) {
      ++surgeries;
      surgery(t);
    } else {
      int x = pick(512);
      if (z < 6750) {
        if (p.legal(x))
          t.set(x, true);
      } else if (p.live[x])
        t.set(x, false);
    }
    if (!t.count)
      continue;
    double diff = reward(p, bias) - old,
           T = max(0.0001, T0 * (1. - double((i - 1) % period) / period));
    bool ok = diff >= 0 || uniform() < exp(diff / T);
    if (ok && p.cc == 1 && p.nv >= 192) {
      int x = 0;
      while (!p.live[x] || popcount(unsigned(p.nb[x])) > 1)
        ++x;
      auto q = p.chain(x);
      if (!valid(q) || q.size() != p.nv)
        abort();
      if (p.nv >= 193 || !known.count(key(q))) {
        cout << "TARGET " << i << " " << q.size() - 1;
        for (int x : q)
          cout << " " << x;
        cout << endl;
        if (q.size() == 192) {
          for (int side = 0; side < 2; ++side) {
            for (int bit = 0; bit < 9; ++bit) {
              int v = (side ? q.back() : q.front()) ^ (1 << bit);
              Path w = q;
              if (side)
                w.push_back(v);
              else
                w.insert(w.begin(), v);
              if (valid(w)) {
                cout << "EXTENDED " << i << " " << w.size() - 1;
                for (int z : w)
                  cout << " " << z;
                cout << endl;
              }
            }
          }
        }
        checkpoint(i);
        return 0;
      }
      if (tabuHits == 0 && tabu) {
        cout << "KNOWN_CANDIDATE " << i << " " << q.size() - 1;
        for (int v : q)
          cout << " " << v;
        cout << endl;
      }
      if (tabu) {
        ok = false;
        ++tabuHits;
      }
    }
    if (ok) {
      ++accepted;
      emit(i);
    } else
      t.revert();
    if ((i & 65535) == 0)
      p.audit();
  }
  checkpoint(actual);
  cout << "ELAPSED " << elapsedBase + nowSeconds() << endl;
  cout << "END best " << allBest << " gap_best " << gapBest << " proposals "
       << actual << " accepted_nonempty " << accepted << " surgeries "
       << surgeries << " rejected_known " << tabuHits << " reports " << updates
       << endl;
}
