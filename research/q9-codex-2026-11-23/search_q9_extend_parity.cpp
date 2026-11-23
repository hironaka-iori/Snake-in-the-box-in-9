#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <sstream>

struct Candidates {
  Search &solver;
  bool majority;
  vector<int> available, slots;
  uint64_t &ruled;
  static uint64_t choose(int n, int k) {
    if (k > n)
      return 0;
    uint64_t result = 1;
    for (int i = 0; i < k; i++)
      result = result * (n - i) / (i + 1);
    return result;
  }
  bool possible(int v) const {
    int options = 0;
    for (int i = 0; i < 9; i++)
      options += popcount(unsigned(solver.axes[v ^ (1 << i)])) <= 1;
    return options >= (majority ? 1 : 2);
  }
  bool visit(int at, int start) {
    if (at == slots.size())
      return solver.test();
    int still = slots.size() - at;
    for (int i = start; i + still <= available.size(); i++) {
      int x = available[i];
      if (!possible(x)) {
        ruled += choose(available.size() - i - 1, still - 1);
        continue;
      }
      int slot = slots[at];
      solver.fixed[slot] = x;
      solver.toggle(x, slot, true);
      if (visit(at + 1, i + 1))
        return true;
      solver.toggle(x, slot, false);
    }
    return false;
  }
};
int main(int argc, char **argv) {
  if (argc != 4)
    return 2;
  int goal = stoi(argv[1]), removed = stoi(argv[2]);
  bool majority = stoi(argv[3]) != 0;
  if (goal % 2 || removed < 0 || removed > 1)
    return 2;
  string line;
  uint64_t tests = 0, ruled = 0, unknown = 0;
  int sides = 0;
  while (getline(cin, line)) {
    istringstream row(line);
    vector<int> p;
    int v;
    while (row >> v)
      p.push_back(v);
    if (p.size() < 3)
      return 2;
    for (int i = 0; i < p.size(); i++) {
      if (p[i] < 0 || p[i] >= 512)
        return 3;
      for (int j = 0; j < i; j++) {
        int d = popcount(unsigned(p[i] ^ p[j]));
        if (d == 0 || ((i == j + 1) != (d == 1)))
          return 3;
      }
    }
    for (int side = 0; side <= 1; side++) {
      vector<int> a;
      for (int j = side; j < p.size(); j += 2)
        a.push_back(p[j]);
      int wanted = goal / 2 + int(majority);
      if (wanted < int(a.size()) || wanted - int(a.size()) + removed > 3)
        return 4;
      ++sides;
      Search s(a, 80000, majority);
      vector<int> pool;
      for (int x = 0; x < 512; x++)
        if (s.slot[x] < 0 && popcount(unsigned(x ^ a[0])) % 2 == 0)
          pool.push_back(x);
      s.fixed.resize(wanted, -1);
      for (int cut = 0; cut < (removed ? a.size() : 1); cut++) {
        Candidates branch{s, majority, {}, {}, ruled};
        if (removed) {
          s.toggle(a[cut], cut, false);
          branch.slots.push_back(cut);
        }
        for (int h = a.size(); h < wanted; h++)
          branch.slots.push_back(h);
        for (int x : pool)
          if (branch.possible(x))
            branch.available.push_back(x);
        int k = branch.slots.size();
        ruled += Candidates::choose(pool.size(), k) -
                 Candidates::choose(branch.available.size(), k);
        if (branch.visit(0, 0))
          return 0;
        if (removed) {
          s.fixed[cut] = a[cut];
          s.toggle(a[cut], cut, true);
        }
      }
      tests += s.tested;
      unknown += s.unknown;
    }
  }
  cout << "sides " << sides << " tested " << tests << " ruled " << ruled
       << " unknown " << unknown << endl;
}
