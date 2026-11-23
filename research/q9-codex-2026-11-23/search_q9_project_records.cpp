// Enumerate coordinate maps onto Q9 up to relabeling. A zero image contracts an
// edge.
#include <algorithm>
#include <array>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
using Path = std::vector<int>;
struct Search {
  int n = 0, minimum = 189, limit = 0, best = 0, row = 0, maps = 0;
  long long total = 0, bridges = 0;
  bool shortcuts = false, cyclic = false;
  Path steps, p;
  std::array<int, 16> mapping{};
  std::array<std::array<int, 10>, 512> near{};
  std::array<std::unordered_set<std::string>, 193> found;
  static bool valid(const Path &seq, int d) {
    std::vector<bool> used(1 << d);
    int prev = -1;
    for (int v : seq) {
      if (used[v] || (prev >= 0 && __builtin_popcount(v ^ prev) != 1))
        return false;
      for (int a = 0; a < d; a++) {
        int w = v ^ (1 << a);
        if (w != prev && used[w])
          return false;
      }
      used[v] = true;
      prev = v;
    }
    return true;
  }
  static std::string key(Path::const_iterator b, Path::const_iterator e) {
    std::string s;
    for (auto i = b + 1; i != e; i++)
      s.push_back(__builtin_ctz(*i ^ *(i - 1)));
    auto normalize = [](std::string w) {
      std::array<int, 9> a;
      a.fill(-1);
      int k = 0;
      for (char &c : w) {
        auto &v = a[int(c)];
        if (v < 0)
          v = k++;
        c = v;
      }
      return w;
    };
    auto f = normalize(s);
    std::reverse(s.begin(), s.end());
    return std::min(f, normalize(s));
  }
  void check() {
    maps++;
    total++;
    p = {0};
    for (int a : steps)
      if (mapping[a])
        p.push_back(p.back() ^ mapping[a]);
    std::array<int, 512> last;
    last.fill(-1);
    int left = 0, longest = 0;
    Path suffix;
    if (shortcuts)
      suffix.resize(p.size());
    for (int i = 0; i < p.size(); i++) {
      if (i >= 2)
        for (int w : near[p[i - 2]])
          last[w] = i - 2;
      left = std::max(left, last[p[i]] + 1);
      int len = i - left;
      best = std::max(best, len);
      longest = std::max(longest, len);
      if (shortcuts)
        suffix[i] = len + 1;
      for (int k = minimum; k <= std::min(len, 192); k++) {
        auto e = p.begin() + i + 1, b = e - k - 1;
        if (found[k].insert(key(b, e)).second) {
          Path hit(b, e);
          if (!valid(hit, 9))
            std::abort();
          std::cout << "PATH " << k << " " << row << " " << maps;
          for (int v : hit)
            std::cout << " " << v;
          std::cout << '\n';
          if (k == 192) {
            std::cout.flush();
            std::exit(0);
          }
        }
      }
    }
    if (shortcuts && 2 * (longest + 1) >= minimum + 1)
      join(suffix);
  }
  void join(const Path &suffix) {
    int n = p.size(), end = n - 1;
    std::array<int, 512> next;
    next.fill(n);
    std::array<Path, 512> positions;
    Path prefix(n);
    for (int i = n - 1; i >= 0; i--) {
      if (i + 2 < n)
        for (int w : near[p[i + 2]])
          next[w] = i + 2;
      end = std::min(end, next[p[i]] - 1);
      prefix[i] = end - i + 1;
      positions[p[i]].push_back(i);
    }
    int maxright = *std::max_element(prefix.begin(), prefix.end());
    for (int i = 0; i < n; i++) {
      if (suffix[i] + maxright <= minimum)
        continue;
      for (int axis = 0; axis < 9; axis++)
        for (int j : positions[p[i] ^ (1 << axis)]) {
          if (j <= i + 1)
            break;
          if (suffix[i] + prefix[j] <= minimum)
            continue;
          bridges++;
          std::array<int, 512> first;
          first.fill(prefix[j]);
          for (int r = prefix[j] - 1; r >= 1; r--)
            for (int w : near[p[j + r]])
              first[w] = r;
          int right = first[p[i]];
          for (int l = 1; l <= suffix[i]; l++) {
            int x = p[i - l + 1];
            if (l > 1) {
              if (__builtin_popcount(x ^ p[j]) <= 1)
                break;
              right = std::min(right, first[x]);
            }
            if (right + suffix[i] <= minimum)
              break;
            for (int k = minimum; k <= std::min(192, l + right - 1); k++) {
              int take = k + 1 - l;
              if (take < 1)
                continue;
              Path hit(p.begin() + i - l + 1, p.begin() + i + 1);
              hit.insert(hit.end(), p.begin() + j, p.begin() + j + take);
              if (!found[k].insert(key(hit.begin(), hit.end())).second)
                continue;
              if (!valid(hit, 9))
                std::abort();
              best = std::max(best, k);
              std::cout << "PATH " << k << " " << row << " " << maps;
              for (int v : hit)
                std::cout << " " << v;
              std::cout << char(10);
              if (k == 192) {
                std::cout.flush();
                std::exit(0);
              }
            }
          }
        }
    }
  }
  void visit(int axis, int used) {
    if ((limit && maps >= limit) || used + n - axis < 9)
      return;
    if (axis == n) {
      check();
      return;
    }
    mapping[axis] = 0;
    visit(axis + 1, used);
    for (int j = 0; j < std::min(9, used + 1); j++) {
      mapping[axis] = 1 << j;
      visit(axis + 1, std::max(used, j + 1));
    }
  }
  void run() {
    for (int v = 0; v < 512; v++) {
      near[v][0] = v;
      for (int i = 0; i < 9; i++)
        near[v][i + 1] = v ^ (1 << i);
    }
    std::string line;
    while (getline(std::cin, line)) {
      std::istringstream s(line);
      if (!(s >> n) || n < 9 || n > 15)
        std::exit(2);
      steps.clear();
      int a;
      Path original{0};
      while (s >> a) {
        if (a < 0 || a >= n)
          std::exit(2);
        steps.push_back(a);
        original.push_back(original.back() ^ (1 << a));
      }
      if (cyclic) {
        if (original.size() < 5 || original.back() != 0)
          std::exit(3);
        original.pop_back();
        // In a chordless cycle, deleting either of two different vertices
        // leaves a snake.
        Path cut(original.begin() + 1, original.end());
        if (!valid(cut, n))
          std::exit(3);
        int adjacent = 0;
        for (int w : original)
          adjacent += __builtin_popcount(unsigned(w)) == 1;
        if (adjacent != 2 ||
            std::count(original.begin(), original.end(), 0) != 1)
          std::exit(3);
        auto loop = steps;
        steps.insert(steps.end(), loop.begin(), loop.end());
      } else if (!valid(original, n))
        std::exit(3);
      row++;
      maps = 0;
      visit(0, 0);
    }
    std::cerr << "rows " << row << " maps " << total << " best " << best;
    for (int k = minimum; k <= 192; k++)
      std::cerr << " length" << k << " " << found[k].size();
    std::cerr << std::endl;
  }
};
int main(int argc, char **argv) {
  Search s;
  if (argc > 1)
    s.minimum = std::stoi(argv[1]);
  if (argc > 2)
    s.limit = std::stoi(argv[2]);
  if (s.minimum < 1 || s.minimum > 192)
    return 2;
  s.shortcuts = argc > 3 && std::string(argv[3]) == "--shortcut";
  for (int i = 3; i < argc; i++) {
    if (std::string(argv[i]) == "--cycle")
      s.cyclic = true;
    if (std::string(argv[i]) == "--shortcut")
      s.shortcuts = true;
  }
  s.run();
  if (s.shortcuts)
    std::cerr << "eligible shortcut pairs " << s.bridges << char(10);
}
