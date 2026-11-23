// Search unrestricted extensions of both ends around sliding central fragments.
#define Q9_FREE_BRIDGE_JOIN_NO_MAIN
#include "search_q9_free_bridge_join.cpp"
using Count = unsigned long long;
int goalEdges, needed, maxRight;
Count leftNodes = 0, rightNodes = 0, preNodes = 0;
Path core, leftAdd, rightAdd;
set<Path> excludedShapes;
Count excludedMatches = 0;
Path shape(const Path &path) {
  int n = path.size() - 1;
  return min(word(path, 0, 1, n), word(path, n, -1, n));
}
void outputBoth() {
  Path candidate(leftAdd.rbegin(), leftAdd.rend());
  candidate.insert(candidate.end(), core.begin(), core.end());
  candidate.insert(candidate.end(), rightAdd.begin(), rightAdd.end());
  if ((int)candidate.size() != goalEdges + 1 || !valid(candidate))
    exit(8);
  if (!excludedShapes.empty() && excludedShapes.count(shape(candidate))) {
    ++excludedMatches;
    return;
  }
  cout << "FOUND";
  for (int x : candidate)
    cout << " " << x;
  cout << endl;
  exit(0);
}
// Cache right-prefix capacities with just the core occupied. Later left
// extensions can only remove legal continuations from any given prefix.
struct RightPrefix {
  array<int, 9> child{};
  int remaining = 0;
};
vector<RightPrefix> rightPrefixes;
constexpr int cacheDepth = 16;
int getRightMax(int v, int dep, int node) {
  ++preNodes;
  maxRight = max(maxRight, dep);
  int longest = 0;
  if (dep < needed) {
    for (int d=0; d<9; ++d) {
      int w=v^(1<<d);
      if(blocked[w]!=1)continue;
      int child=0;
      if(dep<cacheDepth) {
        child=rightPrefixes.size();
        rightPrefixes[node].child[d]=child;
        rightPrefixes.emplace_back();
      }
      mark(w,1);
      longest=max(longest,1+getRightMax(w,dep+1,child));
      mark(w,-1);
    }
  }
  if(node)rightPrefixes[node].remaining=longest;
  return longest;
}
void extendRight(int v, int remain, int node) {
  ++rightNodes;
  if(node && rightPrefixes[node].remaining<remain)return;
  if(!remain){outputBoth();return;}
  for(int d=0;d<9;d++){
    int w=v^(1<<d);
    if(blocked[w]!=1)continue;
    mark(w,1); rightAdd.push_back(w);
    extendRight(w,remain-1,node?rightPrefixes[node].child[d]:0);
    rightAdd.pop_back();mark(w,-1);
  }
}
void extendLeft(int v, int remain) {
  ++leftNodes;
  if (remain <= maxRight)
    extendRight(core.back(), remain, 1);
  if (!remain)
    return;
  for (int d = 0; d < 9; ++d) {
    int w = v ^ (1 << d);
    if (blocked[w] != 1)
      continue;
    mark(w, 1);
    leftAdd.push_back(w);
    extendLeft(w, remain - 1);
    leftAdd.pop_back();
    mark(w, -1);
  }
}
int main(int argc, char **argv) {
  bool skipKnown = argc == 5 && string(argv[4]) == "--outside-input";
  if (argc != 4 && !skipKnown)
    return 1;
  int len = stoi(argv[1]);
  goalEdges = stoi(argv[2]);
  int stride = stoi(argv[3]);
  if (len < 1 || len > goalEdges || goalEdges > 511 || stride < 1)
    return 1;
  needed = goalEdges - len;
  set<Path> seen;
  vector<Path> inputBank;
  string line;
  while (getline(cin, line)) {
    istringstream in(line);
    Path input;
    int x;
    while (in >> x) {
      if (x < 0 || x > 511)
        return 2;
      input.push_back(x);
    }
    if (!in.eof() || !valid(input))
      return 3;
    if (skipKnown && input.size() == goalEdges + 1)
      excludedShapes.insert(shape(input));
    inputBank.push_back(input);
  }
  for (const auto &input : inputBank) {
    for (int a = 0; a + len < input.size(); a += stride) {
      auto w = min(word(input, a, 1, len), word(input, a + len, -1, len));
      if (!seen.insert(w).second)
        continue;
      core.assign(input.begin() + a, input.begin() + a + len + 1);
      blocked.fill(0);
      for (int q : core)
        mark(q, 1);
      maxRight = 0;
      rightPrefixes.assign(2,RightPrefix{});
      getRightMax(core.back(), 0, 1);
      extendLeft(core.front(), needed);
      if (seen.size() % 1000 == 0)
        cerr << "processed " << seen.size() << endl;
    }
  }
  cout << "NO_JOIN cores " << seen.size() << " independent_right_nodes "
       << preNodes << " left_nodes " << leftNodes << " paired_right_nodes "
       << rightNodes << " excluded_matches " << excludedMatches << endl;
}
