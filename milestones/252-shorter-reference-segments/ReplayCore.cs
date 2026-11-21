using System;
using System.Collections.Generic;
using System.Linq;

// Fix the core, grow a short arm trie on one side, and grow the other arm
// independently. Combine a trie branch only if all its vertices avoid the
// closed neighbourhood of the long arm's added vertices.
class ReplayCore {
    sealed class Node {
        public int vertex, first = -1, next = -1, height;
        public Node(int v) { vertex = v; }
    }
    static readonly int[][] ball = new int[256][];
    static readonly HashSet<string> words = new HashSet<string>();
    static readonly int[] axis = new int[256];
    static readonly int[] longPath = new int[99], shortPath = new int[99];
    static int[] core, occupied, cross;
    static int k, shortLimit, longLimit;
    static bool longOnRight;
    static List<Node> trie;
    static long shortNodes, longNodes, fits;

    static void Change(int[] counts, int v, int delta) {
        foreach (int u in ball[v]) counts[u] += delta;
    }

    static int[] BlockCore(int endpoint) {
        int[] counts = new int[256];
        foreach (int v in core) {
            if (v == endpoint) counts[v]++;
            else Change(counts, v, 1);
        }
        return counts;
    }

    static int ShortArm(int tip, int depth, int[] scope) {
        Node node = new Node(tip);
        int index = trie.Count;
        trie.Add(node);
        shortNodes++;
        if (depth == shortLimit) return index;
        for (int j = 0; j < 8; j++) {
            int next = tip ^ (1 << j);
            if (scope[next] != 0) continue;
            Change(scope, tip, 1);
            int child = ShortArm(next, depth + 1, scope);
            Change(scope, tip, -1);
            trie[child].next = node.first;
            node.first = child;
            node.height = Math.Max(node.height, 1 + trie[child].height);
        }
        return index;
    }

    static string Word(int[] path, bool reverse) {
        char[] word = new char[path.Length-1];
        int[] codes = new int[8];
        int letters = 0;
        for (int i = 0; i < word.Length; i++) {
            int t = reverse ? word.Length-1-i : i;
            int a = axis[path[t] ^ path[t+1]];
            if (codes[a] == 0) codes[a] = ++letters;
            word[i] = (char)('0' + codes[a] - 1);
        }
        return new string(word);
    }

    static void Record(int shortDepth, int longDepth) {
        fits++;
        int[] path = new int[k+1+shortDepth+longDepth];
        int n = 0;
        for (int i = shortDepth; i > 0; i--) path[n++] = shortPath[i];
        for (int i = 0; i <= k; i++) path[n++] = core[longOnRight ? i : k-i];
        for (int i = 1; i <= longDepth; i++) path[n++] = longPath[i];
        string a = Word(path, false), b = Word(path, true);
        string word = String.CompareOrdinal(a, b) <= 0 ? a : b;
        if (words.Add(word)) Console.WriteLine("P " + word + " " + String.Join(",", path));
    }

    static void Combine(int index, int depth, int lo, int hi, int longDepth) {
        Node node = trie[index];
        if (depth + node.height < lo) return;
        if (depth >= lo) Record(depth, longDepth);
        if (depth == hi) return;
        for (int c = node.first; c >= 0; c = trie[c].next) {
            int v = trie[c].vertex;
            if (cross[v] != 0) continue;
            shortPath[depth+1] = v;
            Combine(c, depth+1, lo, hi, longDepth);
        }
    }

    static void LongArm(int tip, int depth) {
        longNodes++;
        int lo = Math.Max(0, 96-k-depth);
        int hi = Math.Min(98-k-depth, depth-(longOnRight ? 0 : 1));
        if (lo <= hi && lo <= trie[0].height) Combine(0, 0, lo, hi, depth);
        if (depth == longLimit) return;
        for (int j = 0; j < 8; j++) {
            int next = tip ^ (1 << j);
            if (occupied[next] != 0) continue;
            longPath[depth+1] = next;
            Change(occupied, tip, 1);
            Change(cross, next, 1);
            LongArm(next, depth+1);
            Change(cross, next, -1);
            Change(occupied, tip, -1);
        }
    }

    public static void Main() {
        for (int i = 0; i < 8; i++) axis[1 << i] = i;
        for (int v = 0; v < 256; v++) {
            ball[v] = new int[9]; ball[v][0] = v;
            for (int j = 0; j < 8; j++) ball[v][j+1] = v ^ (1 << j);
        }
        string line;
        while ((line = Console.ReadLine()) != null) {
            string[] parts = line.Split(' ');
            core = Array.ConvertAll(parts[1].Split(','), Int32.Parse);
            k = core.Length-1;
            shortLimit = (98-k)/2;
            longLimit = 98-k;
            shortNodes = longNodes = fits = 0;
            foreach (bool onRight in new bool[]{true,false}) {
                longOnRight = onRight;
                int s = core[onRight ? 0 : k], l = core[onRight ? k : 0];
                trie = new List<Node>();
                ShortArm(s, 0, BlockCore(s));
                cross = new int[256];
                occupied = BlockCore(l);
                LongArm(l, 0);
            }
            Console.WriteLine("C {0} {1} {2} {3}", parts[0], shortNodes, longNodes, fits);
        }
    }
}
