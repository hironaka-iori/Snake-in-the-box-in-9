using System;
using System.Collections.Generic;
using System.Linq;

// An extra vertex closes the two ends of the contracted path into a cycle.
// Its incident edges carry exactly the legal singleton attachment labels.
class ReplayExchange {
    const int Dummy = 48;
    const int Count = 49;

    sealed class Edge {
        public readonly int U, V;
        public readonly List<int> Labels = new List<int>();
        public Edge(int u, int v) { U = u; V = v; }
        public int Other(int v) { return U == v ? V : U; }
    }

    sealed class Side {
        readonly int[] vertices;
        readonly List<Edge> edges = new List<Edge>();
        readonly List<int>[] incident = new List<int>[Count];
        readonly int removed, added;
        long cycles, paths;

        public Side(int[] values, int remove, int add) {
            vertices = values;
            removed = remove;
            added = add;
            int[] index = Enumerable.Repeat(-1, 256).ToArray();
            for (int i = 0; i < Dummy; i++) index[vertices[i]] = i;
            var ids = new Dictionary<int,int>();
            for (int i = 0; i < Count; i++) incident[i] = new List<int>();
            for (int y = 0; y < 256; y++) {
                int first = -1, second = -1, neighbours = 0;
                for (int bit = 0; bit < 8; bit++) {
                    int pos = index[y ^ (1 << bit)];
                    if (pos < 0) continue;
                    neighbours++;
                    if (neighbours == 1) first = pos;
                    if (neighbours == 2) second = pos;
                    if (neighbours == 3) break;
                }
                if (neighbours != 1 && neighbours != 2) continue;
                if (neighbours == 1) second = Dummy;
                int u = Math.Min(first,second), v = Math.Max(first,second);
                int key = Count*u + v, id;
                if (!ids.TryGetValue(key,out id)) {
                    id = edges.Count;
                    ids.Add(key,id);
                    edges.Add(new Edge(u,v));
                    incident[u].Add(id);
                    incident[v].Add(id);
                }
                edges[id].Labels.Add(y);
            }
        }

        // 0 undecided, 1 selected, -1 excluded. Every vertex must have degree two.
        void Select(sbyte[] state) {
            bool changed;
            int branch;
            do {
                changed = false;
                branch = -1;
                int fewest = int.MaxValue;
                for (int u = 0; u < Count; u++) {
                    int taken = 0, available = 0, last = -1;
                    foreach (int e in incident[u]) {
                        if (state[e] == 1) taken++;
                        if (state[e] == 0) { available++; last = e; }
                    }
                    if (taken > 2 || taken + available < 2) return;
                    if (available == 0) continue;
                    if (taken == 2 || taken + available == 2) {
                        sbyte force = (sbyte)(taken == 2 ? -1 : 1);
                        foreach (int e in incident[u]) if (state[e] == 0) state[e] = force;
                        changed = true;
                    } else if (available < fewest) {
                        fewest = available;
                        branch = last;
                    }
                }
            } while (changed);
            if (branch >= 0) {
                var include = (sbyte[])state.Clone();
                include[branch] = 1;
                Select(include);
                state[branch] = -1;
                Select(state);
                return;
            }

            // A two-factor is useful only when its cycle through Dummy spans all 49 vertices.
            // The smaller indexed first edge fixes reversal for the entire cycle.
            int at = Dummy, previous = -1;
            var route = new List<int>();
            do {
                int next = -1;
                foreach (int e in incident[at]) {
                    if (state[e] == 1 && e != previous) { next = e; break; }
                }
                if (next < 0) throw new InvalidOperationException("Degree mismatch");
                route.Add(next);
                at = edges[next].Other(at);
                previous = next;
            } while (at != Dummy);
            if (route.Count != Count) return;
            cycles++;
            int[] path = new int[2*Dummy + 1];
            at = Dummy;
            for (int i = 0; i < Dummy; i++) {
                at = edges[route[i]].Other(at);
                path[2*i+1] = vertices[at];
            }
            Expand(route,0,path);
        }

        void Expand(List<int> route, int i, int[] path) {
            if (i == Count) {
                paths++;
                string sequence = path[0] < path[path.Length-1]
                    ? string.Join(",",path) : string.Join(",",path.Reverse());
                Console.WriteLine("P {0} {1} {2}",removed,added,sequence);
                return;
            }
            foreach (int label in edges[route[i]].Labels) {
                path[2*i] = label;
                Expand(route,i+1,path);
            }
        }

        public void Enumerate() {
            Select(new sbyte[edges.Count]);
            Console.WriteLine("S {0} {1} {2} {3}",removed,added,cycles,paths);
        }
    }

    static int Parity(int v) {
        int parity = 0;
        while (v != 0) { parity ^= 1; v &= v-1; }
        return parity;
    }

    public static void Main() {
        int[] seed = Console.ReadLine().Split(',').Select(int.Parse).OrderBy(v=>v).ToArray();
        if (seed.Length != Dummy || seed.Distinct().Count() != Dummy ||
            seed.Any(v=>v<0 || v>=256 || Parity(v)!=Parity(seed[0]))) {
            throw new ArgumentException("Invalid seed side");
        }
        new Side(seed,-1,-1).Enumerate();
        for (int i = 0; i < seed.Length; i++) {
            for (int v = 0; v < 256; v++) {
                if (Parity(v) != Parity(seed[0]) || Array.BinarySearch(seed,v) >= 0) continue;
                int[] side = (int[])seed.Clone();
                side[i] = v;
                Array.Sort(side);
                new Side(side,seed[i],v).Enumerate();
            }
        }
    }
}
