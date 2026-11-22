using System;
using System.Linq;
using System.Collections.Generic;
using System.Reflection;

// After the deletions, insertions can only increase the occupancy counts at the
// opposite vertices. A selected minority vertex needs two distinct path neighbours.
class EnumerateExchanges {
    static readonly int[][] N = Enumerable.Range(0,256).Select(v =>
        Enumerable.Range(0,8).Select(d => v ^ (1<<d)).ToArray()).ToArray();
    static readonly Type Solver = typeof(ReplayExchange).GetNestedType("Side",BindingFlags.NonPublic);
    static readonly MethodInfo Solve = Solver.GetMethod("Enumerate");
    static int[] seed, outside, drops, adds;
    static readonly int[] counts = new int[256];
    static readonly bool[] used = new bool[256];
    static int radius, removalSets, accepted;

    static void Set(int v, bool value) {
        used[v] = value;
        foreach (int y in N[v]) counts[y] += value ? 1 : -1;
    }
    static int Supply(int v, int limit) {
        int found = 0;
        foreach (int y in N[v]) if (counts[y] <= limit && ++found == 2) return 2;
        return found;
    }
    static bool HasSupply() {
        foreach (int v in seed) if (used[v] && Supply(v,2)<2) return false;
        foreach (int v in adds) if (used[v] && Supply(v,2)<2) return false;
        return true;
    }
    static void Insert(int depth, int start, int[] options) {
        if (depth == radius) {
            if (counts.Count(d=>d==1)<2) return;
            int[] side = Enumerable.Range(0,256).Where(v=>used[v]).ToArray();
            Console.WriteLine("C {0} {1} {2}", accepted, string.Join(",",drops),string.Join(",",adds));
            object instance=Activator.CreateInstance(Solver,new object[]{side,accepted,0});
            Solve.Invoke(instance,null);
            accepted++;
            return;
        }
        for (int j=start;j<=options.Length-(radius-depth);j++) {
            int v=options[j];
            if (Supply(v,1)<2) continue;
            adds[depth]=v;
            Set(v,true);
            if (HasSupply()) Insert(depth+1,j+1,options);
            Set(v,false);
        }
    }
    static void Remove(int depth,int start) {
        if (depth==radius) {
            removalSets++;
            int[] options=outside.Where(v=>Supply(v,1)>=2).ToArray();
            Insert(0,0,options);
            return;
        }
        for (int j=start;j<=seed.Length-(radius-depth);j++) {
            int v=seed[j];
            drops[depth]=v;
            Set(v,false);
            Remove(depth+1,j+1);
            Set(v,true);
        }
    }
    public static void Main(string[] args) {
        radius=int.Parse(args[0]);
        seed=Console.ReadLine().Split(',').Select(int.Parse).ToArray();
        foreach (int v in seed) Set(v,true);
        int parity=Convert.ToString(seed[0],2).Count(c=>c=='1')%2;
        outside=Enumerable.Range(0,256).Where(v=>!used[v] && Convert.ToString(v,2).Count(c=>c=='1')%2==parity).ToArray();
        if (seed.Length!=48 || outside.Length!=80 || seed.Distinct().Count()!=48) throw new ArgumentException();
        drops=new int[radius]; adds=new int[radius];
        Remove(0,0);
        Console.WriteLine("T {0} {1}",removalSets,accepted);
    }
}
