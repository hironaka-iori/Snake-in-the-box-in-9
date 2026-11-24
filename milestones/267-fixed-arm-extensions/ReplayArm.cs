using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;

// Rebuild the full induced graph after deleting and inserting one site.
// This enumerator determines the path order from adjacency, including suffix reversals.
class ReplayArm {
    static readonly int[][] Neighbours = Enumerable.Range(0,256)
        .Select(v => Enumerable.Range(0,8).Select(i => v ^ (1 << i)).ToArray()).ToArray();
    readonly bool[] blocked = new bool[256], occupied = new bool[256];
    readonly int[] degree = new int[256], stamp = new int[256];
    readonly int floor;
    int serial;
    readonly char[] ordered = new char[100];
    HashSet<string> adjacent;

    ReplayArm(string parent, int min) {
        floor=min;
        foreach(char v in parent) if(v!=0) blocked[v]=true;
    }
    void Mark(int v, bool value) {
        occupied[v]=value;
        foreach(int w in Neighbours[v]) degree[w]+=value ? 1 : -1;
    }
    void Admit(string p) {
        if(p.Length-1<floor)return;
        foreach(char v in p) if(v!=0 && blocked[v])return;
        adjacent.Add(p);
    }
    void EndpointChoices(string p) {
        Admit(p);
        if(p.Length-2>=floor)Admit(p.Substring(0,p.Length-1));
        if(p.Length>=99)return;
        foreach(int w in Neighbours[p[p.Length-1]])
            if(!occupied[w] && degree[w]==1 && !blocked[w])Admit(p+(char)w);
    }
    void Inspect(int w,int removedDegree,int count) {
        if(occupied[w] || degree[w]!=removedDegree)return;
        foreach(int v in Neighbours[w])
            if(occupied[v] && degree[v]+1>(v==0 ? 1 : 2))return;
        Mark(w,true);
        if(degree[0]==1) {
            int current=0,previous=-1,length=0;
            while(current!=-1 && length<count) {
                ordered[length++]=(char)current;
                int next=-1;
                foreach(int v in Neighbours[current])if(occupied[v] && v!=previous){next=v;break;}
                previous=current;current=next;
            }
            if(length==count && current==-1)EndpointChoices(new string(ordered,0,count));
        }
        Mark(w,false);
    }
    HashSet<string> Next(string p) {
        adjacent=new HashSet<string>(StringComparer.Ordinal);
        foreach(char v in p)Mark(v,true);
        EndpointChoices(p);
        for(int i=1;i<p.Length;i++) {
            int removed=p[i],d=degree[removed];
            Mark(removed,false);
            serial++;
            foreach(int end in new int[]{0,p[p.Length-1],p[i-1],i+1<p.Length ? p[i+1] : -1}) {
                if(end<0 || !occupied[end])continue;
                foreach(int w in Neighbours[end]) {
                    if(w==removed || stamp[w]==serial)continue;
                    stamp[w]=serial;
                    Inspect(w,d,p.Length);
                }
            }
            Mark(removed,true);
        }
        foreach(char v in p)Mark(v,false);
        return adjacent;
    }
    void Traverse(List<string> start) {
        var seen=new HashSet<string>(start,StringComparer.Ordinal);
        var queue=new Queue<string>(seen);
        long transitions=0;
        while(queue.Count>0) {
            var next=Next(queue.Dequeue());
            transitions+=next.Count;
            foreach(string q in next)if(seen.Add(q))queue.Enqueue(q);
        }
        using(var buffer=new MemoryStream()) {
            foreach(string p in seen.OrderBy(x=>x,StringComparer.Ordinal)){
                buffer.WriteByte((byte)p.Length);
                foreach(char v in p)buffer.WriteByte((byte)v);
            }
            buffer.Position=0;
            using(var hash=SHA256.Create())
                Console.WriteLine(seen.Count+" "+transitions+" "+BitConverter.ToString(hash.ComputeHash(buffer)).Replace("-","").ToLowerInvariant());
        }
    }
    static string Parse(string line){return new string(line.Split(',').Select(v=>(char)int.Parse(v)).ToArray());}
    static void Main(string[] args) {
        var walk=new ReplayArm(Parse(Console.ReadLine()),int.Parse(args[0]));
        var starts=new List<string>();
        string line;
        while((line=Console.ReadLine())!=null)if(line.Length>0)starts.Add(Parse(line));
        walk.Traverse(starts);
    }
}
