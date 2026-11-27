using System;
using System.Linq;
using System.Collections.Generic;
public class Orbit {
    static readonly ulong[] masks={0x5555555555555555UL,0x3333333333333333UL,0x0F0F0F0F0F0F0F0FUL,0x00FF00FF00FF00FFUL,0x0000FFFF0000FFFFUL,0x00000000FFFFFFFFUL};
    static readonly long[] counts=new long[100];
    static readonly ulong[] original=new ulong[4];
    static readonly int[] map=new int[256],perm=new int[8],axis=new int[256],winner=new int[8];
    static int[] sites; static int closest=100,translation;
    static int Pop(ulong x) {x-=((x>>1)&masks[0]); x=(x&masks[1])+((x>>2)&masks[1]);return (int)((((x+(x>>4))&masks[2])*0x0101010101010101UL)>>56);}
    static ulong Shift(ulong x,int i) {int sh=1<<i; return ((x&masks[i])<<sh)|((x>>sh)&masks[i]);}
    static void Visit(int idx,int used) {
        if(idx<8) {for(int b=0;b<8;b++) if((used&(1<<b))==0){perm[idx]=b;Visit(idx+1,used|(1<<b));}return;}
        for(int v=1;v<256;v++) map[v]=map[v&(v-1)]|(1<<perm[axis[v]]);
        ulong[] w=new ulong[4];
        foreach(int v in sites){int x=map[v];w[x>>6]|=1UL<<(x&63);}
        for(int n=0;n<256;n++) {
            if(n!=0){int ax=axis[n];if(ax<6){for(int k=0;k<4;k++)w[k]=Shift(w[k],ax);}
                else{int j=1<<(ax-6);for(int k=0;k<4;k++)if((k&j)==0){ulong u=w[k];w[k]=w[k^j];w[k^j]=u;}}}
            int d=99-Pop(w[0]&original[0])-Pop(w[1]&original[1])-Pop(w[2]&original[2])-Pop(w[3]&original[3]);
            counts[d]++;
            if(d>0 && d<closest){closest=d;translation=n^(n>>1);Array.Copy(perm,winner,8);}
        }
    }
    public static void Main() {sites=Console.ReadLine().Split(',').Select(int.Parse).ToArray();foreach(int x in sites)original[x>>6]|=1UL<<(x&63);
        for(int x=1;x<256;x++){int y=x;while((y&1)==0){axis[x]++;y>>=1;}}
        Visit(0,0);Console.WriteLine(string.Join(",",counts));Console.WriteLine(string.Join(",",winner));Console.WriteLine(translation);}
}
