#define NO_JOINT_MAIN
#include "joint.cpp"
#undef main
struct Early: Joint {
 using Joint::Joint;
 P removed;
 void reorder(P& opts){sort(opts.begin(),opts.end(),[&](int a,int b){return raw.edges[a]!=raw.edges[b]?raw.edges[a]<raw.edges[b]:a<b;});}
 void remove(int x,bool undo){
   if(undo)raw.selected.set(x);else raw.selected.reset(x);
   for(int g=1;g<512;g++)if(raw.selected[x^g]){
     raw.edges[g]+=undo?1:-1;
     raw.hits[g].set(x,undo);raw.hits[g].set(x^g,undo);
   }
 }
 bool budget(){if(++nodes>cap)unknown=true;return !unknown;}
 void arbitrary(int start,int todo,int weight,const Bits&protectedSet){
   if(hit||unknown)return;
   if(!todo){
      if(weight<lo||weight>T-h)return;
      P retained;for(int v:pts)if(raw.selected[v])retained.push_back(v);runs++;
      if(complete_forest(dirs,retained,T,baseid)){
        hit=true;cout<<"EXTRA";for(int x:removed)cout<<' '<<x;cout<<endl;
      }return;
   }
   for(int j=start;j<(int)pts.size();j++){int x=pts[j];if(protectedSet[x]||!raw.selected[x])continue;
      int d=0;for(int g:dirs)d+=raw.selected[x^g];raw.selected.reset(x);removed.push_back(x);
      arbitrary(j+1,todo-1,weight-d,protectedSet);removed.pop_back();raw.selected.set(x);
      if(hit||unknown)return;
   }
 }
 void repair(P opts,int left,int todo,const Bits&forbid,const P&space,const Bits&span){
   if(hit||unknown||!budget())return;
   Bits once,twice,bad;int sum=0;
   for(int g:dirs){sum+=raw.edges[g];bad|=twice&raw.hits[g];twice|=once&raw.hits[g];once^=raw.hits[g];}
   if(sum>T-h+9*todo)return;
   if(bad.any()){
     if(!todo||bad.count()>(dirs.size()+1)*todo)return;
     int x=-1;for(int v:pts)if(bad[v]){x=v;break;}
     P conflict{x};for(int g:dirs)if(raw.selected[x^g]){conflict.push_back(x^g);if(conflict.size()==4)break;}
     Bits protect=forbid;
     for(int v:conflict)if(!protect[v]){
       remove(v,false);removed.push_back(v);repair(opts,left,todo-1,protect,space,span);
       removed.pop_back();remove(v,true);protect.set(v);if(unknown||hit)return;
     }return;
   }
   if(!left){bases++;arbitrary(0,todo,sum,forbid);return;}
   reorder(opts);dfs2(opts,left,todo,sum,forbid,once,twice,space,span);
 }
 void dfs2(const P&opts,int left,int todo,int sum,const Bits&forbid,const Bits&once,const Bits&twice,const P&space,const Bits&span){
   if(hit||unknown||!budget())return;int n=opts.size();if(n<left)return;
   int low=sum,high=sum,ceil=T-h+9*todo;
   for(int j=0;j<left;j++){low+=raw.edges[opts[j]];high+=raw.edges[opts[n-1-j]];}if(low>ceil||high<lo)return;
   for(int j=0;j+left<=n;j++){int g=opts[j],w=sum+raw.edges[g];if(sum+left*raw.edges[g]>ceil)break;if(left==1&&w<lo)continue;
     Bits bad=twice&raw.hits[g];if(bad.count()>(11-left)*todo)continue;
     dirs.push_back(g);
     if(left==1&&!bad.any()){bases++;arbitrary(0,todo,w,forbid);}
     else{
       Bits sp=span;P ext=space;for(int z:space){sp.set(z^g);ext.push_back(z^g);}
       Bits two=twice|(once&raw.hits[g]);P next;int maxg=ceil-w-(left-2)*raw.edges[g];
       for(int k=j+1;k<n&&left>1;k++){int y=opts[k];if(raw.edges[y]>maxg)break;
           if(!sp[y]&&(bad|(two&raw.hits[y])).count()<=(12-left)*todo)next.push_back(y);}
       if(bad.any())repair(next,left-1,todo,forbid,ext,sp);
       else dfs2(next,left-1,todo,w,forbid,once^raw.hits[g],two,ext,sp);
     }
     dirs.pop_back();if(unknown||hit)return;
   }
 }
};
int main(int argc,char**argv){
 if(argc!=4)return 2;int target=atoi(argv[1]),h=atoi(argv[3]);if(h<1||h>3)return 3;long long cap=atoll(argv[2]);int tag=0;string l;
 while(getline(cin,l)){istringstream in(l);string prefix;in>>prefix;if(prefix!="points")return 4;P pts;int x;Bits seen;while(in>>x){if(x<0||x>=512||seen[x])return 5;seen.set(x);pts.push_back(x);}
   Early s(pts,target,cap,tag,h);if(s.t<0||s.t>3)return 6;P opts(511);iota(opts.begin(),opts.end(),1);s.reorder(opts);Bits sp;sp.set(0);
   s.dfs2(opts,9,s.t,0,Bits(),Bits(),Bits(),P{0},sp);
   cout<<"R "<<tag++<<' '<<(s.hit?"FOUND":s.unknown?"UNKNOWN":"CLOSED")<<' '<<s.nodes<<' '<<s.bases<<' '<<s.runs<<endl;if(s.hit)break;
 }
}
