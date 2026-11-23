#include "triple_capture.inc"
#include <numeric>
P readword(string w){P p{0};for(char c:w)p.push_back(p.back() ^ (1<<(c-'0')));check(p);return p;}
int main(int argc,char**argv){
 if(argc!=8)return 2;string mode=argv[1],prefix=argv[7];int per=stoi(argv[2]),maxGap=stoi(argv[3]),cap=stoi(argv[4]),maxBridge=stoi(argv[5]),goal=stoi(argv[6]);
 string source=mode=="control"?"../q9_far189_spring_20261121/comparison191.words":"../q9_uncovered_abab_20261121/outside_wordbanks189.words";
 ifstream in(source);vector<P>src;string w;while(in>>w)src.push_back(readword(w));
 if(mode!="control"&&src.size()!=16)abort();
 mt19937 rng(91277+maxGap);int i=-1;for(const P&p:src){i++;int n=p.size();if(mode=="control"&&i)break;
  Triple e(prefix+to_string(i),goal);e.nodeCap=cap;e.each=maxBridge;for(int v:p)e.host[v]=true;
  int selected=0,different=0,deformed=0;
  for(int job=0;job<per&&!e.stopped;job++){
   int lt=job%4==0?0:rng()%10,rt=job%4==0?0:rng()%10;
   int g1=3+rng()%(maxGap-2),g2=3+rng()%(maxGap-2);
   int lo=lt+8+rng()%(n-rt-lt-g1-g2-24+1);
   int hi=lo+g1+8+rng()%(n-rt-8-g2-(lo+g1+8)+1);
   if(mode=="control"){lt=rt=0;g1=5;g2=7;lo=36;hi=117;}
   P raw[3]={P(p.begin()+lt,p.begin()+lo),P(p.begin()+lo+g1,p.begin()+hi),P(p.begin()+hi+g2,p.end()-rt)};
   int donor=-1,ds=0,len=0,revDon=0;array<int,9>m;iota(m.begin(),m.end(),0);
   if(mode=="graft"){
    donor=rng()%src.size();if(donor==i)donor=(donor+1)%src.size();auto &q=src[donor];
    // Choose an interval of comparable size and match both original cut endpoints after an isometry.
    int old=raw[1].size();bool placed=false;
    for(int s=0;s<14&&!placed;s++){
     len=max(5,old+int(rng()%13)-5);if(len>=(int)q.size())continue;ds=rng()%(q.size()-len+1);revDon=rng()%2;
     int q0=q[ds+(revDon?len-1:0)],q1=q[ds+(revDon?0:len-1)];int from=q0^q1,to=raw[1].front()^raw[1].back();
     if(popcount(unsigned(from))!=popcount(unsigned(to)))continue;
     array<vector<int>,2>orig,dest;for(int d=0;d<9;d++){orig[(from>>d)&1].push_back(d);dest[(to>>d)&1].push_back(d);}
     for(int trial=0;trial<7&&!placed;trial++){
      for(int b=0;b<2;b++){if(trial)shuffle(dest[b].begin(),dest[b].end(),rng);for(int t=0;t<(int)orig[b].size();t++)m[orig[b][t]]=dest[b][t];}
      P alt{raw[1].front()};for(int k=1;k<len;k++){int j=ds+(revDon?len-1-k:k);int diff=q[j]^q[j+(revDon?1:-1)];alt.push_back(alt.back()^(1<<m[countr_zero(unsigned(diff))]));}
      if(alt==raw[1]||alt.back()!=raw[1].back())continue;
      bool bad=false;array<bool,512>mask{};for(int b:{0,2})for(int v:raw[b]){mask[v]=true;for(int d=0;d<9;d++)mask[v^(1<<d)]=true;}
      for(int v:alt)if(mask[v]){bad=true;break;}
      if(!bad){raw[1]=move(alt);placed=true;}
     }
    }
    if(!placed)continue;deformed++;
   }
   array<int,3>ord={0,1,2};int orient=0;
   if(mode=="reorder"){do{shuffle(ord.begin(),ord.end(),rng);orient=rng()%8;}while((ord==array<int,3>{0,1,2}&&orient==0)||(ord==array<int,3>{2,1,0}&&orient==7));different++;}
   else if(mode=="graft"&&job%4==0){orient=2;}
   for(int b=0;b<3;b++){e.parts[b]=raw[ord[b]];if((orient>>b)&1)reverse(e.parts[b].begin(),e.parts[b].end());for(int v:e.parts[b])e.mark(v,1);}
   stringstream tag;tag<<i<<","<<lt<<","<<rt<<","<<lo<<","<<g1<<","<<hi<<","<<g2<<","<<ord[0]<<ord[1]<<ord[2]<<","<<orient<<","<<donor<<","<<ds<<","<<len<<","<<revDon<<",";for(int d:m)tag<<d;
   e.tag=tag.str();e.localNodes=0;e.tries++;selected++;e.connect(0,e.parts[0].back());for(auto&a:e.parts)for(int v:a)e.mark(v,-1);
  }
  cout<<"ROW "<<i<<" "<<per<<" "<<selected<<" "<<different<<" "<<deformed<<" "<<e.calls<<" "<<e.capHits<<" "<<e.connected<<" "<<e.mids.size()<<" "<<e.tipNodes<<" "<<e.tipCuts<<" "<<e.best<<" "<<e.seen191.size()<<endl;
  if(e.stopped)return 0;
 }
}
