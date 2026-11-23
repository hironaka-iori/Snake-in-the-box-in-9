#define main bank_main
#include "join.cpp"
#undef main
U outerMasks[3];int targetOuter;uint64_t parts[5],countBy[60],aligned[60];
int outerEnds[3];
bool complete(R a,int astart,int total){
 int need=goal-total;
 auto p1=options(astart,a.m&~(U(1)<<astart),need-39);if(p1.empty())return false;
 auto p4=options(0,outerMasks[0]&~U(1),need-p1[0].n-26);
 for(auto q:p4){
  auto p3=options(q.tip,outerMasks[1]|(q.m&~(U(1)<<q.tip)),need-q.n-p1[0].n-14);
  if(p3.empty())continue;
  for(auto p:p1){
   if(q.n+p.n+26<need)break;if(q.m&p.m)continue;
   auto p2=options(p.tip,outerMasks[2]|(p.m&~(U(1)<<p.tip)),need-q.n-p.n-p3[0].n);
   for(auto s:p2)for(auto t:p3){
    if(s.n+t.n+p.n+q.n<need)break;
    if(s.tip!=t.tip||(s.m&t.m)!=(U(1)<<s.tip))continue;
    middle[0]=walk(p.m,astart);middle[1]=walk(s.m,p.tip);middle[2]=walk(t.m,s.tip);middle[3]=walk(q.m,q.tip);
    R b{outerMasks[0],outerEnds[0],popcount(outerMasks[0])},c{outerMasks[1],outerEnds[1],popcount(outerMasks[1])},d{outerMasks[2],outerEnds[2],popcount(outerMasks[2])};
    emit(a,b,c,d,astart,0);return true;
   }
  }
 }
 return false;
}
void recurse(int k,int sum,int x,U m,U blocked,int named){
 ++parts[k];int n=popcount(m);constexpr int relax[]={0,14,26};
 if(sum+n+relax[2-k]+14>=targetOuter){
  outerMasks[k]=m;outerEnds[k]=x;
  if(k<2)recurse(k+1,sum+n,x,U(1)<<x,m&~(U(1)<<x),named);
  else{
   U free=~(m|outerMasks[0]);int lo=targetOuter-sum-n;
   if(popcount(free)>=lo){++parts[3];for(U v=free;v;v&=v-1){
    int r=countr_zero(v);for(auto a:options(r,~free,lo)){int total=sum+n+a.n;++countBy[total];++parts[4];
     if(complete(a,r,total)){++aligned[total];cout<<"FOUND"<<endl;exit(0);}
    }
   }}
  }
 }
 for(int i=0;i<5&&i<=named;i++){int y=x^(1<<i);if((m|blocked)&(U(1)<<y))continue;
  recurse(k,sum,y,m|(U(1)<<y),blocked|N[x],named+(i==named));}
}
int main(int argc,char**argv){if(argc!=3)return 2;goal=stoi(argv[1]);targetOuter=stoi(argv[2]);for(int v=0;v<32;v++)for(int d=0;d<5;d++)N[v]|=U(1)<<(v^(1<<d));
 recurse(0,0,0,1,0,0);cout<<"DONE target "<<goal<<" outer_min "<<targetOuter<<" nodes";for(auto v:parts)cout<<" "<<v;cout<<" outerCounts";for(int i=targetOuter;i<55;i++)cout<<" "<<i<<"="<<countBy[i];cout<<endl;}
