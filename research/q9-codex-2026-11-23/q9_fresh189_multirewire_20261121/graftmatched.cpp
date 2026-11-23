#include "triple_capture.inc"
#include <sstream>
int main(int argc,char**argv){
 if(argc!=7)return 2;int per=stoi(argv[1]),maxGap=stoi(argv[2]),maxBridge=stoi(argv[3]),budget=stoi(argv[4]),limit=stoi(argv[5]);string out=argv[6];
 ifstream in("poses.dat");int x,id=0;mt19937 rng(183491+maxGap);Triple e(out,192);e.nodeCap=budget;e.each=maxBridge;
 unsigned long long combos=0,cuts=0,good=0;int poses=0;
 while(in>>x&&!e.stopped){P A(190),B(190);A[0]=x;for(int k=1;k<190;k++)in>>A[k];for(int&v:B)in>>v;id++;if(limit>0&&id>limit)break;poses++;
  for(int which=0;which<2;which++){if(which)swap(A,B);array<int,512>where;where.fill(-1);e.host.fill(false);for(int i=0;i<190;i++){where[B[i]]=i;e.host[A[i]]=true;}
   vector<array<int,4>> choices;
   for(int i=12;i<170;i++)if(where[A[i]]>=0)for(int j=i+8;j<178;j++)if(where[A[j]]>=0){
    int k=where[A[i]],l=where[A[j]];if(abs(l-k)<7||abs(l-k-j+i)>14)continue;
    if(abs(l-k)==j-i){bool eq=true;for(int t=1;t<j-i&&eq;t++)eq=A[i+t]==B[k+(l>k?t:-t)];if(eq)continue;}
    choices.push_back({i,j,k,l});
   }
   combos+=choices.size();if(choices.empty())continue;
   for(int t=0;t<per&&!e.stopped;t++){
    auto [i,j,k,l]=choices[rng()%choices.size()];int g1=3+rng()%(maxGap-2),g2=3+rng()%(maxGap-2);int lt=rng()%9,rt=rng()%9;
    if(i-g1-lt<7||190-j-g2-1-rt<7)continue;cuts++;e.parts[0].assign(A.begin()+lt,A.begin()+i-g1);
    e.parts[1].clear();int d=k<l?1:-1;for(int z=k;;z+=d){e.parts[1].push_back(B[z]);if(z==l)break;}
    e.parts[2].assign(A.begin()+j+g2+1,A.end()-rt);
    int rev=(t%5==0)?2:0;if(rev)reverse(e.parts[1].begin(),e.parts[1].end());
    bool ok=true;for(auto &p:e.parts){for(int v:p)if(e.use[v]||e.adj[v])ok=false;for(int v:p)e.mark(v,1);}
    if(ok){good++;e.tries++;e.tag=to_string(id-1)+","+to_string(which)+","+to_string(lt)+","+to_string(rt)+","+to_string(i)+","+to_string(j)+","+to_string(k)+","+to_string(l)+","+to_string(g1)+","+to_string(g2)+","+to_string(rev);
     e.localNodes=0;e.connect(0,e.parts[0].back());}
    for(auto&p:e.parts)for(int v:p)e.mark(v,-1);
   }
  }
 }
 cout<<"DONE "<<poses<<" "<<combos<<" "<<cuts<<" "<<good<<" "<<e.calls<<" "<<e.capHits<<" "<<e.connected<<" "<<e.mids.size()<<" "<<e.tipNodes<<" "<<e.tipCuts<<" "<<e.best<<" "<<e.seen191.size()<<endl;
}
