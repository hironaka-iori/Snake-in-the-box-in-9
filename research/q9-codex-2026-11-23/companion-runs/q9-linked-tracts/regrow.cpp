#include <algorithm>
#include <array>
#include <fstream>
#include <string>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;using M=array<uint64_t,3>;using Clock=chrono::steady_clock;
int wt(int x){return popcount(unsigned(x));}bool has(M m,int x){return (m[x/64]>>(x%64))&1;}void put(M&m,int x){m[x/64]|=1ull<<(x%64);}M plusM(M a,M b){for(int k=0;k<3;k++)a[k]|=b[k];return a;}M minusM(M a,M b){for(int k=0;k<3;k++)a[k]&=~b[k];return a;}int weight(M a){return popcount(a[0])+popcount(a[1])+popcount(a[2]);}
mt19937 rng;int draw(int n){return rng()%n;}uint64_t rand64(){return (uint64_t(rng())<<32)^rng();}
uint64_t salts[512];int nb[512][9];
bool valid(const P&p){array<unsigned char,512>d{},on{};for(int i=0;i<p.size();i++){int x=p[i];if(on[x]||d[x]!=(i!=0)||(i&&! (wt(x^p[i-1])==1)))return false;on[x]=1;for(int y:nb[x])d[y]++;}return true;}
struct Tr{int i,j,l,r,extra,gain;P inner;M clash{},del{};};
long long sampled=0,legal=0,stored=0,combinations=0,compatible=0,baselines=0,extensions=0,capped=0,best=0,bridgeComb=0,compensated=0;int target,per,cap,extensionCap,maxTr;bool ctrl;
ofstream tracks;int activePair=0,minimumSpan=1;set<string> nearClasses;
string normalize(P const&p){int m[9]={},h=0;string s;for(int i=1;i<p.size();i++){int d=countr_zero(unsigned(p[i]^p[i-1]));if(!m[d])m[d]=++h;s+=('0'+m[d]-1);}return s;}
void logNear(P const&base,P const&l,P const&r){P cand(l.rbegin(),l.rend());cand.insert(cand.end(),base.begin(),base.end());cand.insert(cand.end(),r.begin(),r.end());string a=normalize(cand);reverse(cand.begin(),cand.end());string b=normalize(cand);if(!nearClasses.insert(min(a,b)).second)return;if(!valid(cand))abort();tracks<<activePair;for(int x:cand)tracks<<" "<<x;tracks<<endl;}
struct Work{
 P p,q,witness;array<int,512> pi;array<M,512>halo{};M tipmask{};vector<Tr> tr;set<uint64_t>seen;array<vector<int>,512>anchors;
 int seg[2][7]{},witnessExtra=0;int deg[512]{},occ[512]{};long long localGrow=0;
 Work(P a,P b):p(move(a)),q(move(b)){pi.fill(-1);for(int i=0;i<p.size();i++){int x=p[i];pi[x]=i;put(halo[x],i);for(int y:nb[x])put(halo[y],i);if(i<4||i+4>=p.size())put(tipmask,i);}
 for(int x=0;x<512;x++)for(int i=0;i<p.size();i++){int d=wt(x^p[i]);if(d==1||d==2)anchors[x].push_back(i);}}
 P bridge(int x,int y){int d=x^y;if(wt(d)==1)return {-1};if(wt(d)!=2)return {};int low=d&-d;return {x^low,x^(d^low)};}
 void offer(int i,int j,int l,int r,int bl,int br){++sampled;if(i>=j-2||l>=r||i<3||j+3>=p.size())return;int n=r-l+1+(bl>=0)+(br>=0),gain=n-(j-i-1);if(gain< -5||gain>9)return;
 P v;if(bl>=0)v.push_back(bl);v.insert(v.end(),q.begin()+l,q.begin()+r+1);if(br>=0)v.push_back(br);int L=0,R=v.size();while(L<R&&i+1<j&&p[i+1]==v[L]){i++;L++;}while(R>L&&i+1<j&&p[j-1]==v[R-1]){j--;R--;}
 if(R-L<minimumSpan||j-i-1<minimumSpan)return;uint64_t key=0;for(int k=i+1;k<j;k++)key^=salts[p[k]];for(int k=L;k<R;k++)key^=salts[v[k]];if(!key||seen.count(key))return;
 P segment{p[i]};segment.insert(segment.end(),v.begin()+L,v.begin()+R);segment.push_back(p[j]);if(!valid(segment))return;
 M del{},outside{};for(int k=i+1;k<j;k++)put(del,k);for(int k=L;k<R;k++)outside=plusM(outside,halo[v[k]]);M exc=del;put(exc,i);put(exc,j);outside=minusM(outside,exc);int defects=weight(minusM(outside,tipmask));if(defects>28)return;
 // All external defects from this insertion must be coverable by the partner's one deletion interval.
 int low=999,hi=-1;for(int k=4;k+4<p.size();k++)if(has(outside,k)){low=min(low,k);hi=k;}
 if(hi>=0&&(hi-low>65||(low<i&&hi>j)))return;
 ++legal;seen.insert(key);P body(v.begin()+L,v.begin()+R);tr.push_back({i,j,l,r,(bl>=0)+(br>=0),gain,move(body),outside,del});}
 void build(){int n=q.size();for(int l=0;l<n-6;l++)if(pi[q[l]]>=0)for(int h=l+7;h<n&&h<l+54;h++)if(pi[q[h]]>=0){int i=pi[q[l]],j=pi[q[h]];if(j-i>=5&&abs((h-l)-(j-i))<=5)offer(i,j,l+1,h-1,-1,-1);}
 for(int trial=0;trial<per;trial++){int len=7+draw(39),l=draw(n-len+1),r=l+len-1;auto &as=anchors[q[l]],&bs=anchors[q[r]];if(as.empty()||bs.empty())continue;int si=draw(as.size());
 for(int t=0;t<min(6,int(as.size()));t++){int i=as[(si+t)%as.size()];auto it=lower_bound(bs.begin(),bs.end(),i+len-6);for(;it!=bs.end()&&*it<=i+len+7;it++){int j=*it;
 auto left=bridge(p[i],q[l]),right=bridge(q[r],p[j]);for(int x:left)for(int y:right)offer(i,j,l,r,x,y);}}}
 shuffle(tr.begin(),tr.end(),rng);if(tr.size()>maxTr){stable_sort(tr.begin(),tr.end(),[](auto&a,auto&b){auto score=[](auto&v){int d=weight(v.clash);return (d>10?8:0)+max(0,-v.gain);};return score(a)<score(b);});tr.resize(maxTr);}stored+=tr.size();}
 void mark(int x,int s){occ[x]+=s;for(int y:nb[x])deg[y]+=s;}
 bool grow(P&base,P&l,P&r,int side,int need){if(++localGrow>extensionCap)return false;++extensions;if(base.size()+r.size()+l.size()==192)logNear(base,l,r);best=max(best,(long long)(base.size()+r.size()+l.size()-1));if(need<=0){witness={l.rbegin(),l.rend()};witness.insert(witness.end(),base.begin(),base.end());witness.insert(witness.end(),r.begin(),r.end());return true;}
 if(side==0&&grow(base,l,r,1,need))return true;auto&arm=side?r:l;int end=arm.empty()?(side?base.back():base.front()):arm.back();
 for(int y:nb[end])if(!occ[y]&&deg[y]==1){mark(y,1);arm.push_back(y);bool ok=grow(base,l,r,side,need-1);arm.pop_back();mark(y,-1);if(ok)return true;if(localGrow>extensionCap)break;}return false;}
 bool join(Tr const&A,Tr const&B){if(B.i-A.j<3)return false;++combinations;M bad=plusM(minusM(A.clash,B.del),minusM(B.clash,A.del));if(weight(minusM(bad,tipmask)))return false;
 int dl=0,dr=0;for(int k=0;k<4;k++){if(has(bad,k))dl=k+1;if(has(bad,p.size()-1-k))dr=k+1;}
 int n=p.size()+A.gain+B.gain-dl-dr;if(n<target-8)return false;++compatible;
 P base(p.begin()+dl,p.begin()+A.i+1);base.insert(base.end(),A.inner.begin(),A.inner.end());base.insert(base.end(),p.begin()+A.j,p.begin()+B.i+1);base.insert(base.end(),B.inner.begin(),B.inner.end());base.insert(base.end(),p.begin()+B.j,p.end()-dr);
 if(!valid(base))return false;++baselines;bridgeComb+=bool(A.extra+B.extra);compensated+=weight(minusM(A.clash,tipmask))||weight(minusM(B.clash,tipmask));bool found=false;int actualSize=base.size();
 for(int loss=0;loss<=8&&!found;loss++)for(int el=0;el<=loss&&!found;el++){
  int er=loss-el;if(n-loss<target-14 || dl+el>=A.i || dr+er>=int(p.size())-B.j)continue;
  P trial(base.begin()+el,base.end()-er);for(int x:trial)mark(x,1);
  P left,right;localGrow=0;found=grow(trial,left,right,0,target+1-int(trial.size()));if(localGrow>extensionCap)capped++;
  for(int x:trial)mark(x,-1);if(found)actualSize=trial.size();
 }

 if(found){if(!valid(witness))abort();int z=0;for(auto*t:{&A,&B}){int val[7]={t->i,t->j,t->l,t->r,t->extra,t->gain,weight(t->clash)};copy(val,val+7,seg[z++]);}witnessExtra=witness.size()-actualSize;}return found;}
 bool run(){build();for(int i=0;i<tr.size();i++)for(int j=0;j<i;j++){auto&a=tr[i],&b=tr[j];if((a.i<b.i?join(a,b):join(b,a)))return true;}return false;}
};
int main(int argc,char**argv){if(argc!=10)return 2;tracks.open(argv[8]);minimumSpan=atoi(argv[9]);target=atoi(argv[1]);per=atoi(argv[2]);maxTr=atoi(argv[3]);extensionCap=atoi(argv[4]);int sec=atoi(argv[5]);rng.seed(strtoul(argv[6],nullptr,10));ctrl=atoi(argv[7]);for(int x=0;x<512;x++){salts[x]=rand64();for(int d=0;d<9;d++)nb[x][d]=x^(1<<d);}
 string s;vector<P>bank;while(getline(cin,s)){istringstream in(s);int x;P p;while(in>>x)p.push_back(x);if(!valid(p)||p.size()>192)return 3;bank.push_back(move(p));}auto start=Clock::now();int completed=0,found=0;
 for(int i=0;i+1<bank.size();i+=2){activePair=i/2;Work w(bank[i],bank[i+1]);if(w.run()){found++;cout<<i/2;for(int x:w.witness)cout<<" "<<x;cout<<endl;cerr<<"hit pair "<<i/2<<" extra_endpoints "<<w.witnessExtra;for(auto&a:w.seg){cerr<<" tract";for(int x:a)cerr<<" "<<x;}cerr<<endl;if(!ctrl){completed++;break;}}completed++;if(chrono::duration<double>(Clock::now()-start).count()>=sec)break;}
 cerr<<"pairs "<<completed<<" templates "<<sampled<<" viable_tracts "<<legal<<" stored "<<stored<<" tract_pairs "<<combinations<<" cross_compatible "<<compatible<<" valid_splices "<<baselines<<" free_bridge_splices "<<bridgeComb<<" mutual_or_oneway_defect_repair "<<compensated<<" growth_nodes "<<extensions<<" capped_tips "<<capped<<" best_edges "<<best<<" hits "<<found<<endl;}

