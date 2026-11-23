from pathlib import Path
d=Path(__file__).resolve().parent;s=(d/'ordered.cpp').read_text()
s=s.replace('bool capped=false;','''bool capped=false;vector<char> skip;vector<int> release;long long fillnodes=0;
 bool gap(int i,int j)const{if(abs(i-j)>3||i==j)return false;for(int k=min(i,j)+1;k<max(i,j);k++)if(!skip[k])return false;return true;}
 bool putback(int j){++fillnodes;if(j==(int)release.size())return true;int t=release[j];vector<int>vs;int anchor=-1;
 for(int k:{t-1,t+1})if(k>=0&&k<count&&(!skip[k]||find(release.begin(),release.begin()+j,k)!=release.begin()+j)){anchor=y[k];break;}
 if(anchor<0){vs.resize(512);iota(vs.begin(),vs.end(),0);}else for(int b=0;b<9;b++)vs.push_back(anchor^1<<b);
 for(int v:vs){bool ok=true;for(int u=0;u<count;u++){if(skip[u]&&find(release.begin(),release.begin()+j,u)==release.begin()+j)continue;int d=popcount((unsigned)(y[u]^v));if(abs(t-u)==1?d!=1:d<2){ok=false;break;}}if(ok){y[t]=v;if(putback(j+1))return true;}}return false;}
''')
s=s.replace('if(n==4){++complete;', 'if(n==4){++complete;if(!putback(0))return false;')
s=s.replace("cout<<\"HIT \"<<id<<' '<<a<<' '<<b;for(auto x:y)","cout<<\"HIT \"<<id<<' '<<a<<' '<<b<<' '<<release.size();for(int h:release)cout<<' '<<h;for(auto x:y)")
s=s.replace('done[g[j]]','!skip[j]&&done[g[j]]').replace('done[g[t]]','!skip[t]&&done[g[t]]')
s=s.replace('if(tb<0||score<1)return false;++charts;', '''if(tb<0)return false;int lag=1;
  if(score<1){lag=10;for(int t:S[tb])for(int j=0;j<count;j++)if(!skip[j]&&done[g[j]]&&gap(t,j)&&abs(t-j)<lag){lag=abs(t-j);jp=t;jf=j;}
    if(lag==10){jp=S[tb][0];jf=-1;}}
  ++charts;''')
s=s.replace('if(good)allowed.set(v);','''if(good)for(int t=max(0,i-3);t<=min(count-1,i+3);t++)if(!skip[t]&&done[g[t]]&&abs(t-i)>=2&&gap(i,t)){int h=popcount((unsigned)(v^y[t]));if(h>abs(t-i)||(h-abs(t-i))%2){good=false;break;}}
       if(good)allowed.set(v);''')
s=s.replace('for(int dir=0;dir<9;dir++){Env e;e.block=tb;e.pivot=z[jp];e.root=y[jf]^1<<dir;', '''vector<int>anchorDomain;if(lag==1){for(int dir=0;dir<9;dir++)anchorDomain.push_back(y[jf]^1<<dir);}else{for(int v=0;v<512;v++)if(jf<0||(popcount((unsigned)(v^y[jf]))<=lag&&(popcount((unsigned)(v^y[jf]))-lag)%2==0))anchorDomain.push_back(v);}
  for(int location:anchorDomain){Env e;e.block=tb;e.pivot=z[jp];e.root=location;''')
s=s.replace('g.push_back(c);S[c].push_back(i);','g.push_back(c);if(!skip[i])S[c].push_back(i);')
s=s.replace('if(argc!=4)return 2;','if(argc!=4)return 2;')
s=s.replace('is>>s.id>>s.a>>s.b;s.p.clear();','is>>s.id>>s.a>>s.b;int num,h;is>>num;s.release.clear();for(int j=0;j<num;j++){is>>h;s.release.push_back(h);}s.p.clear();')
s=s.replace('s.rowStart=s.partial;s.capped=false;','s.skip.assign(s.p.size(),false);for(int h:s.release)s.skip[h]=true;s.rowStart=s.partial;s.capped=false;')
s=s.replace('<<" full_solutions "<<s.complete','<<" finished_charts "<<s.complete<<" fill_nodes "<<s.fillnodes')
(d/'ordered_repair.cpp').write_text(s)
