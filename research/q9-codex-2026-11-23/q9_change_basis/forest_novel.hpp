#include <unordered_set>
// A subset of a path is a linear forest. Add arbitrary vertices by growing or merging components.
unordered_set<string> known_paths;
string pattern(const string& word){
    array<char,9> labels{};int count=0;string out;
    for(char d:word){int a=d-'0';if(!labels[a])labels[a]='0'+count++;out+=labels[a];}
    return out;
}
string canonical_path(string w){
    string p=pattern(w);reverse(w.begin(),w.end());return min(p,pattern(w));
}
int components(const Bits &set, array<int,512> &label,array<int,512> &deg){
    label.fill(-1);deg.fill(0);int count=0;
    for(int x=0;x<512;x++)if(set[x])for(int a=0;a<9;a++)deg[x]+=set[x^(1<<a)];
    for(int x=0;x<512;x++)if(set[x]&&label[x]==-1){
        vector<int> q{x};label[x]=count;int twice=0;
        for(size_t j=0;j<q.size();j++){int z=q[j];twice+=deg[z];if(deg[z]>2)return -1;
            for(int a=0;a<9;a++){int y=z^(1<<a);if(set[y]&&label[y]<0){label[y]=count;q.push_back(y);}}
        }
        if(twice!=2*((int)q.size()-1))return -1;
        count++;
    }return count;
}
bool grow_focus(const Bits& set,int remain,vector<int>&out,unordered_set<Bits>&dead){
    if(dead.count(set))return false;
    array<int,512> lab,deg;int count=components(set,lab,deg);
    if(count<1||count>remain+1)return false;
    if(remain==0){
        int x=0;while(x<512&&(!set[x]||deg[x]>1))x++;
        for(int prev=-1;x<512;){out.push_back(x);int next=512;for(int a=0;a<9;a++){int y=x^(1<<a);if(y!=prev&&set[y]){next=y;break;}}prev=x;x=next;}
        if(out.size()!=set.count()){out.clear();return false;}
        string word;for(size_t i=1;i<out.size();i++)word+=char('0'+__builtin_ctz((unsigned)(out[i]^out[i-1])));
        if(known_paths.count(canonical_path(word))){out.clear();return false;}
        return true;
    }
    vector<int> size(count);vector<vector<int>> tips(count);
    for(int x=0;x<512;x++)if(set[x]){size[lab[x]]++;if(deg[x]<2)tips[lab[x]].push_back(x);}
    if(count>1){
        // Every completion links the current components in a line. Its connector cost dominates this MST.
        vector<int> cost(count,1000);vector<bool> used(count);cost[0]=0;int lower=0;
        for(int k=0;k<count;k++){int u=-1;for(int j=0;j<count;j++)if(!used[j]&&(u<0||cost[j]<cost[u]))u=j;
            used[u]=true;lower+=cost[u];if(lower>remain)return false;
            for(int j=0;j<count;j++)if(!used[j])for(int x:tips[u])for(int y:tips[j])
                cost[j]=min(cost[j],__builtin_popcount((unsigned)(x^y))-1);
        }
    }
    int root=max_element(size.begin(),size.end())-size.begin();Bits candidates;
    // Any connected strict completion has a first additional vertex adjacent to the largest component.
    for(int tip:tips[root])for(int a=0;a<9;a++)candidates.set(tip^(1<<a));
    candidates&=~set;
    for(int y=0;y<512;y++)if(candidates[y]){
        int first=-1,h=0;bool ok=true;
        for(int a=0;a<9;a++){int x=y^(1<<a);if(!set[x])continue;
            if(++h>2||deg[x]>=2||lab[x]==first){ok=false;break;}first=lab[x];}
        if(!ok||count+1-h>remain)continue;
        Bits next=set;next.set(y);if(grow_focus(next,remain-1,out,dead))return true;
    }
    if(dead.size()<100000)dead.insert(set);
    return false;
}
bool complete_forest(const vector<int>&basis,const vector<int>&pts,int target,int id){
    array<int,512> coord{};vector<int> space{0};
    for(int a=0;a<9;a++){int n=space.size();for(int j=0;j<n;j++){int y=space[j]^basis[a];coord[y]=coord[space[j]]^(1<<a);space.push_back(y);}}
    Bits set;for(int x:pts)set.set(coord[x]);
    unordered_set<Bits> dead;vector<int> p;if(!grow_focus(set,target+1-(int)pts.size(),p,dead))return false;
    cout<<"FOUND "<<id<<" locked -1 basis";for(int v:basis)cout<<" "<<v;cout<<" path";for(int v:p)cout<<" "<<v;cout<<endl;return true;
}
