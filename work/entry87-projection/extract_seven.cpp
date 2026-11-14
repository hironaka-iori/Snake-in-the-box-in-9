// Enumerate long contiguous sections lying in Q7 from transition streams.
#include <algorithm>
#include <array>
#include <iostream>
#include <map>
#include <string>
#include <vector>
using namespace std;
string normalized(string s){
    array<int,20> name{};name.fill(-1);int n=0;
    for(char& c:s){int b=c-'A';if(name[b]<0)name[b]=n++;c=char('0'+name[b]);}
    return s;
}
int main(int argc,char**argv){
    if(argc!=2)return 2;int minimum=stoi(argv[1]),dim,id;string line;
    map<string,array<int,3>> bank;
    while(cin>>dim>>id>>line){
        array<int,20> count{};int active=0,start=0;
        for(int j=0;j<int(line.size());++j){
            int bit=line[j]-'A';if(bit<0||bit>=dim)return 3;
            if(!count[bit]&&active==7){
                if(j-start>=minimum){
                    string raw=line.substr(start,j-start);string a=normalized(raw);
                    reverse(raw.begin(),raw.end());string b=normalized(raw);
                    bank.try_emplace(min(a,b),array<int,3>{dim,id,start});
                }
                while(active==7){int old=line[start++]-'A';if(!--count[old])--active;}
            }
            if(!count[bit]++)++active;
        }
        if(int(line.size())-start>=minimum){
            string raw=line.substr(start);string a=normalized(raw);reverse(raw.begin(),raw.end());
            bank.try_emplace(min(a,normalized(raw)),array<int,3>{dim,id,start});
        }
    }
    for(const auto& [word,where]:bank)cout<<word<<" "<<where[0]<<" "<<where[1]<<" "<<where[2]<<"\n";
}
