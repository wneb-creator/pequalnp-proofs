#include <iostream>
#include <vector>
#include <unordered_map>
#include <array>
#include <string>
using U=__uint128_t;
struct Hash{size_t operator()(U x)const{return (size_t)x ^ ((size_t)(x>>64)*0x9e3779b97f4a7c15ull);}};
struct Ent{U t; int cost=100,a=-1,b=-1,op=-1;};
std::vector<Ent> es;std::unordered_map<U,int,Hash> ids;
std::string expr(int i){auto e=es[i];if(e.op<0)return std::string("x")+std::to_string(-e.op-2);return "("+expr(e.a)+(e.op?" OR ":" AND ")+expr(e.b)+")";}
int main(){
 std::array<std::pair<int,int>,12>E={{{0,2},{1,3},{0,4},{1,4},{2,4},{0,5},{1,5},{3,5},{0,6},{2,6},{3,6},{5,6}}};
 U var[7];for(int i=0;i<7;i++){var[i]=0;for(int a=0;a<128;a++)if(a>>i&1)var[i]|=U(1)<<a;}
 U ed[12];for(int i=0;i<12;i++)ed[i]=var[E[i].first]&var[E[i].second];
 for(int s=0;s<128;s++){
  U tt=0;std::vector<int> ok;for(int i=0;i<7;i++)if(s>>i&1)tt|=var[i];
  for(int i=0;i<12;i++)if(!((s>>E[i].first&1)||(s>>E[i].second&1)))ok.push_back(i);
  for(int j=0;j<(1<<ok.size());j++){U t=tt;for(int k=0;k<(int)ok.size();k++)if(j>>k&1)t|=ed[ok[k]];if(!ids.count(t)){ids[t]=es.size();es.push_back({t});}}
 }
 U target=0;for(auto e:ed)target|=e;
 std::vector<std::vector<int>> bucket(31);
 for(int i=0;i<7;i++){int v=ids[var[i]];es[v].cost=0;es[v].op=-i-2;bucket[0].push_back(v);}
 for(int cost=1;cost<=20;cost++){
  for(int a=0;a<cost;a++){int b=cost-a-1;if(a>b)break;
   for(int x:bucket[a])for(int y:bucket[b]){if(a==b&&x>=y)continue;
    for(int op=0;op<2;op++){U t=op?(es[x].t|es[y].t):(es[x].t&es[y].t);auto it=ids.find(t);if(it==ids.end())continue;int v=it->second;
     if(es[v].cost>cost){es[v].cost=cost;es[v].a=x;es[v].b=y;es[v].op=op;bucket[cost].push_back(v);}
    }
   }
  }
  std::cout<<"cost "<<cost<<" new "<<bucket[cost].size()<<std::endl;
  int v=ids[target];if(es[v].cost<100){std::cout<<"TARGET "<<es[v].cost<<" "<<expr(v)<<std::endl;return 0;}
 }
}
