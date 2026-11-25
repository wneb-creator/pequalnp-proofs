#include <array>
#include <vector>
#include <queue>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <cstdint>
#include <chrono>
#include <limits>
struct Node {uint32_t sig;int a,b;unsigned char op,cost;bool active,seed;std::array<int,11> dag{};uint64_t fp;};
struct Item{int cost,score,id;bool operator<(const Item&o)const{return cost!=o.cost?cost>o.cost:score!=o.score?score>o.score:id>o.id;}};
std::vector<Node> nodes;
std::vector<std::vector<int>> reps;
std::priority_queue<Item> agenda;
int n,K,R,c0,c1,beam=1000;uint32_t target,truthmask;uint64_t tested=0,accepted=0;bool found=false;
uint64_t hashbit(int i){uint64_t x=uint64_t(i)+0x9e3779b97f4a7c15ULL;x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;x=(x^(x>>27))*0x94d049bb133111ebULL;return 1ULL<<((x^(x>>31))%64);}
uint32_t combine(uint32_t a,uint32_t b,int op){if(!op)return a|b;uint32_t t=(a&b)&truthmask;int dx=(((a>>c0)&1)&&((b>>R)&1))||(((a>>R)&1)&&((b>>c0)&1));int dy=(((a>>c1)&1)&&((b>>(R+1))&1))||(((a>>(R+1))&1)&&((b>>c1)&1));return t|(dx<<R)|(dy<<(R+1));}
int score(uint32_t s){return 2*__builtin_popcount((s&truthmask)&~target)+__builtin_popcount(target&~s)+2*__builtin_popcount(s>>R);}
int mergeD(const Node&a,const Node&b,std::array<int,11>&out){int i=0,j=0,z=0;while(i<a.cost||j<b.cost){int x;if(j==b.cost||(i<a.cost&&a.dag[i]<b.dag[j]))x=a.dag[i++];else if(i==a.cost||b.dag[j]<a.dag[i])x=b.dag[j++];else{x=a.dag[i];++i;++j;}if(z==K)return K+1;out[z++]=x;}return z;}
void dump(int id){std::vector<int> map(nodes.size(),-1);for(int i=0;i<n;++i)map[i]=i;const auto&root=nodes[id];int at=n;std::cout<<"WITNESS gates="<<int(root.cost)<<"\n";for(int j=0;j<root.cost;++j){int x=root.dag[j];const auto&q=nodes[x];std::cout<<at<<" "<<int(q.op)<<" "<<map[q.a]<<" "<<map[q.b]<<"\n";map[x]=at++;}std::cout<<"OUTPUT "<<map[id]<<"\n"<<std::flush;}
int add(uint32_t sig,int a,int b,int op,const std::array<int,11>&children,int count,bool seed=false){
 int cost=count+1;if(cost>K)return -1;
 auto &rs=reps[sig];
 if(!seed&&!rs.empty()){
  int best=100;for(int id:rs)best=std::min(best,int(nodes[id].cost));if(cost>best+2)return -1;
  for(int id:rs)if(std::binary_search(children.begin(),children.begin()+count,id))return -1;
 }
 uint64_t fp=0;for(int j=0;j<count;++j)fp|=hashbit(children[j]);
 int replace=-1;
 if(!seed&&rs.size()>=8){
  int worst=-1;for(int i=0;i<(int)rs.size();++i)if(worst<0||nodes[rs[i]].cost>nodes[rs[worst]].cost)worst=i;
  if(cost>nodes[rs[worst]].cost)return -1;
  if(cost<nodes[rs[worst]].cost)replace=worst;
  else{
   int canddiv=65;for(int id:rs)canddiv=std::min(canddiv,__builtin_popcountll(fp^nodes[id].fp));
   int least=65,which=-1;
   for(int i=0;i<(int)rs.size();++i){if(nodes[rs[i]].seed)continue;int div=65;for(int j=0;j<(int)rs.size();++j)if(i!=j)div=std::min(div,__builtin_popcountll(nodes[rs[i]].fp^nodes[rs[j]].fp));if(div<least){least=div;which=i;}}
   if(which<0||canddiv<=least)return -1;replace=which;
  }
 }
 if(nodes.size()>=8000000&&sig!=target)return -1;
 int id=nodes.size();Node q{sig,a,b,(unsigned char)op,(unsigned char)cost,true,seed,children,fp};q.dag[count]=id;q.fp|=hashbit(id);nodes.push_back(q);
 if(replace>=0){nodes[rs[replace]].active=false;rs[replace]=id;}else rs.push_back(id);
 agenda.push({cost,score(sig),id});++accepted;
 if(sig==target){std::cout<<"FOUND shared DAG\n";dump(id);found=true;}
 return id;
}
int main(int argc,char**argv){std::ifstream in(argv[1]);in>>n>>K>>R>>c0>>c1>>target;truthmask=(1u<<R)-1;double seconds=std::atof(argv[2]);if(argc>3)beam=std::atoi(argv[3]);reps.resize(1u<<(R+2));nodes.reserve(8000000);
 for(int i=0;i<n;++i){uint32_t t;int dx,dy;in>>t>>dx>>dy;Node x{t|(uint32_t(dx)<<R)|(uint32_t(dy)<<(R+1)),-1,-1,0,0,true,true,{},0};nodes.push_back(x);reps[x.sig].push_back(i);agenda.push({0,score(x.sig),i});}
 // Seed useful shared subexpressions of the checked twelve-gate tree.
 std::array<std::array<int,3>,12> seed{{{{0,1,2}},{{0,11,3}},{{1,12,7}},{{0,0,13}},{{0,7,8}},{{0,9,15}},{{0,5,4}},{{0,17,6}},{{0,18,14}},{{1,14,16}},{{0,10,20}},{{1,19,21}}}};
 std::vector<int> sm(23,-1);for(int i=0;i<11;++i)sm[i]=i;
 for(int j=0;j<12;++j){int op=seed[j][0],a=sm[seed[j][1]],b=sm[seed[j][2]];if(a<0||b<0)continue;std::array<int,11> un{};int z=mergeD(nodes[a],nodes[b],un);if(z<K)sm[11+j]=add(combine(nodes[a].sig,nodes[b].sig,op),a,b,op,un,z,true);}
 auto began=std::chrono::steady_clock::now();std::vector<int> processed;std::array<int,12> expanded{};int lastcost=-1;uint64_t pops=0;
 while(!agenda.empty()&&!found){auto item=agenda.top();agenda.pop();int u=item.id;++pops;if(!nodes[u].active||nodes[u].cost>=K)continue;int cost=nodes[u].cost;if(expanded[cost]>=beam&&!nodes[u].seed)continue;
  if(cost!=lastcost){std::cout<<"level="<<cost<<" nodes="<<nodes.size()<<" processed="<<processed.size()<<" tests="<<tested<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count()<<"\n"<<std::flush;lastcost=cost;}
  ++expanded[cost];
  for(int v:processed){if(!nodes[v].active&&!nodes[v].seed)continue;++tested;
   if(int(nodes[u].cost)+nodes[v].cost+1>K&&!(nodes[u].fp&nodes[v].fp))continue;
   std::array<int,11> un{};int z=mergeD(nodes[u],nodes[v],un);if(z>=K)continue;
   for(int op=0;op<2;++op){uint32_t sig=combine(nodes[u].sig,nodes[v].sig,op);add(sig,std::min(u,v),std::max(u,v),op,un,z);if(found)break;}if(found)break;
   if((tested&65535)==0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count()>seconds)goto finished;
  }
  // A distinct duplicate of a gate can be useful for the derivative signature.
  if(!found&&cost>0&&cost+2<=K){uint32_t s=combine(nodes[u].sig,nodes[u].sig,1);if(s!=nodes[u].sig){Node dup=nodes[u];int cp=nodes.size();dup.dag[cost-1]=cp;dup.fp|=hashbit(cp);dup.active=false;dup.seed=false;nodes.push_back(dup);auto un=nodes[u].dag;un[cost]=cp;add(s,u,cp,1,un,cost+1);}}
  processed.push_back(u);
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count()>seconds)break;
 }
 finished:std::cout<<"DONE found="<<found<<" nodes="<<nodes.size()<<" accepted="<<accepted<<" processed="<<processed.size()<<" pairs="<<tested<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count()<<" beam="<<beam<<"\n";
 for(int i=0;i<K;++i)std::cout<<"expanded["<<i<<"]="<<expanded[i]<<"\n";
}
