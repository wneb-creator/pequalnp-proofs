#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>
#include <vector>
using U=uint64_t;
struct Gate {int a,b,op;};
struct Circuit {std::vector<Gate> gs;};
int n,words;std::vector<std::pair<int,int>> edges;std::vector<int> assignments;std::vector<U> goal;std::vector<std::vector<U>> ivals;
std::mt19937_64 rng(2585);
int rnd(int n){return rng()%n;}
int score(const Circuit& c){
 U vals[128][16]{};
 for(int i=0;i<n;i++)for(int w=0;w<words;w++)vals[i][w]=ivals[i][w];
 for(int j=0;j<int(c.gs.size());j++){
  auto g=c.gs[j];for(int w=0;w<words;w++)vals[n+j][w]=g.op?(vals[g.a][w]|vals[g.b][w]):(vals[g.a][w]&vals[g.b][w]);
 }
 int s=0;for(int w=0;w<words;w++)s+=__builtin_popcountll(vals[n+c.gs.size()-1][w]^goal[w]);return s;
}
Circuit stars(int p,int l){
 std::vector<int> centres(p);for(int i=0;i<p;i++)centres[i]=i;std::shuffle(centres.begin(),centres.end(),rng);
 Circuit c;std::vector<int>roots;
 auto add=[&](int a,int b,int op){c.gs.push_back({a,b,op});return n+int(c.gs.size())-1;};
 for(int a:centres){std::vector<int>ns;for(auto e:edges)if(e.first==a)ns.push_back(e.second);std::shuffle(ns.begin(),ns.end(),rng);if(ns.empty())continue;
 int rt=ns[0];for(size_t i=1;i<ns.size();i++)rt=add(rt,ns[i],1);roots.push_back(add(a,rt,0));}
 std::shuffle(roots.begin(),roots.end(),rng);int rt=roots[0];for(size_t i=1;i<roots.size();i++)rt=add(rt,roots[i],1);return c;
}
Circuit remove(Circuit c,int j,int choice){
 auto removed=c.gs[j];int replacement=choice?removed.a:removed.b;
 c.gs.erase(c.gs.begin()+j);
 for(auto &g:c.gs){for(int *x:{&g.a,&g.b}){if(*x==n+j)*x=replacement;else if(*x>n+j)--*x;}}
 return c;
}
int main(int argc,char**argv){
 int mode=std::atoi(argv[1]),seconds=std::atoi(argv[2]);if(argc>3)rng.seed(std::strtoull(argv[3],nullptr,10));int p,l;
 if(mode==0){p=l=3;for(int i=0;i<3;i++)for(int j=0;j<3;j++)if(i!=j)edges.push_back({i,p+j});}
 else if(mode==1){p=l=7;for(int i=0;i<7;i++)for(int j=0;j<7;j++)if((j-i+7)%7==0||(j-i+7)%7==1||(j-i+7)%7==3)edges.push_back({i,p+j});}
 else if(mode==4){p=l=13;for(int i=0;i<13;i++)for(int j=0;j<13;j++)if((j-i+13)%13==0||(j-i+13)%13==1||(j-i+13)%13==3||(j-i+13)%13==9)edges.push_back({i,p+j});}
 else {p=mode==2?4:5;l=p*(p-1)/2;int col=0;for(int i=0;i<p;i++)for(int j=i+1;j<p;j++){edges.push_back({i,p+col});edges.push_back({j,p+col});++col;}}
 n=p+l;
 for(auto e:edges)assignments.push_back((1<<e.first)|(1<<e.second));
 int positive=assignments.size();
 std::vector<int>row(p,0);for(auto e:edges)row[e.first]|=1<<(e.second-p);
 for(int points=0;points<(1<<p);points++){
  int forbidden=0;for(int i=0;i<p;i++)if(points>>i&1)forbidden|=row[i];
  int lines=((1<<l)-1)^forbidden;
  int closure=0;for(int i=0;i<p;i++)if(!(row[i]&lines))closure|=1<<i;
  if(closure==points)assignments.push_back(points|(lines<<p));
 }
 words=(assignments.size()+63)/64;if(words>16)return 5;
 goal.assign(words,0);for(int a=0;a<positive;a++)goal[a/64]|=U(1)<<(a%64);
 ivals.assign(n,std::vector<U>(words,0));for(int i=0;i<n;i++)for(int a=0;a<int(assignments.size());a++)if(assignments[a]>>i&1)ivals[i][a/64]|=U(1)<<(a%64);
 auto check=stars(p,l);if(score(check)){std::cout<<"BUG baseline score "<<score(check)<<std::endl;return 4;}
 std::cout<<"mode "<<mode<<" inputs "<<n<<" tests "<<assignments.size()<<" edges "<<edges.size()<<" baseline gates "<<check.gs.size()<<" target gates "<<check.gs.size()-1<<std::endl;
 auto start=std::chrono::steady_clock::now();long long trials=0;int best=100000,restarts=0;
 while(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<seconds){
  ++restarts;auto c=stars(p,l);c=remove(c,rnd(c.gs.size()-1),rnd(2));int cur=score(c);
  for(int it=0;it<50000;it++){
   Circuit d=c;int z=rnd(100);int changes=z<2?5:z<15?2:1;
   for(int k=0;k<changes;k++){int j=rnd(d.gs.size());int kind=rnd(3);if(kind==0)d.gs[j].a=rnd(n+j);else if(kind==1)d.gs[j].b=rnd(n+j);else d.gs[j].op^=1;}
   int s=score(d);++trials;
   if(s<best){best=s;std::cout<<"best error "<<best<<" trials "<<trials<<" restarts "<<restarts<<std::endl;}
   if(s==0){std::cout<<"FOUND\n";for(auto g:d.gs)std::cout<<g.a<<" "<<g.b<<" "<<g.op<<"\n";return 2;}
   // Walk across plateaux; infrequent uphill moves explore other neutral components.
   double temperature=1.5*(1.0-double(it)/50000.0)+0.05;
   if(s<=cur || double(rng()%1000000)/1000000.0<std::exp(double(cur-s)/temperature)){c=std::move(d);cur=s;}
  }
 }
 std::cout<<"Finished no witness; best "<<best<<" trials "<<trials<<" restarts "<<restarts<<std::endl;
}
