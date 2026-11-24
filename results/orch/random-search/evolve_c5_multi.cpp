#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>
#include <vector>
using U=uint32_t;constexpr int n=5,m=8;
struct Gate{int a,b,op;};struct Circuit{std::array<Gate,m>g;int score;};
std::array<U,n>inputs;std::array<U,3>targets;std::mt19937_64 rng;
std::array<U,n+m>eval(const Circuit&c){std::array<U,n+m>v;for(int i=0;i<n;i++)v[i]=inputs[i];for(int j=0;j<m;j++){auto g=c.g[j];v[n+j]=g.op?(v[g.a]|v[g.b]):(v[g.a]&v[g.b]);}return v;}
int score(Circuit&c){auto v=eval(c);int total=0;for(U t:targets){int d=32;for(U x:v)d=std::min(d,std::popcount(x^t));total+=d;}return c.score=total;}
void print(const Circuit&c){std::cout<<"score "<<c.score<<std::endl;for(int j=0;j<m;j++)std::cout<<(n+j)<<" "<<(c.g[j].op?"or":"and")<<" "<<c.g[j].a<<" "<<c.g[j].b<<std::endl;auto v=eval(c);for(int q=0;q<3;q++){std::cout<<"output "<<q;for(int j=0;j<n+m;j++)if(v[j]==targets[q])std::cout<<" "<<j;std::cout<<std::endl;}}
Circuit seed(){
 std::vector<unsigned>covers;for(unsigned s=0;s<32;s++)if(std::popcount(s)==3){bool ok=true;for(int i=0;i<5;i++)if(!(s>>i&1)&&!(s>>((i+1)%5)&1))ok=false;if(ok)covers.push_back(s);}
 unsigned cover=covers[rng()%covers.size()];std::array<std::vector<int>,5>stars;
 for(int i=0;i<5;i++){int a=i,b=(i+1)%5;if(!(cover>>a&1)||((cover>>b&1)&&rng()%2))std::swap(a,b);stars[a].push_back(b);}
 std::vector<int>ord;for(int i=0;i<5;i++)if(!stars[i].empty())ord.push_back(i);std::shuffle(ord.begin(),ord.end(),rng);
 std::vector<Gate>gs;std::vector<int>terms;
 for(int a:ord){auto&vs=stars[a];std::shuffle(vs.begin(),vs.end(),rng);int u=vs[0];for(int k=1;k<(int)vs.size();k++){gs.push_back({u,vs[k],1});u=n+gs.size()-1;}gs.push_back({a,u,0});terms.push_back(n+gs.size()-1);}
 int q=terms[0];for(int k=1;k<(int)terms.size();k++){gs.push_back({q,terms[k],1});q=n+gs.size()-1;}
 gs.push_back({0,1,1});gs.push_back({2,3,1});if(gs.size()!=9){std::cerr<<"bad seed"<<std::endl;exit(2);}
 Circuit best;best.score=1000;
 for(int kill=0;kill<9;kill++)for(int side=0;side<2;side++){
  int rep=side?gs[kill].a:gs[kill].b;Circuit c;int j=0;
  for(int k=0;k<9;k++)if(k!=kill){auto g=gs[k];if(g.a==n+kill)g.a=rep;if(g.b==n+kill)g.b=rep;if(g.a>n+kill)g.a--;if(g.b>n+kill)g.b--;c.g[j++]=g;}
  score(c);if(c.score<best.score)best=c;
 }
 return best;
}
void mutate(Circuit&c){
 if(rng()%2){int j=rng()%m;int choice=rng()%3;if(!choice)c.g[j].op^=1;else if(choice==1)c.g[j].a=rng()%(n+j);else c.g[j].b=rng()%(n+j);return;}
 auto v=eval(c);std::vector<std::pair<int,int>>errors;
 for(int q=0;q<3;q++){int d=33,jj=0;for(int j=0;j<n+m;j++){int e=std::popcount(v[j]^targets[q]);if(e<d){d=e;jj=j;}}if(d)errors.push_back({q,jj});}
 if(errors.empty())return;auto[q,node]=errors[rng()%errors.size()];if(node<n){int j=rng()%m;c.g[j]={rng()%unsigned(n+j),rng()%unsigned(n+j),int(rng()%2)};return;}
 U diff=v[node]^targets[q];std::vector<int>bad;while(diff){int b=std::countr_zero(diff);bad.push_back(b);diff&=diff-1;}int bit=bad[rng()%bad.size()];bool want=targets[q]>>bit&1;auto val=[&](int j){return bool(v[j]>>bit&1);};
 int depth=rng()%5;for(int d=0;d<depth;d++){auto g=c.g[node-n];std::vector<int>kids;if(val(g.a)!=want)kids.push_back(g.a);if(val(g.b)!=want)kids.push_back(g.b);if(kids.empty())break;int next=kids[rng()%kids.size()];if(next<n)break;node=next;}
 auto&g=c.g[node-n];std::vector<int>sides;if(val(g.a)!=want)sides.push_back(0);if(val(g.b)!=want)sides.push_back(1);if(sides.empty())return;int side=sides[rng()%sides.size()];std::vector<int>choices;for(int j=0;j<node;j++)if(val(j)==want)choices.push_back(j);if(choices.empty())return;int x=choices[rng()%choices.size()];if(side)g.b=x;else g.a=x;
}
int main(int argc,char**argv){long long rounds=argc>1?atoll(argv[1]):1000000;int seednum=argc>2?atoi(argv[2]):2028;rng.seed(seednum);for(int i=0;i<n;i++)for(int x=0;x<32;x++)if(x>>i&1)inputs[i]|=U(1)<<x;for(int i=0;i<5;i++)targets[0]|=inputs[i]&inputs[(i+1)%5];targets[1]=inputs[0]|inputs[1];targets[2]=inputs[2]|inputs[3];std::array<Circuit,32>pool;for(auto&c:pool)c=seed();Circuit best=pool[0];for(auto&c:pool)if(c.score<best.score)best=c;std::cout<<"initial "<<best.score<<std::endl;auto start=std::chrono::steady_clock::now();for(long long trial=0;trial<rounds;trial++){int j=rng()%pool.size();Circuit c=pool[j];mutate(c);score(c);if(c.score<=pool[j].score)pool[j]=c;if(c.score<best.score){best=c;std::cout<<"BEST "<<best.score<<" trial "<<trial<<std::endl;print(best);}if(best.score==0){std::cout<<"EXACT MULTIOUTPUT WITNESS"<<std::endl;return 0;}if(trial&&trial%100000==0){pool[rng()%pool.size()]=seed();pool[0]=best;}}std::cout<<"DONE best "<<best.score<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;print(best);}
