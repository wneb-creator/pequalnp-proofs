#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>
using Word=unsigned __int128;
int bits(Word x){return __builtin_popcountll(uint64_t(x))+__builtin_popcountll(uint64_t(x>>64));}
int lowbit(Word x){return uint64_t(x)?__builtin_ctzll(uint64_t(x)):64+__builtin_ctzll(uint64_t(x>>64));}
int singletonOffset;std::array<int,16384> starComp;std::array<unsigned,16384> starEdgeMask;
struct Gate { bool isOr; int a,b; };
struct Circuit { std::vector<Gate> g; };
bool requireTzero=true;
struct Result { int pos,neg,mixed,dead,uncovered; double cost()const{return pos+2.0*neg+(requireTzero?2.0*mixed:0.0)+0.025*dead+0.5*uncovered;} bool exact()const{return pos==0&&neg==0&&(!requireTzero||mixed==0)&&uncovered==0;} };
std::mt19937_64 rng; int p,l,n,na,no; std::vector<std::pair<int,int>> edges;std::vector<unsigned> tests;std::vector<Word> inputs; Word target, allmask;unsigned lm,rm;
int ri(int n){return int(rng()%n);}double rf(){return (rng()>>11)*0x1.0p-53;}
Result eval(Circuit const&c){Word v[100];unsigned r[100];bool used[100]={};for(int i=0;i<n;++i){v[i]=inputs[i];r[i]=1u<<i;}int mixed=0;unsigned covered=0;for(int i=0;i<(int)c.g.size();++i){auto g=c.g[i];v[n+i]=g.isOr?(v[g.a]|v[g.b]):(v[g.a]&v[g.b]);r[n+i]=g.isOr?(r[g.a]|r[g.b]):0; if(g.isOr&&(r[n+i]&lm)&&(r[n+i]&rm))++mixed;if(g.isOr){unsigned sm=unsigned((v[n+i]>>singletonOffset)&((1u<<n)-1));if(starComp[sm]>=0&&!((v[n+i]>>starComp[sm])&1))covered|=starEdgeMask[sm];}}used[n+c.g.size()-1]=true;int dead=0;for(int i=int(c.g.size())-1;i>=0;--i){if(used[n+i])used[c.g[i].a]=used[c.g[i].b]=true;else ++dead;}Word out=v[n+c.g.size()-1];return{bits(target&~out),bits(out&~target&allmask),mixed,dead,int(edges.size())-__builtin_popcount(covered)};}
void print(Circuit const&c){for(int i=0;i<(int)c.g.size();++i)std::cout<<n+i<<" "<<(c.g[i].isOr?"OR":"AND")<<" "<<c.g[i].a<<" "<<c.g[i].b<<"\n";}
Circuit initial(){Circuit c;std::vector<int> terms;std::vector<int> order(p);std::iota(order.begin(),order.end(),0);std::shuffle(order.begin(),order.end(),rng);for(int a:order){std::vector<int> nb;for(auto e:edges)if(e.first==a)nb.push_back(p+e.second);std::shuffle(nb.begin(),nb.end(),rng);int root=nb[0];for(int j=1;j<(int)nb.size();++j){c.g.push_back({true,root,nb[j]});root=n+c.g.size()-1;}c.g.push_back({false,a,root});terms.push_back(n+c.g.size()-1);}int root=terms[0];for(int j=1;j<(int)terms.size();++j){c.g.push_back({true,root,terms[j]});root=n+c.g.size()-1;}
auto counts=[&](){int ac=0;for(auto g:c.g)ac+=!g.isOr;return ac;};
while((int)c.g.size()>na+no){int ac=counts(),oc=c.g.size()-ac;std::vector<int> choices;for(int i=0;i+1<(int)c.g.size();++i)if((c.g[i].isOr&&oc>no)||(!c.g[i].isOr&&ac>na))choices.push_back(i);int j=choices.empty()?ri(c.g.size()-1):choices[ri(choices.size())];int repl=ri(2)?c.g[j].a:c.g[j].b;c.g.erase(c.g.begin()+j);for(auto &g:c.g){if(g.a==n+j)g.a=repl;if(g.b==n+j)g.b=repl;if(g.a>n+j)--g.a;if(g.b>n+j)--g.b;}}
while((int)c.g.size()<na+no){int ac=counts();bool op=ac>=na;int j=ri(c.g.size());for(auto&g:c.g){if(g.a>=n+j)++g.a;if(g.b>=n+j)++g.b;}int a=ri(n+j);c.g.insert(c.g.begin()+j,{op,a,a});}
while(counts()!=na){bool wantAnd=counts()<na;std::vector<int> choices;for(int i=0;i<(int)c.g.size();++i)if(c.g[i].isOr==wantAnd)choices.push_back(i);int j=choices[ri(choices.size())];c.g[j].isOr=!wantAnd;}
return c;}
bool fullVerify(Circuit const&c){for(unsigned x=0;x<(1u<<n);++x){bool v[100];for(int i=0;i<n;++i)v[i]=(x>>i)&1;for(int i=0;i<(int)c.g.size();++i){auto g=c.g[i];v[n+i]=g.isOr?(v[g.a]||v[g.b]):(v[g.a]&&v[g.b]);}bool t=false;for(auto e:edges)t|=((x>>e.first)&1)&&((x>>(p+e.second))&1);if(v[n+c.g.size()-1]!=t)return false;}return true;}

void targetMutation(Circuit&c){
 Word v[100];for(int i=0;i<n;++i)v[i]=inputs[i];for(int i=0;i<(int)c.g.size();++i){auto g=c.g[i];v[n+i]=g.isOr?(v[g.a]|v[g.b]):(v[g.a]&v[g.b]);}
 Word bad=(v[n+c.g.size()-1]^target)&allmask;if(!bad)return;int ix=ri(bits(bad));while(ix--)bad&=bad-1;int t=lowbit(bad);bool want=(target>>t)&1;int w=n+c.g.size()-1,j=w-n;
 for(int depth=0;depth<n+(int)c.g.size();++depth){j=w-n;auto g=c.g[j];if(ri(4)==0)break;std::vector<int> next;if(((v[g.a]>>t)&1)!=want&&g.a>=n)next.push_back(g.a);if(((v[g.b]>>t)&1)!=want&&g.b>=n)next.push_back(g.b);if(next.empty())break;w=next[ri(next.size())];}
 std::vector<int> choices;for(int i=0;i<n+j;++i)if(((v[i]>>t)&1)==want)choices.push_back(i);if(choices.empty())return;int repl=choices[ri(choices.size())];bool ba=((v[c.g[j].a]>>t)&1)!=want,bb=((v[c.g[j].b]>>t)&1)!=want;
 if(ba&&bb){if(ri(4)==0)c.g[j].a=c.g[j].b=repl;else if(ri(2))c.g[j].a=repl;else c.g[j].b=repl;}else if(ba)c.g[j].a=repl;else if(bb)c.g[j].b=repl;
}
void moveGate(Circuit&c){
 bool used[100]={};used[n+c.g.size()-1]=true;for(int i=int(c.g.size())-1;i>=0;--i)if(used[n+i])used[c.g[i].a]=used[c.g[i].b]=true;
 std::vector<int> dead;for(int i=0;i+1<(int)c.g.size();++i)if(!used[n+i])dead.push_back(i);int j=!dead.empty()&&ri(5)?dead[ri(dead.size())]:ri(c.g.size()-1);auto old=c.g[j];int repl=ri(2)?old.a:old.b;c.g.erase(c.g.begin()+j);for(auto&g:c.g){if(g.a==n+j)g.a=repl;if(g.b==n+j)g.b=repl;if(g.a>n+j)--g.a;if(g.b>n+j)--g.b;}
 int at=ri(c.g.size());for(auto&g:c.g){if(g.a>=n+at)++g.a;if(g.b>=n+at)++g.b;}int a=ri(n+at),b=ri(2)?a:ri(n+at);c.g.insert(c.g.begin()+at,{old.isOr,a,b});
}

int main(int argc,char**argv){if(argc!=8){std::cerr<<"usage: anneal_graph subK4|Fano ANDcount ORcount iterations seed seconds requireTzero\n";return 1;}std::string name=argv[1];na=std::stoi(argv[2]);no=std::stoi(argv[3]);uint64_t iterations=std::stoull(argv[4]),seed=std::stoull(argv[5]);double maxSeconds=std::stod(argv[6]);requireTzero=std::stoi(argv[7])!=0;rng.seed(seed);if(name=="subK4"){p=4;l=6;int j=0;for(int a=0;a<4;++a)for(int b=a+1;b<4;++b){edges.push_back({a,j});edges.push_back({b,j++});}}else{p=l=7;for(int a=0;a<7;++a)for(int b=0;b<7;++b)if(__builtin_popcount((a+1)&(b+1))%2==0)edges.push_back({a,b});}n=p+l;lm=(1u<<p)-1;rm=((1u<<l)-1)<<p;for(auto e:edges)tests.push_back((1u<<e.first)|(1u<<(p+e.second)));target=(Word(1)<<tests.size())-1;for(unsigned x=0;x<(1u<<n);++x){bool independent=true;for(auto e:edges)if((x&(1u<<e.first))&&(x&(1u<<(p+e.second))))independent=false;if(!independent)continue;bool maximal=true;for(int i=0;i<n;++i)if(!(x&(1u<<i))){unsigned y=x|(1u<<i);bool hit=false;for(auto e:edges)hit|=(y&(1u<<e.first))&&(y&(1u<<(p+e.second)));if(!hit)maximal=false;}if(maximal)tests.push_back(x);}int basePatterns=tests.size();singletonOffset=tests.size();for(int i=0;i<n;++i)tests.push_back(1u<<i);starComp.fill(-1);starEdgeMask.fill(0);for(int side=0;side<2;++side)for(int c=0;c<(side?l:p);++c){std::vector<std::pair<int,int>> nb;for(int e=0;e<(int)edges.size();++e)if((side?edges[e].second:edges[e].first)==c)nb.push_back({side?edges[e].first:p+edges[e].second,e});for(unsigned mask=1;mask<(1u<<nb.size());++mask)if(__builtin_popcount(mask)>=2){unsigned q=0,em=0;for(unsigned h=0;h<nb.size();++h)if(mask&(1u<<h)){q|=1u<<nb[h].first;em|=1u<<nb[h].second;}if(starComp[q]<0){starComp[q]=tests.size();tests.push_back(((1u<<n)-1)^q);}starEdgeMask[q]|=em;}}if(tests.size()>128)return 3;allmask=(Word(1)<<basePatterns)-1;for(int i=0;i<n;++i){Word v=0;for(unsigned k=0;k<tests.size();++k)if(tests[k]&(1u<<i))v|=Word(1)<<k;inputs.push_back(v);}std::cout<<"graph="<<name<<" AND="<<na<<" OR="<<no<<" tests="<<tests.size()<<" seed="<<seed<<std::endl;
Circuit best=initial();Result br=eval(best);std::cout<<"initial pos="<<br.pos<<" neg="<<br.neg<<" T="<<br.mixed<<" uncovered="<<br.uncovered<<" dead="<<br.dead<<std::endl;Circuit cur=best;Result cr=br;uint64_t restarts=0,accepted=0;double baseTemp=2.0;auto start=std::chrono::steady_clock::now();
uint64_t k=0;for(;k<iterations;++k){if(k%1000000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=maxSeconds)break;if(k%50000000==0)std::cout<<"checkpoint iteration="<<k<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" best_pos="<<br.pos<<" best_neg="<<br.neg<<" best_T="<<br.mixed<<" best_uncovered="<<br.uncovered<<std::endl;if(k%100000==0){++restarts;cur=(ri(10)<7)?best:initial();cr=eval(cur);baseTemp=std::pow(2.0,ri(7)-4);}Circuit cand=cur;int j=ri(cand.g.size()),kind=ri(100);if(kind<40){targetMutation(cand);}else if(kind<46){moveGate(cand);}else if(kind<78){if(ri(2))cand.g[j].a=ri(n+j);else cand.g[j].b=ri(n+j);}else if(kind<90){cand.g[j].a=ri(n+j);cand.g[j].b=ri(n+j);}else{int h=ri(cand.g.size());std::swap(cand.g[j].isOr,cand.g[h].isOr);}if(ri(100)<12){int extra=1+ri(4);while(extra--){int h=ri(cand.g.size());if(ri(2))cand.g[h].a=ri(n+h);else cand.g[h].b=ri(n+h);}}auto nr=eval(cand);if(nr.exact()){std::cout<<"FOUND iteration="<<k<<" full_truth="<<fullVerify(cand)<<" AND="<<na<<" OR="<<no<<std::endl;print(cand);return 0;}if(nr.cost()<br.cost()){best=cand;br=nr;std::cout<<"best iteration="<<k<<" pos="<<br.pos<<" neg="<<br.neg<<" T="<<br.mixed<<" uncovered="<<br.uncovered<<" dead="<<br.dead<<std::endl;print(best);std::cout.flush();}double frac=double(k%100000)/100000.0;double temp=baseTemp*std::pow(0.05,frac);double delta=nr.cost()-cr.cost();if(delta<=0||rf()<std::exp(-delta/temp)){cur=std::move(cand);cr=nr;++accepted;}}
std::cout<<"DONE iterations="<<k<<" restarts="<<restarts<<" accepted="<<accepted<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" best_pos="<<br.pos<<" best_neg="<<br.neg<<" best_T="<<br.mixed<<" best_uncovered="<<br.uncovered<<" best_uncovered="<<br.uncovered<<" best_dead="<<br.dead<<std::endl;print(best);return 0;}
