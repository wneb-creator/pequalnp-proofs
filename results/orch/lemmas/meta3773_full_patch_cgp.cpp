#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <algorithm>
#include <iostream>
#include <cassert>
#include <cmath>
#include <cstdint>
using namespace std;
constexpr int R=14,N=29,G=64;
const vector<int> point_ids{0,1,2,5},line_ids{0,1,2,3,4,7,8,9,11,12};
const vector<vector<int>> groups{{11,13},{4,12},{7,9,10},{6,9,11},{5,10},{4,8,9},{7,8,13},{6,7,12},{5,6,8}};
struct Gate{int op,a,b;};
struct Program{array<Gate,G> g;array<int,9> choice;int out;};
struct Evaluation{int err,cost;array<int,N+G> rep,pa,pb;vector<int> active;uint32_t output;};
array<uint32_t,R> raw_inputs;
uint32_t target;
vector<pair<int,int>> edges;
vector<pair<int,int>> free_gates(const Program&p){vector<pair<int,int>> answer;for(int i=0;i<9;i++){const auto&g=groups[i];if(g.size()==2)answer.push_back({g[0],g[1]});else{int excluded=p.choice[i];assert(excluded>=0&&excluded<3);vector<int> pair;for(int j=0;j<3;j++)if(j!=excluded)pair.push_back(g[j]);int w=R+answer.size();answer.push_back({pair[0],pair[1]});answer.push_back({w,g[excluded]});}}assert(answer.size()==15);return answer;}
Evaluation evaluate(const Program&p){Evaluation e;array<uint32_t,N+G>v;array<int,128>slot;slot.fill(-1);for(int i=0;i<R;i++)v[i]=raw_inputs[i];int cur=R;for(int i=0;i<9;i++){const auto&g=groups[i];if(g.size()==2)v[cur++]=v[g[0]]|v[g[1]];else{int excluded=p.choice[i],a=g[(excluded+1)%3],b=g[(excluded+2)%3];v[cur]=v[a]|v[b];v[cur+1]=v[cur]|v[g[excluded]];cur+=2;}}assert(cur==N);
 auto insert=[&](uint32_t value,int index){unsigned h=(value*2654435761u)>>25;while(slot[h]>=0&&v[slot[h]]!=value)h=(h+1)&127;if(slot[h]<0)slot[h]=index;return slot[h];};for(int i=0;i<N;i++)e.rep[i]=insert(v[i],i);
 for(int i=0;i<G;i++){int w=N+i;const auto&t=p.g[i];assert(t.a<w&&t.b<w);v[w]=t.op?(v[t.a]|v[t.b]):(v[t.a]&v[t.b]);e.pa[w]=e.rep[t.a];e.pb[w]=e.rep[t.b];e.rep[w]=insert(v[w],w);}e.output=v[p.out];e.err=__builtin_popcount(e.output^target);array<bool,N+G>used{};auto visit=[&](auto&&self,int w)->void{w=e.rep[w];if(w<N||used[w])return;used[w]=true;self(self,e.pa[w]);self(self,e.pb[w]);e.active.push_back(w);};visit(visit,p.out);e.cost=e.active.size();return e;}
Program seed_program(mt19937_64&rng,int style){Program p;for(int i=0;i<9;i++)p.choice[i]=groups[i].size()==3?rng()%3:0;vector<Gate>list;auto gate=[&](int op,int a,int b){int w=N+list.size();list.push_back({op,a,b});return w;};auto orlist=[&](vector<int>vs){shuffle(vs.begin(),vs.end(),rng);int w=vs[0];for(size_t i=1;i<vs.size();i++)w=gate(1,w,vs[i]);return w;};vector<int>terms;
 if(style==1){int cen=gate(1,0,1);int u=orlist({5,7,11}),v=orlist({6,10,13});int t0=gate(0,0,u),t1=gate(0,1,v);int inside=orlist({4,t0,t1});terms.push_back(gate(0,cen,inside));for(int i=2;i<4;i++){vector<int>ns;for(auto[a,b]:edges)if(a==i)ns.push_back(b);int q=orlist(ns);terms.push_back(gate(0,i,q));}}
 else{for(int i=0;i<4;i++){vector<int>ns;for(auto[a,b]:edges)if(a==i)ns.push_back(b);int q=orlist(ns);terms.push_back(gate(0,i,q));}}
 p.out=orlist(terms);assert(list.size()<=G);for(int i=0;i<G;i++){if(i<(int)list.size())p.g[i]=list[i];else p.g[i]={(int)(rng()%2),(int)(rng()%(N+i)),(int)(rng()%(N+i))};}return p;}
void output_solution(const Program&p,const Evaluation&e){array<int,N+G>mapped;mapped.fill(-1);for(int i=0;i<N;i++)mapped[i]=i;vector<Gate>answer;for(int w:e.active){int a=mapped[e.pa[w]],b=mapped[e.pb[w]];assert(a>=0&&b>=0);mapped[w]=N+answer.size();answer.push_back({p.g[w-N].op,a,b});}int out=mapped[e.rep[p.out]];assert(out>=0);auto fg=free_gates(p);
 for(int mask=0;mask<(1<<R);mask++){vector<bool>val;for(int i=0;i<R;i++)val.push_back((mask>>i)&1);for(auto[a,b]:fg)val.push_back(val[a]||val[b]);assert(val.size()==N);for(auto t:answer)val.push_back(t.op?(val[t.a]||val[t.b]):(val[t.a]&&val[t.b]));bool f=false;for(auto[a,b]:edges)f=f||(val[a]&&val[b]);assert(val[out]==f);}
 cout<<"{\"stage\":\"solution\",\"free_ors\":[";for(size_t i=0;i<fg.size();i++){if(i)cout<<',';cout<<'['<<fg[i].first<<','<<fg[i].second<<']';}cout<<"],\"gates\":[";for(size_t i=0;i<answer.size();i++){auto t=answer[i];if(i)cout<<',';cout<<'['<<t.op<<','<<t.a<<','<<t.b<<']';}cout<<"],\"output\":"<<out<<",\"size\":"<<answer.size()<<",\"physical_truth_table_verified\":true}"<<endl;}
int main(int argc,char**argv){assert(argc==3);int seconds=stoi(argv[1]);assert(seconds>0&&seconds<=180);uint64_t sd=stoull(argv[2]);mt19937_64 rng(sd);auto inD=[](int x){return x==0||x==1||x==3||x==9;};for(int i=0;i<4;i++)for(int j=0;j<10;j++)if(inD((point_ids[i]+line_ids[j])%13))edges.push_back({i,4+j});assert(edges.size()==16);vector<int>samples;for(auto[a,b]:edges)samples.push_back((1<<a)|(1<<b));int positives=samples.size();array<int,R>adj{};for(auto[a,b]:edges){adj[a]|=1<<b;adj[b]|=1<<a;}for(int m=0;m<(1<<R);m++){bool ind=true,maximal=true;for(auto[a,b]:edges)if((m>>a&1)&&(m>>b&1))ind=false;if(!ind)continue;for(int a=0;a<R;a++)if(!(m>>a&1)&&!(adj[a]&m))maximal=false;if(maximal)samples.push_back(m);}assert(samples.size()==32);target=(1u<<positives)-1;for(int row=0;row<(int)samples.size();row++){int m=samples[row];for(int i=0;i<R;i++)if(m>>i&1)raw_inputs[i]|=1u<<row;}
 cout<<"{\"stage\":\"start\",\"seed\":"<<sd<<",\"samples\":"<<samples.size()<<",\"genotype_gates\":"<<G<<",\"raw_inputs\":"<<R<<",\"free_or_count\":15,\"outside_points_in_order\":[4,3,6,7,8,9,10,11,12]}"<<endl;
 auto start=chrono::steady_clock::now();uint64_t iterations=0,restarts=0;int best=19;Program p=seed_program(rng,0);Evaluation e=evaluate(p);assert(e.err==0&&e.cost==19);vector<Program>pool;pool.push_back(p);auto value=[](const Evaluation&v){return 12.0*v.err+max(0,v.cost-18)+0.002*v.cost;};double score=value(e);
 while(true){if(iterations%1024==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;if(iterations%80000==0){int style=rng()%4;p=style<3?seed_program(rng,style==1?1:0):pool[rng()%pool.size()];e=evaluate(p);assert(e.err==0);score=value(e);restarts++;}
 Program q=p;int changes=(rng()%12==0)?2:1;for(int step=0;step<changes;step++){int what=rng()%40;if(what==0){int i=rng()%9;if(groups[i].size()==3)q.choice[i]=rng()%3;}else if(what<3)q.out=rng()%(N+G);else{int k=(rng()%4!=0&&!e.active.empty())?e.active[rng()%e.active.size()]-N:rng()%G;int which=rng()%3;if(which==0)q.g[k].op^=1;else if(which==1)q.g[k].a=rng()%(N+k);else q.g[k].b=rng()%(N+k);}}
 Evaluation f=evaluate(q);double next=value(f);double phase=double(iterations%80000)/80000.0;double temperature=0.08+3.5*(1-phase)*(1-phase);bool accept=next<=score||generate_canonical<double,53>(rng)<exp((score-next)/temperature);if(accept){p=q;e=f;score=next;}if(f.err==0&&f.cost<best){best=f.cost;cout<<"{\"stage\":\"best\",\"iterations\":"<<iterations<<",\"size\":"<<best<<"}"<<endl;if(best<=18){output_solution(q,f);return 0;}}if(e.err==0&&e.cost<=19&&iterations%1000==0){if(pool.size()<16)pool.push_back(p);else pool[rng()%pool.size()]=p;}iterations++;}
 cout<<"{\"stage\":\"finished\",\"iterations\":"<<iterations<<",\"restarts\":"<<restarts<<",\"best_valid_size\":"<<best<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"}"<<endl;}
