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
#include "meta3773_five_patch_data.hpp"
struct Gate{int op,a,b;};
struct Program{array<Gate,G> g;array<int,8> choice;int out;};
struct Evaluation{int err,cost;bool bad;array<int,N+G> rep,pa,pb;vector<int> active;uint64_t output;};
array<uint64_t,R> raw_inputs;
uint64_t target;
vector<pair<int,int>> edges;
vector<pair<int,int>> free_gates(const Program&p){vector<pair<int,int>>answer;for(int i=0;i<8;i++){const auto&variant=free_variants[i][p.choice[i]];answer.insert(answer.end(),variant.begin(),variant.end());}assert(answer.size()==N-R);return answer;}
Evaluation evaluate(const Program&p){Evaluation e;array<uint64_t,N+G>v;array<int,256>slot;slot.fill(-1);for(int i=0;i<R;i++)v[i]=raw_inputs[i];int cur=R;for(int i=0;i<8;i++)for(auto[a,b]:free_variants[i][p.choice[i]]){assert(a<cur&&b<cur);v[cur++]=v[a]|v[b];}assert(cur==N);
 auto insert=[&](uint64_t value,int index){unsigned h=(value*11400714819323198485ull)>>56;while(slot[h]>=0&&v[slot[h]]!=value)h=(h+1)&255;if(slot[h]<0)slot[h]=index;return slot[h];};for(int i=0;i<N;i++)e.rep[i]=insert(v[i],i);
 for(int i=0;i<G;i++){int w=N+i;const auto&t=p.g[i];assert(t.a<w&&t.b<w);v[w]=t.op?(v[t.a]|v[t.b]):(v[t.a]&v[t.b]);e.pa[w]=e.rep[t.a];e.pb[w]=e.rep[t.b];e.rep[w]=insert(v[w],w);}e.output=v[p.out];e.err=__builtin_popcountll(e.output^target);array<bool,N+G>used{};auto visit=[&](auto&&self,int w)->void{w=e.rep[w];if(w<N||used[w])return;used[w]=true;self(self,e.pa[w]);self(self,e.pb[w]);e.active.push_back(w);};visit(visit,p.out);e.cost=e.active.size();e.bad=false;for(int w:e.active)if(p.g[w-N].op==0&&(v[w]&target)&&(v[w]&~target))e.bad=true;return e;}
Program seed_program(mt19937_64&rng,int style){Program p;for(int i=0;i<8;i++)p.choice[i]=rng()%free_variants[i].size();vector<Gate>list;auto gate=[&](int op,int a,int b){int w=N+list.size();list.push_back({op,a,b});return w;};auto orlist=[&](vector<int>vs){shuffle(vs.begin(),vs.end(),rng);int w=vs[0];for(size_t i=1;i<vs.size();i++)w=gate(1,w,vs[i]);return w;};vector<vector<int>>neighbors(K);for(auto[a,b]:edges)neighbors[a].push_back(b);vector<int>terms;int first=0;
 if(style){vector<int>u,v;int common=-1;for(int w:neighbors[0])if(find(neighbors[1].begin(),neighbors[1].end(),w)!=neighbors[1].end())common=w;assert(common>=0);for(int w:neighbors[0])if(w!=common)u.push_back(w);for(int w:neighbors[1])if(w!=common)v.push_back(w);int U=orlist(u),V=orlist(v),centers=gate(1,0,1);
 if(style==1){int t0=gate(0,0,U),t1=gate(0,1,V);int inside=orlist({common,t0,t1});terms.push_back(gate(0,centers,inside));}
 else{int neighbor=gate(1,U,common),unsafe=gate(0,neighbor,centers),filter=gate(1,0,common),filtered=gate(0,unsafe,filter),other=gate(0,1,V);terms.push_back(gate(1,filtered,other));}first=2;}
 for(int i=first;i<K;i++){int q=orlist(neighbors[i]);terms.push_back(gate(0,i,q));}p.out=orlist(terms);assert(list.size()<=G);for(int i=0;i<G;i++){if(i<(int)list.size())p.g[i]=list[i];else p.g[i]={(int)(rng()%2),(int)(rng()%(N+i)),(int)(rng()%(N+i))};}return p;}
void output_solution(const Program&p,const Evaluation&e){array<int,N+G>mapped;mapped.fill(-1);for(int i=0;i<N;i++)mapped[i]=i;vector<Gate>answer;for(int w:e.active){int a=mapped[e.pa[w]],b=mapped[e.pb[w]];assert(a>=0&&b>=0);mapped[w]=N+answer.size();answer.push_back({p.g[w-N].op,a,b});}int out=mapped[e.rep[p.out]];assert(out>=0);auto fg=free_gates(p);
 for(int mask=0;mask<(1<<R);mask++){vector<bool>val;for(int i=0;i<R;i++)val.push_back((mask>>i)&1);for(auto[a,b]:fg)val.push_back(val[a]||val[b]);assert(val.size()==N);for(auto t:answer)val.push_back(t.op?(val[t.a]||val[t.b]):(val[t.a]&&val[t.b]));bool f=false;for(auto[a,b]:edges)f=f||(val[a]&&val[b]);assert(val[out]==f);}
 cout<<"{\"stage\":\"verified_patch\",\"free_ors\":[";for(size_t i=0;i<fg.size();i++){if(i)cout<<',';cout<<'['<<fg[i].first<<','<<fg[i].second<<']';}cout<<"],\"gates\":[";for(size_t i=0;i<answer.size();i++){auto t=answer[i];if(i)cout<<',';cout<<'['<<t.op<<','<<t.a<<','<<t.b<<']';}cout<<"],\"output\":"<<out<<",\"size\":"<<answer.size()<<",\"assembled_global_size\":"<<(BASE+answer.size())<<",\"physical_truth_table_verified\":true}"<<endl;}
int main(int argc,char**argv){assert(argc==3);int seconds=stoi(argv[1]);assert(seconds>0&&seconds<=180);uint64_t sd=stoull(argv[2]);mt19937_64 rng(sd);auto inD=[](int x){return x==0||x==1||x==3||x==9;};for(int i=0;i<K;i++)for(int j=0;j<(int)line_ids.size();j++)if(inD((point_ids[i]+line_ids[j])%13))edges.push_back({i,K+j});assert(edges.size()==4*K);vector<int>samples;for(auto[a,b]:edges)samples.push_back((1<<a)|(1<<b));int positives=samples.size();array<int,R>adj{};for(auto[a,b]:edges){adj[a]|=1<<b;adj[b]|=1<<a;}for(int m=0;m<(1<<R);m++){bool ind=true,maximal=true;for(auto[a,b]:edges)if((m>>a&1)&&(m>>b&1))ind=false;if(!ind)continue;for(int a=0;a<R;a++)if(!(m>>a&1)&&!(adj[a]&m))maximal=false;if(maximal)samples.push_back(m);}assert(samples.size()<=64);target=(1ull<<positives)-1;for(int row=0;row<(int)samples.size();row++){int m=samples[row];for(int i=0;i<R;i++)if(m>>i&1)raw_inputs[i]|=1ull<<row;}
 cout<<"{\"stage\":\"start\",\"seed\":"<<sd<<",\"samples\":"<<samples.size()<<",\"genotype_gates\":"<<G<<",\"raw_inputs\":"<<R<<",\"free_or_count\":16,\"outside_points_in_order\":[4,5,7,8,9,10,11,12]}"<<endl;
 auto start=chrono::steady_clock::now();uint64_t iterations=0,restarts=0;int best=TARGET+1,bestbad=100;Program p=seed_program(rng,0);Evaluation e=evaluate(p);assert(e.err==0&&e.cost==TARGET+1);vector<Program>pool;pool.push_back(p);auto value=[](const Evaluation&v){return 12.0*v.err+max(0,v.cost-TARGET)+0.002*v.cost+(v.bad?0:5.0);};double score=value(e);
 while(true){if(iterations%1024==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;if(iterations%80000==0){int style=rng()%4;p=style<3?seed_program(rng,style):pool[rng()%pool.size()];e=evaluate(p);assert(e.err==0);score=value(e);restarts++;}
 Program q=p;int changes=(rng()%12==0)?2:1;for(int step=0;step<changes;step++){int what=rng()%40;if(what==0){int i=rng()%8;q.choice[i]=rng()%free_variants[i].size();}else if(what<3)q.out=rng()%(N+G);else{int k=(rng()%4!=0&&!e.active.empty())?e.active[rng()%e.active.size()]-N:rng()%G;int which=rng()%3;if(which==0)q.g[k].op^=1;else if(which==1)q.g[k].a=rng()%(N+k);else q.g[k].b=rng()%(N+k);}}
 Evaluation f=evaluate(q);double next=value(f);double phase=double(iterations%80000)/80000.0;double temperature=0.08+3.5*(1-phase)*(1-phase);bool accept=next<=score||generate_canonical<double,53>(rng)<exp((score-next)/temperature);if(accept){p=q;e=f;score=next;}if(f.err==0&&f.cost<best){best=f.cost;cout<<"{\"stage\":\"best\",\"iterations\":"<<iterations<<",\"size\":"<<best<<"}"<<endl;if(best<=TARGET){output_solution(q,f);return 0;}}if(f.err==0&&f.bad&&f.cost<bestbad){bestbad=f.cost;cout<<"{\"stage\":\"best_bad_and_patch\",\"size\":"<<bestbad<<"}"<<endl;output_solution(q,f);}
 if(e.err==0&&e.bad&&e.cost<=TARGET+3&&iterations%1000==0){if(pool.size()<16)pool.push_back(p);else pool[rng()%pool.size()]=p;}iterations++;}
 cout<<"{\"stage\":\"finished\",\"iterations\":"<<iterations<<",\"restarts\":"<<restarts<<",\"best_valid_size\":"<<best<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"}"<<endl;}
