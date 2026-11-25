#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <string>
#include <vector>
using TT = std::array<uint64_t,16>;
struct Gate { int op,a,b; };
struct Circuit { std::vector<Gate> gates; int output=0, aux=0, score=100000, errors=100000, auxerr=0; };
std::mt19937_64 rng;
int rnd(int n){return int(rng()%n);}
std::array<TT,10> inputs;
TT target[2], extra, critical;
std::vector<std::pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
std::vector<int> covers[2];
int distance(const TT&a,const TT&b,bool weighted){int s=0;for(int j=0;j<16;j++){auto x=a[j]^b[j];s+=std::popcount(x);if(weighted)s+=8*std::popcount(x&critical[j]);}return s;}
void evaluate(Circuit& c,int mode){
 std::array<TT,31> vals{};for(int j=0;j<10;j++)vals[j]=inputs[j];
 int ns=0;for(int i=0;i<(int)c.gates.size();i++){auto g=c.gates[i];ns+=g.op==2;for(int j=0;j<16;j++)vals[10+i][j]=g.op==0?(vals[g.a][j]&vals[g.b][j]):g.op==1?(vals[g.a][j]|vals[g.b][j]):~vals[g.a][j];}
 int best=100000,auxbest=100000;for(int i=0;i<10+(int)c.gates.size();i++){
  int d=distance(vals[i],target[mode],true);if(d<best){best=d;c.output=i;c.errors=distance(vals[i],target[mode],false);}
  if(mode){int e=distance(vals[i],extra,true);if(e<auxbest){auxbest=e;c.aux=i;c.auxerr=distance(vals[i],extra,false);}}
 }
 c.score=best+(mode?auxbest:0)+(ns==0?24:0)+(ns>2?1000*(ns-2):0);
}
void dump(const Circuit& c,int mode,const std::string& path){std::ofstream f(path);f<<"{\"mode\":"<<mode<<",\"score\":"<<c.score<<",\"errors\":"<<c.errors<<",\"aux_errors\":"<<c.auxerr<<",\"output\":"<<c.output<<",\"aux_output\":"<<c.aux<<",\"gates\":[";for(int i=0;i<(int)c.gates.size();i++){if(i)f<<",";auto g=c.gates[i];f<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}f<<"]}\n";}
Circuit star(int mode){
 Circuit c;int mask=covers[mode][rnd(covers[mode].size())];std::vector<int> vs;for(int i=0;i<10;i++)if(mask&(1<<i))vs.push_back(i);std::shuffle(vs.begin(),vs.end(),rng);std::vector<int> leaves[10];
 for(auto [a,b]:edges){if(mode&&(a==9||b==9))continue;bool ca=mask&(1<<a),cb=mask&(1<<b);int center=ca&&cb?(rnd(2)?a:b):(ca?a:b);leaves[center].push_back(center==a?b:a);}
 std::vector<int> terms;for(int v:vs){auto l=leaves[v];if(l.empty())continue;std::shuffle(l.begin(),l.end(),rng);while(l.size()>1){int a=l.back();l.pop_back();int b=l.back();l.pop_back();int w=10+c.gates.size();c.gates.push_back({1,a,b});l.push_back(w);}int w=10+c.gates.size();c.gates.push_back({0,v,l[0]});terms.push_back(w);}
 while(terms.size()>1){std::shuffle(terms.begin(),terms.end(),rng);int a=terms.back();terms.pop_back();int b=terms.back();terms.pop_back();int w=10+c.gates.size();c.gates.push_back({1,a,b});terms.push_back(w);}c.output=terms[0];return c;
}
void erase_gate(Circuit& c,int at){int w=10+at;int repl=rnd(2)?c.gates[at].a:c.gates[at].b;if(repl>=w)repl=rnd(10);c.gates.erase(c.gates.begin()+at);for(auto&g:c.gates){for(int*p:{&g.a,&g.b}){if(*p==w)*p=repl;else if(*p>w)--*p;}}if(c.output==w)c.output=repl;else if(c.output>w)--c.output;}
Circuit seed(int mode){Circuit c=star(mode);int n=mode?16:19;while((int)c.gates.size()>n)erase_gate(c,rnd(c.gates.size()));while((int)c.gates.size()<n){int i=c.gates.size();c.gates.push_back({rnd(3),rnd(10+i),rnd(10+i)});}if(mode&&rnd(2)){int i=rnd(n);c.gates[i]={1,4,6};}if(rnd(4))c.gates[rnd(n)].op=2;evaluate(c,mode);return c;}
void mutate(Circuit& c){int n=c.gates.size();int k=rnd(100)<75?1:rnd(100)<80?2:3+rnd(4);for(int z=0;z<k;z++){int i=rnd(n),m=rnd(100);auto&g=c.gates[i];if(m<35)g.a=rnd(11+i);else if(m<70)g.b=rnd(11+i);else if(m<87)g.op=rnd(3);else if(m<95){int j=rnd(n);std::swap(g.op,c.gates[j].op);}else {g={rnd(3),rnd(11+i),rnd(11+i)};}}}
std::vector<Circuit> read_sat(const std::string& path){std::ifstream f(path);std::string line;std::vector<Circuit> out;Circuit cur;bool active=false;while(std::getline(f,line)){if(line.find("MODEL_BEGIN")!=std::string::npos){active=true;cur={};}else if(line.find("MODEL_END")!=std::string::npos){if(active&&cur.gates.size()==19){evaluate(cur,0);out.push_back(cur);}active=false;}else if(active){std::istringstream ss(line);Gate g;if(ss>>g.op>>g.a>>g.b)cur.gates.push_back(g);}}return out;}
int main(int argc,char**argv){
 int seconds=argc>1?std::stoi(argv[1]):1200;uint64_t seednum=argc>2?std::stoull(argv[2]):118;rng.seed(seednum);std::string folder=argc>3?argv[3]:".";std::string sat=argc>4?argv[4]:"";
 for(int x=0;x<1024;x++){int j=x/64,b=x%64;uint64_t bit=uint64_t(1)<<b;for(int k=0;k<10;k++)if(x&(1<<k))inputs[k][j]|=bit;for(auto [a,c]:edges){if((x&(1<<a))&&(x&(1<<c))){target[0][j]|=bit;if(a!=9&&c!=9)target[1][j]|=bit;}}if((x&(1<<4))||(x&(1<<6)))extra[j]|=bit;if(std::popcount(unsigned(x))<=2)critical[j]|=bit;}
 for(int m=0;m<2;m++)for(int mask=0;mask<1024;mask++){if(std::popcount(unsigned(mask))!=(m?5:6))continue;bool ok=true;for(auto [a,b]:edges){if(m&&(a==9||b==9))continue;if(!(mask&(1<<a))&&!(mask&(1<<b)))ok=false;}if(ok)covers[m].push_back(mask);}
 std::cout<<"seed "<<seednum<<" seconds "<<seconds<<" full covers "<<covers[0].size()<<" H covers "<<covers[1].size()<<std::endl;
 Circuit best[2];uint64_t iters=0,restarts=0;auto start=std::chrono::steady_clock::now();double nextlog=0,nextsat=0;std::vector<Circuit> satseeds;
 while(true){double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();if(elapsed>=seconds)break;int mode=int(elapsed/30)%2;if(elapsed>=nextsat){satseeds=read_sat(sat);nextsat=elapsed+15;}
  Circuit cur;if(mode==0&&!satseeds.empty()&&rnd(5)==0)cur=satseeds[rnd(satseeds.size())];else if(best[mode].score<100000&&rnd(3)==0){cur=best[mode];for(int q=0;q<3+rnd(12);q++)mutate(cur);evaluate(cur,mode);}else cur=seed(mode);
  for(int j=0;j<30000;j++){Circuit cand=cur;mutate(cand);evaluate(cand,mode);iters++;double temp=0.2+8.0*std::pow(1.0-double(j)/30000,3);int delta=cur.score-cand.score;double u=(rng()>>11)*0x1.0p-53;if(delta>=0||u<std::exp(double(delta)/temp))cur=cand;
   if(cand.score<best[mode].score){best[mode]=cand;dump(cand,mode,folder+"/best-"+std::to_string(mode)+".json");double t=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();std::cout<<"BEST t="<<t<<" mode="<<mode<<" score="<<cand.score<<" errors="<<cand.errors<<" aux="<<cand.auxerr<<" iterations="<<iters<<std::endl;if(cand.score==0){dump(cand,mode,folder+"/WITNESS.json");std::cout<<"WITNESS FULL TRUTH TABLE VERIFIED"<<std::endl;return 0;}}
  }restarts++;elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();if(elapsed>=nextlog){std::cout<<"STATUS seconds="<<elapsed<<" iterations="<<iters<<" restarts="<<restarts<<" fullscore="<<best[0].score<<" fullerrors="<<best[0].errors<<" Hscore="<<best[1].score<<" Herrors="<<best[1].errors<<" Haux="<<best[1].auxerr<<" SATseeds="<<satseeds.size()<<std::endl;nextlog=elapsed+15;}
 }
 std::cout<<"FINISHED iterations="<<iters<<" restarts="<<restarts<<" fullscore="<<best[0].score<<" Hscore="<<best[1].score<<std::endl;return 2;
}
