#include <array>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
using TT = array<uint64_t,16>;
struct Gate { int op,a,b; };
using Circuit = vector<Gate>;
int NN=19; bool signedMode=false;
const vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
const vector<Gate> seed={{1,9,5},{1,0,9},{1,0,6},{1,7,3},{0,1,12},{1,6,5},{1,11,3},{1,13,1},{1,14,2},{0,12,15},{0,4,16},{0,19,11},{1,7,21},{0,18,17},{1,20,23},{1,3,15},{0,25,8},{0,22,10},{1,27,26},{1,24,28}};
array<TT,10> inputs{}; TT target{},critical{};
mt19937_64 rng;
int rnd(int n){return rng()%n;}
int rop(){if(!signedMode)return rnd(3);int ops[]={0,0,0,7,7,7,1,2};return ops[rnd(8)];}
pair<int,int> fitness(const Circuit& c){
 array<TT,29> v{};
 copy(inputs.begin(),inputs.end(),v.begin());
 bool nt=false;uint32_t nots=0;array<uint32_t,29> cones{};
 for(int j=0;j<NN;j++){
  const auto& g=c[j]; nt|=g.op==2; if(g.op==2)nots|=uint32_t(1)<<j;cones[10+j]=(uint32_t(1)<<j)|cones[g.a]|((!signedMode&&g.op==2)?0:cones[g.b]);
  for(int k=0;k<16;k++){
   if(signedMode){uint64_t a=(g.op&1)?~v[g.a][k]:v[g.a][k];uint64_t b=(g.op&2)?~v[g.b][k]:v[g.b][k];v[10+j][k]=(g.op&4)?~(a&b):(a&b);}
   else v[10+j][k]=g.op==0?(v[g.a][k]&v[g.b][k]):g.op==1?(v[g.a][k]|v[g.b][k]):~v[g.a][k];
  }
 }
 int fp=0,fn=0,crit=0;
 for(int k=0;k<16;k++) {fp+=__builtin_popcountll(v[10+NN-1][k]&~target[k]);fn+=__builtin_popcountll(~v[10+NN-1][k]&target[k]);crit+=__builtin_popcountll((v[10+NN-1][k]^target[k])&critical[k]);}
 return {4*fp+fn+7*crit+(signedMode||(nots&cones[10+NN-1])?0:8),fp+fn};
}
void output(const Circuit& c,ostream& f){
 for(int j=0;j<NN;j++) f<<10+j<<" "<<c[j].op<<" "<<c[j].a<<" "<<c[j].b<<"\n";
 f.flush();
}
Circuit fresh(){
 vector<Gate> v=seed;
 if(signedMode)for(auto&g:v)if(g.op==1)g.op=7;
 while((int)v.size()>NN){
  int removed=rnd(v.size()-1);int replacement=rnd(2)?v[removed].a:v[removed].b;
  v.erase(v.begin()+removed);
  for(auto&g:v)for(int*p:{&g.a,&g.b}){if(*p==10+removed)*p=replacement;else if(*p>10+removed)--*p;}
 }
 if(!signedMode&&rnd(2))v[rnd(NN-1)].op=2;
 if(rnd(5)==0)for(int j=0;j<NN;j++)v[j]={rop(),rnd(10+j),rnd(10+j)};
 return v;
}
int main(int argc,char**argv){
 int seconds=argc>1?stoi(argv[1]):300;
 rng.seed(argc>2?stoull(argv[2]):1);
 signedMode=argc>3;NN=signedMode?18:19;
 for(int x=0;x<1024;x++){
  for(int i=0;i<10;i++) if((x>>i)&1)inputs[i][x/64]|=uint64_t(1)<<(x%64);
  bool b=false;for(auto [a,z]:edges)b|=((x>>a)&(x>>z)&1);
  if(b)target[x/64]|=uint64_t(1)<<(x%64);
  if(__builtin_popcount((unsigned)x)<=2)critical[x/64]|=uint64_t(1)<<(x%64);
 }
 auto start=chrono::steady_clock::now();
 int best=10000; uint64_t it=0,restarts=0;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  Circuit c=fresh(); int score=fitness(c).first,flat=0;
  for(int epoch=0;epoch<200000;epoch++){
   Circuit m=c;
   int changes=1+(rnd(7)==0)+(rnd(25)==0);
   for(int k=0;k<changes;k++){
    int j=rnd(NN),which=rnd(3);
    if(which==0)m[j].op=rop();else if(which==1)m[j].a=rnd(10+j);else m[j].b=rnd(10+j);
   }
   auto [s,err]=fitness(m);it++;
   if(s<=score){if(s<score)flat=0;else flat++;c=m;score=s;}
   if(s<best){best=s;cerr<<"best "<<best<<" raw "<<err<<" iterations "<<it<<" restarts "<<restarts<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";output(m,cout);}
   if(s==0){cerr<<"FOUND\n";return 0;}
   if(flat>10000)break;
   if(it%100000==0 && chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;
  }
  restarts++;
 }
 cerr<<"Finished best "<<best<<" iterations "<<it<<" restarts "<<restarts<<"\n";
}
