#include <array>
#include <vector>
#include <random>
#include <algorithm>
#include <chrono>
#include <iostream>
#include <cmath>
#include <cstdint>
#include <cstdlib>
using namespace std;
constexpr int INPUTS=14, GATES=26;
struct Gate {int op,a,b;};
using Circ=array<Gate,GATES>;
const array<uint64_t,INPUTS> initial={36591884419335893ULL,4504981298302097ULL,72068589181933955ULL,88555960018949ULL,1271061582053427ULL,11294185286009743ULL,162411061562112127ULL,1049129947434ULL,7800873329228ULL,61663119197296ULL,492655857436544ULL,3940759220910080ULL,31525326274035712ULL,252201716538146816ULL};
const uint64_t goal=288230238712758272ULL;
const array<pair<int,int>,21> edges={{{0,7},{1,7},{3,7},{1,8},{2,8},{4,8},{2,9},{3,9},{5,9},{3,10},{4,10},{6,10},{4,11},{5,11},{0,11},{5,12},{6,12},{1,12},{6,13},{0,13},{2,13}}};
mt19937_64 gen;
uint64_t evaluations=0;
int rnd(int n){return gen()%n;}
double uniform(){return double(gen()>>11)*0x1.0p-53;}
struct Score {int fp,fn;int value(int weight)const{return fp*weight+fn;}};
Score eval(const Circ& c){
 array<uint64_t,INPUTS+GATES> w;
 for(int i=0;i<INPUTS;i++)w[i]=initial[i];
 for(int j=0;j<GATES;j++){
  auto g=c[j];
  w[INPUTS+j]=g.op==0?w[g.a]&w[g.b]:w[g.a]|w[g.b];
 }
 evaluations++;
 uint64_t out=w.back();
 return {__builtin_popcountll(out&~goal),__builtin_popcountll(goal&~out)};
}
void print(const Circ& c,Score s){
 cout<<"score fp="<<s.fp<<" fn="<<s.fn<<" evaluations="<<evaluations<<"\n";
 for(int j=0;j<GATES;j++)cout<<INPUTS+j<<" "<<c[j].op<<" "<<c[j].a<<" "<<c[j].b<<"\n";
 cout.flush();
}
Circ seed(){
 vector<int> centers;
 int shore=rnd(2)*7;
 for(int i=0;i<7;i++)centers.push_back(shore+i);
 shuffle(centers.begin(),centers.end(),gen);
 vector<Gate> c;
 vector<int> outs;
 for(int center:centers){
  vector<int> neighbors;
  for(auto [a,b]:edges){if(a==center)neighbors.push_back(b);if(b==center)neighbors.push_back(a);}
  shuffle(neighbors.begin(),neighbors.end(),gen);
  int wire=neighbors[0];
  for(int k=1;k<3;k++){c.push_back({1,wire,neighbors[k]});wire=INPUTS-1+c.size();}
  c.push_back({0,center,wire});outs.push_back(INPUTS-1+c.size());
 }
 while(outs.size()>1){
  shuffle(outs.begin(),outs.end(),gen);
  int a=outs.back();outs.pop_back();int b=outs.back();outs.pop_back();
  c.push_back({1,a,b});outs.push_back(INPUTS-1+c.size());
 }
 if(c.size()!=27)abort();
 int gone=rnd(c.size()),replacement=rnd(2)?c[gone].a:c[gone].b;
 Circ result;
 for(int i=0,j=0;i<27;i++)if(i!=gone){
  auto g=c[i];
  auto map=[&](int x){if(x==INPUTS+gone)x=replacement;return x>INPUTS+gone?x-1:x;};
  result[j++]={g.op,map(g.a),map(g.b)};
 }
 return result;
}
int main(int argc,char**argv){
 int seconds=argc>1?atoi(argv[1]):600;
 uint64_t random_seed=argc>2?strtoull(argv[2],nullptr,10):2583;
 gen.seed(random_seed);
 cout<<"seed="<<random_seed<<" seconds="<<seconds<<" inputs=14 gates=26 critical_rows=58\n";
 auto start=chrono::steady_clock::now();
 int best=1000;uint64_t rounds=0;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  Circ current=seed();Score sc=eval(current);int weight=1+rnd(5),cost=sc.value(weight);
  for(int iteration=0;iteration<100000;iteration++){
   Circ candidate=current;
   int changes=rnd(16)==0?2+rnd(4):1;
   for(int k=0;k<changes;k++){
    int j=rnd(GATES),part=rnd(3);
    if(part==0)candidate[j].op=rnd(2);
    else if(part==1)candidate[j].a=rnd(INPUTS+j);
    else candidate[j].b=rnd(INPUTS+j);
   }
   Score sd=eval(candidate);int nextcost=sd.value(weight);
   double temperature=(iteration%20000<1000)?0.4:0.04;
   if(nextcost<=cost||uniform()<exp(double(cost-nextcost)/temperature)){current=candidate;cost=nextcost;sc=sd;}
   if(sd.fp+sd.fn<best){best=sd.fp+sd.fn;print(candidate,sd);}
   if(sd.fp==0&&sd.fn==0){cout<<"FOUND\n";print(candidate,sd);return 0;}
   if(iteration%1000==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;
  }
  rounds++;
 }
 cout<<"DONE rounds="<<rounds<<" evaluations="<<evaluations<<" best_critical_errors="<<best<<"\n";
}
