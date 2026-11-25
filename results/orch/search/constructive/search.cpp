#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>

using U = uint64_t;
struct Gate { int a,b; bool land; };
using Circuit = std::array<Gate,26>;
std::mt19937_64 rng(2732);
std::vector<std::pair<int,int>> edges = {{0,7},{0,8},{0,10},{1,7},{1,9},{1,13},{2,8},{2,12},{2,13},{3,7},{3,11},{3,12},{4,10},{4,11},{4,13},{5,9},{5,10},{5,12},{6,8},{6,9},{6,11}};
std::vector<int> rows;
std::array<U,14> inputs;
U target;
int rnd(int n) { return int(rng()%n); }
bool isfalse(int mask) { for(auto [a,b]:edges) if((mask>>a&1)&&(mask>>b&1)) return false; return true; }
U eval(const Circuit &c) {
  U wires[40]; for(int i=0;i<14;i++) wires[i]=inputs[i];
  for(int i=0;i<26;i++) { const auto &g=c[i]; wires[14+i]=g.land ? wires[g.a]&wires[g.b] : wires[g.a]|wires[g.b]; }
  return wires[39];
}
Circuit seed() {
  std::vector<Gate> gates;
  std::vector<int> terms, order={0,1,2,3,4,5,6};
  std::shuffle(order.begin(),order.end(),rng);
  bool reverse=rnd(2);
  for(int i:order) {
    int v=i+(reverse?7:0); std::vector<int> ns;
    for(auto [a,b]:edges) { if(a==v) ns.push_back(b); if(b==v) ns.push_back(a); }
    std::shuffle(ns.begin(),ns.end(),rng);
    gates.push_back({ns[0],ns[1],false});
    gates.push_back({14+int(gates.size())-1,ns[2],false});
    gates.push_back({v,14+int(gates.size())-1,true});
    terms.push_back(14+int(gates.size())-1);
  }
  while(terms.size()>1) {
    int a=rnd(int(terms.size())); int v=terms[a]; terms.erase(terms.begin()+a);
    int b=rnd(int(terms.size())); int w=terms[b]; terms.erase(terms.begin()+b);
    gates.push_back({v,w,false}); terms.push_back(14+int(gates.size())-1);
  }
  int remove=rnd(26); int bypass=rnd(2)?gates[remove].a:gates[remove].b;
  auto remap=[&](int n) { if(n==14+remove)n=bypass; if(n>14+remove)n--; return n; };
  Circuit c;
  for(int i=0,j=0;i<27;i++) if(i!=remove) { c[j++]={remap(gates[i].a),remap(gates[i].b),gates[i].land}; }
  return c;
}
void mutate(Circuit &c,int mode) {
  int times=1+(rnd(100)<25)+(rnd(100)<10);
  for(int k=0;k<times;k++) {
    int i=rnd(26); int type=rnd(10);
    if(type==0)c[i].land=!c[i].land;
    else if(type<5)c[i].a=rnd(14+i);
    else c[i].b=rnd(14+i);
    if(c[i].a==c[i].b) c[i].b=(c[i].b+1)%(14+i);
  }
  if(mode==1&&rnd(50)==0) {
    int i=rnd(25),j=i+1;
    if(c[j].a!=14+i && c[j].b!=14+i) {
      std::swap(c[i],c[j]);
      for(int k=j+1;k<26;k++)for(int* p:{&c[k].a,&c[k].b}) {
        if(*p==14+i)*p=14+j; else if(*p==14+j)*p=14+i;
      }
    }
  }
}
int weighted(U bad,const std::vector<int>&w) {
  int r=0; while(bad) { int i=std::countr_zero(bad); bad&=bad-1; r+=w[i]; } return r;
}
void write(const Circuit &c,const std::string &path) {
  std::ofstream out(path); out<<"[\n";
  for(int i=0;i<26;i++) out<<"["<<c[i].a<<","<<c[i].b<<",\""<<(c[i].land?"and":"or")<<"\"]"<<(i==25?"\n":",\n");
  out<<"]\n";
}
int main(int argc,char**argv) {
  int seconds=argc>1?std::stoi(argv[1]):600; std::string prefix=argc>2?argv[2]:"search";
  if(argc>3)rng.seed(std::stoull(argv[3]));
  for(auto[a,b]:edges)rows.push_back((1<<a)|(1<<b));
  for(int mask=0;mask<(1<<14);mask++)if(isfalse(mask)) {
    bool maximal=true; for(int i=0;i<14;i++)if(!(mask>>i&1)&&isfalse(mask|(1<<i))) { maximal=false;break; }
    if(maximal)rows.push_back(mask);
  }
  if(rows.size()>64)return 2;
  for(size_t r=0;r<rows.size();r++)for(int i=0;i<14;i++)if(rows[r]>>i&1)inputs[i]|=U(1)<<r;
  target=(U(1)<<21)-1;
  std::cout<<"rows="<<rows.size()<<" budget_seconds="<<seconds<<std::endl;
  auto start=std::chrono::steady_clock::now();
  U iterations=0, seen_single_errors=0; int restarts=0,best=100; double nextreport=0;
  while(true) {
    Circuit current=seed(); U bad=eval(current)^target;
    std::vector<int>w(rows.size(),1); int score=weighted(bad,w);
    double temp=0.15+0.35*double(rnd(100))/100;
    for(int k=0;k<250000;k++,iterations++) {
      Circuit next=current; mutate(next,restarts%2); U nbad=eval(next)^target; int mism=std::popcount(nbad);
      if(mism==1 && !(seen_single_errors&nbad)) {
        seen_single_errors|=nbad; int row=std::countr_zero(nbad);
        write(next,prefix+"-error-row-"+std::to_string(row)+".json");
        std::cout<<"single_error_row="<<row<<" input_mask="<<rows[row]<<" false_positive="<<(row>=21)<<" iterations="<<iterations<<std::endl;
      }
      if(mism<best) { best=mism; write(next,prefix+"-best.json"); std::cout<<"best="<<best<<" iterations="<<iterations<<" bad="<<nbad<<std::endl; }
      if(!nbad) { write(next,prefix+"-solution.json"); std::cout<<"FOUND"<<std::endl; return 0; }
      int ns=weighted(nbad,w);
      if(ns<=score || double(rng())/double(UINT64_MAX)<std::exp(double(score-ns)/temp)) { current=next;bad=nbad;score=ns; }
      if(k%5000==4999) {
        U bits=bad; while(bits){int b=std::countr_zero(bits);bits&=bits-1;w[b]++;}
        score=weighted(bad,w); temp=0.2+0.03*double(k/5000);
      }
      if(k%4096==0) {
        double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        if(elapsed>=seconds) { std::cout<<"DONE iterations="<<iterations<<" restarts="<<restarts<<" best="<<best<<" seen_single_errors="<<seen_single_errors<<std::endl; return 1; }
        if(elapsed>=nextreport) { std::cout<<"progress seconds="<<elapsed<<" iterations="<<iterations<<" restarts="<<restarts<<" best="<<best<<std::endl; nextreport=elapsed+30; }
      }
    }
    restarts++;
  }
}
