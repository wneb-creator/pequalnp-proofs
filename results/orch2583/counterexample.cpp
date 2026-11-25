#include "cadical.hpp"
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

struct Gate { int op,a,b; };
struct Problem {
  CaDiCaL::Solver sat;
  int inputs,count,nv=0,zero;
  std::vector<std::pair<int,int>> edges;
  std::vector<std::array<std::vector<int>,2>> selectors;
  std::vector<int> isOr;
  std::vector<std::vector<int>> matrix;
  std::vector<bool> rowTargets;
  int fresh(){return ++nv;}
  bool target(int x)const{
    for(auto [a,b]:edges)if((x&(1<<a))&&(x&(1<<b)))return true;
    return false;
  }
  void onehot(const std::vector<int>&v){
    sat.clause(v);
    for(size_t i=0;i<v.size();++i)for(size_t j=0;j<i;++j)sat.clause(-v[i],-v[j]);
  }
  Problem(const char* graph,int gates,int seed,bool ordered,int protectedPrefix):count(gates),selectors(count),isOr(count){
    std::ifstream f(graph);int m;f>>inputs>>m;
    for(int i=0;i<m;++i){int a,b;f>>a>>b;edges.push_back({a,b});}
    sat.set("quiet",1);sat.set("seed",seed);zero=fresh();sat.clause(-zero);
    for(int g=0;g<count;++g){
      isOr[g]=fresh();
      for(int k=0;k<2;++k){for(int s=0;s<inputs+g;++s)selectors[g][k].push_back(fresh());onehot(selectors[g][k]);}
      for(int a=0;a<inputs+g;++a)for(int b=0;b<a;++b)sat.clause(-selectors[g][0][a],-selectors[g][1][b]);
    }
    for(int g=0;g+1<count;++g){
      std::vector<int> used;
      for(int h=g+1;h<count;++h)for(int k=0;k<2;++k)used.push_back(selectors[h][k][inputs+g]);
      if(g>=protectedPrefix)sat.clause(used);
      if(ordered&&g>=protectedPrefix){
        for(int b=0;b<inputs+g;++b)for(int c=0;c<b;++c)sat.clause(-selectors[g][1][b],-selectors[g+1][1][c]);
        for(int b=0;b<inputs+g;++b)for(int a=0;a<=b;++a)for(int c=0;c<a;++c)
          sat.clause(-selectors[g][1][b],-selectors[g+1][1][b],-selectors[g][0][a],-selectors[g+1][0][c]);
      }
    }
  }
  void addrow(int x){
    std::vector<int> values;for(int i=0;i<inputs;++i)values.push_back((x&(1<<i))?-zero:zero);
    for(int g=0;g<count;++g){
      int a=fresh(),b=fresh(),c=fresh(),v[2]={a,b};
      for(int k=0;k<2;++k)for(int s=0;s<inputs+g;++s){int q=selectors[g][k][s],u=v[k],w=values[s];
        sat.clause(-q,-u,w);sat.clause(-q,u,-w);}
      int o=isOr[g];
      sat.clause(o,-c,a);sat.clause(o,-c,b);sat.clause(o,c,-a,-b);
      sat.clause(-o,c,-a);sat.clause(-o,c,-b);sat.clause(-o,-c,a,b);
      values.push_back(c);
    }
    sat.clause(target(x)?values.back():-values.back());
    matrix.push_back(values);rowTargets.push_back(target(x));
  }
  void addDominanceNormalForm(int protectedPrefix){
    std::vector<int> padding(count);for(int&v:padding)v=fresh();
    sat.clause(-padding[0]);
    for(int g=0;g<count;++g){
      if(g+1<count)sat.clause(-padding[g],padding[g+1]);
      if(g){sat.clause(-padding[g],-isOr[g]);
        for(int k=0;k<2;++k)sat.clause(-padding[g],selectors[g][k][inputs+g-1]);}
      if(g<protectedPrefix){sat.clause(-padding[g]);continue;}
      std::vector<int> hasPositive={padding[g]},hasNegative={padding[g]};
      for(size_t r=0;r<matrix.size();++r){int v=matrix[r][inputs+g];
        if(rowTargets[r])hasPositive.push_back(v);else hasNegative.push_back(-v);}
      sat.clause(hasPositive);sat.clause(hasNegative);
      for(int h=0;h<inputs+g;++h){
        std::vector<int> better={padding[g]};
        for(size_t r=0;r<matrix.size();++r){
          int gval=matrix[r][inputs+g],hval=matrix[r][h];
          int goodG=rowTargets[r]?gval:-gval, badH=rowTargets[r]?-hval:hval;
          if(badH==zero)continue;
          if(badH==-zero){better.push_back(goodG);continue;}
          int d=fresh();sat.clause(-d,goodG);sat.clause(-d,badH);better.push_back(d);
        }
        sat.clause(better);
      }
    }
  }
  std::vector<Gate> model(){
    std::vector<Gate> out;
    for(int g=0;g<count;++g){Gate z{sat.val(isOr[g])>0,-1,-1};
      for(int s=0;s<inputs+g;++s){if(sat.val(selectors[g][0][s])>0)z.a=s;if(sat.val(selectors[g][1][s])>0)z.b=s;}
      out.push_back(z);}
    return out;
  }
};
bool eval(const std::vector<Gate>&gs,int inputs,int x){
  bool values[256];for(int i=0;i<inputs;++i)values[i]=x&(1<<i);
  for(size_t g=0;g<gs.size();++g){auto z=gs[g];values[inputs+g]=z.op?(values[z.a]||values[z.b]):(values[z.a]&&values[z.b]);}
  return values[inputs+gs.size()-1];
}
bool readOneOnPair(const std::vector<Gate>&gs,int inputs,int point,int line){
  unsigned vectors[256]={};vectors[point]=1u<<3;vectors[line]=1u<<1;
  for(size_t g=0;g<gs.size();++g){auto z=gs[g];unsigned result=0;
    if(z.op)result=vectors[z.a]|vectors[z.b];
    else for(int a=0;a<9;++a)if(vectors[z.a]&(1u<<a))for(int b=0;b<9;++b)if(vectors[z.b]&(1u<<b)){
      int p=std::min(2,a/3+b/3),l=std::min(2,a%3+b%3);result|=1u<<(3*p+l);}
    vectors[inputs+g]=result;
  }
  return vectors[inputs+gs.size()-1]&(1u<<4);
}
int main(int argc,char**argv){
  if(argc<5){std::cerr<<"usage: graph gate-count seconds seed [pins-or-none] [ordered-or-none] [dominance] [protected-prefix]\n";return 2;}
  int n=std::atoi(argv[2]),duration=std::atoi(argv[3]),seed=std::atoi(argv[4]);
  int protectedPrefix=argc>8?std::atoi(argv[8]):0;
  Problem p(argv[1],n,seed,argc>6&&std::string(argv[6])=="ordered",protectedPrefix);
  if(argc>5&&std::string(argv[5])!="none"){
    std::ifstream f(argv[5]);
    for(int g=0;g<n;++g){int op,a,b;if(!(f>>op>>a>>b))break;if(a>b)std::swap(a,b);
      p.sat.clause(op?p.isOr[g]:-p.isOr[g]);p.sat.clause(p.selectors[g][0][a]);p.sat.clause(p.selectors[g][1][b]);}
  }
  int rows=0;
  for(int x=0;x<(1<<p.inputs);++x){
    bool maximal=!p.target(x);
    if(maximal)for(int i=0;i<p.inputs;++i)if(!(x&(1<<i))&&!p.target(x|(1<<i)))maximal=false;
    if(maximal||(__builtin_popcount(unsigned(x))==2&&p.target(x))){p.addrow(x);++rows;}
  }
  if(argc>7&&std::string(argv[7])=="dominance")p.addDominanceNormalForm(protectedPrefix);
  std::cout<<"extremal rows "<<rows<<" variables "<<p.nv<<"\n"<<std::flush;
  auto start=std::chrono::steady_clock::now();int round=0;
  while(true){
    int elapsed=std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now()-start).count();
    if(elapsed>duration){std::cout<<"TIME LIMIT, inconclusive\n"<<std::flush;return 0;}
    std::cout<<"round "<<round++<<" elapsed "<<elapsed<<"\n"<<std::flush;
    p.sat.limit("conflicts",100000);int result=p.sat.solve();
    if(!result){std::cout<<"conflict budget, continuing\n"<<std::flush;continue;}
    if(result==20){std::cout<<"UNSAT for encoded AO2 class\n"<<std::flush;return 20;}
    auto gs=p.model();int bad=0;
    for(int x=0;x<(1<<p.inputs);++x)if(eval(gs,p.inputs,x)!=p.target(x))++bad;
    std::cout<<"SAT full truth-table mismatches "<<bad<<"\n";
    for(auto z:gs)std::cout<<(z.op?"OR ":"AND ")<<z.a<<" "<<z.b<<"\n";
    int reads=0;for(auto [a,b]:p.edges)if(readOneOnPair(gs,p.inputs,a,b))++reads;
    std::cout<<"read1 incident pairs "<<reads<<" / "<<p.edges.size()<<"\n"<<std::flush;
    return bad?3:10;
  }
}
