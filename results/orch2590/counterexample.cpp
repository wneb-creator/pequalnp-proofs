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
  std::vector<int> padding;
  std::vector<std::vector<int>> singleProof,pairProof;
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
    padding.resize(count);for(int&v:padding)v=fresh();
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
  int selectedProof(int g,int k,const std::vector<std::vector<int>>&flags,int column){
    int value=fresh();
    for(int s=0;s<inputs+g;++s){int q=selectors[g][k][s],w=flags[s][column];
      sat.clause(-q,-value,w);sat.clause(-q,value,-w);}
    return value;
  }
  int conjunction(int a,int b){
    int c=fresh();sat.clause(-c,a);sat.clause(-c,b);sat.clause(c,-a,-b);return c;
  }
  void addReadOne(bool requireReadOne){
    for(int s=0;s<inputs;++s){
      std::vector<int> singles(inputs,zero);singles[s]=-zero;singleProof.push_back(singles);
      pairProof.push_back(std::vector<int>(edges.size(),zero));
    }
    for(int g=0;g<count;++g){
      std::vector<int> singles,pairs;std::array<std::vector<int>,2> selectedSingles;
      int o=isOr[g];
      for(int v=0;v<inputs;++v){
        int a=selectedProof(g,0,singleProof,v),b=selectedProof(g,1,singleProof,v),c=fresh();
        selectedSingles[0].push_back(a);selectedSingles[1].push_back(b);
        sat.clause(-c,o);sat.clause(-c,a,b);sat.clause(-o,-a,c);sat.clause(-o,-b,c);
        singles.push_back(c);
      }
      for(size_t e=0;e<edges.size();++e){
        auto [u,v]=edges[e];
        int a=selectedProof(g,0,pairProof,e),b=selectedProof(g,1,pairProof,e),c=fresh();
        int ab=conjunction(selectedSingles[0][u],selectedSingles[1][v]);
        int ba=conjunction(selectedSingles[0][v],selectedSingles[1][u]);
        sat.clause(-o,-c,a,b);sat.clause(-o,-a,c);sat.clause(-o,-b,c);
        sat.clause(o,-c,ab,ba);sat.clause(o,-ab,c);sat.clause(o,-ba,c);
        pairs.push_back(c);
      }
      singleProof.push_back(singles);pairProof.push_back(pairs);
    }
    for(int g=0;g<count;++g){
      std::vector<int> inactive;
      if(!padding.empty()){
        inactive.push_back(padding[g]);
        if(g+1<count)inactive.push_back(-padding[g+1]);
      }else if(g+1<count)continue;
      if(requireReadOne){
        for(int p:pairProof[inputs+g]){auto c=inactive;c.push_back(p);sat.clause(c);}
      }else{
        for(int p:pairProof[inputs+g])inactive.push_back(-p);
        sat.clause(inactive);
      }
    }
  }
  void atMost(const std::vector<int>&literals,int cap){
    if(cap<0){sat.clause(std::vector<int>{});return;}
    if(cap>=int(literals.size()))return;
    std::vector<int> prev(cap+2,zero);prev[0]=-zero;
    for(int e:literals){
      std::vector<int> next(cap+2);next[0]=-zero;
      for(int j=1;j<=cap+1;++j){next[j]=fresh();
        sat.clause(-prev[j],next[j]);sat.clause(-e,-prev[j-1],next[j]);}
      prev=next;
    }
    sat.clause(-prev[cap+1]);
  }
  void addFalseCut(int fixedMask,int lower){
      std::vector<int> cf(inputs,zero);
      for(int i=0;i<inputs;++i)if(fixedMask&(1<<i))cf[i]=-zero;
      std::vector<int> eliminated;
      for(int g=0;g<count;++g){
        int a=fresh(),b=fresh(),c=fresh(),loss=fresh(),v[2]={a,b};
        for(int k=0;k<2;++k)for(int s=0;s<inputs+g;++s){int q=selectors[g][k][s],w=cf[s];
          sat.clause(-q,-v[k],w);sat.clause(-q,v[k],-w);}
        // Constant-false propagates by OR through AND, and AND through OR.
        int o=-isOr[g];
        sat.clause(o,-c,a);sat.clause(o,-c,b);sat.clause(o,c,-a,-b);
        sat.clause(-o,c,-a);sat.clause(-o,c,-b);sat.clause(-o,-c,a,b);
        // An OR with one false input aliases its other input and also vanishes.
        sat.clause(-a,loss);sat.clause(-b,loss);sat.clause(-loss,a,b);
        cf.push_back(c);eliminated.push_back(loss);
      }
      atMost(eliminated,count-lower);
  }
  void addSingletonFalseCuts(int lower){
    for(int fixed=0;fixed<inputs;++fixed)addFalseCut(1<<fixed,lower);
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
  if(argc<5){std::cerr<<"usage: graph gate-count seconds seed [pins-or-none] [ordered-or-none] [dominance] [protected-prefix] [petersen-or-none] [read1-or-nonread1]\n";return 2;}
  int n=std::atoi(argv[2]),duration=std::atoi(argv[3]),seed=std::atoi(argv[4]);
  int protectedPrefix=argc>8?std::atoi(argv[8]):0;
  Problem p(argv[1],n,seed,argc>6&&std::string(argv[6])=="ordered",protectedPrefix);
  if(argc>9&&std::string(argv[9])=="petersen"){
    p.sat.clause(p.selectors[0][0][0]);
    p.sat.clause(p.selectors[0][1][1],p.selectors[0][1][2]);
  }
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
  if(argc>10){std::string readMode=argv[10];
    if(readMode=="read1"||readMode=="nonread1")p.addReadOne(readMode=="read1");}
  if(argc>11&&std::string(argv[11])=="cofactor16")p.addSingletonFalseCuts(16);
  else if(argc>11&&std::string(argv[11])!="none"){
    std::ifstream f(argv[11]);int mask,lower;
    while(f>>mask>>lower)p.addFalseCut(mask,lower);
  }
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
    std::cout<<"output "<<p.inputs+int(gs.size())-1<<"\n";
    int reads=0;for(auto [a,b]:p.edges)if(readOneOnPair(gs,p.inputs,a,b))++reads;
    std::cout<<"read1 incident pairs "<<reads<<" / "<<p.edges.size()<<"\n"<<std::flush;
    if(!p.pairProof.empty()){
      int last=n-1;while(last>0&&!p.padding.empty()&&p.sat.val(p.padding[last])>0)--last;
      int encoded=0;for(int q:p.pairProof[p.inputs+last])if(p.sat.val(q)>0)++encoded;
      auto active=gs;active.resize(last+1);int checked=0;
      for(auto [a,b]:p.edges)if(readOneOnPair(active,p.inputs,a,b))++checked;
      std::cout<<"active prefix gates "<<last+1<<" encoded read1 "<<encoded<<" checked read1 "<<checked<<"\n"<<std::flush;
      if(encoded!=checked)return 4;
    }
    return bad?3:10;
  }
}
