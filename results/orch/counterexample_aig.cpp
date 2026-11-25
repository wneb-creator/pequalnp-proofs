#include "cadical.hpp"
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <string>
#include <vector>

struct Node { int a,b,pa,pb; };
static const std::array<std::pair<int,int>,15> edges={{{0,1},{1,2},{2,3},{3,4},{4,0},
  {0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
bool target(int x) {
  for(auto [a,b]:edges)if((x&(1<<a))&&(x&(1<<b)))return true;
  return false;
}
struct Problem {
  CaDiCaL::Solver sat;
  int n,nv=0,zero,finalPhase;
  std::vector<std::array<std::vector<int>,2>> sel;
  std::vector<std::array<int,2>> phase;
  std::array<bool,1024> rows{};
  int fresh(){return ++nv;}
  void onehot(const std::vector<int>&v){
    sat.clause(v);
    for(size_t i=0;i<v.size();++i)for(size_t j=0;j<i;++j)sat.clause(-v[i],-v[j]);
  }
  Problem(int count,int seed):n(count),sel(n),phase(n){
    sat.set("quiet",1);sat.set("seed",seed);zero=fresh();sat.clause(-zero);finalPhase=fresh();
    for(int g=0;g<n;++g){
      for(int k=0;k<2;++k){
        phase[g][k]=fresh();
        for(int a=0;a<11+g;++a)sel[g][k].push_back(fresh());
        onehot(sel[g][k]);
      }
      for(int a=0;a<11+g;++a)for(int b=0;b<a;++b)sat.clause(-sel[g][0][a],-sel[g][1][b]);
    }
    // Remove disconnected topology: unused capacity can instead be padded by
    // an output-copy AND gate, so this keeps every at-most-n witness representable.
    for(int g=0;g+1<n;++g){
      std::vector<int> used;
      for(int h=g+1;h<n;++h)for(int k=0;k<2;++k)used.push_back(sel[h][k][11+g]);
      sat.clause(used);
    }
  }
  void addrow(int x){
    if(rows[x])return;rows[x]=true;
    std::vector<int> v;
    for(int i=0;i<10;++i)v.push_back((x&(1<<i))?-zero:zero);
    v.push_back(zero);
    for(int g=0;g<n;++g){
      int a=fresh(),b=fresh(),c=fresh();int u[2]={a,b};
      for(int k=0;k<2;++k)for(int src=0;src<11+g;++src){
        int s=sel[g][k][src],t=v[src],p=phase[g][k],z=u[k];
        sat.clause(-s,t,p,-z);sat.clause(-s,t,-p,z);
        sat.clause(-s,-t,p,z);sat.clause(-s,-t,-p,-z);
      }
      sat.clause(-c,a);sat.clause(-c,b);sat.clause(c,-a,-b);v.push_back(c);
    }
    if(target(x)){sat.clause(v.back(),finalPhase);sat.clause(-v.back(),-finalPhase);}
    else{sat.clause(v.back(),-finalPhase);sat.clause(-v.back(),finalPhase);}
  }
  void atMost(const std::vector<int>& literals,int cap){
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
  void addCut(int fixed,int assignment,int lower){
    std::vector<std::array<int,2>> status;
    for(int i=0;i<10;++i){
      if(!(fixed&(1<<i)))status.push_back({zero,zero});
      else if(assignment&(1<<i))status.push_back({zero,-zero});
      else status.push_back({-zero,zero});
    }
    status.push_back({-zero,zero});
    std::vector<int> eliminated;
    for(int g=0;g<n;++g){
      int known[2][2]={{fresh(),fresh()},{fresh(),fresh()}};
      int cf=fresh(),ct=fresh(),loss=fresh();
      for(int k=0;k<2;++k)for(int src=0;src<11+g;++src)for(int bit=0;bit<2;++bit){
        int s=sel[g][k][src],p=phase[g][k],v=known[k][bit];
        int ordinary=status[src][bit],flipped=status[src][1-bit];
        sat.clause(-s,p,-v,ordinary);sat.clause(-s,p,v,-ordinary);
        sat.clause(-s,-p,-v,flipped);sat.clause(-s,-p,v,-flipped);
      }
      int af=known[0][0],at=known[0][1],bf=known[1][0],bt=known[1][1];
      sat.clause(-af,cf);sat.clause(-bf,cf);sat.clause(-cf,af,bf);
      sat.clause(-ct,at);sat.clause(-ct,bt);sat.clause(ct,-at,-bt);
      sat.clause(-cf,-ct);
      for(int v:{af,at,bf,bt})sat.clause(-v,loss);
      sat.clause(-loss,af,at,bf,bt);
      status.push_back({cf,ct});eliminated.push_back(loss);
    }
    atMost(eliminated,n-lower);
  }
  std::vector<Node> model(){
    std::vector<Node> v;
    for(int g=0;g<n;++g){
      Node z{-1,-1,sat.val(phase[g][0])>0,sat.val(phase[g][1])>0};
      for(int a=0;a<11+g;++a){if(sat.val(sel[g][0][a])>0)z.a=a;if(sat.val(sel[g][1][a])>0)z.b=a;}
      v.push_back(z);
    }return v;
  }
};
bool evaluate(const std::vector<Node>&gs,int inv,int x){
  bool v[64];for(int i=0;i<10;++i)v[i]=x&(1<<i);v[10]=false;
  for(size_t g=0;g<gs.size();++g){auto z=gs[g];v[11+g]=(v[z.a]^bool(z.pa))&&(v[z.b]^bool(z.pb));}
  return v[10+gs.size()]^bool(inv);
}
std::pair<int,unsigned> optimize(const std::vector<Node>&gs,int inv){
  int n=gs.size(),best=99;unsigned bm=0;
  for(unsigned m=0;m<(1u<<n);++m){
    unsigned long long need=0;
    for(int g=0;g<n;++g){
      auto z=gs[g];int pg=(m>>g)&1;
      int pa=z.a<11?0:(m>>(z.a-11))&1;
      int pb=z.b<11?0:(m>>(z.b-11))&1;
      if(pa^pg^z.pa)need|=1ull<<z.a;
      if(pb^pg^z.pb)need|=1ull<<z.b;
    }
    if(int((m>>(n-1))&1)!=inv)need|=1ull<<(10+n);
    int score=__builtin_popcountll(need);
    if(score<best){best=score;bm=m;}
  }return {best,bm};
}
void emit(const std::vector<Node>&gs,int inv,unsigned m){
  int n=gs.size();unsigned long long need=0;
  for(int g=0;g<n;++g){
    auto z=gs[g];int pg=(m>>g)&1;
    int pa=z.a<11?0:(m>>(z.a-11))&1,pb=z.b<11?0:(m>>(z.b-11))&1;
    if(pa^pg^z.pa)need|=1ull<<z.a;
    if(pb^pg^z.pb)need|=1ull<<z.b;
  }
  if(int((m>>(n-1))&1)!=inv)need|=1ull<<(10+n);
  int base[64],neg[64],next=10;
  for(int i=0;i<11;++i){base[i]=i==10?1000000:i;if(need&(1ull<<i)){neg[i]=next++;std::cout<<"NOT "<<base[i]<<"\n";}}
  for(int g=0;g<n;++g){
    auto z=gs[g];int pg=(m>>g)&1;
    int pa=z.a<11?0:(m>>(z.a-11))&1,pb=z.b<11?0:(m>>(z.b-11))&1;
    int a=(pa^pg^z.pa)?neg[z.a]:base[z.a],b=(pb^pg^z.pb)?neg[z.b]:base[z.b];
    base[11+g]=next++;std::cout<<(pg?"OR ":"AND ")<<a<<" "<<b<<"\n";
    if(need&(1ull<<(11+g))){neg[11+g]=next++;std::cout<<"NOT "<<base[11+g]<<"\n";}
  }
  int out=(inv^int((m>>(n-1))&1))?neg[10+n]:base[10+n];
  if(!need){++next;std::cout<<"NOT 1000000\n";}
  std::cout<<"OUTPUT "<<out<<" SIZE "<<next-10<<"\n";
}
int main(int argc,char**argv){
  int n=argc>1?std::atoi(argv[1]):18,duration=argc>2?std::atoi(argv[2]):1200,seed=argc>3?std::atoi(argv[3]):108;
  Problem p(n,seed);
  if(argc>4){
    std::ifstream f(argv[4]);int inv;
    if(f>>inv)p.sat.clause(inv?p.finalPhase:-p.finalPhase);
    for(int g=0;g<n;++g){int a,b,pa,pb;if(!(f>>a>>b>>pa>>pb))break;if(a>b){std::swap(a,b);std::swap(pa,pb);}
      p.sat.clause(p.sel[g][0][a]);p.sat.clause(p.sel[g][1][b]);
      p.sat.clause(pa?p.phase[g][0]:-p.phase[g][0]);p.sat.clause(pb?p.phase[g][1]:-p.phase[g][1]);}
  }
  if(argc>5 && std::string(argv[5])!="none"){
    int budget=std::atoi(argv[5]);
    std::vector<int> orient(n),negative(n+11);
    for(int&v:orient)v=p.fresh();for(int&v:negative)v=p.fresh();
    for(int g=0;g<n;++g)for(int k=0;k<2;++k)for(int src=0;src<11+g;++src){
      int e=p.phase[g][k],a=orient[g],b=src<11?p.zero:orient[src-11];
      for(int eb=0;eb<2;++eb)for(int ab=0;ab<2;++ab)for(int bb=0;bb<2;++bb)
        if(eb^ab^bb)p.sat.clause(-p.sel[g][k][src],negative[src],eb?-e:e,ab?-a:a,bb?-b:b);
    }
    p.sat.clause(negative.back(),-p.finalPhase,orient.back());
    p.sat.clause(negative.back(),p.finalPhase,-orient.back());
    std::vector<int> selected;
    std::function<void(int,int)> subsets=[&](int start,int left){
      if(!left){p.sat.clause(selected);return;}
      for(int i=start;i<=int(negative.size())-left;++i){selected.push_back(-negative[i]);subsets(i+1,left-1);selected.pop_back();}
    };
    subsets(0,budget+1);
  }
  if(argc>6 && std::string(argv[6])!="none"){
    int partner=std::atoi(argv[6]);
    p.sat.clause(p.sel[0][0][0]);p.sat.clause(p.sel[0][1][partner]);
    for(int g=0;g<n;++g)for(int k=0;k<2;++k){
      p.sat.clause(-p.sel[g][k][0],p.phase[g][k]);
      p.sat.clause(-p.sel[g][k][partner],p.phase[g][k]);
    }
    for(int src: {0,partner}){
      std::vector<int> again;
      for(int g=1;g<n;++g)for(int k=0;k<2;++k)again.push_back(p.sel[g][k][src]);
      p.sat.clause(again);
    }
  }
  if(argc>7 && std::string(argv[7])!="none"){
    int cap=std::atoi(argv[7]);
    // These optional reader caps are used only for minimum signed circuits.
    // Such a circuit has no constant/identity binary nodes.
    for(int g=0;g<n;++g){
      p.sat.clause(-p.sel[g][0][10]);p.sat.clause(-p.sel[g][1][10]);
      for(int src=0;src<11+g;++src)p.sat.clause(-p.sel[g][0][src],-p.sel[g][1][src]);
    }
    if(argc>6 && std::string(argv[6])!="none"){int partner=std::atoi(argv[6]);
      for(int g=1;g<n;++g){
        p.sat.clause(-p.sel[g][0][0],-p.sel[g][1][partner]);
        p.sat.clause(-p.sel[g][0][0],-p.sel[g][1][11]);
        p.sat.clause(-p.sel[g][0][partner],-p.sel[g][1][11]);
      }
    }
    std::vector<std::array<int,10>> reads(n);
    for(int g=0;g<n;++g)for(int src=0;src<10;++src){
      int r=reads[g][src]=p.fresh();
      p.sat.clause(-p.sel[g][0][src],r);p.sat.clause(-p.sel[g][1][src],r);
      p.sat.clause(-r,p.sel[g][0][src],p.sel[g][1][src]);
    }
    for(int src=0;src<10;++src){
      std::vector<int> essential,selected;
      for(int g=0;g<n;++g)essential.push_back(reads[g][src]);p.sat.clause(essential);
      std::function<void(int,int)> subsets=[&](int start,int left){
        if(!left){p.sat.clause(selected);return;}
        for(int i=start;i<=n-left;++i){selected.push_back(-reads[i][src]);subsets(i+1,left-1);selected.pop_back();}
      };
      subsets(0,cap+1);
    }
  }
  if(argc>8){
    std::ifstream f(argv[8]);int fixed,value,lower,count=0;
    while(f>>fixed>>value>>lower){p.addCut(fixed,value,lower);++count;}
    std::cout<<"cofactor cuts "<<count<<"\n"<<std::flush;
  }
  if(argc>10 && std::string(argv[10])=="ordered17"){
    std::cout<<"canonical gate ordering and global primary-pair phases\n"<<std::flush;
    for(int g=0;g+1<n;++g){
      for(int b=0;b<11+g;++b)for(int c=0;c<b;++c)
        p.sat.clause(-p.sel[g][1][b],-p.sel[g+1][1][c]);
      for(int b=0;b<11+g;++b)for(int a=0;a<b;++a)for(int c=0;c<a;++c)
        p.sat.clause(-p.sel[g][1][b],-p.sel[g+1][1][b],-p.sel[g][0][a],-p.sel[g+1][0][c]);
    }
    std::array<int,10> touched;for(int&x:touched)x=p.fresh();
    std::vector<std::array<int,2>> primary(n);
    for(int g=0;g<n;++g)for(int k=0;k<2;++k){
      int x=primary[g][k]=p.fresh();std::vector<int> cover={-x};
      for(int src=0;src<10;++src){p.sat.clause(-p.sel[g][k][src],x);cover.push_back(p.sel[g][k][src]);}
      p.sat.clause(cover);
    }
    for(int src=0;src<10;++src)for(int g=0;g<n;++g)for(int k=0;k<2;++k){
      p.sat.clause(-p.sel[g][k][src],-primary[g][1-k],touched[src]);
      p.sat.clause(-touched[src],-p.sel[g][k][src],p.phase[g][k]);
      std::vector<int> again={-touched[src],-p.sel[g][k][src]};
      for(int h=0;h<n;++h)if(h!=g)for(int q=0;q<2;++q)again.push_back(p.sel[h][q][src]);
      p.sat.clause(again);
    }
  }
  for(int x=0;x<1024;++x){bool mx=!target(x);if(mx)for(int i=0;i<10;++i)if(!(x&(1<<i))&&!target(x|(1<<i)))mx=false;
    if(mx||(__builtin_popcount((unsigned)x)==2&&target(x))||x==0||x==1023)p.addrow(x);}
  if(argc>9){std::ifstream f(argv[9]);int row;while(f>>row)p.addrow(row);}
  auto start=std::chrono::steady_clock::now();int round=0;
  while(true){int elapsed=std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now()-start).count();
    if(elapsed>duration){std::cout<<"TIME LIMIT, inconclusive\n"<<std::flush;return 0;}
    std::cout<<"round "<<round++<<" elapsed "<<elapsed<<" vars "<<p.nv<<" rows "<<std::count(p.rows.begin(),p.rows.end(),true)<<"\n"<<std::flush;
    p.sat.limit("conflicts",100000);int r=p.sat.solve();
    if(!r){std::cout<<"conflict budget, continuing\n"<<std::flush;continue;}
    if(r==20){std::cout<<"UNSAT for encoded AIG class\n"<<std::flush;return 20;}
    auto gs=p.model();int inv=p.sat.val(p.finalPhase)>0;std::vector<int>bad;
    std::cout<<"CANDIDATE_AIG output_phase "<<inv<<"\n";
    for(auto z:gs)std::cout<<z.a<<" "<<z.b<<" "<<z.pa<<" "<<z.pb<<"\n";
    for(int x=0;x<1024;++x)if(evaluate(gs,inv,x)!=target(x))bad.push_back(x);
    std::cout<<"candidate mismatches "<<bad.size()<<"\n"<<std::flush;
    if(bad.empty()){auto [extra,m]=optimize(gs,inv);std::cout<<"AIG WITNESS nodes "<<n<<" minimum NOTs for topology "<<extra<<"\n";
      emit(gs,inv,m);std::cout<<std::flush;return 10;}
    // Refine with a spread of assignments, keeping the next SAT instance small.
    std::vector<int> chosen;
    while(!bad.empty()&&chosen.size()<32){
      size_t best=0;int score=-1;
      for(size_t i=0;i<bad.size();++i){int distance=11;
        for(int y:chosen)distance=std::min(distance,__builtin_popcount(unsigned(bad[i]^y)));
        if(distance>score){score=distance;best=i;}
      }
      chosen.push_back(bad[best]);bad.erase(bad.begin()+best);
    }
    for(int x:chosen)p.addrow(x);
  }
}
