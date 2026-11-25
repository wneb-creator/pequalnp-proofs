#include <cadical.hpp>
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdlib>
#include <functional>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <vector>

using namespace std;
const vector<pair<int,int>> edges = {{0,1},{1,2},{2,3},{3,4},{4,0},
  {0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
bool target(int x) { for (auto [a,b]:edges) if ((x>>a&1)&&(x>>b&1)) return true; return false; }
struct Timer : CaDiCaL::Terminator {
  chrono::steady_clock::time_point end;
  explicit Timer(int sec):end(chrono::steady_clock::now()+chrono::seconds(sec)){}
  bool terminate() override { return chrono::steady_clock::now()>=end; }
};
struct Gate { int op,a,b; };
struct Encoder {
  CaDiCaL::Solver solver;
  int n,vars=0; long long clauses=0;
  vector<array<int,3>> op;
  vector<vector<int>> a,b;
  set<int> rows;
  int fresh() { return ++vars; }
  void clause(vector<int> c) { for(int l:c) solver.add(l); solver.add(0); ++clauses; }
  void onehot(const vector<int>& x) { clause(x); for(size_t i=0;i<x.size();i++) for(size_t j=i+1;j<x.size();j++) clause({-x[i],-x[j]}); }
  Encoder(int count,int lo,int hi,int first,int seed,bool ordered):n(count),op(n),a(n),b(n) {
    solver.set("quiet",1); solver.set("seed",seed);
    for(int i=0;i<n;i++) {
      for(int j=0;j<3;j++) op[i][j]=fresh();
      onehot({op[i][0],op[i][1],op[i][2]});
      for(int j=0;j<10+i;j++) { a[i].push_back(fresh()); b[i].push_back(fresh()); }
      onehot(a[i]); onehot(b[i]);
      for(int j=0;j<10+i;j++) for(int k=0;k<10+i;k++) {
        if(j>k) clause({-a[i][j],-b[i][k]});
        if(j==k) clause({-a[i][j],-b[i][k],op[i][2]});
        else clause({-a[i][j],-b[i][k],-op[i][2]});
      }
      if(ordered && i) {
        for(int j=0;j<9+i;j++) for(int k=j+1;k<9+i;k++) clause({-b[i][j],-b[i-1][k]});
      }
    }
    // Exact unary/binary gate budget: dynamic programming count encoding.
    vector<vector<int>> d(n+1,vector<int>(n+1));
    for(auto& row:d) for(int& v:row) v=fresh();
    clause({d[0][0]}); for(int j=1;j<=n;j++) clause({-d[0][j]});
    for(int i=1;i<=n;i++) {
      for(int j=0;j<=n;j++) {
        int now=d[i][j], prev=d[i-1][j], t=op[i-1][2];
        // If t=false now=prev; if t=true now=previous count j-1.
        clause({t,-now,prev}); clause({t,now,-prev});
        if(j==0) clause({-t,-now});
        else { int less=d[i-1][j-1]; clause({-t,-now,less}); clause({-t,now,-less}); }
      }
    }
    vector<int> allowed; for(int j=lo;j<=hi;j++) allowed.push_back(d[n][j]); clause(allowed);
    // Search only connected reduced programs. This is a search restriction,
    // not claimed as a complete encoding of every circuit in the Lean model.
    for(int i=0;i<n-1;i++) {
      vector<int> used;
      for(int j=i+1;j<n;j++) { used.push_back(a[j][10+i]); used.push_back(b[j][10+i]); }
      clause(used);
    }
    if(first>=0) {
      if(first==4) { clause({op[0][2]}); clause({a[0][0]}); clause({b[0][0]}); }
      else { clause({op[0][first/2]}); clause({a[0][0]}); clause({b[0][first%2?2:1]}); }
    }
  }
  void row(int mask) {
    if(!rows.insert(mask).second) return;
    vector<int> w(10+n);
    for(int& x:w) x=fresh();
    for(int i=0;i<10;i++) clause({(mask>>i&1)?w[i]:-w[i]});
    for(int i=0;i<n;i++) {
      int x=fresh(),y=fresh(),z=w[10+i];
      for(int j=0;j<10+i;j++) {
        clause({-a[i][j],-x,w[j]}); clause({-a[i][j],x,-w[j]});
        clause({-b[i][j],-y,w[j]}); clause({-b[i][j],y,-w[j]});
      }
      int an=op[i][0], o=op[i][1], nt=op[i][2];
      clause({-an,-z,x}); clause({-an,-z,y}); clause({-an,z,-x,-y});
      clause({-o,z,-x}); clause({-o,z,-y}); clause({-o,-z,x,y});
      clause({-nt,-z,-x}); clause({-nt,z,x});
    }
    clause({target(mask)?w.back():-w.back()});
  }
  vector<Gate> model() {
    vector<Gate> gs;
    for(int i=0;i<n;i++) {
      Gate g{-1,-1,-1};
      for(int j=0;j<3;j++) if(solver.val(op[i][j])>0) g.op=j;
      for(int j=0;j<10+i;j++) { if(solver.val(a[i][j])>0) g.a=j; if(solver.val(b[i][j])>0) g.b=j; }
      gs.push_back(g);
    }
    return gs;
  }
};
bool eval(const vector<Gate>& gs,int mask) {
  vector<bool> w;
  for(int i=0;i<10;i++) w.push_back(mask>>i&1);
  for(auto g:gs) w.push_back(g.op==0?(w[g.a]&&w[g.b]):g.op==1?(w[g.a]||w[g.b]):!w[g.a]);
  return w.back();
}
vector<Gate> known_twenty() {
  int cover=-1;
  for(int m=0;m<1024;m++) if(__builtin_popcount((unsigned)m)==6) {
    bool ok=true; for(auto [a,b]:edges) if(!(m>>a&1)&&!(m>>b&1)) ok=false;
    if(ok) { cover=m; break; }
  }
  vector<vector<int>> ns(10);
  for(auto [a,b]:edges) { if(cover>>a&1) ns[a].push_back(b); else ns[b].push_back(a); }
  vector<Gate> gs; vector<int> terms;
  auto add=[&](int op,int a,int b){ if(a>b) swap(a,b); gs.push_back({op,a,b}); return 9+(int)gs.size(); };
  for(int i=0;i<10;i++) if(!ns[i].empty()) {
    int acc=ns[i][0]; for(int j=1;j<(int)ns[i].size();j++) acc=add(1,acc,ns[i][j]);
    terms.push_back(add(0,i,acc));
  }
  int acc=terms[0]; for(int j=1;j<(int)terms.size();j++) acc=add(1,acc,terms[j]);
  return gs;
}
int main(int argc,char**argv) {
  if(argc==6 && string(argv[1])=="local") {
    ifstream in(argv[2]); string line,word; getline(in,line);
    vector<Gate> base;
    for(int i=0;i<19;i++) {
      int index,a,b; in>>index>>word>>a>>b;
      int op=word=="and"?0:word=="or"?1:2;
      if(op==2) b=a; else if(a>b) swap(a,b);
      if(!in || index!=10+i || a>=10+i || b>=10+i) return 2;
      base.push_back({op,a,b});
    }
    int seconds=stoi(argv[3]),seed=stoi(argv[4]),freecount=stoi(argv[5]);
    Timer timer(seconds); Encoder e(19,1,4,-1,seed,false);
    e.solver.connect_terminator(&timer);
    for(int x=0;x<1024;x++) e.row(x);
    for(int i=0;i<19;i++) {
      e.solver.phase(e.op[i][base[i].op]);
      e.solver.phase(e.a[i][base[i].a]); e.solver.phase(e.b[i][base[i].b]);
    }
    mt19937 rng(seed); vector<int> positions(19); iota(positions.begin(),positions.end(),0);
    int unsats=0,unknowns=0;
    for(int trial=0;!timer.terminate();trial++) {
      shuffle(positions.begin(),positions.end(),rng);
      set<int> freed(positions.begin(),positions.begin()+freecount);
      for(int i=0;i<19;i++) if(!freed.count(i)) {
        e.solver.assume(e.op[i][base[i].op]);
        e.solver.assume(e.a[i][base[i].a]); e.solver.assume(e.b[i][base[i].b]);
      }
      e.solver.limit("conflicts",3000);
      int status=e.solver.solve();
      if(status==20) ++unsats; else if(status==0) ++unknowns;
      else {
        auto gs=e.model(); int bad=0;
        for(int x=0;x<1024;x++) if(eval(gs,x)!=target(x)) ++bad;
        cout<<"LOCAL SAT trial="<<trial<<" mismatches="<<bad<<endl;
        for(int i=0;i<19;i++) cout<<10+i<<" "<<gs[i].op<<" "<<gs[i].a<<" "<<gs[i].b<<"\n";
        cout<<flush; return bad?3:10;
      }
      if(trial%100==0) cout<<"local trial="<<trial<<" unsats="<<unsats<<" unknowns="<<unknowns<<endl;
    }
    cout<<"LOCAL FINISHED unsats="<<unsats<<" unknowns="<<unknowns<<endl; return 0;
  }
  if(argc==2 && string(argv[1])=="selftest") {
    auto gs=known_twenty();
    if(gs.size()!=20) return 2;
    for(int x=0;x<1024;x++) if(eval(gs,x)!=target(x)) return 3;
    for(int corrupt=0;corrupt<=1;corrupt++) {
      Encoder e(20,0,0,-1,0,false);
      for(int x=0;x<1024;x++) e.row(x);
      for(int i=0;i<20;i++) {
        e.clause({e.op[i][(i==19&&corrupt)?0:gs[i].op]});
        e.clause({e.a[i][gs[i].a]}); e.clause({e.b[i][gs[i].b]});
      }
      int status=e.solver.solve();
      cout<<"selftest corrupt="<<corrupt<<" status="<<status<<endl;
      if(status!=(corrupt?20:10)) return 4;
    }
    cout<<"SELFTEST PASS full1024 known20 and corrupted20\n"; return 0;
  }
  if(argc<7) { cerr<<"usage: sat_search GATES MIN_NOT MAX_NOT FIRST_CASE SECONDS SEED [ORDERED] [ALL_ROWS]\n"; return 2; }
  int n=stoi(argv[1]),lo=stoi(argv[2]),hi=stoi(argv[3]),first=stoi(argv[4]),sec=stoi(argv[5]),seed=stoi(argv[6]);
  bool ordered=argc>7?stoi(argv[7]):true, all=argc>8?stoi(argv[8]):false;
  Timer timer(sec); Encoder e(n,lo,hi,first,seed,ordered); e.solver.connect_terminator(&timer);
  for(int x=0;x<1024;x++) if(all||__builtin_popcount((unsigned)x)<=2) e.row(x);
  // Add the true all-ones and all-but-one rows early; these constrain negative phases.
  e.row(1023); for(int i=0;i<10;i++) e.row(1023^(1<<i));
  for(int round=0;round<1024;round++) {
    cout<<"solve round="<<round<<" rows="<<e.rows.size()<<" vars="<<e.vars<<" clauses="<<e.clauses<<endl;
    int status=e.solver.solve(); cout<<"status="<<status<<endl;
    if(status!=10) { e.solver.statistics(); return status==20?20:0; }
    auto gs=e.model(); vector<int> bad;
    for(int x=0;x<1024;x++) if(eval(gs,x)!=target(x)) bad.push_back(x);
    cout<<"candidate mismatches="<<bad.size()<<endl;
    for(int i=0;i<n;i++) cout<<10+i<<" "<<gs[i].op<<" "<<gs[i].a<<" "<<gs[i].b<<"\n";
    cout<<flush;
    if(bad.empty()) { cout<<"WITNESS all1024 rows passed\n"; return 10; }
    for(int j=0;j<(int)bad.size();j+=max(1,(int)bad.size()/16)) e.row(bad[j]);
  }
}
