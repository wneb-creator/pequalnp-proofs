#include <cadical.hpp>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Timer : CaDiCaL::Terminator {
  chrono::steady_clock::time_point end;
  explicit Timer(int sec):end(chrono::steady_clock::now()+chrono::seconds(sec)){}
  bool terminate() override { return chrono::steady_clock::now()>=end; }
};
struct Gate { int op,a,b; };
struct Problem {
  int n,left; vector<pair<int,int>> edges; vector<pair<uint64_t,bool>> rows;
  explicit Problem(const char* path) {
    ifstream in(path);int ne,nr;string header;getline(in,header);istringstream h(header);vector<int>head;int z;while(h>>z)head.push_back(z);
    if(head.size()==3){n=head[0];left=n/2;ne=head[1];nr=head[2];}
    else if(head.size()==4){n=head[0];left=head[1];ne=head[2];nr=head[3];}
    else throw runtime_error("invalid problem header");
    for(int i=0;i<ne;i++) {int a,b; in>>a>>b; edges.emplace_back(a,b);}
    for(int i=0;i<nr;i++) {uint64_t r;int b;in>>r>>b;rows.emplace_back(r,b);}
    if(!in) throw runtime_error("invalid problem file");
  }
  bool target(uint64_t r) const { for(auto[a,b]:edges) if((r>>a&1)&&(r>>b&1)) return true; return false; }
};
struct Encoder {
  CaDiCaL::Solver solver;
  int n,s,vars=0; long long clauses=0;
  vector<int> op; vector<vector<int>> a,b,muxA,muxB; set<uint64_t> rows;
  int fresh(){return ++vars;}
  void clause(const vector<int>& c){for(int x:c)solver.add(x);solver.add(0);++clauses;}
  void onehot(const vector<int>& c){clause(c);for(size_t i=0;i<c.size();i++)for(size_t j=i+1;j<c.size();j++)clause({-c[i],-c[j]});}
  Encoder(int nn,int ss,int seed,int firstcase,bool ordered):n(nn),s(ss),op(s),a(s),b(s),muxA(s),muxB(s){
    solver.set("quiet",1);solver.set("seed",seed);
    for(int i=0;i<s;i++){
      op[i]=fresh();
      for(int j=0;j<n+i;j++){a[i].push_back(fresh());b[i].push_back(fresh());}
      onehot(a[i]);onehot(b[i]);
      for(int j=0;j<n+i;j++)for(int k=0;k<=j;k++)clause({-a[i][j],-b[i][k]});
      if(ordered&&i)for(int j=0;j<n+i-1;j++)for(int k=j+1;k<n+i-1;k++)clause({-b[i][j],-b[i-1][k]});
    }
    for(int i=0;i<s-1;i++){
      vector<int> c;for(int j=i+1;j<s;j++){c.push_back(a[j][n+i]);c.push_back(b[j][n+i]);}clause(c);
    }
    // First-gate orbit choices are search restrictions; no completeness claimed.
    if(firstcase>=0){
      int source=firstcase%3==0?1:firstcase%3==1?14:13;
      clause({a[0][0]});clause({b[0][source]});clause({firstcase<3?op[0]:-op[0]});
    }
  }
  void row(uint64_t mask,bool target){
    if(!rows.insert(mask).second)return;
    vector<int>w(s);for(int&v:w)v=fresh();
    for(int i=0;i<s;i++){
      int x=fresh(),y=fresh(),z=w[i];
      muxA[i].push_back(x);muxB[i].push_back(y);
      for(int j=0;j<n+i;j++){
        if(j<n){clause({-a[i][j],(mask>>j&1)?x:-x});clause({-b[i][j],(mask>>j&1)?y:-y});}
        else {clause({-a[i][j],-x,w[j-n]});clause({-a[i][j],x,-w[j-n]});clause({-b[i][j],-y,w[j-n]});clause({-b[i][j],y,-w[j-n]});}
      }
      int o=op[i];
      clause({o,-z,x});clause({o,-z,y});clause({o,z,-x,-y});
      clause({-o,z,-x});clause({-o,z,-y});clause({-o,-z,x,y});
    }
    clause({target?w.back():-w.back()});
  }
  void incomparable(){
    for(int i=0;i<s;i++){
      vector<int>ab,ba;
      for(size_t j=0;j<muxA[i].size();j++){
        int x=muxA[i][j],y=muxB[i][j],u=fresh(),v=fresh();ab.push_back(u);ba.push_back(v);
        clause({-u,x});clause({-u,-y});clause({u,-x,y});
        clause({-v,-x});clause({-v,y});clause({v,x,-y});
      }
      clause(ab);clause(ba);
    }
  }
  void exact_and_count(int k){
    vector<vector<int>>d(s+1,vector<int>(k+2));for(auto&row:d)for(int&v:row)v=fresh();
    for(int i=0;i<=s;i++)clause({d[i][0]});
    for(int j=1;j<=k+1;j++)clause({-d[0][j]});
    for(int i=1;i<=s;i++)for(int j=1;j<=k+1;j++){
      int now=d[i][j],prev=d[i-1][j],less=d[i-1][j-1],o=op[i-1];
      clause({-now,prev,-o});clause({-now,prev,less});clause({-prev,now});clause({o,-less,now});
    }
    clause({d[s][k]});clause({-d[s][k+1]});
  }
  void not_read1_pair(int p,int q){
    vector<vector<int>>w(3,vector<int>(s));for(auto&v:w)for(int&x:v)x=fresh();
    for(int i=0;i<s;i++){
      int x[3],y[3];for(int k=0;k<3;k++){x[k]=fresh();y[k]=fresh();}
      for(int j=0;j<n+i;j++)for(int k=0;k<3;k++){
        if(j<n){bool value=k==0?j==p:k==1?j==q:false;clause({-a[i][j],value?x[k]:-x[k]});clause({-b[i][j],value?y[k]:-y[k]});}
        else{int z=w[k][j-n];clause({-a[i][j],-x[k],z});clause({-a[i][j],x[k],-z});clause({-b[i][j],-y[k],z});clause({-b[i][j],y[k],-z});}
      }
      for(int k=0;k<2;k++){
        int z=w[k][i];clause({-z,op[i]});clause({-z,x[k],y[k]});clause({z,-op[i],-x[k]});clause({z,-op[i],-y[k]});
      }
      int c=fresh(),d=fresh();
      clause({-c,x[0]});clause({-c,y[1]});clause({c,-x[0],-y[1]});
      clause({-d,x[1]});clause({-d,y[0]});clause({d,-x[1],-y[0]});
      int z=w[2][i],o=op[i];
      clause({-o,z,-x[2]});clause({-o,z,-y[2]});clause({-o,-z,x[2],y[2]});
      clause({o,z,-c});clause({o,z,-d});clause({o,-z,c,d});
    }
    clause({-w[2].back()});
  }
  vector<Gate> model(){
    vector<Gate>gs;
    for(int i=0;i<s;i++){
      Gate g{solver.val(op[i])>0?1:0,-1,-1};
      for(int j=0;j<n+i;j++){if(solver.val(a[i][j])>0)g.a=j;if(solver.val(b[i][j])>0)g.b=j;}gs.push_back(g);
    }return gs;
  }
};
bool evaluate(int n,const vector<Gate>&gs,uint64_t mask){
  vector<bool>w;for(int i=0;i<n;i++)w.push_back(mask>>i&1);
  for(auto g:gs)w.push_back(g.op?(w[g.a]||w[g.b]):(w[g.a]&&w[g.b]));return w.back();
}
int complete_boundary_errors(const Problem&p,const vector<Gate>&gs){
  int N=p.left,bad=0;
  for(auto[a,b]:p.edges)if(!evaluate(p.n,gs,(uint64_t(1)<<a)|(uint64_t(1)<<b)))++bad;
  for(uint64_t points=0;points<(uint64_t(1)<<N);points++){
    uint64_t mask=points;
    for(int l=N;l<p.n;l++){
      bool allowed=true;for(auto[a,b]:p.edges)if(b==l&&(points>>a&1))allowed=false;
      if(allowed)mask|=uint64_t(1)<<l;
    }
    if(evaluate(p.n,gs,mask))++bad;
  }
  return bad;
}
vector<Gate> star(const Problem&p){
  vector<Gate>gs;vector<int>terms;
  auto add=[&](int op,int a,int b){if(a>b)swap(a,b);gs.push_back({op,a,b});return p.n+(int)gs.size()-1;};
  for(int center=0;center<p.left;center++){
    vector<int>ns;for(auto[a,b]:p.edges)if(b==center)ns.push_back(a);else if(a==center)ns.push_back(b);
    int acc=ns.at(0);for(size_t j=1;j<ns.size();j++)acc=add(1,acc,ns[j]);terms.push_back(add(0,center,acc));
  }
  int acc=terms.at(0);for(size_t j=1;j<terms.size();j++)acc=add(1,acc,terms[j]);return gs;
}
int main(int argc,char**argv){
  if(argc<3){cerr<<"usage: sat_mono_2583 DATA selftest | DATA GATES SECONDS SEED FIRST_CASE [ORDERED] [INITIAL_FALSE_ROWS]\n";return 2;}
  Problem p(argv[1]);
  for(auto[r,v]:p.rows)if(v!=p.target(r))return 3;
  if(string(argv[2])=="local"){
    if(argc<7)return 2;
    ifstream in(argv[3]);string line;getline(in,line);vector<Gate>base;
    while(getline(in,line)){
      istringstream row(line);int wire,a,b;string op;
      if(!(row>>wire>>op>>a>>b))break;
      if(wire!=p.n+(int)base.size()||(op!="and"&&op!="or")||a>=wire||b>=wire)return 6;
      if(a>b)swap(a,b);base.push_back({op=="or"?1:0,a,b});
    }
    int seconds=stoi(argv[4]),seed=stoi(argv[5]),freecount=stoi(argv[6]);
    set<int>mandatory;vector<int>pool;
    auto parse=[](string arg){vector<int>v;replace(arg.begin(),arg.end(),',',' ');istringstream s(arg);int k;while(s>>k)v.push_back(k);return v;};
    if(argc>7)for(int k:parse(argv[7]))mandatory.insert(k);
    if(argc>8)pool=parse(argv[8]);else{pool.resize(base.size());iota(pool.begin(),pool.end(),0);}
    if((int)mandatory.size()>freecount||freecount>(int)base.size())return 7;
    Timer timer(seconds);Encoder e(p.n,base.size(),seed,-1,false);e.solver.connect_terminator(&timer);
    for(auto[r,v]:p.rows)e.row(r,v);
    for(int i=0;i<(int)base.size();i++){e.solver.phase(base[i].op?e.op[i]:-e.op[i]);e.solver.phase(e.a[i][base[i].a]);e.solver.phase(e.b[i][base[i].b]);}
    mt19937 rng(seed);int unsats=0,unknowns=0;
    for(int trial=0;!timer.terminate();trial++){
      shuffle(pool.begin(),pool.end(),rng);set<int>freed=mandatory;
      for(int k:pool){if((int)freed.size()>=freecount)break;freed.insert(k);}
      if((int)freed.size()!=freecount)return 8;
      for(int i=0;i<(int)base.size();i++)if(!freed.count(i)){e.solver.assume(base[i].op?e.op[i]:-e.op[i]);e.solver.assume(e.a[i][base[i].a]);e.solver.assume(e.b[i][base[i].b]);}
      e.solver.limit("conflicts",3000);int status=e.solver.solve();
      if(status==20)++unsats;else if(status==0)++unknowns;else{
        auto gs=e.model();int bad=0;for(auto[r,v]:p.rows)if(evaluate(p.n,gs,r)!=v)++bad;
        int complete=complete_boundary_errors(p,gs);
        cout<<"LOCAL SAT trial="<<trial<<" boundary_mismatches="<<bad<<" complete_boundary_errors="<<complete<<endl;
        for(int i=0;i<(int)gs.size();i++)cout<<p.n+i<<" "<<(gs[i].op?"or":"and")<<" "<<gs[i].a<<" "<<gs[i].b<<"\n";
        cout<<flush;return (bad||complete)?9:10;
      }
      if(trial%20==0)cout<<"local trial="<<trial<<" unsats="<<unsats<<" unknowns="<<unknowns<<endl;
    }
    cout<<"LOCAL FINISHED unsats="<<unsats<<" unknowns="<<unknowns<<endl;return 0;
  }
  if(string(argv[2])=="selftest"){
    auto gs=star(p);for(auto[r,v]:p.rows)if(evaluate(p.n,gs,r)!=v)return 4;
    if(complete_boundary_errors(p,gs))return 12;
    for(int bad=0;bad<2;bad++){
      Encoder e(p.n,gs.size(),0,-1,false);for(auto[r,v]:p.rows)e.row(r,v);e.incomparable();
      for(int i=0;i<(int)gs.size();i++){e.clause({(bad&&i==(int)gs.size()-1)?-e.op[i]:gs[i].op?e.op[i]:-e.op[i]});e.clause({e.a[i][gs[i].a]});e.clause({e.b[i][gs[i].b]});}
      int status=e.solver.solve();cout<<"selftest gates="<<gs.size()<<" rows="<<p.rows.size()<<" corrupt="<<bad<<" status="<<status<<endl;if(status!=(bad?20:10))return 5;
    }
    for(int reread=0;reread<2;reread++){
      auto altered=gs;auto [p0,q0]=p.edges.front();
      if(reread){int old=p.n+(int)altered.size()-1;altered.push_back({1,min(p0,q0),max(p0,q0)});altered.push_back({0,old,old+1});}
      Encoder e(p.n,altered.size(),0,-1,false);e.not_read1_pair(p0,q0);
      for(int i=0;i<(int)altered.size();i++){auto g=altered[i];e.clause({g.op?e.op[i]:-e.op[i]});e.clause({e.a[i][g.a]});e.clause({e.b[i][g.b]});}
      int status=e.solver.solve();cout<<"selftest forced_nonread1 reread="<<reread<<" status="<<status<<endl;if(status!=(reread?10:20))return 14;
    }
    int ands=count_if(gs.begin(),gs.end(),[](Gate g){return !g.op;});
    for(int wrong=0;wrong<2;wrong++){
      Encoder e(p.n,gs.size(),0,-1,false);e.exact_and_count(ands+wrong);
      for(int i=0;i<(int)gs.size();i++){auto g=gs[i];e.clause({g.op?e.op[i]:-e.op[i]});e.clause({e.a[i][g.a]});e.clause({e.b[i][g.b]});}
      int status=e.solver.solve();cout<<"selftest exact_AND expected="<<ands<<" requested="<<ands+wrong<<" status="<<status<<endl;if(status!=(wrong?20:10))return 15;
    }
    cout<<"SELFTEST PASS\n";return 0;
  }
  if(argc<7)return 2;
  int count=stoi(argv[2]),sec=stoi(argv[3]),seed=stoi(argv[4]),first=stoi(argv[5]);
  bool ordered=stoi(argv[6]);int initial=argc>7?stoi(argv[7]):64;
  Timer timer(sec);Encoder e(p.n,count,seed,first,ordered);e.solver.connect_terminator(&timer);
  if(argc>11){e.not_read1_pair(stoi(argv[10]),stoi(argv[11]));cout<<"forced nonread1 edge "<<argv[10]<<" "<<argv[11]<<endl;}
  if(argc>8){
    ifstream hint(argv[8]);string line;getline(hint,line);
    for(int i=0;i<count;i++){
      int wire,a,b;string op;hint>>wire>>op>>a>>b;
      if(!hint||wire!=p.n+i||a<0||b<0||a>=wire||b>=wire)return 11;
      if(a>b)swap(a,b);
      e.solver.phase(op=="or"?e.op[i]:-e.op[i]);
      for(int j=0;j<p.n+i;j++){e.solver.phase(j==a?e.a[i][j]:-e.a[i][j]);e.solver.phase(j==b?e.b[i][j]:-e.b[i][j]);}
    }
    cout<<"loaded structural phase hint\n";
  }
  vector<pair<uint64_t,bool>>negative;for(auto row:p.rows)if(row.second)e.row(row.first,true);else negative.push_back(row);
  mt19937 rng(seed);shuffle(negative.begin(),negative.end(),rng);
  for(int i=0;i<min(initial,(int)negative.size());i++)e.row(negative[i].first,false);
  int high=argc>9?stoi(argv[9]):p.n/2;
  for(auto row:negative)if(__builtin_popcountll(row.first)>=high)e.row(row.first,false);
  if(argc>12&&stoi(argv[12])){e.incomparable();cout<<"enforced operand incomparability on initial rows\n";}
  if(argc>13&&stoi(argv[13])>=0){e.exact_and_count(stoi(argv[13]));cout<<"forced AND count "<<argv[13]<<endl;}
  for(int round=0;!timer.terminate();round++){
    cout<<"solve round="<<round<<" rows="<<e.rows.size()<<" vars="<<e.vars<<" clauses="<<e.clauses<<endl;
    int status=e.solver.solve();cout<<"status="<<status<<endl;if(status!=10)return status==20?20:0;
    auto gs=e.model();vector<pair<uint64_t,bool>>bad;
    for(auto row:p.rows)if(evaluate(p.n,gs,row.first)!=row.second)bad.push_back(row);
    cout<<"candidate mismatches="<<bad.size()<<endl;
    for(int i=0;i<count;i++)cout<<p.n+i<<" "<<(gs[i].op?"or":"and")<<" "<<gs[i].a<<" "<<gs[i].b<<"\n";
    cout<<flush;if(bad.empty()){int complete=complete_boundary_errors(p,gs);cout<<"complete_boundary_errors="<<complete<<endl;if(complete)return 13;cout<<"WITNESS all point-subset closures and edges passed\n";return 10;}
    shuffle(bad.begin(),bad.end(),rng);for(int i=0;i<min(32,(int)bad.size());i++)e.row(bad[i].first,bad[i].second);
  }
}
