#define main globalSynthesisMain
#include "counterexample_sat.cpp"
#undef main

std::vector<Gate> coverWitness() {
 const std::array<bool,10> cover={false,true,false,true,true,true,true,true,false,false};
 std::array<std::vector<int>,10> nbrs;
 for(auto [a,b]:edges){if(!cover[a])std::swap(a,b);nbrs[a].push_back(b);}
 std::vector<Gate> c;std::vector<int> stars;
 for(int i=0;i<10;i++)if(!nbrs[i].empty()) {
  int x=nbrs[i][0];
  for(size_t j=1;j<nbrs[i].size();j++){c.push_back({1,x,nbrs[i][j]});x=9+c.size();}
  c.push_back({0,i,x});stars.push_back(9+c.size());
 }
 int x=stars[0];
 for(size_t i=1;i<stars.size();i++){c.push_back({1,x,stars[i]});x=9+c.size();}
 return c;
}
bool check(std::vector<Gate> c,int mode,bool expected,const char*label) {
 if(std::getenv("PNP_ORDERED")) {
  std::vector<Gate> ordered;std::vector<int> mapped(c.size(),-1);
  for(size_t step=0;step<c.size();step++) {
   int best=-1;std::array<int,4> key{};Gate bestGate{};
   for(size_t i=0;i<c.size();i++)if(mapped[i]<0) {
    auto g=c[i];bool ready=true;
    if(g.a>=10){if(mapped[g.a-10]<0)ready=false;else g.a=mapped[g.a-10];}
    if(g.op!=2&&g.b>=10){if(mapped[g.b-10]<0)ready=false;else g.b=mapped[g.b-10];}
    if(!ready)continue;
    int hi=g.op==2?g.a:std::max(g.a,g.b),lo=g.op==2?0:std::min(g.a,g.b);
    std::array<int,4> k={hi,lo,g.op,int(i)};
    if(best<0||k<key){best=i;key=k;bestGate=g;}
   }
   if(best<0)return false;
   mapped[best]=10+ordered.size();ordered.push_back(bestGate);
  }
  if(mapped.back()!=int(9+c.size()))return false;
  c=ordered;
 }
 for(auto &g:c){if(g.op!=2&&g.a>g.b)std::swap(g.a,g.b);if(g.op==2)g.b=0;}
 bool correct=true;
 for(int x=0;x<1024;x++)if(eval(c,x)!=target(x))correct=false;
 if(correct!=expected){std::cerr<<label<<" direct evaluation mismatch\n";return false;}
 Synthesis s(c.size(),mode,127);Timer timer;timer.end=std::chrono::steady_clock::now()+std::chrono::seconds(20);s.sat.connect_terminator(&timer);
 for(size_t i=0;i<c.size();i++){auto g=c[i];s.clause({s.op[i][g.op]});s.clause({s.left[i][g.a]});s.clause({s.right[i][g.b]});}
 for(int x=0;x<1024;x++)s.sample(x);
 int result=s.sat.solve();std::cout<<label<<" gates="<<c.size()<<" direct="<<correct<<" solver="<<result<<std::endl;
 if(result!=(expected?10:20))return false;
 if(result==10){auto d=s.model();for(int x=0;x<1024;x++)if(eval(d,x)!=target(x))return false;}
 return true;
}
int main() {
 auto w=coverWitness();
 if(w.size()!=20||!check(w,0,true,"monotone-positive"))return 1;
 auto one=w;for(auto &g:one){if(g.a>=10)g.a++;if(g.b>=10)g.b++;}one.insert(one.begin(),{2,0,0});
 if(!check(one,1,true,"unused-not-positive"))return 1;
 auto two=w;two.push_back({2,29,0});two.push_back({2,30,0});
 if(!check(two,2,true,"double-not-positive"))return 1;
 auto bad=w;bad[0].op=1-bad[0].op;
 if(!check(bad,0,false,"mutated-negative"))return 1;
 std::cout<<"PASS all controls on all1024 inputs\n";
}
