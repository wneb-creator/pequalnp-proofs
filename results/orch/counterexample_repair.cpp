#define main globalSynthesisMain
#include "counterexample_sat.cpp"
#undef main

int main(int argc,char**argv) {
 if(argc!=5){std::cerr<<"usage: repair seconds seed circuit output-prefix\n";return 2;}
 int seconds=std::atoi(argv[1]),seed=std::atoi(argv[2]);std::string prefix=argv[4];
 std::ifstream f(argv[3]);std::vector<Gate> original;int index,a,b;std::string op;
 while(f>>index>>op>>a>>b) {
  if(op!="not"&&a>b)std::swap(a,b);
  if(op=="not")b=0;
  original.push_back({op=="and"?0:op=="or"?1:2,a,b});
 }
 if(original.size()!=19){std::cerr<<"expected 19 gates\n";return 2;}
 auto start=std::chrono::steady_clock::now(),finish=start+std::chrono::seconds(seconds);
 Timer timer;Synthesis s(19,1,seed);s.sat.connect_terminator(&timer);
 for(int x=0;x<1024;x++)if(!target(x)||std::popcount(unsigned(x))==2)s.sample(x);
 std::mt19937 rng(seed);int satCount=0,unsatCount=0,unknownCount=0;
 for(int round=0;std::chrono::steady_clock::now()<finish;round++) {
  timer.end=std::min(finish,std::chrono::steady_clock::now()+std::chrono::seconds(2));
  std::vector<int> order;for(int i=0;i<19;i++)order.push_back(i);std::shuffle(order.begin(),order.end(),rng);
  int fixed=9+rng()%7;
  for(int j=0;j<fixed;j++) {
   int i=order[j];auto g=original[i];
   s.sat.assume(s.op[i][g.op]);s.sat.assume(s.left[i][g.a]);s.sat.assume(s.right[i][g.b]);
  }
  int result=s.sat.solve();
  if(result==20)unsatCount++;else if(result==0)unknownCount++;else {
   satCount++;auto c=s.model();std::vector<int> errors;
   for(int x=0;x<1024;x++)if(eval(c,x)!=target(x))errors.push_back(x);
   std::cout<<"SAT round="<<round<<" errors="<<errors.size()<<" fixed="<<fixed<<std::endl;
   dump(c,prefix+"-candidate.txt");
   if(errors.empty()){dump(c,prefix+"-witness.txt");return 10;}
   std::shuffle(errors.begin(),errors.end(),rng);
   for(size_t i=0;i<std::min(size_t(8),errors.size());i++)s.sample(errors[i]);
  }
  if(round%1000==0)std::cout<<"round="<<round<<" sat="<<satCount<<" unsat="<<unsatCount<<" unknown="<<unknownCount<<" samples="<<s.samples.size()<<" elapsed="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
 }
 std::cout<<"DONE local-repair sat="<<satCount<<" unsat="<<unsatCount<<" unknown="<<unknownCount<<std::endl;
}
