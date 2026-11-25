#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
extern "C" {
void *ccadical_init();
void ccadical_release(void *);
void ccadical_add(void *,int);
int ccadical_solve(void *);
int ccadical_val(void *,int);
void ccadical_freeze(void *,int);
void ccadical_set_option(void *,const char *,int);
void ccadical_set_terminate(void *,void *,int (*)(void *));
}
using Clock=std::chrono::steady_clock;
static constexpr int N=10,S=19,R=1024,A=1055;
static const std::array<std::array<int,2>,15> edges={{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
int ix(int k,int j,int a){return (k*20+j)*A+a+1;}
bool target(int r){for(auto e:edges)if((r>>e[0]&1)&&(r>>e[1]&1))return true;return false;}
int terminate(void *p){return Clock::now()>=*static_cast<Clock::time_point*>(p);}
struct Solver {
 void *p=ccadical_init();std::vector<std::vector<int>> F;std::array<bool,R> encoded{};
 ~Solver(){ccadical_release(p);}
 void add(std::vector<int> c){for(int l:c)ccadical_add(p,l);ccadical_add(p,0);F.push_back(std::move(c));}
 void row(int r){
  if(encoded[r])return;encoded[r]=true;
  for(int sd=1;sd<=2;sd++)for(int j=0;j<S;j++)for(int k=0;k<=N+j;k++){
   int sel=ix(sd,j,k),v=ix(sd+3,j,r);
   if(k<N)add({-sel,(r>>k&1)?v:-v});
   else if(k<N+j){int w=ix(3,k-N,r);add({-sel,-v,w});add({-sel,v,-w});}
   else add({-sel,-v});
  }
  for(int j=0;j<S;j++){
   int o0=ix(0,j,0),o1=ix(0,j,1),o2=ix(0,j,2),o3=ix(0,j,3),w=ix(3,j,r),u=ix(4,j,r),v=ix(5,j,r);
   add({-o0,-w,u});add({-o0,-w,v});add({-o0,w,-u,-v});add({-o1,w,-u});add({-o1,w,-v});add({-o1,-w,u,v});add({-o2,w});add({-o3,w,u});add({-o3,-w,-u});
  }
  for(int k=0;k<=N+S;k++){
   int sel=ix(6,0,k);
   if(k<N){if(bool(r>>k&1)!=target(r))add({-sel});}
   else if(k<N+S){int w=ix(3,k-N,r);add({-sel,target(r)?w:-w});}
   else if(target(r))add({-sel});
  }
 }
 int selected(int kd,int j,int count){for(int k=0;k<count;k++)if(ccadical_val(p,ix(kd,j,k))>0)return k;throw std::runtime_error("missing selector");}
};
int main(int argc,char **argv){
 if(argc!=5){std::cerr<<"usage: sat_incremental BASECNF CASE OUTPUT_PREFIX TOTAL_SECONDS\n";return 2;}
 std::string which=argv[2],prefix=argv[3];int total=std::stoi(argv[4]);auto start=Clock::now(),end=start+std::chrono::seconds(total);
 Solver q;ccadical_set_option(q.p,"quiet",1);
 std::ifstream in(argv[1]);if(!in)return 3;std::string line;
 while(std::getline(in,line)){if(line.empty()||line[0]=='c'||line[0]=='p')continue;std::istringstream t(line);int v;std::vector<int> c;while(t>>v&&v)c.push_back(v);q.add(c);}
 for(int r=0;r<R;r++){
  bool b=target(r),boundary=true;
  for(int i=0;i<N;i++)if(b?(r>>i&1):!(r>>i&1)){if(target(b?(r&~(1<<i)):(r|(1<<i)))==b){boundary=false;break;}}
  if(boundary)q.encoded[r]=true;
 }
 for(int j=0;j<S;j++){
  for(auto kcnt:std::array<std::array<int,2>,3>{{{0,4},{1,N+j+1},{2,N+j+1}}}){
   int kd=kcnt[0],count=kcnt[1];for(int k=0;k<count;k++){ccadical_freeze(q.p,ix(kd,j,k));for(int l=0;l<k;l++)q.add({-ix(kd,j,k),-ix(kd,j,l)});}
  }
 }
 for(int k=0;k<=N+S;k++)ccadical_freeze(q.p,ix(6,0,k));
 int op=which.rfind("not",0)==0?3:which.rfind("and",0)==0?0:1;
 int second=which.rfind("not",0)==0?0:which.find("nonedge")!=std::string::npos?2:1;
 q.add({ix(0,0,op)});q.add({ix(1,0,0)});q.add({ix(2,0,second)});
 std::vector<int> anyNot;for(int j=0;j<S;j++)anyNot.push_back(ix(0,j,3));q.add(anyNot);
 if(which!="not_unbounded") for(int a=0;a<S;a++)for(int b=0;b<a;b++)for(int c=0;c<b;c++)for(int d=0;d<c;d++)for(int e=0;e<d;e++)q.add({-ix(0,a,3),-ix(0,b,3),-ix(0,c,3),-ix(0,d,3),-ix(0,e,3)});
 q.row(0);q.row(R-1);for(int i=0;i<N;i++)q.row(1<<i);
 if(which.rfind("not_one",0)==0){
  for(int j=1;j<S;j++)q.add({-ix(0,j,3)});
  for(int r:std::vector<int>{6,12,24,66,132,160,264,288,320,528,576,640,50,104,116,138,200,208,276,402,548,554,770,772,3,13,17,33,133,265,321,577,641,69,201,385,521,773})q.row(r);
 }
 if(which=="not_one_single1"||which=="not_one_single2"){
  int v=which.back()-'0';std::vector<int> uses;
  for(int j=0;j<S;j++)for(int sd=1;sd<=2;sd++)uses.push_back(ix(sd,j,v));
  q.add(uses);for(size_t j=0;j<uses.size();j++)for(size_t k=0;k<j;k++)q.add({-uses[j],-uses[k]});
  for(int j=1;j<S;j++)for(int other=0;other<=N;other++){
   q.add({-ix(1,j,v),-ix(2,j,other)});q.add({-ix(2,j,v),-ix(1,j,other)});
  }
  for(int a=0;a<=N;a++)for(int b=a+1;b<=N;b++)if(a!=v&&b!=v)for(int hop=0;hop<2;hop++)for(int gop=0;gop<2;gop++){
   bool compatible=true;
   for(int r=0;r<R;r++)if(!(r>>v&1)&&target(r)!=target(r|(1<<v))){
    bool x=a==N?!(r&1):(r>>a&1),y=b==N?!(r&1):(r>>b&1),h=hop?(x||y):(x&&y);
    if(h!=(gop==0)){compatible=false;break;}
   }
   if(!compatible)for(int j=2;j<S;j++)q.add({-ix(0,1,hop),-ix(1,1,a),-ix(2,1,b),-ix(0,j,gop),-ix(1,j,v),-ix(2,j,N+1)});
  }
 }
 int round=0,ret=0;
 while(Clock::now()<end){
  auto deadline=std::min(end,Clock::now()+std::chrono::seconds(180));ccadical_set_terminate(q.p,&deadline,terminate);
  int rows=std::count(q.encoded.begin(),q.encoded.end(),true);
  std::cout<<"round "<<round<<" rows "<<rows<<" clauses "<<q.F.size()<<std::endl;
  ret=ccadical_solve(q.p);
  auto elapsed=std::chrono::duration_cast<std::chrono::seconds>(Clock::now()-start).count();
  std::cout<<"result "<<ret<<" elapsed "<<elapsed<<std::endl;
  if(ret==20)break;
  if(ret==0){round++;continue;}
  std::array<std::array<int,3>,S> gates;int notCount=0;
  for(int j=0;j<S;j++){gates[j]={q.selected(0,j,4),q.selected(1,j,N+j+1),q.selected(2,j,N+j+1)};notCount+=gates[j][0]==3;}
  int output=q.selected(6,0,N+S+1);std::vector<int> bad;
  for(int r=0;r<R;r++){
   std::array<bool,N+S+1> w{};for(int i=0;i<N;i++)w[i]=r>>i&1;
   for(int j=0;j<S;j++){auto g=gates[j];bool x=g[1]<N+j?w[g[1]]:false,y=g[2]<N+j?w[g[2]]:false;w[N+j]=g[0]==0?x&&y:g[0]==1?x||y:g[0]==2?true:!x;}
   if(w[output]!=target(r)){if(q.encoded[r]){std::cerr<<"ENCODING DISAGREEMENT "<<r<<std::endl;return 4;}bad.push_back(r);}
  }
  std::ofstream model(prefix+"-"+std::to_string(round)+".json");model<<"{\"not_count\":"<<notCount<<",\"output\":"<<output<<",\"gates\":[";
  for(int j=0;j<S;j++){if(j)model<<',';model<<'['<<gates[j][0]<<','<<gates[j][1]<<','<<gates[j][2]<<']';}model<<"],\"bad_rows\":[";
  for(size_t j=0;j<bad.size();j++){if(j)model<<',';model<<bad[j];}model<<"]}\n";model.close();
  std::cout<<"candidate NOTs "<<notCount<<" wrong "<<bad.size()<<std::endl;
  if(bad.empty()){std::cout<<"VALID COUNTEREXAMPLE "<<prefix<<'-'<<round<<".json"<<std::endl;break;}
  std::sort(bad.begin(),bad.end(),[](int x,int y){int a=__builtin_popcount(x),b=__builtin_popcount(y);return a!=b?a<b:x<y;});
  for(size_t i=0;i<std::min<size_t>(16,bad.size());i++)q.row(bad[i]);
  round++;
 }
 std::ofstream cnf(prefix+"-final.cnf");cnf<<"p cnf "<<10*20*A<<' '<<q.F.size()<<'\n';for(auto &c:q.F){for(int v:c)cnf<<v<<' ';cnf<<"0\n";}
 return 0;
}
