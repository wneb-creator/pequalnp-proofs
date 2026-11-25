#define main cdcl_main
#include "cdcl_search.cpp"
#undef main
#include <fstream>

vector<Clause> readRun(const char* name){ifstream in(name);int n;in>>n;vector<Clause>run;for(int i=0;i<n;i++){int k;in>>k;vector<int>a(k);for(int&l:a)in>>l;run.push_back(clause(a));}if(!in){cerr<<"FAULT input"<<endl;exit(2);}return run;}
bool checkRun(const vector<Clause>&run){auto db=base;for(auto c:run){if(!rup(db,c))return false;db.push_back(c);}return !run.empty()&&run.back().lits.empty();}
void strengthen(vector<Clause>&run){
 auto db=base;
 for(size_t k=0;k<run.size();k++){
  auto a=run[k].lits;shuffle(a.begin(),a.end(),rng);
  for(int i=0;i<int(a.size());){auto b=a;b.erase(b.begin()+i);auto c=clause(b);if(rup(db,c))a=b;else i++;}
  run[k]=clause(a);db.push_back(run[k]);if(a.empty()){run.resize(k+1);return;}
 }
}
Clause proposal(const vector<Clause>&db,int polarity){
 for(int attempt=0;attempt<80;attempt++){
  vector<int>a;unsigned used=0;
  if(rng()%3==0){
   const auto&u=db[rng()%db.size()];const auto&v=db[rng()%db.size()];unsigned piv=(u.pos&v.neg)|(u.neg&v.pos);if(!piv)continue;int var=__builtin_ctz(piv);for(int l:u.lits)if(abs(l)!=var+1)a.push_back(l);for(int l:v.lits)if(abs(l)!=var+1)a.push_back(l);sort(a.begin(),a.end());a.erase(unique(a.begin(),a.end()),a.end());
  }else{
   int width=2+rng()%5;for(int i=0;i<width;i++){int v=rng()%20;if(used>>v&1)continue;used|=1u<<v;bool positive=rng()%100<polarity;a.push_back(positive?-v-1:v+1);}
  }
  Clause c=clause(a);if(c.pos&c.neg||!rup(db,c))continue;
  shuffle(a.begin(),a.end(),rng);for(int i=0;i<int(a.size());){auto b=a;b.erase(b.begin()+i);auto d=clause(b);if(rup(db,d)){a=b;c=d;}else i++;}
  bool old=false;for(const auto&d:db)if((d.pos&~c.pos)==0&&(d.neg&~c.neg)==0){old=true;break;}if(old)continue;
  return c;
 }
 return clause({1,-1});
}
void compressKeep(vector<Clause>&run,int protectedIndex){
 for(;;){vector<int>order(run.size());for(int i=0;i<int(order.size());i++)order[i]=i;shuffle(order.begin(),order.end(),rng);bool changed=false;
  for(int i:order){if(i==protectedIndex||run[i].lits.empty())continue;auto trial=run;trial.erase(trial.begin()+i);if(checkRun(trial)){run=trial;if(i<protectedIndex)protectedIndex--;changed=true;break;}}
  if(!changed)break;
 }
}
int main(int argc,char**argv){
 if(argc<4)return 2;
 for(int p=0;p<5;p++){vector<int>a;for(int h=0;h<4;h++)a.push_back(4*p+h+1);base.push_back(clause(a));}
 for(int p=0;p<5;p++)for(int q=p+1;q<5;q++)for(int h=0;h<4;h++)base.push_back(clause({-(4*p+h+1),-(4*q+h+1)}));
 rng.seed(stoul(argv[2]));int seconds=stoi(argv[3]);signal(SIGINT,stopped);signal(SIGTERM,stopped);
 auto initial=readRun(argv[1]);if(!checkRun(initial)){cerr<<"FAULT initial invalid"<<endl;return 2;}strengthen(initial);minimize(initial);int best=initial.size();show(initial,0);vector<vector<Clause>>archive={initial};auto start=chrono::steady_clock::now();auto current=initial;
 for(int trial=1;;trial++){
  if(stopFlag||chrono::duration<double>(chrono::steady_clock::now()-start).count()>seconds){cout<<"DONE trials="<<trial<<" best="<<best<<endl;return 0;}
  if(trial%50==0)current=archive[rng()%archive.size()];int i=rng()%current.size();auto db=base;db.insert(db.end(),current.begin(),current.begin()+i);auto next=current;int kind=rng()%6;
  if(kind==0){
   if(i+1>=int(current.size())||!rup(db,current[i+1]))continue;swap(next[i],next[i+1]);strengthen(next);minimize(next);
  }else if(kind==1){
   int j=rng()%current.size();vector<int>a;for(int l:current[i].lits)if(find(current[j].lits.begin(),current[j].lits.end(),l)!=current[j].lits.end())a.push_back(l);Clause c=clause(a);if(!rup(db,c))continue;next[i]=c;if(a.empty())next.resize(i+1);strengthen(next);minimize(next);
  }else if(kind==2){strengthen(next);minimize(next);}
  else{
   Clause c=proposal(db,(trial/50)%3==0?100:(trial/50)%3==1?85:50);if(c.pos&c.neg)continue;
   next.insert(next.begin()+i,c);if(c.lits.empty())next.resize(i+1);else compressKeep(next,i);strengthen(next);if(rng()%2)minimize(next);
  }
  if(!checkRun(next)){cerr<<"FAULT optimized run"<<endl;return 2;}
  if(next.size()<current.size()||(next.size()==current.size()&&rng()%4!=0)||(next.size()<=size_t(best+2)&&rng()%32==0))current=next;
  if(int(next.size())<best){best=next.size();show(next,trial);if(best<=12)return 0;archive.clear();archive.push_back(next);current=next;}
  else if(next.size()<=size_t(best+2)&&rng()%10==0){if(archive.size()<32)archive.push_back(next);else archive[rng()%archive.size()]=next;}
 }
}
