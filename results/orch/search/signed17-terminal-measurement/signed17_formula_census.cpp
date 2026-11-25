#include "signed17_formula_measured.cpp"
#include <iomanip>

ofstream packed;
void putvar(uint64_t x){while(x>=128){packed.put(char((x&127)|128));x>>=7;}packed.put(char(x));}
Word parseword(string text){
 if(text.size()!=258||text.substr(0,2)!="0x")throw runtime_error("word length");
 for(char c:text.substr(2))if(!isxdigit((unsigned char)c))throw runtime_error("word digit");
 Word w;for(int j=0;j<16;j++)w.a[15-j]=stoull(text.substr(2+16*j,16),nullptr,16);return w;
}
int measured(const vector<int>&state, vector<FormEntry>&es, const string&part, int node, int copy){
 measuredTries=measuredRejects=0;measuredRows.clear();
 int ans=formula_check(state,&es,false);
 cout<<"{\"part\":\""<<part<<"\",\"node\":"<<node<<",\"copy\":"<<copy<<",\"answer\":"<<ans<<",\"roots\":"<<state.size()<<",\"entries\":"<<es.size()<<",\"tries\":"<<measuredTries<<",\"row_rejects\":"<<measuredRejects<<",\"distinct_rows\":"<<measuredRows.size()<<"}\n";
 if(ans==0){
  putvar(state.size());putvar(es.size()-state.size());
  for(size_t j=state.size();j<es.size();j++){auto e=es[j];putvar(e.op);putvar(e.left);putvar(e.right);}
  vector<int>rows(measuredRows.begin(),measuredRows.end());sort(rows.begin(),rows.end());putvar(rows.size());for(int r:rows)putvar(r);
 }
 return ans;
}
int main(int argc,char**argv){
 if(argc!=4){cerr<<"usage: census input packed seconds\n";return 2;}
 signedmode=true;seconds=stod(argv[3]);beginat=lastreport=chrono::steady_clock::now();packed.open(argv[2],ios::binary);if(!packed)return 2;
 vector<pair<int,int>>edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
 Word target;array<Word,10>inwords;
 for(int r=0;r<1024;r++)for(int i=0;i<10;i++)if(r>>i&1)setbit(inwords[i],r);
 for(auto[a,b]:edges){target=bor(target,band(inwords[a],inwords[b]));positives.push_back((1<<a)|(1<<b));}
 for(int r=0;r<1024;r++)if(!bit(target,r))negatives.push_back(r);
 for(int k=0;k<int(positives.size()*negatives.size());k++)allcov.a[k/64]|=1ull<<(k%64);
 intern(Word{});for(int i=0;i<10;i++)inputs[i]=intern(inwords[i]);targetid=intern(target);
 ifstream in(argv[1]);int count;if(!(in>>count))return 2;vector<int>ids;
 for(int i=0;i<count;i++){string s;in>>s;ids.push_back(intern(parseword(s)));}
 int banks;in>>banks;int completed=0;
 try{
 for(int k=0;k<banks;k++){
  string part;int node,kind,n;in>>part>>node>>kind>>n;vector<int>state;
  for(int j=0;j<n;j++){int id;in>>id;state.push_back(ids.at(id));}
  if(!in)throw runtime_error("truncated bank");
  vector<FormEntry>es;int result=measured(state,es,part,node,-1);if(result!=0)return 3;
  if(kind)for(int j=0;j<int(es.size());j++){
   auto e=es[j];vector<int>leaves;for(int t=0;t<n;t++)if(!(e.mask>>t&1))leaves.push_back(state[t]);leaves.push_back(e.sig);leaves.push_back(e.sig);
   vector<FormEntry>cs;result=measured(leaves,cs,part,node,j);if(result!=0)return 4;
  }
  completed++;if(completed%100==0){cout.flush();cerr<<"completed="<<completed<<" signals="<<sigs.size()<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-beginat).count()<<"\n";}
 }
 }catch(Limit const&){cerr<<"ordinary census time limit after "<<completed<<" banks\n";return 5;}
 cout<<"{\"completed\":"<<completed<<",\"expected\":"<<banks<<",\"signals\":"<<sigs.size()<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-beginat).count()<<"}\n";
 return 0;
}
