#define main search_main
#include "plane2056_strata69.cpp"
#undef main
int referenceShared(const Data&d,const Net&c){

 auto values=d.val;std::array<std::vector<int>,96>parents;for(int j=0;j<GATES;j++){auto g=c[j];int w=d.inputs+j;parents[g.a].push_back(w);parents[g.b].push_back(w);for(int k=0;k<WORDS;k++)values[w][k]=g.op?(values[g.a][k]|values[g.b][k]):(values[g.a][k]&values[g.b][k]);}
 bool live[96]={};live[d.inputs+GATES-1]=true;for(int j=GATES-1;j>=0;j--)if(live[d.inputs+j]){live[c[j].a]=true;live[c[j].b]=true;}
 int result=0;for(int j=0;j<GATES;j++){int w=d.inputs+j;if(c[j].op||!live[w]||!(values[w][0]&d.target[0]))continue;bool dirty=false;for(int row=(int)d.edges.size();row<(int)d.rows.size();row++)if((values[w][row/64]>>(row%64))&1){dirty=true;break;}if(!dirty)continue;std::vector<int>pending=parents[w];bool visited[96]={};int terminals=0;while(!pending.empty()){int x=pending.back();pending.pop_back();if(!live[x]||visited[x])continue;visited[x]=true;if(c[x-d.inputs].op==0){if(values[x][0]&d.target[0])terminals++;}else for(int next:parents[x])pending.push_back(next);}if(terminals>=2)result++;}return result;
}
int main(int argc,char**argv){
 if(argc!=4)return 2;std::ifstream f(argv[1]);Data d;int points,budget,pos,neg;f>>d.inputs>>points>>budget>>pos>>neg;
 for(int k=0;k<pos+neg;k++){int r;f>>r;d.rows.push_back(r);int word=k/64,bit=k%64;for(int i=0;i<d.inputs;i++)if((r>>i)&1)d.val[i][word]|=U(1)<<bit;if(k<pos){d.target[word]|=U(1)<<bit;d.edges.push_back({std::countr_zero((unsigned)r),std::countr_zero((unsigned)(r&(r-1)))});}else d.negative[word]|=U(1)<<bit;d.mask[word]|=U(1)<<bit;}
 std::ifstream sf(argv[2]),mf(argv[3]);int count,mcount;sf>>count;mf>>mcount;if(count!=mcount)return 15;std::mt19937 rng(205614);int checked=0,reused=0,nestedCases=0,sharedCases=0;
 for(int k=0;k<count;k++){int size,nkeep;sf>>size>>nkeep;std::vector<int>guards(nkeep);for(int&g:guards)sf>>g;std::vector<Gate>base(size);for(auto&g:base)sf>>g.op>>g.a>>g.b;if(!sf)return 3;int dcount;mf>>dcount;std::vector<int>dirtyWires(dcount);for(int&w:dirtyWires)mf>>w;if(!mf)return 16;
  for(int trial=0;trial<32;trial++){
   Net c=deleted(d,base,rng,guards);if(!valid(d,c))return 4;if(trial>=16){mutate(d,c,rng,1+rng()%8);if(!valid(d,c))continue;}
   if(trial<16&&!dirtyWires.empty()){
    for(int j=0;j<=dirtyWires.back()-d.inputs;j++)if(c[j].op!=base[j].op||c[j].a!=base[j].a||c[j].b!=base[j].b)return 5;
    bool live[96]={};live[d.inputs+GATES-1]=true;std::array<std::vector<int>,96>parents;
    for(int j=0;j<GATES;j++){parents[c[j].a].push_back(d.inputs+j);parents[c[j].b].push_back(d.inputs+j);}
    for(int j=GATES-1;j>=0;j--)if(live[d.inputs+j]){live[c[j].a]=true;live[c[j].b]=true;}
    for(int dw:dirtyWires){std::vector<int>pending=parents[dw];bool visited[96]={},term[96]={};int terminals=0;while(!pending.empty()){int w=pending.back();pending.pop_back();if(!live[w]||visited[w])continue;visited[w]=true;if(c[w-d.inputs].op==0){term[w]=true;terminals++;}else for(int x:parents[w])pending.push_back(x);}if(terminals!=2)return 6;if(dirtyWires.size()==2&&dw==dirtyWires[0]&&!term[dirtyWires[1]])return 14;}
    reused++;nestedCases+=dirtyWires.size()==2;
   }
   auto v=d.val;for(int j=0;j<GATES;j++){auto g=c[j];for(int w=0;w<WORDS;w++)v[d.inputs+j][w]=g.op?(v[g.a][w]|v[g.b][w]):(v[g.a][w]&v[g.b][w]);}Bits before=v[d.inputs+GATES-1];
   int score=eval(d,c,2);if(d.raw==0){show(d,c,score,2,0,"witness");return 0;}if(!valid(d,c))return 7;if(referenceShared(d,c)!=d.shared)return 13;sharedCases+=d.shared>0;
   v=d.val;for(int j=0;j<GATES;j++){auto g=c[j];for(int w=0;w<WORDS;w++)v[d.inputs+j][w]=g.op?(v[g.a][w]|v[g.b][w]):(v[g.a][w]&v[g.b][w]);}Bits after=v[d.inputs+GATES-1];
   if(after!=d.val[d.inputs+GATES-1])return 8;
   for(int w=0;w<WORDS;w++){if((before[w]&d.target[w]&~after[w])!=0)return 9;if((after[w]&d.negative[w]&~before[w])!=0)return 10;}
   checked++;
  }
 }
 std::cout<<"PASS "<<checked<<" valid deleted/mutated nets; "<<reused<<" preserve reused paths, including "<<nestedCases<<" nested cases before normalization; "<<sharedCases<<" have independently matched dirty reuse; no lost positives, no new negatives, emitted nets match, backward reads valid"<<std::endl;return 0;
}
