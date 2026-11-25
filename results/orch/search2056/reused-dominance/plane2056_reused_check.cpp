#define main search_main
#include "plane2056_reused.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=3)return 2;std::ifstream f(argv[1]);Data d;int points,budget,pos,neg;f>>d.inputs>>points>>budget>>pos>>neg;
 for(int k=0;k<pos+neg;k++){int r;f>>r;d.rows.push_back(r);int word=k/64,bit=k%64;for(int i=0;i<d.inputs;i++)if((r>>i)&1)d.val[i][word]|=U(1)<<bit;if(k<pos){d.target[word]|=U(1)<<bit;d.edges.push_back({std::countr_zero((unsigned)r),std::countr_zero((unsigned)(r&(r-1)))});}else d.negative[word]|=U(1)<<bit;d.mask[word]|=U(1)<<bit;}
 std::ifstream sf(argv[2]);int count;sf>>count;std::mt19937 rng(205614);int checked=0,reused=0;
 for(int k=0;k<count;k++){int size,nkeep;sf>>size>>nkeep;std::vector<int>guards(nkeep);for(int&g:guards)sf>>g;std::vector<Gate>base(size);for(auto&g:base)sf>>g.op>>g.a>>g.b;if(!sf)return 3;
  for(int trial=0;trial<16;trial++){
   Net c=deleted(d,base,rng,guards);if(!valid(d,c))return 4;
   if(size==67){
    for(int j=0;j<3;j++)if(c[j].op!=base[j].op||c[j].a!=base[j].a||c[j].b!=base[j].b)return 5;
    bool cone[96]={},contains[96]={};cone[d.inputs+GATES-1]=true;
    for(int j=GATES-1;j>=0;j--)if(cone[d.inputs+j]&&c[j].op){cone[c[j].a]=true;cone[c[j].b]=true;}
    int terminals=0;for(int j=0;j<GATES;j++){int w=d.inputs+j;auto g=c[j];if(w==28)contains[w]=true;else if(g.op)contains[w]=contains[g.a]||contains[g.b];else if(cone[w]&&(contains[g.a]||contains[g.b]))terminals++;}
    if(terminals!=2)return 6;reused++;
   }
   auto v=d.val;for(int j=0;j<GATES;j++){auto g=c[j];for(int w=0;w<WORDS;w++)v[d.inputs+j][w]=g.op?(v[g.a][w]|v[g.b][w]):(v[g.a][w]&v[g.b][w]);}Bits before=v[d.inputs+GATES-1];
   int score=eval(d,c,1);if(d.raw==0){show(d,c,score,1,0);return 0;}if(!valid(d,c))return 7;
   v=d.val;for(int j=0;j<GATES;j++){auto g=c[j];for(int w=0;w<WORDS;w++)v[d.inputs+j][w]=g.op?(v[g.a][w]|v[g.b][w]):(v[g.a][w]&v[g.b][w]);}Bits after=v[d.inputs+GATES-1];
   if(after!=d.val[d.inputs+GATES-1])return 8;
   for(int w=0;w<WORDS;w++){if((before[w]&d.target[w]&~after[w])!=0)return 9;if((after[w]&d.negative[w]&~before[w])!=0)return 10;}
   checked++;
  }
 }
 std::cout<<"PASS "<<checked<<" valid deleted nets; "<<reused<<" preserve both reused dirty paths before normalization; no lost positives, no new negatives, emitted nets match, backward reads valid"<<std::endl;return 0;
}
