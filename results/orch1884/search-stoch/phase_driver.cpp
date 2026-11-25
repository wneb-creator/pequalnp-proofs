#define main signedSearchMain
#include "search_signed17.cpp"
#undef main
int main(){
 setup();Circuit c;
 for(auto&g:c)if(!(cin>>g.op>>g.a>>g.b))return 2;
 auto p=phaseOpt(c);auto r=realize(c,p);validateRealization(c,r,false);
 cout<<"{\"paid_not\":"<<p.count<<",\"free_primary\":"<<p.freeInput
     <<",\"binary\":"<<p.binary<<",\"phase\":"<<p.phase<<"}"<<endl;
 return 0;
}
