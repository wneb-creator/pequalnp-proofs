#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <cctype>
#include <chrono>
using namespace std;
struct Gate{int op,a,b;};
using Bits=array<unsigned long long,16>;
array<Bits,10>ins;Bits target;
vector<pair<int,int>>E={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
bool exact(const vector<Gate>&c){
 array<Bits,29>w;for(int i=0;i<10;i++)w[i]=ins[i];int nt=0;
 for(int g=0;g<19;g++){auto[op,a,b]=c[g];nt+=op==2;for(int j=0;j<16;j++)w[g+10][j]=op==0?w[a][j]&w[b][j]:op==1?w[a][j]|w[b][j]:~w[a][j];}
 if(!nt)return false;for(int j=0;j<16;j++)if(w[28][j]!=target[j])return false;return true;
}
int main(int argc,char**argv){
 if(argc!=2)return 2;ifstream f(argv[1]);vector<int>v;char ch;int n=-1;while(f.get(ch)){if(isdigit(ch)){if(n<0)n=0;n=n*10+ch-'0';}else if(n>=0){v.push_back(n);n=-1;}}if(v.size()!=57)return 3;
 vector<Gate>base;for(int i=0;i<57;i+=3)base.push_back({v[i],v[i+1],v[i+2]});vector<Gate>c=base;
 for(int x=0;x<1024;x++){for(int i=0;i<10;i++)if(x>>i&1)ins[i][x/64]|=1ull<<(x%64);for(auto[i,j]:E)if((x>>i&1)&&(x>>j&1)){target[x/64]|=1ull<<(x%64);break;}}
 vector<vector<Gate>>choices(19);for(int i=0;i<19;i++)for(int op=0;op<3;op++)for(int a=0;a<i+10;a++)for(int b=(op==2?a:a+1);b<(op==2?a+1:i+10);b++)choices[i].push_back({op,a,b});
 long long count=0;auto start=chrono::steady_clock::now();
 for(int i=0;i<19;i++)for(int j=i+1;j<19;j++)for(auto a:choices[i])for(auto b:choices[j]){c[i]=a;c[j]=b;count++;if(exact(c)){cout<<"WITNESS "<<i<<' '<<j<<endl;for(auto g:c)cout<<'['<<g.op<<','<<g.a<<','<<g.b<<"],";cout<<endl;return 0;}c[i]=base[i];c[j]=base[j];}
 cout<<"NONE among "<<count<<" two-gate replacements; seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
