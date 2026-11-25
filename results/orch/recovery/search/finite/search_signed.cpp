#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <cmath>
#include <iostream>
#include <algorithm>
#include <bit>
using namespace std;
struct Gate{int op,a,b;bool na,nb;};
struct Circuit{vector<Gate>g;bool flip=false;};
using Bits=array<unsigned long long,16>;
array<Bits,10> ins; Bits target,negative;
vector<pair<int,int>>E={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
mt19937_64 rng(1094);int rr(int n){return rng()%n;}int K=15,B=4;
pair<int,int> evaluate(const Circuit&c){
 array<Bits,40>w; for(int i=0;i<10;i++)w[i]=ins[i];unsigned negs=0;
 for(int g=0;g<(int)c.g.size();g++){auto z=c.g[g];if(z.na)negs|=1u<<z.a;if(z.nb)negs|=1u<<z.b;
  for(int j=0;j<16;j++){auto a=z.na?~w[z.a][j]:w[z.a][j],b=z.nb?~w[z.b][j]:w[z.b][j];w[g+10][j]=z.op?(a|b):(a&b);}}
 if(c.flip)negs|=1u<<(K+9);int neg=popcount(negs),err=0;
 for(int j=0;j<16;j++){auto v=c.flip?~w[K+9][j]:w[K+9][j];auto d=v^target[j];err+=popcount(d)+3*popcount(d&negative[j]);}
 return {err+100*max(0,neg-B),neg};
}
void show(const Circuit&c){cout<<"gates [";for(auto z:c.g)cout<<'['<<z.op<<','<<z.a<<','<<z.b<<','<<z.na<<','<<z.nb<<"],";cout<<"] flip "<<c.flip<<endl;}
Circuit seed(){
 vector<int>I;for(int x=0;x<1024;x++)if(popcount((unsigned)x)==4){bool ok=1;for(auto [i,j]:E)if((x>>i&1)&&(x>>j&1))ok=0;if(ok)I.push_back(x);}
 int independent=I[rr(I.size())];vector<vector<int>>N(10);
 for(auto [i,j]:E){if(independent>>i&1)swap(i,j);else if(!(independent>>j&1)&&rr(2))swap(i,j);N[i].push_back(j);}
 vector<int>order;for(int i=0;i<10;i++)if(N[i].size())order.push_back(i);shuffle(order.begin(),order.end(),rng);
 Circuit c;vector<int>stars;
 for(int i:order){shuffle(N[i].begin(),N[i].end(),rng);int w=N[i][0];for(int j=1;j<(int)N[i].size();j++){c.g.push_back({1,w,N[i][j],false,false});w=c.g.size()+9;}c.g.push_back({0,i,w,false,false});stars.push_back(c.g.size()+9);}
 shuffle(stars.begin(),stars.end(),rng);int w=stars[0];for(int i=1;i<(int)stars.size();i++){c.g.push_back({1,w,stars[i],false,false});w=c.g.size()+9;}
 while((int)c.g.size()>K){int k=rr(c.g.size()-1),alias=rr(2)?c.g[k].a:c.g[k].b;c.g.erase(c.g.begin()+k);for(auto &z:c.g)for(int*q:{&z.a,&z.b}){if(*q==k+10)*q=alias;else if(*q>k+10)(*q)--;}}
 return c;
}
int main(int argc,char**argv){int seconds=argc>1?atoi(argv[1]):300;if(argc>2)rng.seed(atoi(argv[2]));if(argc>3)K=atoi(argv[3]);if(argc>4)B=atoi(argv[4]);
 for(int x=0;x<1024;x++){for(int i=0;i<10;i++)if(x>>i&1)ins[i][x/64]|=1ull<<(x%64);bool f=0;for(auto [i,j]:E)if((x>>i&1)&&(x>>j&1))f=1;(f?target:negative)[x/64]|=1ull<<(x%64);}
 auto started=chrono::steady_clock::now();long long tries=0;int best=10000;
 while(chrono::duration<double>(chrono::steady_clock::now()-started).count()<seconds){Circuit c=seed();int score=evaluate(c).first;
  for(int t=0;t<30000;t++){Circuit old=c;int k=rr(K),field=rr(24);
   if(field<2)c.g[k].op^=1;else if(field<8)c.g[k].a=rr(k+10);else if(field<14)c.g[k].b=rr(k+10);else if(field<17)c.g[k].na=!c.g[k].na;else if(field<19)c.g[k].nb=!c.g[k].nb;else if(field==19)c.flip=!c.flip;else{c.g[k].op^=1;c.g[k].na=!c.g[k].na;c.g[k].nb=!c.g[k].nb;for(int h=k+1;h<K;h++){if(c.g[h].a==10+k)c.g[h].na=!c.g[h].na;if(c.g[h].b==10+k)c.g[h].nb=!c.g[h].nb;}if(k==K-1)c.flip=!c.flip;}
   auto [ns,nots]=evaluate(c);tries++;double temp=0.2+3.0*(30000-t)/30000.;if(ns<=score||generate_canonical<double,53>(rng)<exp((score-ns)/temp))score=ns;else c=old;
   if(score<best){best=score;cout<<"best "<<best<<" neg "<<evaluate(c).second<<" trials "<<tries<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;show(c);}
   if(score==0){cout<<"WITNESS binary "<<K<<" neg "<<evaluate(c).second<<endl;return 0;}
  }
 }
 cout<<"finished best "<<best<<" trials "<<tries<<endl;
}
