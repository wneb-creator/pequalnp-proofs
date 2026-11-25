#include "cadical.hpp"
#include <array>
#include <vector>
#include <algorithm>
#include <chrono>
#include <iostream>
#include <fstream>
#include <random>
#include <set>
#include <cstdlib>
using namespace std;
struct Timer:CaDiCaL::Terminator { chrono::steady_clock::time_point end; bool terminate() override {return chrono::steady_clock::now()>end;} };
struct Synth {
 CaDiCaL::Solver s; int nv=0,ng,cas; vector<array<int,3>> O; vector<vector<int>> A,B; set<int> rows;
 int var(){return ++nv;} void cl(initializer_list<int>x){for(int a:x)s.add(a);s.add(0);} void cl(vector<int>x){for(int a:x)s.add(a);s.add(0);}
 void one(vector<int> x){cl(x);for(int a=0;a<(int)x.size();a++)for(int b=a+1;b<(int)x.size();b++)cl({-x[a],-x[b]});}
 Synth(int n,int c,int seed,int maxnot):ng(n),cas(c){s.set("quiet",1);s.set("seed",seed);O.resize(n);A.resize(n);B.resize(n);
 for(int i=0;i<n;i++){for(int &v:O[i])v=var();one({O[i][0],O[i][1],O[i][2]});A[i].resize(10+i);B[i].resize(10+i);for(int&v:A[i])v=var();for(int&v:B[i])v=var();one(A[i]);one(B[i]);cl({-O[i][2],B[i][0]});for(int a=0;a<10+i;a++)for(int b=0;b<=a;b++)cl({-A[i][a],-B[i][b],O[i][2]});}
 vector<int> any;for(auto o:O)any.push_back(o[2]);cl(any);
 vector<vector<int>> S(n, vector<int>(maxnot));for(int i=0;i<n;i++){for(int&v:S[i])v=var();cl({-O[i][2],S[i][0]});if(i) {for(int j=0;j<maxnot;j++)cl({-S[i-1][j],S[i][j]});for(int j=1;j<maxnot;j++)cl({-O[i][2],-S[i-1][j-1],S[i][j]});cl({-O[i][2],-S[i-1][maxnot-1]});}}
 for(int i=0;i<n-1;i++){vector<int> used;for(int k=i+1;k<n;k++){used.push_back(A[k][10+i]);used.push_back(B[k][10+i]);}cl(used);}
 
 vector<int> diff={-O[0][1],-A[0][5],-B[0][9],-O[1][0],-A[1][7],-B[1][10],-O[2][1],-A[2][1],-B[2][9],-O[3][0],-A[3][6],-B[3][12],-O[4][1],-A[4][3],-B[4][9],-O[5][0],-A[5][4],-B[5][14],-O[6][2],-A[6][3],-B[6][0],-O[7][0],-A[7][0],-B[7][4],-O[8][1],-A[8][3],-B[8][7],-O[9][1],-A[9][1],-B[9][18],-O[10][0],-A[10][2],-B[10][19],-O[11][1],-A[11][3],-B[11][5],-O[12][1],-A[12][6],-B[12][21],-O[13][0],-A[13][8],-B[13][22],-O[14][1],-A[14][13],-B[14][17],-O[15][1],-A[15][20],-B[15][24],-O[16][1],-A[16][11],-B[16][25],-O[17][1],-A[17][15],-B[17][26],-O[18][1],-A[18][23],-B[18][27]};
for(int d:diff)s.phase(-d);int lim=c;vector<vector<int>> T(diff.size(),vector<int>(lim));for(int i=0;i<(int)diff.size();i++){for(int&v:T[i])v=var();cl({-diff[i],T[i][0]});if(i){for(int j=0;j<lim;j++)cl({-T[i-1][j],T[i][j]});for(int j=1;j<lim;j++)cl({-diff[i],-T[i-1][j-1],T[i][j]});cl({-diff[i],-T[i-1][lim-1]});}}
 }
 static bool goal(int x){int es[15][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};for(auto&e:es)if((x>>e[0]&1)&&(x>>e[1]&1))return true;return false;}
 void row(int x){if(!rows.insert(x).second)return;vector<int>V;for(int i=0;i<ng;i++){int a=var(),b=var(),y=var();for(int j=0;j<10+i;j++) {if(j<10){cl({-A[i][j],(x>>j&1)?a:-a});cl({-B[i][j],(x>>j&1)?b:-b});}else{cl({-A[i][j],-a,V[j-10]});cl({-A[i][j],a,-V[j-10]});cl({-B[i][j],-b,V[j-10]});cl({-B[i][j],b,-V[j-10]});}}
 cl({-O[i][0],-a,-b,y});cl({-O[i][0],a,-y});cl({-O[i][0],b,-y});cl({-O[i][1],a,b,-y});cl({-O[i][1],-a,y});cl({-O[i][1],-b,y});cl({-O[i][2],a,y});cl({-O[i][2],-a,-y});V.push_back(y);}
 cl({goal(x)?V.back():-V.back()});}
 vector<array<int,3>> model(){vector<array<int,3>>m(ng);for(int i=0;i<ng;i++){for(int j=0;j<3;j++)if(s.val(O[i][j])>0)m[i][0]=j;for(int j=0;j<10+i;j++){if(s.val(A[i][j])>0)m[i][1]=j;if(s.val(B[i][j])>0)m[i][2]=j;}}return m;}
 bool eval(vector<array<int,3>>&m,int x){vector<bool>v;for(int j=0;j<10;j++)v.push_back(x>>j&1);for(auto g:m)v.push_back(g[0]==0?v[g[1]]&&v[g[2]]:g[0]==1?v[g[1]]||v[g[2]]:!v[g[1]]);return v.back();}
};
int main(int argc,char**argv){int cas=argc>1?atoi(argv[1]):0;int budget=argc>2?atoi(argv[2]):1800;int seed=argc>3?atoi(argv[3]):0;int maxnot=argc>4?atoi(argv[4]):3;Synth syn(19,cas,seed,maxnot);auto start=chrono::steady_clock::now();mt19937 rng(seed);for(int x=0;x<1024;x++)if(x==1023||__builtin_popcount((unsigned)x)<=2||!Synth::goal(x))syn.row(x);Timer t;syn.s.connect_terminator(&t);int it=0;while(chrono::steady_clock::now()-start<chrono::seconds(budget)){t.end=min(start+chrono::seconds(budget),chrono::steady_clock::now()+chrono::seconds(60));int r=syn.s.solve();cout<<"case "<<cas<<" round "<<it<<" rows "<<syn.rows.size()<<" result "<<r<<" time "<<chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now()-start).count()<<endl;if(r==20)return 0;if(r==0)continue;auto m=syn.model();cout<<"MODEL_BEGIN\n";for(auto g:m)cout<<g[0]<<" "<<g[1]<<" "<<g[2]<<"\n";cout<<"MODEL_END"<<endl;vector<int>bad;for(int x=0;x<1024;x++)if(syn.eval(m,x)!=Synth::goal(x))bad.push_back(x);cout<<"errors "<<bad.size()<<endl;if(bad.empty()){cout<<"FOUND\n";for(auto g:m)cout<<g[0]<<" "<<g[1]<<" "<<g[2]<<"\n";return 10;}shuffle(bad.begin(),bad.end(),rng);for(int i=0;i<min((int)bad.size(),32);i++)syn.row(bad[i]);it++;}return 1;}
