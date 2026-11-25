#include <bits/stdc++.h>
#include <immintrin.h>
using namespace std;
using U=uint32_t;
array<U,128> kept,offset;
vector<unsigned char> cost;
array<vector<U>,14> layer;
U target;
size_t operations=0;
static U compress(U a,U mask){
#if defined(__BMI2__)
 return _pext_u32(a,mask);
#else
 U r=0,b=1;while(mask){U k=mask&-mask;if(a&k)r|=b;b<<=1;mask^=k;}return r;
#endif
}
static size_t ix(U a){U s=a&127;return offset[s]+compress(a>>7,kept[s]);}
void save(const string&file,int c,int i,size_t a){
 ofstream f(file,ios::binary);f.write((char*)&c,sizeof(c));f.write((char*)&i,sizeof(i));f.write((char*)&a,sizeof(a));
 size_t z=cost.size();f.write((char*)&z,sizeof(z));f.write((char*)cost.data(),z);
 for(auto &v:layer){z=v.size();f.write((char*)&z,sizeof(z));f.write((char*)v.data(),z*sizeof(U));}
}
bool load(const string&file,int&c,int&i,size_t&a){
 ifstream f(file,ios::binary);if(!f)return false;f.read((char*)&c,sizeof(c));f.read((char*)&i,sizeof(i));f.read((char*)&a,sizeof(a));
 size_t z;f.read((char*)&z,sizeof(z));cost.resize(z);f.read((char*)cost.data(),z);
 for(auto&v:layer){f.read((char*)&z,sizeof(z));v.resize(z);f.read((char*)v.data(),z*sizeof(U));}
 return bool(f);
}
int main(int argc,char**argv){
 string file=argc>1?argv[1]:"full-formula.checkpoint";
 int c=1,ii=0;size_t aa=0;U vars[7]={};U total=0;
 vector<pair<int,int>> pairs;for(int i=0;i<7;i++)for(int j=i+1;j<7;j++)pairs.push_back({i,j});
 vector<pair<int,int>> E={{0,2},{1,3},{0,4},{1,4},{2,4},{0,5},{1,5},{3,5},{0,6},{2,6},{3,6},{5,6}};
 for(int s=0;s<128;s++){
  U mask=0;for(int k=0;k<21;k++){auto [i,j]=pairs[k];if(!(s>>i&1)&&!(s>>j&1))mask|=1U<<k;}
  kept[s]=mask;offset[s]=total;total+=1U<<__builtin_popcount(mask);
 }
 for(int i=0;i<7;i++){vars[i]=1U<<i;for(int k=0;k<21;k++)if(pairs[k].first==i||pairs[k].second==i)vars[i]|=1U<<(7+k);}
 for(auto e:E){int k=find(pairs.begin(),pairs.end(),e)-pairs.begin();target|=1U<<(7+k);}
 if(!load(file,c,ii,aa)){
  cost.assign(total,255);
  for(U x:vars){cost[ix(x)]=0;layer[0].push_back(x);}
  for(U x:{0U,(1U<<28)-1}){cost[ix(x)]=0;layer[0].push_back(x);}
 }
 cout<<"states "<<total<<" start cost "<<c<<" pair "<<ii<<" a "<<aa<<" targetcost "<<int(cost[ix(target)])<<endl;
 auto start=chrono::steady_clock::now();
 for(;c<=13;c++,ii=0,aa=0){
  for(int i=ii;i<=(c-1)/2;i++,aa=0){
   int j=c-1-i;
   const auto&A=layer[i];const auto&B=layer[j];
   for(size_t a=aa;a<A.size();a++){
    U x=A[a];size_t end=i==j?a+1:B.size();
    for(size_t b=0;b<end;b++){
     U y=B[b];U u=x&y;size_t k=ix(u);if(cost[k]==255){cost[k]=c;layer[c].push_back(u);}
     u=x|y;k=ix(u);if(cost[k]==255){cost[k]=c;layer[c].push_back(u);}
    }
    operations+=2*end;
    if((a&63)==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>550){
     save(file,c,i,a+1);cout<<"CHECKPOINT cost "<<c<<" pair "<<i<<","<<j<<" a "<<a+1<<"/"<<A.size()<<" new "<<layer[c].size()<<" operations "<<operations<<" targetcost "<<int(cost[ix(target)])<<endl;return 0;
    }
   }
  }
  cout<<"COMPLETE cost "<<c<<" layer "<<layer[c].size()<<" operations "<<operations<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<" targetcost "<<int(cost[ix(target)])<<endl;
  save(file,c+1,0,0);
  if(cost[ix(target)]!=255){cout<<"TARGET MINIMUM "<<int(cost[ix(target)])<<endl;return 0;}
 }
 cout<<"TARGET LOWER 14"<<endl;
}
