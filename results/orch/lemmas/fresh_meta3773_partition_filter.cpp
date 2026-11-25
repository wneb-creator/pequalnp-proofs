#include <algorithm>
#include <array>
#include <cstdint>
#include <vector>
using namespace std;
namespace {
struct Join {array<int,24> father;explicit Join(int n){for(int i=0;i<n;i++)father[i]=i;} int root(int i){return father[i]==i?i:father[i]=root(father[i]);}void merge(int a,int b){father[root(a)]=root(b);} };
// In an OR at the root, a positive row must be served by one child; every
// row pair uniquely separable by one primitive forces that primitive's side.
bool can_split(const vector<vector<unsigned>>& sep,int n) {
 Join groups(n);for(auto& row:sep){int previous=-1;for(unsigned m:row)if(!(m&(m-1))){int bit=__builtin_ctz(m);if(previous>=0)groups.merge(previous,bit);previous=bit;}}
 array<unsigned,24> classes{};for(int i=0;i<n;i++)classes[groups.root(i)]|=1u<<i;vector<unsigned> parts;for(unsigned f:classes)if(f)parts.push_back(f);
 int count=parts.size();if(count>=13)return true;const unsigned full=(1u<<n)-1;vector<unsigned>sides(1<<(count-1));for(int x=1;x<int(sides.size());x++){sides[x]=sides[x&(x-1)]|parts[__builtin_ctz(x)];unsigned t=sides[x],u=full^t;bool good=true;for(auto& row:sep){bool left=true,right=true;for(unsigned m:row){left=left&&bool(t&m);right=right&&bool(u&m);if(!left&&!right)break;}if(!left&&!right){good=false;break;}}if(good)return true;}
 return false;
}
}
extern "C" int root_possible(int n,const uint64_t*f,uint64_t p,uint64_t q){
 if(!p||!q||n<=1)return 1;
 vector<vector<unsigned>>sep(__builtin_popcountll(p),vector<unsigned>(__builtin_popcountll(q)));vector<vector<unsigned>>dual(sep[0].size(),vector<unsigned>(sep.size()));
 int i=0;for(uint64_t x=p;x;x&=x-1,i++){int j=0;for(uint64_t y=q;y;y&=y-1,j++){unsigned m=0;for(int z=0;z<n;z++)if((f[z]&(x&-x))&&!(f[z]&(y&-y)))m|=1u<<z;if(!m)return 0;sep[i][j]=dual[j][i]=m;}}
 return can_split(sep,n)||can_split(dual,n);
}
