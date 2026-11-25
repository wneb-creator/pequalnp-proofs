#include <algorithm>
#include <cstdint>
extern "C" long long rectangle_dynamic(int nr, int nc, const long long* values,
                                       unsigned pmask, unsigned nmask) {
  if(nr<0 || nc<0 || nr>21 || nc>21) return -1;
  int p[21],n[21],np=0,nn=0;
  for(int i=0;i<nr;i++) if(pmask&(1u<<i)) p[np++]=i;
  for(int i=0;i<nc;i++) if(nmask&(1u<<i)) n[nn++]=i;
  if(!np || !nn) return 0;
  long long w[21][21],sums[21]={};
  int a=std::min(np,nn),b=std::max(np,nn);
  for(int i=0;i<a;i++) for(int j=0;j<b;j++)
    w[i][j]=np<=nn?values[p[i]*nc+n[j]]:values[p[j]*nc+n[i]];
  long long best=0; unsigned prev=0;
  for(unsigned mask=1;mask<(1u<<a);mask++) {
    unsigned gray=mask^(mask>>1),diff=gray^prev;
    int i=__builtin_ctz(diff),sign=(gray&diff)?1:-1;long long total=0;
    for(int j=0;j<b;j++) {sums[j]+=sign*w[i][j];total+=std::max(sums[j],0LL);}
    best=std::max(best,total);prev=gray;
  }
  return best;
}
