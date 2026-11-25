#include <gmpxx.h>
#include <fstream>
#include <string>
#include <cstddef>
int main(int argc,char**argv){
 if(argc!=3)return 2;std::ifstream in(argv[1]);std::ofstream out(argv[2]);std::size_t count;std::string token;if(!(in>>count>>token)||count>100000)return 3;mpz_class modulus;if(modulus.set_str(token,0)!=0||modulus<2)return 4;mpz_class half=modulus/2,bound;mpz_sqrt(bound.get_mpz_t(),half.get_mpz_t());out<<"{\"fractions\":[";
 for(std::size_t i=0;i<count;i++){
  if(!(in>>token))return 5;mpz_class a;if(a.set_str(token,0)!=0||a<0||a>=modulus)return 6;if(i)out<<",";
  if(a==0){out<<"[\"0\",\"1\"]";continue;}
  mpz_class r0=modulus,r1=a,t0=0,t1=1;
  while(abs(r1)>bound){mpz_class q=r0/r1;mpz_class r=r0-q*r1,t=t0-q*t1;r0=r1;r1=r;t0=t1;t1=t;}
  if(t1<0){r1=-r1;t1=-t1;}mpz_class gcd;mpz_gcd(gcd.get_mpz_t(),r1.get_mpz_t(),t1.get_mpz_t());mpz_class congruence=r1-a*t1;
  if(t1>0&&t1<=bound&&gcd==1&&mpz_divisible_p(congruence.get_mpz_t(),modulus.get_mpz_t()))out<<"[\""<<r1.get_str(16)<<"\",\""<<t1.get_str(16)<<"\"]";else out<<"null";
 }
 if(in>>token)return 7;out<<"]}\n";return out?0:8;
}
