#include <gmpxx.h>
#include <vector>
#include <iostream>
#include <fstream>
#include <stdexcept>
using Q=mpq_class;
using Poly=std::vector<Q>;
void trim(Poly& p){while(!p.empty() && p.back()==0)p.pop_back();}
Poly add(Poly a,const Poly& b,Q factor=1){if(a.size()<b.size())a.resize(b.size());for(size_t i=0;i<b.size();++i)a[i]+=factor*b[i];trim(a);return a;}
Poly mul(const Poly& a,const Poly& b){if(a.empty()||b.empty())return{};Poly r(a.size()+b.size()-1);for(size_t i=0;i<a.size();++i)for(size_t j=0;j<b.size();++j)r[i+j]+=a[i]*b[j];trim(r);return r;}
std::pair<Poly,Poly> divrem(Poly a,const Poly& b){if(b.empty())throw std::runtime_error("zero divisor");Poly q(a.size()>=b.size()?a.size()-b.size()+1:0);while(a.size()>=b.size()&&!a.empty()){size_t d=a.size()-b.size();Q c=a.back()/b.back();q[d]+=c;for(size_t j=0;j<b.size();++j)a[d+j]-=c*b[j];trim(a);}trim(q);return{q,a};}
Poly read(std::istream& in){size_t n; if(!(in>>n)||n>10000)throw std::runtime_error("invalid degree");Poly p(n);for(auto&c:p){mpz_class a,b;if(!(in>>a>>b)||b==0)throw std::runtime_error("invalid coefficient");c=Q(a,b);c.canonicalize();}trim(p);return p;}
void write(std::ostream& out,const Poly& p){out<<p.size()<<'\n';for(auto&c:p)out<<c.get_num()<<' '<<c.get_den()<<'\n';}
int main(int argc,char**argv){try{if(argc!=3)throw std::runtime_error("usage: input output");std::ifstream in(argv[1]);if(!in)throw std::runtime_error("input open");Poly f=read(in),g=read(in);std::string extra;if(in>>extra)throw std::runtime_error("extra input");Poly r0=f,r1=g,s0{Q(1)},s1,t0,t1{Q(1)};size_t steps=0;while(!r1.empty()){auto qr=divrem(r0,r1);Poly sn=add(s0,mul(qr.first,s1),-1),tn=add(t0,mul(qr.first,t1),-1);r0=std::move(r1);r1=std::move(qr.second);s0=std::move(s1);s1=std::move(sn);t0=std::move(t1);t1=std::move(tn);std::cerr<<"step "<<++steps<<" remainder_degree "<<(r1.empty()?-1:(long)r1.size()-1)<<'\n';}
if(r0.size()!=1)throw std::runtime_error("not coprime");Q c=r0[0];for(auto&x:s0)x/=c;for(auto&x:t0)x/=c;if(add(mul(s0,f),mul(t0,g))!=Poly{Q(1)})throw std::runtime_error("identity failure");std::ofstream out(argv[2]);if(!out)throw std::runtime_error("output open");write(out,s0);write(out,t0);if(!out)throw std::runtime_error("output failure");std::cerr<<"VERIFIED_BEZOUT "<<s0.size()<<' '<<t0.size()<<'\n';return 0;}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
