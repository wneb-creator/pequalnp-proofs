#include "cadical-2.1.2.hpp"
#include <cstdio>
int main(){CaDiCaL::Solver s;s.set("quiet",1);s.add(1);s.add(2);s.add(0);std::printf("%s\n",s.signature());int a=s.solve();s.add(-1);s.add(0);int b=s.solve();s.add(-2);s.add(0);int c=s.solve();std::printf("%d %d %d\n",a,b,c);return !(a==10&&b==10&&c==20);}
