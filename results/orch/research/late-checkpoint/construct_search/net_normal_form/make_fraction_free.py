from pathlib import Path
import itertools
p=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form')
for tag,ss,tt in [('10',1,0),('01',0,1),('11',1,1)]:
 lines=['ring R=0,(k,l,b,c,d,e),(dp(2),dp(4));','short=0;','option(redSB);',f'int s={ss};int t={tt};','poly a=1;poly f=-1-b-c-d-e;','poly E=a*b*c*d*e*f;','poly AA=a*f;poly BB=b*e;poly CC=c*d;','poly uu=a+f;poly vv=b+e;poly ww=c+d;poly pp=a-f;poly qq=b-e;poly rr=c-d;','poly delta=uu*(BB-CC)+vv*(CC-AA)+ww*(AA-BB);','poly RH=AA+BB+CC;poly TH=d*e*f+b*c*f+a*c*e+a*b*d;','ideal HI=std(ideal(RH,TH));','matrix H[4][4];']
 edges=list(itertools.combinations(range(4),2))
 for (i,j),v in zip(edges,['a','b','c','d','e','f']):lines.append(f'H[{i+1},{j+1}]={v};H[{j+1},{i+1}]={v};')
 lines+=['matrix One[4][1]=1,1,1,1;','matrix Rows=H*One;','matrix Tau[4][1]=d*e*f,b*c*f,a*c*e,a*b*d;','matrix Sigma[4][1]=a*b*c,a*d*e,b*d*f,c*e*f;','matrix D[4][1]=a*c*s+l,a*e*t+l,-d*f*s-b*f*t+l,l;','matrix Amat[4][4];matrix hvec[4][1];']
 for i in range(4):
  lines.append(f'Amat[{i+1},{i+1}]=Rows[{i+1},1]^2;')
  sums='+'.join(f'H[{j+1},{kk+1}]^2' for j,kk in edges if i not in [j,kk])
  lines.append(f'hvec[{i+1},1]=-(Rows[{i+1},1]^2)/2+({sums})/4;')
 for i,j in edges:
  kk,ll=[x for x in range(4) if x not in [i,j]]
  lines.append(f'Amat[{i+1},{j+1}]=Rows[{i+1},1]*Rows[{j+1},1]+(H[{kk+1},{ll+1}]^2)/2;Amat[{j+1},{i+1}]=Amat[{i+1},{j+1}];')
 lines+=['matrix Cmat[4][4];int ii;int jj;','for(ii=1;ii<=4;ii++){for(jj=1;jj<=4;jj++){Cmat[ii,jj]=-Amat[ii,jj]/2+(hvec[jj,1]-hvec[ii,1])/4;}}','matrix Raw=Cmat*D;for(ii=1;ii<=4;ii++){Raw[ii,1]=Sigma[ii,1]*Raw[ii,1];}','poly mean=(Raw[1,1]+Raw[2,1]+Raw[3,1]+Raw[4,1])/4;','matrix Kdiv[4][4];']
 for i,j in edges:
  kk,ll=[x for x in range(4) if x not in [i,j]];pm=[i,j,kk,ll];sign=(-1)**sum(pm[x]>pm[y] for x in range(4) for y in range(x+1,4))
  lines.append(f'Kdiv[{i+1},{j+1}]={sign}*Tau[{j+1},1]*(Tau[{kk+1},1]-Tau[{ll+1},1]);Kdiv[{j+1},{i+1}]=-({sign})*Tau[{i+1},1]*(Tau[{kk+1},1]-Tau[{ll+1},1]);')
 lines+=['matrix Nu=Raw-mean*One+k*Kdiv*D;','poly mx=(Nu[3,1]+Nu[4,1])/2;poly my=(Nu[2,1]+Nu[4,1])/2;poly mz=(Nu[2,1]+Nu[3,1])/2;','poly ER=E*(Rows[1,1]*D[1,1]+Rows[2,1]*D[2,1]+Rows[3,1]*D[3,1]+Rows[4,1]*D[4,1])/2;','poly EG=-E*(D[1,1]+D[2,1]+D[3,1]+D[4,1])/2-pp*mx-qq*my-rr*mz;','poly lx=-(vv-ww)*ER+(BB-CC)*EG;poly ly=(uu-ww)*ER-(AA-CC)*EG;poly lz=-lx-ly;','poly oa=a*(lx+delta*mx);poly ob=b*(ly+delta*my);poly oc=c*(lz+delta*mz);poly od=d*(lz-delta*mz);poly oe=e*(ly-delta*my);poly of=f*(lx-delta*mx);','matrix Diag=E*delta*D;','matrix ORows[4][1]=oa+ob+oc,oa+od+oe,ob+od+of,oc+oe+of;','poly traceD=Diag[1,1]+Diag[2,1]+Diag[3,1]+Diag[4,1];','poly Ro=oa*of+ob*oe+oc*od;','print("CHART_BUILT");','poly Q=4*Ro-(traceD^2)/2;for(ii=1;ii<=4;ii++){Q=Q-Diag[ii,1]^2-4*Diag[ii,1]*ORows[ii,1];}','poly Ttwo=a*ob*od+oa*b*od+oa*ob*d+a*oc*oe+oa*c*oe+oa*oc*e+b*oc*of+ob*c*of+ob*oc*f+d*oe*of+od*e*of+od*oe*f;','poly Ctwo=Diag[1,1]*Diag[2,1]*f+Diag[1,1]*Diag[3,1]*e+Diag[1,1]*Diag[4,1]*d+Diag[2,1]*Diag[3,1]*c+Diag[2,1]*Diag[4,1]*b+Diag[3,1]*Diag[4,1]*a+Ttwo;','for(ii=1;ii<=4;ii++){Ctwo=Ctwo+Diag[ii,1]*Rows[ii,1]*ORows[ii,1];}Ctwo=2*Ctwo;','print("RAW_TERM_COUNTS");size(Q);size(Ctwo);','Q=reduce(Q,HI);Ctwo=reduce(Ctwo,HI);','print("REDUCED_TERM_COUNTS");size(Q);size(Ctwo);','ideal GF=b,c,d,e,f,delta;','proc strip(poly v){int index;int count;poly rem;matrix quot;for(index=1;index<=6;index++){count=0;while(v!=0 && count<40){rem=reduce(v,std(ideal(GF[index])));if(rem!=0){break;}quot=lift(ideal(GF[index]),ideal(v));v=quot[1,1];count++;}print("STRIPPED_GUARD_FACTOR");index;count;}return(cleardenom(v));}','Q=strip(Q);Ctwo=strip(Ctwo);','print("FINAL_TERM_COUNTS");size(Q);size(Ctwo);','print("DEGREES");deg(Q);deg(Ctwo);','if(size(Q)<=5000 && size(Ctwo)<=5000){print("EQUATION_Q");print(string(Q));print("EQUATION_C");print(string(Ctwo));}else{print("EXPORT_TOO_LARGE");}','print("HOLLOW_QUADRATIC");print(string(RH));print("HOLLOW_CUBIC");print(string(TH));print("GUARD");print(string(b*c*d*e*f*delta));','print("DONE");quit;']
 (p/f'fraction-free-{tag}.sing').write_text('\n'.join(lines)+'\n')
print('fraction-free source scripts written',flush=True)
