from pathlib import Path
exec(Path('fresh_exception_horner_review.py').read_text().split('fe=[2,3,5,6,7]')[0])
main=src.split('lemma raw_equations_impossible',1)[1];q=parse(re.search(r'\(hQ : (.*?)=0\)',main)[1]);n=lambda a:poly(a);qraw=(defs['raw0'],defs['raw1']);fac1=n('r*b2+b4');fac2=n('r*b2+b4-2*(r+1)*b5');m=n('(b0+b3+b5+2*(b1+b2+b4)+2)/16-b5');assert mul(fac1,fac2)==add(qraw[0],mul(m,qraw[1]));assert 'linear_combination he0-(b5-(b0+b3+b5+2*(b1+b2+b4)+2)/16)*he1' in main
sets=main.split('  · have he4 := h4')[1:];assert len(sets)==2
for tag,br,sg in zip(['plus','minus'],sets,[fac1,fac2]):
 for j in range(3):
  sub=br.split('    have hG'+str(j)+' : ',1)[1].split('      exact (mul_eq_zero.mp hh)',1)[0];D=int(re.search(r'have hh : \((\d+):ℂ\)',sub)[1]);row=re.search(r'        linear_combination (.*)',sub)[1].split(' + ');ws=[parse(a.rsplit('*',1)[0]) for a in row];assert [a.rsplit('*',1)[1] for a in row]==['he4','he1','hbranch','hQ'];g=defs[tag+'G'+str(j)];res={}
  for a,b in zip(ws,[defs['raw4'],defs['raw1'],sg,q]):res=add(res,mul(a,b))
  assert res==mul({z:D},g)
 assert 'exact h'+tag+' b3 b4 b5 r hg0 hg1 hg2 hg3 hg4 hQ' in br
 print('PASS',tag,'three actual-source pivot identities')
print('PASS actual raw factorization and all six pivot combinations exactly over Q. SHA256',hashlib.sha256(target.read_bytes()).hexdigest())
