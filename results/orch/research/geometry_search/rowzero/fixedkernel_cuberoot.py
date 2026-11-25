import itertools
import sympy as S

om=S.symbols('om')
a,b,c,e,k=S.symbols('a b c e k')
u=S.Matrix([1,om,-1-om,0])
w=S.Matrix([1,1,1,-3])
one=S.ones(4,1)
T=a*u*u.T+b*(u*w.T+w*u.T)+c*(u*one.T+one*u.T)+e*(k*w*w.T+w*one.T+one*w.T)
T=T.applyfunc(lambda v:S.rem(S.expand(v),om**2+om+1,om))
f=0
for rows in itertools.combinations(range(4),3):
    for cols in itertools.combinations(range(4),3):
        f+=sum(S.prod(T[rows[i],cols[pm[i]]] for i in range(3)) for pm in itertools.permutations(range(3)))
f=S.rem(S.rem(S.expand(f),om**2+om+1,om),k**2-2,k)
expected=6*(a**3+8*(c-2*b)*(c+b)**2+(320+224*k)*e**3)
assert S.expand(f-expected)==0
print('Cubic:',S.factor(f))
print('Verified exact identity modulo om^2+om+1=0 and k^2=2.')
print('With p=c+b and q=c-2b, divide by6: a^3+8*p^2*q+(320+224*k)*e^3.')
print('No linear factor: factor involvingq leaves a^3 after substitution;')
print('factor independentq must divide bothp^2 and a^3+(320+224*k)*e^3.')
