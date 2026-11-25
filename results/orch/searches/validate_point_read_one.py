# Verify the one-point-occurrence abstract polynomial multiplication table.
terms=[(1,0),(0,1),(1,1)]
for a in range(8):
 for b in range(8):
  left={terms[i] for i in range(3) if a>>i&1}
  right={terms[i] for i in range(3) if b>>i&1}
  expected={(x[0]+y[0],min(1,x[1]+y[1])) for x in left for y in right if x[0]+y[0]<=1}
  bits=sum(1<<i for i,t in enumerate(terms) if t in expected)
  ab=(((a&1)<<1)|((a&4)>>1))&(b&2)
  ba=(a&2)&(((b&1)<<1)|((b&4)>>1))
  actual=(a&b&2)|((ab|ba)<<1)
  assert actual==bits,(a,b,actual,bits)
print('All64 state multiplication cases verified against exponent-pair convolution.')
