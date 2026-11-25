#include <gmp.h>
#include <stdint.h>
#include <stdio.h>
#include <assert.h>
typedef uint32_t len_t;
typedef uint32_t hi_t;
static unsigned calls;
static mpz_t logged_num,logged_den;
static void ct_scale(const void *row,mpz_srcptr num,mpz_srcptr den) {
 assert(row);calls++;mpz_set(logged_num,num);mpz_set(logged_den,den);
}
static void ct_primitive_dense_row(mpz_t *dense,mpz_t *retained,len_t retained_count,
                                   hi_t first,hi_t end) {
    mpz_t content;
    mpz_init_set_ui(content,0);
    for (len_t j=0;j<retained_count && mpz_cmp_ui(content,1)!=0;j++) {
        if (mpz_sgn(retained[j])) mpz_gcd(content,content,retained[j]);
    }
    for (hi_t j=first;j<end && mpz_cmp_ui(content,1)!=0;j++) {
        if (mpz_sgn(dense[j])) mpz_gcd(content,content,dense[j]);
    }
    if (mpz_cmp_ui(content,1)>0) {
        for (len_t j=0;j<retained_count;j++) mpz_divexact(retained[j],retained[j],content);
        for (hi_t j=first;j<end;j++) {
            if (mpz_sgn(dense[j])) mpz_divexact(dense[j],dense[j],content);
        }
        mpz_t one;mpz_init_set_ui(one,1);
        ct_scale(dense,one,content);
        mpz_clear(one);
    }
    mpz_clear(content);
}

int main(void) {
 mpz_t dense[12],retained[8],before_dense[12],before_retained[8],content,expected;
 mpz_inits(logged_num,logged_den,content,expected,NULL);
 for(int i=0;i<12;i++) {mpz_init(dense[i]);mpz_init(before_dense[i]);}
 for(int i=0;i<8;i++) {mpz_init(retained[i]);mpz_init(before_retained[i]);}
 unsigned checked=0;
 for(unsigned count=0;count<=8;count++) for(unsigned first=0;first<=12;first++)
 for(unsigned sample=0;sample<64;sample++) {
   unsigned factor=1+(sample%11);
   for(unsigned i=0;i<12;i++) {
     long value=sample==0?0:((long)((sample*17+i*29)%13)-6)*(long)factor;
     mpz_set_si(dense[i],value);mpz_set(before_dense[i],dense[i]);
   }
   for(unsigned i=0;i<8;i++) {
     long value=sample==0?0:((long)((sample*23+i*7)%9)-4)*(long)factor;
     mpz_set_si(retained[i],value);mpz_set(before_retained[i],retained[i]);
   }
   mpz_set_ui(content,0);
   for(unsigned i=0;i<count;i++)mpz_gcd(content,content,retained[i]);
   for(unsigned i=first;i<12;i++)mpz_gcd(content,content,dense[i]);
   calls=0;ct_primitive_dense_row(dense,count?retained:NULL,count,first,12);
   unsigned scaling=mpz_cmp_ui(content,1)>0;
   assert(calls==scaling);
   if(scaling) {assert(mpz_cmp_ui(logged_num,1)==0);assert(mpz_cmp(logged_den,content)==0);}
   for(unsigned i=0;i<12;i++) {
     mpz_set(expected,before_dense[i]);
     if(scaling && i>=first)mpz_divexact(expected,expected,content);
     assert(mpz_cmp(dense[i],expected)==0);
   }
   for(unsigned i=0;i<8;i++) {
     mpz_set(expected,before_retained[i]);
     if(scaling && i<count)mpz_divexact(expected,expected,content);
     assert(mpz_cmp(retained[i],expected)==0);
   }
   checked++;
 }
 for(int i=0;i<12;i++) {mpz_clear(dense[i]);mpz_clear(before_dense[i]);}
 for(int i=0;i<8;i++) {mpz_clear(retained[i]);mpz_clear(before_retained[i]);}
 mpz_clears(logged_num,logged_den,content,expected,NULL);
 printf("PASS %u boundary/sign/zero/gcd cases; exact source function; explicit scale identity\n",checked);
 return 0;
}
