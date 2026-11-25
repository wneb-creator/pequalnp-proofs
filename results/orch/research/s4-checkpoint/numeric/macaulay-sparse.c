#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>

typedef struct { uint32_t row, col; int64_t value; } Entry;
typedef struct { uint32_t rows, cols; uint64_t nnz; Entry *e; uint64_t *offsets; } Matrix;
#ifdef FIXED_PRIME
#define prime ((uint64_t)(FIXED_PRIME))
static uint64_t state;
#else
static uint64_t prime, state;
#endif
static int64_t *acc;
static uint64_t *rowwork, *colwork, *wd, *dd;

static void read_exact(FILE *f, void *p, size_t size) {
    if (fread(p,size,1,f)!=1) { fprintf(stderr,"Truncated input\n"); exit(2); }
}
static uint64_t random_nonzero(void) {
    state^=state<<13; state^=state>>7; state^=state<<17;
    return state%(prime-1)+1;
}
static uint64_t inverse(uint64_t a) {
    int64_t r=(int64_t)prime,s=(int64_t)a,t=0,u=1;
    while(s) {
        int64_t q=r/s,next_r=r-q*s,next_t=t-q*u;
        r=s;s=next_r;t=u;u=next_t;
    }
    if(r!=1){fprintf(stderr,"Noninvertible field element\n");exit(2);}
    return t<0?(uint64_t)(t+(int64_t)prime):(uint64_t)t;
}
static uint64_t residue(int64_t x) {
    int64_t y=x%(int64_t)prime;
    return y<0 ? (uint64_t)(y+(int64_t)prime) : (uint64_t)y;
}
static void mul(const Matrix *a,const uint64_t *x,uint64_t *y,int transpose) {
    if (transpose) {
        memset(acc,0,(size_t)a->cols*sizeof(*acc));
        for(uint32_t i=0;i<a->rows;i++) {
            int64_t value=(int64_t)x[i];
            for(uint64_t k=a->offsets[i];k<a->offsets[i+1];k++) {
                Entry e=a->e[k];acc[e.col]+=e.value*value;
            }
        }
        for(uint32_t j=0;j<a->cols;j++)y[j]=residue(acc[j]);
    } else {
        for(uint32_t i=0;i<a->rows;i++) {
            int64_t value=0;
            for(uint64_t k=a->offsets[i];k<a->offsets[i+1];k++) {
                Entry e=a->e[k];value+=e.value*(int64_t)x[e.col];
            }
            y[i]=residue(value);
        }
    }
}
static void normal(const Matrix *a,const uint64_t *x,uint64_t *y) {
    for(uint32_t i=0;i<a->rows;i++)rowwork[i]=wd[i]*x[i]%prime;
    mul(a,rowwork,colwork,1);
    for(uint32_t j=0;j<a->cols;j++)colwork[j]=dd[j]*colwork[j]%prime;
    mul(a,colwork,y,0);
    for(uint32_t i=0;i<a->rows;i++)y[i]=wd[i]*y[i]%prime;
}
static uint64_t dot(const uint64_t *x,const uint64_t *y,uint32_t n) {
    __uint128_t value=0;
    for(uint32_t i=0;i<n;i++)value+=(__uint128_t)x[i]*y[i];
    return (uint64_t)(value%prime);
}
static int zero(const uint64_t *x,uint32_t n) {
    for(uint32_t i=0;i<n;i++)if(x[i])return 0;
    return 1;
}
int main(int argc,char **argv) {
    if(argc!=6) {
        fprintf(stderr,"Usage: macaulay-sparse matrix.bin prime constant-column seed witness.txt\n");
        return argc==2?0:2;
    }
#ifdef FIXED_PRIME
    if(strtoull(argv[2],NULL,10)!=prime)return 2;
#else
    prime=strtoull(argv[2],NULL,10);
#endif
    uint32_t target=(uint32_t)strtoul(argv[3],NULL,10);
    state=strtoull(argv[4],NULL,10);if(!state)state=1;
    if(prime<5 || prime>2147483647ULL)return 2;
    FILE *f=strcmp(argv[1],"-")==0?stdin:fopen(argv[1],"rb");if(!f){perror("input");return 2;}
    Matrix a;read_exact(f,&a.rows,4);read_exact(f,&a.cols,4);read_exact(f,&a.nnz,8);
    if(target>=a.cols)return 2;
    a.e=malloc(a.nnz*sizeof(Entry));if(!a.e)return 2;
    a.offsets=calloc((size_t)a.rows+1,sizeof(uint64_t));if(!a.offsets)return 2;
    int64_t *rowbound=calloc(a.rows,sizeof(int64_t)),*colbound=calloc(a.cols,sizeof(int64_t));
    for(uint64_t k=0;k<a.nnz;k++) {
        Entry *e=&a.e[k];read_exact(f,&e->row,4);read_exact(f,&e->col,4);read_exact(f,&e->value,8);
        if(e->row>=a.rows || e->col>=a.cols || e->value==INT64_MIN)return 2;
        if(k && e->row<a.e[k-1].row){fprintf(stderr,"Input rows must be grouped\n");return 2;}
        a.offsets[e->row+1]++;
        uint64_t v=e->value<0?(uint64_t)(-e->value):(uint64_t)e->value;
        if(v>1000000)return 2;
        rowbound[e->row]+=(int64_t)v;colbound[e->col]+=(int64_t)v;
    }
    if(fgetc(f)!=EOF)return 2;fclose(f);
    for(uint32_t i=0;i<a.rows;i++)a.offsets[i+1]+=a.offsets[i];
    for(uint32_t i=0;i<a.rows;i++)if((__uint128_t)rowbound[i]*(prime-1)>INT64_MAX)return 2;
    for(uint32_t i=0;i<a.cols;i++)if((__uint128_t)colbound[i]*(prime-1)>INT64_MAX)return 2;
    free(rowbound);free(colbound);
    uint32_t n=a.rows,m=a.cols,capacity=n>m?n:m;
    acc=calloc(capacity,sizeof(*acc));rowwork=calloc(n,sizeof(uint64_t));colwork=calloc(m,sizeof(uint64_t));
    wd=calloc(n,sizeof(uint64_t));dd=calloc(m,sizeof(uint64_t));
    uint64_t *x=calloc(n,sizeof(uint64_t)),*r=calloc(n,sizeof(uint64_t)),*p=calloc(n,sizeof(uint64_t)),*ap=calloc(n,sizeof(uint64_t));
    if(!acc||!rowwork||!colwork||!wd||!dd||!x||!r||!p||!ap)return 2;
    for(uint32_t i=0;i<n;i++)wd[i]=random_nonzero();
    for(uint32_t i=0;i<m;i++)dd[i]=random_nonzero();
    colwork[target]=dd[target];mul(&a,colwork,r,0);
    for(uint32_t i=0;i<n;i++)p[i]=r[i]=wd[i]*r[i]%prime;
    uint64_t rr=dot(r,r,n);uint32_t iterations=0;
    const char *verdict="iteration_limit";int solved=zero(r,n);
    clock_t start=clock();
    fprintf(stderr,"SPARSE rows=%u columns=%u nnz=%" PRIu64 " prime=%" PRIu64 "\n",n,m,a.nnz,prime);fflush(stderr);
    for(;!solved && iterations<n+4;iterations++) {
        if(rr==0){verdict="breakdown";break;}
        normal(&a,p,ap);uint64_t denominator=dot(p,ap,n);
        if(denominator==0){verdict="breakdown";break;}
        uint64_t alpha=rr*inverse(denominator)%prime;
        for(uint32_t i=0;i<n;i++) {
            x[i]=(x[i]+alpha*p[i]%prime)%prime;
            r[i]=(r[i]+prime-alpha*ap[i]%prime)%prime;
        }
        if(zero(r,n)){solved=1;iterations++;break;}
        uint64_t next=dot(r,r,n),beta=next*inverse(rr)%prime;
        for(uint32_t i=0;i<n;i++)p[i]=(r[i]+beta*p[i]%prime)%prime;
        rr=next;
        if((iterations+1)%100==0){fprintf(stderr,"iteration=%u cpu=%.3f\n",iterations+1,(double)(clock()-start)/CLOCKS_PER_SEC);fflush(stderr);}
    }
    uint32_t witness_length=0;uint64_t *witness=NULL;
    if(solved) {
        for(uint32_t i=0;i<n;i++)rowwork[i]=wd[i]*x[i]%prime;
        mul(&a,rowwork,colwork,1);
        int primal=1;
        for(uint32_t j=0;j<m;j++)if(colwork[j]!=(uint64_t)(j==target))primal=0;
        if(primal){verdict="primal";witness=rowwork;witness_length=n;}
        else {
            for(uint32_t j=0;j<m;j++)colwork[j]=dd[j]*((colwork[j]+prime-(uint64_t)(j==target))%prime)%prime;
            mul(&a,colwork,ap,0);
            if(zero(ap,n) && colwork[target]) {
                uint64_t scale=inverse(colwork[target]);
                for(uint32_t j=0;j<m;j++)colwork[j]=colwork[j]*scale%prime;
                mul(&a,colwork,ap,0);
                if(!zero(ap,n)||colwork[target]!=1){fprintf(stderr,"Dual verification failed\n");return 4;}
                verdict="dual";witness=colwork;witness_length=m;
            } else verdict="inconclusive_normal_solution";
        }
    }
    size_t support=0;
    if(witness) {
        FILE *out=fopen(argv[5],"w");if(!out){perror("witness");return 2;}
        for(uint32_t i=0;i<witness_length;i++)if(witness[i]){fprintf(out,"%u %" PRIu64 "\n",i,witness[i]);support++;}
        fclose(out);
    }
    struct rusage usage;getrusage(RUSAGE_SELF,&usage);
    printf("{\"verdict\":\"%s\",\"verified\":%s,\"rows\":%u,\"columns\":%u,\"prime\":%" PRIu64 ",\"iterations\":%u,\"support\":%zu,\"cpu_seconds\":%.6f,\"peak_rss_kib\":%ld}\n",verdict,witness?"true":"false",n,m,prime,iterations,support,(double)(clock()-start)/CLOCKS_PER_SEC,usage.ru_maxrss);
    free(a.e);free(a.offsets);free(acc);free(rowwork);free(colwork);free(wd);free(dd);free(x);free(r);free(p);free(ap);
    return 0;
}
