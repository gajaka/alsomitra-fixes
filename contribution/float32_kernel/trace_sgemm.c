/* Observation-only interposer, loaded in a dedicated subprocess.
   It records SGEMM arguments and forwards the operation without changing data. */
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>

typedef void (*sgemm_fn)(const char*, const char*, const int*, const int*, const int*,
                        const float*, const float*, const int*, const float*, const int*,
                        const float*, float*, const int*);
extern void sgemm_(const char*, const char*, const int*, const int*, const int*,
                   const float*, const float*, const int*, const float*, const int*,
                   const float*, float*, const int*);
static void traced_sgemm(const char *ta,const char *tb,const int *m,const int *n,const int *k,
                         const float *alpha,const float *a,const int *lda,const float *b,
                         const int *ldb,const float *beta,float *c,const int *ldc) {
    static sgemm_fn original;
    static _Thread_local int active;
    if (active) { fprintf(stderr,"PPG_TRACE_ERROR recursive interposition\n"); abort(); }
    active=1;
    if (!original) {
        /* References originating in the interposer image retain the original
           symbol binding; dlsym can return the interposed function on Darwin. */
        original=sgemm_;
        if (!original) { fprintf(stderr,"PPG_TRACE_ERROR missing original sgemm\n"); abort(); }
        Dl_info info;
        if (dladdr((void*)original,&info)) fprintf(stderr,"PPG_SGEMM_IMAGE %s\n",info.dli_fname);
    }
    fprintf(stderr,"PPG_SGEMM %c %c %d %d %d %d %d %d %.9g %.9g\n",
            *ta,*tb,*m,*n,*k,*lda,*ldb,*ldc,*alpha,*beta);
    original(ta,tb,m,n,k,alpha,a,lda,b,ldb,beta,c,ldc);
    active=0;
}
__attribute__((used)) static struct { const void *replacement; const void *replacee; }
interposition __attribute__((section("__DATA,__interpose"))) = {
    (const void*)traced_sgemm, (const void*)sgemm_
};
