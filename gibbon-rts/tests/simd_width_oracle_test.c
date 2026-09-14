/* Standalone differential test of Gibbon's emitted SIMD helpers against the
   Integer/two's-complement reference the RTS scalar helpers implement. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <xmmintrin.h>
#include <emmintrin.h>
#ifdef __SSE4_1__
#include <smmintrin.h>
#endif
typedef int8_t GibInt8; typedef int16_t GibInt16;
typedef int32_t GibInt32; typedef int64_t GibInt64;
typedef int64_t GibInt; typedef uint64_t GibSym;
typedef char GibChar; typedef bool GibBool; typedef float GibFloat;
typedef char* GibCursor;
/* Two's-complement scalar reference for the widths under test. */
#include "gib_simd_helpers.h"

static int fails = 0;
#define CHK(cond, fmt, ...) do { if(!(cond)) { if (fails < 20) printf("FAIL: " fmt "\n", __VA_ARGS__); fails++; } } while(0)

/* scalar oracle: wrap to N bits */
static int8_t  w8 (int64_t v){ uint64_t m=(uint64_t)v & 0xFFu;   return m<0x80u   ? (int8_t)m   : (int8_t)((int64_t)m-0x100); }
static int16_t w16(int64_t v){ uint64_t m=(uint64_t)v & 0xFFFFu; return m<0x8000u ? (int16_t)m  : (int16_t)((int64_t)m-0x10000); }
static int32_t w32(int64_t v){ uint64_t m=(uint64_t)v & 0xFFFFFFFFu; return m<0x80000000u ? (int32_t)m : (int32_t)((int64_t)m-0x100000000LL); }

static uint64_t rng = 88172645463325252ULL;
static uint64_t nx(void){ rng^=rng<<13; rng^=rng>>7; rng^=rng<<17; return rng; }

int main(void){
  /* ---- Int8 x16 : exhaustive mul/add/sub/cmp over all 256x256 byte pairs ---- */
  {
    int8_t A[16], B[16], R[16];
    for (int a = -128; a <= 127; a++) {
      for (int base = -128; base <= 127; base += 16) {
        for (int i=0;i<16;i++){ A[i]=(int8_t)a; B[i]=(int8_t)(base+i); }
        __m128i va=_mm_loadu_si128((const __m128i*)A), vb=_mm_loadu_si128((const __m128i*)B);
        _mm_storeu_si128((__m128i*)R, gib_vec_mul_int8x16(va,vb));
        for(int i=0;i<16;i++) CHK(R[i]==w8((int64_t)A[i]*(int64_t)B[i]), "i8 mul %d*%d got %d want %d", A[i],B[i],R[i],w8((int64_t)A[i]*(int64_t)B[i]));
        _mm_storeu_si128((__m128i*)R, gib_vec_add_int8x16(va,vb));
        for(int i=0;i<16;i++) CHK(R[i]==w8((int64_t)A[i]+(int64_t)B[i]), "i8 add %d+%d got %d want %d", A[i],B[i],R[i],w8((int64_t)A[i]+(int64_t)B[i]));
        _mm_storeu_si128((__m128i*)R, gib_vec_sub_int8x16(va,vb));
        for(int i=0;i<16;i++) CHK(R[i]==w8((int64_t)A[i]-(int64_t)B[i]), "i8 sub %d-%d got %d want %d", A[i],B[i],R[i],w8((int64_t)A[i]-(int64_t)B[i]));
        _mm_storeu_si128((__m128i*)R, gib_vec_lt_int8x16(va,vb));
        for(int i=0;i<16;i++) CHK(R[i]==(int8_t)((A[i]<B[i])?-1:0), "i8 lt %d<%d got %d", A[i],B[i],R[i]);
        _mm_storeu_si128((__m128i*)R, gib_vec_le_int8x16(va,vb));
        for(int i=0;i<16;i++) CHK(R[i]==(int8_t)((A[i]<=B[i])?-1:0), "i8 le %d<=%d got %d", A[i],B[i],R[i]);
        _mm_storeu_si128((__m128i*)R, gib_vec_ge_int8x16(va,vb));
        for(int i=0;i<16;i++) CHK(R[i]==(int8_t)((A[i]>=B[i])?-1:0), "i8 ge %d>=%d got %d", A[i],B[i],R[i]);
        _mm_storeu_si128((__m128i*)R, gib_vec_gt_int8x16(va,vb));
        for(int i=0;i<16;i++) CHK(R[i]==(int8_t)((A[i]>B[i])?-1:0), "i8 gt %d>%d got %d", A[i],B[i],R[i]);
      }
    }
    printf("int8x16 exhaustive done, fails=%d\n", fails);
  }
  /* ---- Int16 x8 randomized ---- */
  {
    int16_t A[8],B[8],R[8];
    for(long t=0;t<400000;t++){
      for(int i=0;i<8;i++){ A[i]=(int16_t)nx(); B[i]=(int16_t)nx(); }
      if(t<8){ A[0]=INT16_MIN; B[0]=-1; A[1]=INT16_MIN; B[1]=INT16_MIN; A[2]=INT16_MAX; B[2]=INT16_MAX; }
      __m128i va=_mm_loadu_si128((const __m128i*)A), vb=_mm_loadu_si128((const __m128i*)B);
      _mm_storeu_si128((__m128i*)R, gib_vec_mul_int16x8(va,vb));
      for(int i=0;i<8;i++) CHK(R[i]==w16((int64_t)A[i]*(int64_t)B[i]), "i16 mul %d*%d got %d want %d",A[i],B[i],R[i],w16((int64_t)A[i]*(int64_t)B[i]));
      _mm_storeu_si128((__m128i*)R, gib_vec_add_int16x8(va,vb));
      for(int i=0;i<8;i++) CHK(R[i]==w16((int64_t)A[i]+(int64_t)B[i]), "i16 add %d+%d got %d want %d",A[i],B[i],R[i],w16((int64_t)A[i]+(int64_t)B[i]));
      _mm_storeu_si128((__m128i*)R, gib_vec_sub_int16x8(va,vb));
      for(int i=0;i<8;i++) CHK(R[i]==w16((int64_t)A[i]-(int64_t)B[i]), "i16 sub got %d want %d",R[i],w16((int64_t)A[i]-(int64_t)B[i]),0);
      _mm_storeu_si128((__m128i*)R, gib_vec_lt_int16x8(va,vb));
      for(int i=0;i<8;i++) CHK(R[i]==(int16_t)((A[i]<B[i])?-1:0), "i16 lt %d<%d got %d",A[i],B[i],R[i]);
      _mm_storeu_si128((__m128i*)R, gib_vec_le_int16x8(va,vb));
      for(int i=0;i<8;i++) CHK(R[i]==(int16_t)((A[i]<=B[i])?-1:0), "i16 le %d<=%d got %d",A[i],B[i],R[i]);
      _mm_storeu_si128((__m128i*)R, gib_vec_ge_int16x8(va,vb));
      for(int i=0;i<8;i++) CHK(R[i]==(int16_t)((A[i]>=B[i])?-1:0), "i16 ge %d>=%d got %d",A[i],B[i],R[i]);
    }
    printf("int16x8 random done, fails=%d\n", fails);
  }
  /* ---- Int32 x4 randomized ---- */
  {
    int32_t A[4],B[4],R[4];
    for(long t=0;t<600000;t++){
      for(int i=0;i<4;i++){ A[i]=(int32_t)nx(); B[i]=(int32_t)nx(); }
      if(t<8){ A[0]=INT32_MIN; B[0]=-1; A[1]=INT32_MIN; B[1]=INT32_MIN; A[2]=INT32_MAX; B[2]=INT32_MAX; A[3]=-1; B[3]=-1; }
      __m128i va=_mm_loadu_si128((const __m128i*)A), vb=_mm_loadu_si128((const __m128i*)B);
      _mm_storeu_si128((__m128i*)R, gib_vec_mul_int32x4(va,vb));
      for(int i=0;i<4;i++) CHK(R[i]==w32((int64_t)A[i]*(int64_t)B[i]), "i32 mul %d*%d got %d want %d",A[i],B[i],R[i],w32((int64_t)A[i]*(int64_t)B[i]));
      _mm_storeu_si128((__m128i*)R, gib_vec_add_int32x4(va,vb));
      for(int i=0;i<4;i++) CHK(R[i]==w32((int64_t)A[i]+(int64_t)B[i]), "i32 add got %d want %d",R[i],w32((int64_t)A[i]+(int64_t)B[i]),0);
      _mm_storeu_si128((__m128i*)R, gib_vec_gt_int32x4(va,vb));
      for(int i=0;i<4;i++) CHK(R[i]==(int32_t)((A[i]>B[i])?-1:0), "i32 gt %d>%d got %d",A[i],B[i],R[i]);
      _mm_storeu_si128((__m128i*)R, gib_vec_le_int32x4(va,vb));
      for(int i=0;i<4;i++) CHK(R[i]==(int32_t)((A[i]<=B[i])?-1:0), "i32 le %d<=%d got %d",A[i],B[i],R[i]);
    }
    printf("int32x4 random done, fails=%d\n", fails);
  }
  /* ---- Int64 x2 randomized (mul/div/mod) ---- */
  {
    int64_t A[2],B[2],R[2];
    for(long t=0;t<400000;t++){
      for(int i=0;i<2;i++){ A[i]=(int64_t)nx(); B[i]=(int64_t)nx(); if(B[i]==0) B[i]=1; }
      if(t<4){ A[0]=INT64_MIN; B[0]=-1; }
      __m128i va=_mm_loadu_si128((const __m128i*)A), vb=_mm_loadu_si128((const __m128i*)B);
      _mm_storeu_si128((__m128i*)R, gib_vec_mul_int64x2(va,vb));
      for(int i=0;i<2;i++){ int64_t want=(int64_t)((uint64_t)A[i]*(uint64_t)B[i]);
        CHK(R[i]==want, "i64 mul %lld*%lld got %lld want %lld",(long long)A[i],(long long)B[i],(long long)R[i],(long long)want); }
      _mm_storeu_si128((__m128i*)R, gib_vec_add_int64x2(va,vb));
      for(int i=0;i<2;i++){ int64_t want=(int64_t)((uint64_t)A[i]+(uint64_t)B[i]);
        CHK(R[i]==want, "i64 add got %lld want %lld",(long long)R[i],(long long)want,0); }
      _mm_storeu_si128((__m128i*)R, gib_vec_div_int64x2(va,vb));
      for(int i=0;i<2;i++){ int64_t want = (B[i]==-1) ? (int64_t)(0-(uint64_t)A[i]) : A[i]/B[i];
        CHK(R[i]==want, "i64 div %lld/%lld got %lld want %lld",(long long)A[i],(long long)B[i],(long long)R[i],(long long)want); }
      _mm_storeu_si128((__m128i*)R, gib_vec_mod_int64x2(va,vb));
      for(int i=0;i<2;i++){ int64_t want = (B[i]==-1) ? 0 : A[i]%B[i];
        CHK(R[i]==want, "i64 mod %lld%%%lld got %lld want %lld",(long long)A[i],(long long)B[i],(long long)R[i],(long long)want); }
    }
    printf("int64x2 random done, fails=%d\n", fails);
  }
  printf("TOTAL FAILS = %d\n", fails);
  return fails ? 1 : 0;
}
