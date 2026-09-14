#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
typedef int64_t GibInt; typedef int64_t GibInt64; typedef int32_t GibInt32;
typedef int16_t GibInt16; typedef int8_t GibInt8; typedef int64_t GibSym;
typedef char GibChar; typedef char GibBool; typedef float GibFloat;
typedef char* GibCursor;
#include "gib_simd_helpers.h"

static uint64_t rnd_s = 88172645463325252ULL;
static uint64_t rnd(void){rnd_s^=rnd_s<<13;rnd_s^=rnd_s>>7;rnd_s^=rnd_s<<17;return rnd_s;}

int main(void){
  long bad=0, n=0;
  /* --- Int8 x16: EXHAUSTIVE over all 256*256 operand pairs --- */
  for(int ai=-128; ai<128; ai++) for(int bi=-128; bi<128; bi++){
    int8_t av[16], bv[16], rv[16];
    for(int k=0;k<16;k++){av[k]=(int8_t)(ai+k); bv[k]=(int8_t)(bi-k);}
    __m128i A,B,R; memcpy(&A,av,16); memcpy(&B,bv,16);
    R=gib_vec_mul_int8x16(A,B); memcpy(rv,&R,16);
    for(int k=0;k<16;k++){ int8_t want=(int8_t)((uint8_t)av[k]*(uint8_t)bv[k]); n++;
      if(rv[k]!=want){ if(bad<5) printf("W8 MUL MISMATCH %d*%d got %d want %d\n",av[k],bv[k],rv[k],want); bad++; } }
    R=gib_vec_add_int8x16(A,B); memcpy(rv,&R,16);
    for(int k=0;k<16;k++){ int8_t want=(int8_t)((uint8_t)av[k]+(uint8_t)bv[k]); n++;
      if(rv[k]!=want){ if(bad<5) printf("W8 ADD MISMATCH\n"); bad++; } }
    R=gib_vec_gt_int8x16(A,B); memcpy(rv,&R,16);
    for(int k=0;k<16;k++){ int8_t want=(av[k]>bv[k])?-1:0; n++;
      if(rv[k]!=want){ if(bad<5) printf("W8 GT MISMATCH %d>%d got %d\n",av[k],bv[k],rv[k]); bad++; } }
    R=gib_vec_le_int8x16(A,B); memcpy(rv,&R,16);
    for(int k=0;k<16;k++){ int8_t want=(av[k]<=bv[k])?-1:0; n++;
      if(rv[k]!=want){ if(bad<5) printf("W8 LE MISMATCH\n"); bad++; } }
  }
  printf("Int8x16: %ld lane-checks, %ld bad\n", n, bad);
  /* --- Int16 x8 and Int32 x4: 4M random operand pairs each --- */
  long b16=0,b32=0,b64=0;
  for(long t=0;t<4000000;t++){
    int16_t av[8],bv[8],rv[8];
    for(int k=0;k<8;k++){av[k]=(int16_t)rnd(); bv[k]=(int16_t)rnd();}
    __m128i A,B,R; memcpy(&A,av,16); memcpy(&B,bv,16);
    R=gib_vec_mul_int16x8(A,B); memcpy(rv,&R,16);
    for(int k=0;k<8;k++){ int16_t want=(int16_t)((uint16_t)av[k]*(uint16_t)bv[k]);
      if(rv[k]!=want){ if(b16<5) printf("W16 MUL MISMATCH %d*%d got %d want %d\n",av[k],bv[k],rv[k],want); b16++; } }
    R=gib_vec_gt_int16x8(A,B); memcpy(rv,&R,16);
    for(int k=0;k<8;k++){ int16_t want=(av[k]>bv[k])?-1:0; if(rv[k]!=want){b16++;} }
    int32_t a4[4],b4[4],r4[4];
    for(int k=0;k<4;k++){a4[k]=(int32_t)rnd(); b4[k]=(int32_t)rnd();}
    memcpy(&A,a4,16); memcpy(&B,b4,16);
    R=gib_vec_mul_int32x4(A,B); memcpy(r4,&R,16);
    for(int k=0;k<4;k++){ int32_t want=(int32_t)((uint32_t)a4[k]*(uint32_t)b4[k]);
      if(r4[k]!=want){ if(b32<5) printf("W32 MUL MISMATCH %d*%d got %d want %d\n",a4[k],b4[k],r4[k],want); b32++; } }
    R=gib_vec_lt_int32x4(A,B); memcpy(r4,&R,16);
    for(int k=0;k<4;k++){ int32_t want=(a4[k]<b4[k])?-1:0; if(r4[k]!=want){b32++;} }
    int64_t a2[2],b2[2],r2[2];
    for(int k=0;k<2;k++){a2[k]=(int64_t)rnd(); b2[k]=(int64_t)rnd();}
    memcpy(&A,a2,16); memcpy(&B,b2,16);
    R=gib_vec_mul_int64x2(A,B); memcpy(r2,&R,16);
    for(int k=0;k<2;k++){ int64_t want=(int64_t)((uint64_t)a2[k]*(uint64_t)b2[k]);
      if(r2[k]!=want){ if(b64<5) printf("W64 MUL MISMATCH got %lld want %lld\n",(long long)r2[k],(long long)want); b64++; } }
    R=gib_vec_eq_int64x2(A,B); memcpy(r2,&R,16);
    for(int k=0;k<2;k++){ int64_t want=(a2[k]==b2[k])?-1:0; if(r2[k]!=want){b64++;} }
  }
  printf("Int16x8 bad=%ld  Int32x4 bad=%ld  Int64x2 bad=%ld\n", b16,b32,b64);
  /* --- AVX2 vector-extension helpers: 2M random pairs at each width --- */
  long e8=0,e16=0,e32=0,e64=0;
  for(long t=0;t<2000000;t++){
    int8_t a32b[32],b32b[32],r32b[32];
    for(int k=0;k<32;k++){a32b[k]=(int8_t)rnd(); b32b[k]=(int8_t)rnd();}
    gib_v32i8 A8,B8,R8; memcpy(&A8,a32b,32); memcpy(&B8,b32b,32);
    R8=gib_vec_mul_int8x32(A8,B8); memcpy(r32b,&R8,32);
    for(int k=0;k<32;k++){ int8_t w=(int8_t)((uint8_t)a32b[k]*(uint8_t)b32b[k]); if(r32b[k]!=w){ if(e8<5) printf("AVX2 W8 MUL MISMATCH %d*%d got %d want %d\n",a32b[k],b32b[k],r32b[k],w); e8++; } }
    R8=gib_vec_ge_int8x32(A8,B8); memcpy(r32b,&R8,32);
    for(int k=0;k<32;k++){ int8_t w=(a32b[k]>=b32b[k])?-1:0; if(r32b[k]!=w){e8++;} }
    int16_t a16[16],b16v[16],r16[16];
    for(int k=0;k<16;k++){a16[k]=(int16_t)rnd(); b16v[k]=(int16_t)rnd();}
    gib_v16i16 A16,B16,R16; memcpy(&A16,a16,32); memcpy(&B16,b16v,32);
    R16=gib_vec_mul_int16x16(A16,B16); memcpy(r16,&R16,32);
    for(int k=0;k<16;k++){ int16_t w=(int16_t)((uint16_t)a16[k]*(uint16_t)b16v[k]); if(r16[k]!=w){e16++;} }
    int32_t a8[8],b8[8],r8[8];
    for(int k=0;k<8;k++){a8[k]=(int32_t)rnd(); b8[k]=(int32_t)rnd();}
    gib_v8i32 A32,B32,R32; memcpy(&A32,a8,32); memcpy(&B32,b8,32);
    R32=gib_vec_mul_int32x8(A32,B32); memcpy(r8,&R32,32);
    for(int k=0;k<8;k++){ int32_t w=(int32_t)((uint32_t)a8[k]*(uint32_t)b8[k]); if(r8[k]!=w){e32++;} }
    int64_t a4v[4],b4v[4],r4v[4];
    for(int k=0;k<4;k++){a4v[k]=(int64_t)rnd(); b4v[k]=(int64_t)rnd();}
    gib_v4i64 A64,B64,R64; memcpy(&A64,a4v,32); memcpy(&B64,b4v,32);
    R64=gib_vec_mul_int64x4(A64,B64); memcpy(r4v,&R64,32);
    for(int k=0;k<4;k++){ int64_t w=(int64_t)((uint64_t)a4v[k]*(uint64_t)b4v[k]); if(r4v[k]!=w){e64++;} }
  }
  printf("AVX2 bad: W8=%ld W16=%ld W32=%ld W64=%ld\n", e8,e16,e32,e64);
  printf("%s\n", (bad|b16|b32|b64|e8|e16|e32|e64) ? "FAILURES" : "ALL OK");
  return 0;
}
