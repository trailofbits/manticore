/* test_tweetnacl_scalarmult.c
 *
 *     Tests:
 *         TweetNacl scalar multiplication
 *         Modified example from: http://seb.dbzteam.org/blog/2014/04/28/tweetnacl_arithmetic_bug.html
 *
 *     Description:
 *         This is a test case that uses concolic execution
 *         in order to determine a scalar that results in
 *         carry mis-propagation in scalar multiplication by
 *         the base point in Curve25519
 *
 *     Results:
 *         5a22083abc7bdb6371f4e40a6e562b7d3fe3ba87131ab6e9feb341f909f3f581
 */
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#define FOR(i,n) for (i = 0;i < n;++i)
#define sv static void

typedef unsigned char u8;
typedef unsigned long u32;
typedef unsigned long long u64;
typedef long long i64;
typedef i64 gf[16];


static const u8
  _0[16],
  _9[32] = {9};
static const gf
  gf0,
  gf1 = {1},
  _121665 = {0xDB41,1};


static int fd = -1;

void randombytes(unsigned char *x, unsigned long long xlen)
{
  int i;

  if (fd == -1) {
    for (;;) {
      fd = open("/dev/urandom",O_RDONLY);
      if (fd != -1) break;
      sleep(1);
    }
  }

  while (xlen > 0) {
    if (xlen < 1048576) i = xlen; else i = 1048576;

    i = read(fd,x,i);
    if (i < 1) {
      sleep(1);
      continue;
    }

    x += i;
    xlen -= i;
  }
}


void hex_to_bytes(unsigned char *b, const unsigned char *s) {
  int i;

  unsigned char buf[3];
  buf[2] = '\0';

  for (i = 0; i < 32; ++i) {
    buf[0] = s[2*i];
    buf[1] = s[2*i+1];
    long h = strtol((const char *)buf, NULL, 16);
    b[i] = (unsigned char)h;
  }
}


static int vn(const u8 *x,const u8 *y,int n)
{
  u32 i,d = 0;
  FOR(i,n) d |= x[i]^y[i];
  return (1 & ((d - 1) >> 8)) - 1;
}

int crypto_verify_16(const u8 *x,const u8 *y)
{
  return vn(x,y,16);
}

int crypto_verify_32(const u8 *x,const u8 *y)
{
  return vn(x,y,32);
}

sv set25519(gf r, const gf a)
{
  int i;
  FOR(i,16) r[i]=a[i];
}

sv car25519(gf o)
{
  int i;
  i64 c;
  FOR(i,16) {
    o[i]+=(1LL<<16);
    c=o[i]>>16;
    o[(i+1)*(i<15)]+=c-1+37*(c-1)*(i==15);
    o[i]-=c<<16;
  }
}

sv sel25519(gf p,gf q,int b)
{
  i64 t,i,c=~(b-1);
  FOR(i,16) {
    t= c&(p[i]^q[i]);
    p[i]^=t;
    q[i]^=t;
  }
}

static int pack25519(u8 *o,const gf n, int bug_opt)
{
  int i,j,b;
  gf m,t;

  if (bug_opt < 0 && n[15] >= 0xffff)
    return 1;

  FOR(i,16) t[i]=n[i];
  car25519(t);
  car25519(t);
  car25519(t);
  FOR(j,2) {
    m[0]=t[0]-0xffed;
    for(i=1;i<15;i++) {
      m[i]=t[i]-0xffff-((m[i-1]>>16)&1);
      m[i-1]&=0xffff;
    }
    m[15]=t[15]-0x7fff-((m[14]>>16)&1);
    if (bug_opt == 0)
      m[14]&=0xffff;
    b=(m[15]>>16)&1;
    m[15]&=0xffff;
    sel25519(t,m,1-b);
  }
  FOR(i,16) {
    o[2*i]=t[i]&0xff;
    o[2*i+1]=t[i]>>8;
  }
  return 0;
}

sv unpack25519(gf o, const u8 *n)
{
  int i;
  FOR(i,16) o[i]=n[2*i]+((i64)n[2*i+1]<<8);
  o[15]&=0x7fff;
}

sv A(gf o,const gf a,const gf b)
{
  int i;
  FOR(i,16) o[i]=a[i]+b[i];
}

sv Z(gf o,const gf a,const gf b)
{
  int i;
  FOR(i,16) o[i]=a[i]-b[i];
}

sv M(gf o,const gf a,const gf b)
{
  i64 i,j,t[31];
  FOR(i,31) t[i]=0;
  FOR(i,16) FOR(j,16) t[i+j]+=a[i]*b[j];
  FOR(i,15) t[i]+=38*t[i+16];
  FOR(i,16) o[i]=t[i];
  car25519(o);
  car25519(o);
}

sv S(gf o,const gf a)
{
  M(o,a,a);
}

sv inv25519(gf o,const gf i)
{
  gf c;
  int a;
  FOR(a,16) c[a]=i[a];
  for(a=253;a>=0;a--) {
    S(c,c);
    if(a!=2&&a!=4) M(c,c,i);
  }
  FOR(a,16) o[a]=c[a];
}

sv pow2523(gf o,const gf i)
{
  gf c;
  int a;
  FOR(a,16) c[a]=i[a];
  for(a=250;a>=0;a--) {
    S(c,c);
    if(a!=1) M(c,c,i);
  }
  FOR(a,16) o[a]=c[a];
}

int crypto_scalarmult(u8 *q,const u8 *n,const u8 *p, int bug_opt)
{
  u8 z[32];
  i64 x[96],r,i;
  gf a,b,c,d,e,f;
  FOR(i,31) z[i]=n[i];
  z[31]=(n[31]&127)|64;
  z[0]&=248;
  unpack25519(x,p);
  FOR(i,16) {
    b[i]=x[i];
    d[i]=a[i]=c[i]=0;
  }
  a[0]=d[0]=1;
  for(i=254;i>=0;--i) {
    r=(z[i>>3]>>(i&7))&1;
    sel25519(a,b,r);
    sel25519(c,d,r);
    A(e,a,c);
    Z(a,a,c);
    A(c,b,d);
    Z(b,b,d);
    S(d,e);
    S(f,a);
    M(a,c,a);
    M(c,b,e);
    A(e,a,c);
    Z(a,a,c);
    S(b,a);
    Z(c,d,f);
    M(a,c,_121665);
    A(a,a,d);
    M(c,c,a);
    M(a,d,f);
    M(d,b,x);
    S(b,e);
    sel25519(a,b,r);
    sel25519(c,d,r);
  }
  FOR(i,16) {
    x[i+32]=a[i];
    x[i+48]=c[i];
    x[i+64]=b[i];
    x[i+80]=d[i];
  }
  inv25519(x+48,x+48);
  M(x+32,x+32,x+48);
  return pack25519(q,x+32, bug_opt);
}

int crypto_scalarmult_base(u8 *q,const u8 *n, int bug_opt)
{
  return crypto_scalarmult(q,n,_9, bug_opt);
}

////////////////////////////////////////////////////////////////

void SANDSHREW_crypto_scalarmult_base(u8 *output, const u8 *input, int flag)
{
    crypto_scalarmult_base(output, input, flag);
}


int
main(int argc, char *argv[])
{
    unsigned char in[32];
    u8 out1[32];
    u8 out2[32];

    //hex_to_bytes(in, (unsigned char *) argv[1]);
    SANDSHREW_crypto_scalarmult_base(out1, argv[1], 1);
    SANDSHREW_crypto_scalarmult_base(out2, argv[1], 0);

    if (strcmp(out1, out2) != 0)
	    abort();
    return 0;
}
