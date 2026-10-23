#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 4000
int n,K; int rho[MAXN], sig[MAXN];
int beta[MAXN]; int bmaxr[MAXN+2], bmins[MAXN+2];
int order[MAXN]; int endLow[MAXN], endHigh[MAXN];
int lowT[MAXN+2], highT[MAXN+2];
long nodes, LIMIT=50000000;
static int ok_block(int u){
  if (bmaxr[u]-2 > bmins[u]) return 0;
  if (lowT[u] && bmaxr[u] > 2) return 0;
  if (highT[u] && bmins[u] < K-3) return 0;
  return 1;
}
int dfs(int pos){
  if(pos==n) return 1;
  if(++nodes>LIMIT) return -1;
  int t=order[pos]; int prev = (t>order[0])? t-1 : t+1;
  int lo,hi;
  if(pos==0){lo=hi=0;} else {lo=beta[prev]-1; hi=beta[prev]+1; if(lo<0)lo=0;}
  for(int u=lo;u<=hi;u++){
    int or_=bmaxr[u], os=bmins[u];
    if(rho[t]>bmaxr[u]) bmaxr[u]=rho[t];
    if(sig[t]<bmins[u]) bmins[u]=sig[t];
    lowT[u]+=endLow[t]; highT[u]+=endHigh[t];
    beta[t]=u;
    if(ok_block(u)){ int r=dfs(pos+1); if(r!=0) return r; }
    lowT[u]-=endLow[t]; highT[u]-=endHigh[t];
    bmaxr[u]=or_; bmins[u]=os;
  }
  return 0;
}
int meets(int t,int j){ for(int u=t-1;u<=t+1;u++){ if(u<0||u>=n) continue; if(rho[u]<=j && j<=sig[u]) return 1;} return 0;}
int check(int withEnd,int i){
  for(int u=0;u<=n+1;u++){bmaxr[u]=-100;bmins[u]=100;lowT[u]=0;highT[u]=0;}
  for(int t=0;t<n;t++){endLow[t]=endHigh[t]=0;}
  if(withEnd){ int e[2]={0,n-1}; for(int a=0;a<2;a++){int t=e[a]; if(meets(t,0)) endLow[t]=1; if(meets(t,K-1)) endHigh[t]=1;} }
  int p=0; order[p++]=i; for(int t=i+1;t<n;t++) order[p++]=t; for(int t=i-1;t>=0;t--) order[p++]=t;
  nodes=0; return dfs(0);
}
typedef struct { int *v; int n; } Path;
static Path bpath(int a, int b) {
  Path p; int d = a < b ? b - a : a - b;
  if (d <= 2) { p.n = d + 1; p.v = malloc(sizeof(int) * p.n); int s = (a <= b) ? 1 : -1;
    for (int u = 0; u < p.n; u++) p.v[u] = a + s * u; return p; }
  int mid = (a < b) ? b - 1 : b + 1; int c = (a < b) ? a + 1 : a - 1;
  Path p1 = bpath(a, mid), p2 = bpath(mid, c), p3 = bpath(c, b);
  p.n = p1.n + p2.n - 1 + p3.n - 1; p.v = malloc(sizeof(int) * p.n);
  memcpy(p.v, p1.v, sizeof(int) * p1.n); memcpy(p.v + p1.n, p2.v + 1, sizeof(int) * (p2.n - 1));
  memcpy(p.v + p1.n + p2.n - 1, p3.v + 1, sizeof(int) * (p3.n - 1)); return p;
}
int main(int argc,char**argv){
  int KK=atoi(argv[1]);
  Path P=bpath(0,KK-1);
  printf("len %d\n",P.n);
  long tested=0,fails=0,unk=0;
  for(int l=0;l<P.n;l++) for(int r=l+2;r<P.n;r++){
    n=r-l+1; int mn=100,mx=-1;
    for(int t=0;t<n;t++){rho[t]=sig[t]=P.v[l+t]; if(rho[t]<mn)mn=rho[t]; if(sig[t]>mx)mx=sig[t];}
    for(int t=0;t<n;t++){rho[t]-=mn;sig[t]-=mn;} K=mx-mn+1; if(K<5) continue;
    if(!(meets(0,0)||meets(0,K-1)||meets(n-1,0)||meets(n-1,K-1))) continue;
    for(int i=1;i<n-1;i++){ tested++;
      int c=check(1,i);
      if(c==0){ fails++; if(fails<10){printf("FAIL l=%d r=%d i=%d K=%d: ",l,r,i,K); for(int t=0;t<n;t++)printf("%d",rho[t]); printf("\n");}}
      if(c<0) unk++;
    }
  }
  printf("K=%d tested=%ld fails=%ld unknown=%ld\n",KK,tested,fails,unk);
}
