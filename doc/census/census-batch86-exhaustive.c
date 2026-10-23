#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 24
int n,K; int rho[MAXN], sig[MAXN];
int beta[MAXN]; int bmaxr[MAXN+2], bmins[MAXN+2];
int order[MAXN]; int endLow[MAXN], endHigh[MAXN];
int lowT[MAXN+2], highT[MAXN+2]; /* count of end-clause obligations at time */
static int ok_block(int u){
  if (bmaxr[u]-2 > bmins[u]) return 0;
  if (lowT[u] && bmaxr[u] > 2) return 0;
  if (highT[u] && bmins[u] < K-3) return 0;
  return 1;
}
long nodes;
int dfs(int pos){
  if(pos==n) return 1;
  nodes++;
  int t=order[pos]; int prev = (t>order[0])? t-1 : t+1;
  if(pos==0) prev=-1;
  int lo,hi;
  if(prev<0){lo=hi=0;} else {lo=beta[prev]-1; hi=beta[prev]+1; if(lo<0)lo=0;}
  for(int u=lo;u<=hi;u++){
    int or_=bmaxr[u], os=bmins[u];
    if(rho[t]>bmaxr[u]) bmaxr[u]=rho[t];
    if(sig[t]<bmins[u]) bmins[u]=sig[t];
    lowT[u]+=endLow[t]; highT[u]+=endHigh[t];
    beta[t]=u;
    if(ok_block(u) && dfs(pos+1)) return 1;
    lowT[u]-=endLow[t]; highT[u]-=endHigh[t];
    bmaxr[u]=or_; bmins[u]=os;
  }
  return 0;
}
int meets(int t,int j){ for(int u=t-1;u<=t+1;u++){ if(u<0||u>=n) continue; if(rho[u]<=j && j<=sig[u]) return 1;} return 0;}
int crooked(){
  for(int s=0;s<n;s++) for(int t=s+1;t<n;t++)
   for(int h=0;h<K;h++) for(int k=0;k<K;k++){
     if(abs(h-k)<3) continue;
     if(!meets(s,h)||!meets(t,k)) continue;
     int need1 = h<k? k-1: k+1, need2 = h<k? h+1: h-1;
     int found=0;
     for(int r=s+1;r<t && !found;r++) if(rho[r]<=need1&&need1<=sig[r])
       for(int r2=r+1;r2<t;r2++) if(rho[r2]<=need2&&need2<=sig[r2]){found=1;break;}
     if(!found) return 0;
   }
  return 1;
}
int check(int withEnd,int i){
  for(int u=0;u<=n+1;u++){bmaxr[u]=-100;bmins[u]=100;lowT[u]=0;highT[u]=0;}
  for(int t=0;t<n;t++){endLow[t]=endHigh[t]=0;}
  if(withEnd){ int e[2]={0,n-1}; for(int a=0;a<2;a++){int t=e[a]; if(meets(t,0)) endLow[t]=1; if(meets(t,K-1)) endHigh[t]=1;} }
  int p=0; order[p++]=i; for(int t=i+1;t<n;t++) order[p++]=t; for(int t=i-1;t>=0;t--) order[p++]=t;
  return dfs(0);
}
long cnt=0, fails=0, fail3=0;
void gen(int t){
  if(t==n){
    int mx=0; for(int a=0;a<n;a++) if(sig[a]>mx) mx=sig[a];
    if(mx+1!=K) return;
    int mn=100; for(int a=0;a<n;a++) if(rho[a]<mn) mn=rho[a]; if(mn!=0) return;
    if(!crooked()) return;
    cnt++;
    for(int i=0;i<n;i++){
      if(!check(0,i)){ fail3++; printf("THM3 FAIL?! i=%d\n",i); }
      else if(!check(1,i)){ fails++; if(fails<=20){ printf("ENDFAIL n=%d K=%d i=%d rho=",n,K,i); for(int a=0;a<n;a++)printf("%d",rho[a]); printf(" sig="); for(int a=0;a<n;a++)printf("%d",sig[a]); printf("\n"); fflush(stdout);} }
    }
    return;
  }
  for(int r=0;r<K;r++) for(int w=0;w<2;w++){
    int s=r+w; if(s>=K) continue;
    if(t>0){ int mx= s>sig[t-1]?s:sig[t-1]; int mn= r<rho[t-1]?r:rho[t-1]; if(mx>mn+1) continue; }
    rho[t]=r; sig[t]=s; gen(t+1);
  }
}
int main(int argc,char**argv){ n=atoi(argv[1]); K=atoi(argv[2]); gen(0); printf("n=%d K=%d crooked=%ld endfails=%ld thm3fails=%ld\n",n,K,cnt,fails,fail3); }
