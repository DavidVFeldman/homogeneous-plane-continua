/* probe59c.c -- batch 59, question 1, third pass: are the index bounds of the
 * landmark sentence load-bearing?
 *
 * The same sentence as probe59.c, but with every index bound of the landmark
 * chain weakened to "strictly later" (idx = 0): the levels are still asked for,
 * in order, but not the gaps the walk's own positions dictate.  Random
 * 1-Lipschitz arms of the band [0,9] at every parameter set of the window.
 *
 * Usage: probe59c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXW 128
static int W[MAXW], WL;
static int buildWalk4(int *w,int start,int a,int b,int c,int e){int len=0,cur=start;w[len++]=cur;int t[4]={a,b,c,e};
 for(int q=0;q<4;q++){if(t[q]==cur)return -1;int s=t[q]>cur?1:-1;while(cur!=t[q]){cur+=s;if(len>=MAXW)return -1;w[len++]=cur;}}return len;}
static int folds(const int*f,int m){char cur[MAXW],nxt[MAXW];for(int u=0;u<WL;u++)cur[u]=0;
 if(f[0]-W[0]>1||W[0]-f[0]>1)return 0;cur[0]=1;
 for(int j=1;j<m;j++){int any=0;for(int u=0;u<WL;u++)nxt[u]=0;
  for(int u=0;u<WL;u++){if(!cur[u])continue;for(int e=-1;e<=1;e++){int u2=u+e;if(u2<0||u2>=WL)continue;int d=f[j]-W[u2];if(d<=1&&d>=-1){nxt[u2]=1;any=1;}}}
  if(!any)return 0;memcpy(cur,nxt,WL);}return 1;}
static int land(const int*f,int m,int K,int M,int P,int idx){const int H=9;int A=K-P+1;
 if(f[0]<P-2||f[0]>P)return 0;
 int t1=-1,t2=-1,t3=-1;
 for(int j=(idx?A:0);j<m;j++)if(f[j]>=K-1){t1=j;break;}
 if(t1>=0)for(int k=t1+(idx?(K-M):1);k<m;k++)if(f[k]<=M+1){t2=k;break;}
 if(t2>=0)for(int l=t2+(idx?(H-1-M):1);l<m;l++)if(f[l]>=H-2){t3=l;break;}
 for(int d=0;d<m;d++){
  if(f[d]<=P-3&&(t1<0||t1+(idx?(K-1-f[d]):1)>d))return 0;
  if(f[d]<=M-2&&(t3<0||t3+(idx?(H-2-f[d]):1)>d))return 0;
  if(f[d]>=K+2&&(t2<0||t2+(idx?(f[d]-M-1):1)>d))return 0;}
 return 1;}
static unsigned long long rs=12345;static unsigned long long rnd(void){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
int main(void){long bad=0,tested=0,shown=0;int f[200];
 for(int P=2;P<=6;P++)for(int K=(P>6?P:6);K<=8;K++)for(int M=1;M<=P-2;M++){if(M+3>K)continue;
  WL=buildWalk4(W,P-1,K,M,8,1);if(WL<0)continue;
  for(long r=0;r<200000;r++){int m=1+(int)(rnd()%40);f[0]=P-2+(int)(rnd()%3);if(f[0]<0)f[0]=0;if(f[0]>9)f[0]=9;
   for(int t=1;t<m;t++){int e=(int)(rnd()%3)-1;int v=f[t-1]+e;if(v<0||v>9)v=f[t-1];f[t]=v;}
   tested++;int fo=folds(f,m),l0=land(f,m,K,M,P,0);
   if(l0&&!fo){bad++;if(shown<3){shown++;printf("  no-index sentence holds, no fold, P%d K%d M%d:",P,K,M);for(int t=0;t<m;t++)printf(" %d",f[t]);printf("\n");}}}}
 printf("tested %ld; the sentence without its index bounds holds without the fold at %ld\n",tested,bad);return 0;}
