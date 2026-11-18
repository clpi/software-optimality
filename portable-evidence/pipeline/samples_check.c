/* C99 bridge verifies count, range and EOF. Summary is not a benchmark qualification. */
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
static int number(uint64_t *out) {
  char s[128], *end;
  if (!fgets(s, sizeof s, stdin)) return 0;
  size_t n = strlen(s);
  if (n == 0 || s[n-1] != '\n') return 0;
  for (size_t i=0; i<n-1; i++) if(s[i]<'0'||s[i]>'9') return 0;
  if(n==1) return 0;
  errno=0;
  uintmax_t v=strtoumax(s,&end,10);
  if(errno || *end!='\n' || v>UINT64_MAX) return 0;
  *out=(uint64_t)v; return 1;
}
int main(void) {
  uint64_t count,n,min=UINT64_MAX,max=0;
  if(!number(&count)) return 2;
  for(uint64_t i=0;i<count;i++) {
    if(!number(&n)) return 2;
    if(n<min) min=n;
    if(n>max) max=n;
  }
  if(getchar()!=EOF) return 2;
  if(count) printf("count=%"PRIu64" min_ns=%"PRIu64" max_ns=%"PRIu64"\n",count,min,max);
  else puts("count=0");
  return 0;
}
