// Backward multi-target trimming of an LRAT-style proof read in REVERSE line order (pipe through tac).
// mode lidrup: targets are all 'u' lines; mode lrat: target is the empty clause.
// Prints JSON: kept steps, their hints, target hints, inputs used, ...
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static uint8_t *mark; static size_t cap;
static void ensure(size_t id){ if(id>=cap){ size_t n=cap?cap:1<<20; while(n<=id) n*=2; mark=realloc(mark,n); memset(mark+cap,0,n-cap); cap=n; } }
static int is(size_t id){ return id<cap && mark[id]; }
static void setm(size_t id){ ensure(id); mark[id]=1; }
int main(int argc,char**argv){
  int lidrup = argc>1 && !strcmp(argv[1],"lidrup");
  long long ninput_orig = argc>2 ? atoll(argv[2]) : -1;
  static char buf[1<<24]; FILE *dump = argc>3 ? fopen(argv[3],"w") : NULL;
  long long steps=0,hints=0,targets=0,thints=0,inputs=0,neg=0,lemmas=0,lines=0,maxlen=0,tlits=0,wr=0,ilines=0,extra_in=0;
  int found_empty=0; int prev_i_marked=0;
  while(fgets(buf,sizeof buf,stdin)){
    lines++;
    char *p=buf; char *e;
    if(lidrup){
      char t=*p; if(t=='w'||t=='r') wr++;
      int pim=prev_i_marked; prev_i_marked=0; (void)pim;
      if(t=='u'){ if(dump) fputs(buf,dump); p++; targets++; if(pim) extra_in++;
        long long v; int nl=0; while(1){ v=strtoll(p,&e,10); p=e; if(v==0)break; nl++; }
        tlits+=nl;
        while(1){ v=strtoll(p,&e,10); if(e==p)break; p=e; if(v==0)break; if(v<0){neg++; v=-v;} setm(v); thints++; }
        continue; }
      if(t=='l'){ p++; lemmas++;
        long long id=strtoll(p,&e,10); p=e;
        int len=0; long long v; while(1){ v=strtoll(p,&e,10); p=e; if(v==0)break; len++; }
        if(!is(id)) continue;
        steps++; if(len>maxlen)maxlen=len; if(dump) fputs(buf,dump);
        while(1){ v=strtoll(p,&e,10); if(e==p)break; p=e; if(v==0)break; if(v<0){neg++; v=-v;} setm(v); hints++; }
        continue; }
      if(t=='i'){ p++; ilines++; long long id=strtoll(p,&e,10); if(is(id)){ inputs++; prev_i_marked=1; if(dump) fputs(buf,dump); } continue; }
      continue;
    } else {
      long long id=strtoll(p,&e,10); if(e==p) continue; p=e;
      while(*p==' ')p++;
      if(*p=='d') continue;
      lemmas++;
      int len=0; long long v; while(1){ v=strtoll(p,&e,10); p=e; if(v==0)break; len++; }
      if(len==0 && !found_empty){ found_empty=1; setm(id); }
      if(!is(id)) continue;
      steps++; if(len>maxlen)maxlen=len;
      while(1){ v=strtoll(p,&e,10); if(e==p)break; p=e; if(v==0)break; if(v<0){neg++; v=-v;} setm(v); hints++; }
    }
  }
  if(dump) fclose(dump);
  if(!lidrup && ninput_orig>=0){ for(long long i=1;i<=ninput_orig;i++) if(is(i)) inputs++; }
  printf("{\"steps\": %lld, \"step_hints\": %lld, \"targets\": %lld, \"target_hints\": %lld, \"hints\": %lld, \"target_lits\": %lld, \"inputs_used\": %lld, \"extra_inputs_used\": %lld, \"neg_hints\": %lld, \"lemmas_total\": %lld, \"lines\": %lld, \"weaken_restore\": %lld, \"max_len\": %lld}\n",
    steps,hints,targets,thints,hints+thints,tlits,inputs,extra_in,neg,lemmas,lines,wr,maxlen);
  return 0;
}
