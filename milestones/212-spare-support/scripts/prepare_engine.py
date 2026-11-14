"""Create a separate engine enforcing spare-capacity partner support."""
from pathlib import Path
H=Path(__file__).resolve().parents[1];P=H.parent/'209-slice-capacity'
def sub(s,a,b):
 if s.count(a)!=1:raise RuntimeError(a[:80])
 return s.replace(a,b)
c=(P/'scripts/history_solver.c').read_text()
c=sub(c,'static int pending_count;',r'''static int pending_count;
typedef struct {
  int count, outside_count, clique[NMAX], outside[NMAX];
  int partner_count[NMAX], partners[NMAX][NMAX];
  uint64_t words;
} SupportFamily;
static int family_count;
static SupportFamily families[2];
static uint64_t support_calls,support_removals,support_failures,saturated_budgets;
''')
c=sub(c,'    if (!altered) return 1;',r'''    for (int f=0;f<family_count;f++) {
      SupportFamily *family=&families[f];
      int spare=__builtin_popcountll(family->words)-family->count,forced_count=0;
      unsigned char forced[NMAX];uint64_t available[NMAX];
      support_calls++;
      for (int k=0;k<family->outside_count;k++) {
        available[k]=0;
        for (int j=0;j<family->partner_count[k];j++)
          available[k]|=domains[family->partners[k][j]];
        forced[k]=(domains[family->outside[k]]&available[k])==0;
        forced_count+=forced[k];
      }
      if (forced_count>spare) { support_failures++;return 0; }
      if (forced_count==spare) {
        saturated_budgets++;
        for (int k=0;k<family->outside_count;k++) if (!forced[k]) {
          int x=family->outside[k];uint64_t before=domains[x],kept=before&available[k];
          if (kept!=before) {
            uint64_t removed=(uint64_t)__builtin_popcountll(before^kept);
            domains[x]=kept;removals+=removed;support_removals+=removed;altered=1;
            if (!kept) { support_failures++;return 0; }
            changed(x);
          }
        }
      }
    }
    if (!altered) return 1;''')
c=sub(c,'  started=GetTickCount64();int result=visit(initial);',r'''  family_count=read_int();
  if (family_count<1 || family_count>2) fail("Invalid family count");
  for (int f=0;f<family_count;f++) {
    SupportFamily *family=&families[f];
    family->count=read_int();family->words=read_mask();family->outside_count=read_int();
    if (family->count<1 || family->count>__builtin_popcountll(family->words)
        || family->count>NMAX || (family->words&~allowed)
        || family->outside_count<0 || family->outside_count>NMAX) fail("Invalid family header");
    unsigned char chosen[NMAX]={0},outside[NMAX]={0};
    for (int k=0;k<family->count;k++) {
      int x=read_int();
      if (x<0 || x>=n || chosen[x] || (initial[x]&~family->words)) fail("Invalid family member");
      chosen[x]=1;family->clique[k]=x;
    }
    for (int k=0;k<family->outside_count;k++) {
      int x=read_int(),count=read_int();
      if (x<0 || x>=n || chosen[x] || outside[x] || count<0 || count>family->count
          || (initial[x]&~family->words)) fail("Invalid outside member");
      outside[x]=1;family->outside[k]=x;family->partner_count[k]=count;
      unsigned char partners[NMAX]={0};
      for (int j=0;j<count;j++) {
        int y=read_int();
        if (y<0 || y>=n || !chosen[y] || partners[y]) fail("Invalid support partner");
        partners[y]=1;family->partners[k][j]=y;
      }
    }
  }
  started=GetTickCount64();int result=visit(initial);''')
c=sub(c,'  puts("]}");return 0;',r'''  printf("],\"support_calls\":%" PRIu64 ",\"support_removals\":%" PRIu64 ",\"support_failures\":%" PRIu64 ",\"saturated_budgets\":%" PRIu64 "}\n",
    support_calls,support_removals,support_failures,saturated_budgets);return 0;''')
(H/'scripts/spare_solver.c').write_text(c,encoding='utf-8',newline='\n')
p=(H.parent/'211-subset-capacity/scripts/capacity_continue.py').read_text()
p=p.replace('capacity_solver','spare_solver').replace('all(i==23 for i in a.indices)','all(i==22 for i in a.indices)').replace('default=[23]','default=[22]')
p=p.replace('capacity-batch-','spare-batch-').replace('capacity-search-progress.json','spare-search-progress.json')
p=p.replace('Subset-capacity continuation from an explicit transferred frontier; native evidence.','Spare-capacity support continuation; explicit source model and native evidence.')
(H/'scripts/spare_continue.py').write_text(p,encoding='utf-8',newline='\n')
p=(H.parent/'211-subset-capacity/scripts/compile_capacity.py').read_text().replace('capacity_solver','spare_solver').replace('capacity-compiler','spare-compiler')
(H/'scripts/compile_spare.py').write_text(p,encoding='utf-8',newline='\n')
print('Prepared separate spare-support engine.')
