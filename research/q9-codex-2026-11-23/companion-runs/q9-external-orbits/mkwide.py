from pathlib import Path
r=Path(__file__).resolve().parent;s=(r/'orbit.cpp').read_text()
i=s.index(' if(typ==0)');j=s.index('if(typ==6)',i)
s=s[:i]+''' if(typ==0){for(int k=1;k<5;k++)tr(0,k);}
 if(typ==1){for(int k=1;k<6;k++)tr(0,k);}
 if(typ==2){for(int k=0;k<5;k++)sw(k,k+1);}
 if(typ==3){for(int k=0;k<4;k++)sw(k,k+1);tr(5,6);tr(5,7);}
 if(typ==4){for(int k=1;k<4;k++)tr(0,k);sw(4,5);sw(5,6);}
 if(typ==5){for(int k=1;k<5;k++)tr(0,k);sw(5,6);}
 '''+s[j:]
(r/'wide.cpp').write_text(s)

