import re, sys, collections
txt=open(sys.argv[1]).read()
samples=txt.split('\n=== ')
selfc=collections.Counter(); incl=collections.Counter(); n=0; top3=collections.Counter()
def fn(line):
    m=re.match(r'#\d+\s+(?:0x[0-9a-f]+ in )?(.*?)( \(|$)', line)
    s=m.group(1) if m else line
    s=re.sub(r'std::__1::','',s)
    s=re.sub(r'<[^<>]*>','',s); s=re.sub(r'<[^<>]*>','',s); s=re.sub(r'<[^<>]*>','',s)
    return s[:90]
for smp in samples:
    for th in smp.split('\nThread ')[1:]:
        lines=[l for l in th.split('\n') if l.startswith('#')]
        if any('type_checker' in l for l in lines):
            n+=1
            fs=[fn(l) for l in lines]
            selfc[fs[0]]+=1
            for f in set(fs): incl[f]+=1
            # first kernel-level frame
            k=[f for f in fs if 'lean::' in f and 'hash' not in f][:2]
            top3[' < '.join(k)]+=1
print('samples in kernel', n)
print('--- self'); [print('%5.1f%% %s'%(100*c/n,f)) for f,c in selfc.most_common(25)]
print('--- incl'); [print('%5.1f%% %s'%(100*c/n,f)) for f,c in incl.most_common(45)]
print('--- first lean frames'); [print('%5.1f%% %s'%(100*c/n,f)) for f,c in top3.most_common(25)]
