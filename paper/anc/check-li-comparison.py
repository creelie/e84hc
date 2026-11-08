"""Independent exact checks for the seven named comparison tuples, not a census."""
from collections import Counter
from itertools import combinations
from math import gcd,lcm
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
SEEDS=[(21,(1,4,9,15,16,18)),(33,(1,4,16,22,25,31)),
 (39,(1,7,16,22,34,37)),(39,(1,14,16,22,29,35)),
 (45,(1,19,20,28,30,37)),(105,(1,22,43,64,90,95)),(105,(3,24,50,66,85,87))]
def units(m):return [t for t in range(1,m) if gcd(t,m)==1]
def balanced(a,m):return all(x%m for x in a) and sum(a)%m==0 and all(sum(t*x%m for x in a)==len(a)*m//2 for t in units(m))
def inverse(a,m):return any((a[i]+a[j])%m==0 for i in range(len(a)) for j in range(i))
def canonical(a,m):return min(tuple(sorted(t*x%m for x in a)) for t in units(m))
def profile(a,m):return tuple(sorted((m//gcd(x,m) for x in a),reverse=True))
def positive(a,m):
 if inverse(a,m):return {'predicate':'inverse_pair'}
 for ids in combinations(range(1,6),2):
  chosen=(0,)+ids;other=tuple(i for i in range(6) if i not in chosen)
  b=tuple(a[i] for i in chosen);c=tuple(a[i] for i in other);k=sum(b)%m
  if k and balanced(b+((-k)%m,),m) and balanced((k,)+c,m):
   return {'predicate':'surface_contraction','triples':[b,c],'distinguished':k,'quadruples':[b+((-k)%m,),(k,)+c]}
 if m%5==0:
  for x in range(1,m//5):
   std=tuple(sorted([x+j*(m//5) for j in range(5)]+[(-5*x)%m]))
   if tuple(sorted(a))==std:return {'predicate':'exact_standard','x':x}
 return {'predicate':'residual'}
def moves(a,m):
 found=[]
 for p in range(3,m+1,2):
  if m%p or any(p%q==0 for q in range(2,p)):continue
  for x in range(1,m//p):
   phi=[x+j*(m//p) for j in range(p)];common=[v for v in phi if v in a]
   if 7+p-2*len(common)>6:continue
   rest=list(a)
   for v in common:rest.remove(v)
   out=tuple(sorted(rest+[(-v)%m for v in phi if v not in common]+[(p*x)%m]))
   if len(out)<=4 or profile(out,m)<profile(a,m):
    assert balanced(out,m)
    padding=[v for y in phi if y not in common for v in [y,(-y)%m]]+[(p*x)%m,(-p*x)%m]
    sigma=phi+[(-p*x)%m]
    assert Counter(out+tuple(sigma))==Counter(a+tuple(padding))
    found.append({'prime':p,'x':x,'output':out,'source_profile':profile(a,m),'output_profile':profile(out,m),'padding':padding,'standard':sigma,'kind':'direct' if len(out)<=4 else 'lowering'})
 return found
rows=[]
for m,a in SEEDS:
 assert balanced(a,m) and not inverse(a,m) and lcm(*(m//gcd(x,m) for x in a))==m
 pred=positive(a,m);ms=moves(a,m)
 if m==21:assert pred['predicate']=='surface_contraction' and not ms
 else:assert pred['predicate']=='residual'
 if m in (21,33) or (m==39 and a[1]==7):assert not ms
 else:assert ms
 # Inflation is checked at each seed's first two larger odd multiples as a finite fixture.
 for g in [3,5]:
  inflated=tuple(g*x for x in a)
  assert balanced(inflated,g*m)
  assert positive(inflated,g*m)['predicate']==pred['predicate']
 rows.append({'degree':m,'tuple':a,'unit_translates_checked':len(units(m)),'positive_criterion':pred,'profile_moves':ms[:3]})
for m in [39,45,105]:
 reps=[a for d,a in SEEDS if d==m]
 assert len({canonical(a,m) for a in reps})==len(reps)
record={'scope':'Seven explicitly listed tuples and two inflations each; no assertion of a complete census or an all-conductor theorem.','status':'passed','named_tuples':len(rows),'rows':rows}
(ROOT/'li-comparison-checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,indent=2))
