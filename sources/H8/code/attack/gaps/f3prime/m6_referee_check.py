#!/usr/bin/env python3
# Supporting script for item (LXI), code/k3_hodge.py: the referee's independent checks (round 19).
# Independent checks: (1) polarised Fujiki form for n=3 gives B(x,y)=c/(2n-1) q(h)^{n-2}[q(h)q(x,y)+2(n-1)q(x,h)q(y,h)];
# (2) int c_phi x y = tr(phi) q(x,y) + 2 q(phi x,y) for self-adjoint phi (n=2 Fujiki form);
# (3) Delta^* Z'_u = Sym^2 NS part + kappa^{-1} c_{(u+u*)/2} for a random q-isometry u of T (n=3).
import itertools, random
from fractions import Fraction as Fr
random.seed(1)
def matmul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def inv(M):
    n=len(M); A=[row[:]+[Fr(int(i==j)) for j in range(n)] for i,row in enumerate(M)]
    for c in range(n):
        p=next(r for r in range(c,n) if A[r][c]!=0); A[c],A[p]=A[p],A[c]
        pv=A[c][c]; A[c]=[x/pv for x in A[c]]
        for r in range(n):
            if r!=c and A[r][c]!=0:
                f=A[r][c]; A[r]=[a-f*b for a,b in zip(A[r],A[c])]
    return [row[n:] for row in A]
def T(M): return [list(r) for r in zip(*M)]
# lattice: NS = <h> with q(h)=2, T = diag(-1,-2,3) (dim 3), total dim 4
Q=[[Fr(2),0,0,0],[0,Fr(-1),0,0],[0,0,Fr(-2),0],[0,0,0,Fr(3)]]
Q=[[Fr(x) for x in r] for r in Q]
d=4
def q(x,y): return sum(x[i]*Q[i][j]*y[j] for i in range(d) for j in range(d))
def matchings(lst):
    if not lst: yield []; return
    a=lst[0]
    for i in range(1,len(lst)):
        b=lst[i]; rest=lst[1:i]+lst[i+1:]
        for m in matchings(rest): yield [(a,b)]+m
def fujiki(vs,c):
    # symmetric multilinear form with int a^{2n} = c q(a)^n
    k=len(vs); nm=1
    for i in range(1,k,2): nm*=i
    return Fr(c,nm)*sum(eval_m(m,vs) for m in matchings(list(range(k))))
def eval_m(m,vs):
    r=Fr(1)
    for a,b in m: r*=q(vs[a],vs[b])
    return r
e=[[Fr(int(i==j)) for j in range(d)] for i in range(d)]
h=e[0]
# (1) n=3, c=15 (any c)
c=15; n=3
ok1=all(fujiki([x,y,h,h,h,h],c)== Fr(c,2*n-1)*q(h,h)**(n-2)*(q(h,h)*q(x,y)+2*(n-1)*q(x,h)*q(y,h)) for x in e for y in e)
print("(1) n=3 polarised Fujiki B formula:",ok1)
# random rational isometry of T: Cayley transform u=(1+S)(1-S)^{-1} with S q-antisymmetric on T
QT=[[Q[i][j] for j in range(1,4)] for i in range(1,4)]
A=[[Fr(random.randint(-3,3)) for j in range(3)] for i in range(3)]
Aanti=[[A[i][j]-A[j][i] for j in range(3)] for i in range(3)]
S=matmul(inv(QT),Aanti)  # q(Sx,y)=-q(x,Sy)
I3=[[Fr(int(i==j)) for j in range(3)] for i in range(3)]
U=matmul([[I3[i][j]+S[i][j] for j in range(3)] for i in range(3)], inv([[I3[i][j]-S[i][j] for j in range(3)] for i in range(3)]))
assert T(U)==T(U) and matmul(matmul(T(U),QT),U)==QT
F=[[Fr(int(i==j)) for j in range(d)] for i in range(d)]
for i in range(3):
    for j in range(3): F[1+i][1+j]=U[i][j]
# B on H^2 for n=3
B=[[fujiki([e[i],e[j],h,h,h,h],c) for j in range(d)] for i in range(d)]
Binv=inv(B)
# Z' = sum_i b_i (x) f(a_i), b_i B-dual basis: b_i = sum_j Binv[j][i] e_j ; Delta^* gives symmetric tensor sum_i b_i . f(e_i)
def sym_tensor_from(pairs):
    M=[[Fr(0)]*d for _ in range(d)]
    for a,b in pairs:
        for i in range(d):
            for j in range(d):
                M[i][j]+= (a[i]*b[j]+a[j]*b[i])/2
    return M
bs=[[Binv[j][i] for j in range(d)] for i in range(d)]
fa=[[F[j][i] for j in range(d)] for i in range(d)]  # columns = f(e_i)
Zp=sym_tensor_from(list(zip(bs,fa)))
kappa=Fr(c,2*n-1)*q(h,h)**(n-1)
# c_phi with phi=(u+u*)/2 on T, u*=Q^{-1}U^T Q
Ustar=matmul(matmul(inv(QT),T(U)),QT)
Phi=[[(U[i][j]+Ustar[i][j])/2 for j in range(3)] for i in range(3)]
QTinv=inv(QT)
tv=[[Fr(0)]+[QTinv[j][i] for j in range(3)] for i in range(3)]  # q-dual basis of T
pt=[[Fr(0)]+[Phi[j][i] for j in range(3)] for i in range(3)]
cphi=sym_tensor_from(list(zip(tv,pt)))
diff=[[Zp[i][j]-cphi[i][j]/kappa for j in range(d)] for i in range(d)]
ok3=all(diff[i][j]==0 for i in range(d) for j in range(d) if not (i==0 and j==0))
print("(3) Delta^*Z'_u - kappa^{-1} c_{(u+u*)/2} lies in Sym^2 NS (n=3):",ok3, " NS part:",diff[0][0])
# (2) n=2, c=3: int c_phi x y = tr(phi) q(x,y) + 2 q(phi x,y) for x,y in T
def pair_sym(Msym,x,y,c2=3):
    return sum(Msym[i][j]*fujiki([e[i],e[j],x,y],c2) for i in range(d) for j in range(d))
trphi=sum(Phi[i][i] for i in range(3))
PhiF=[[Fr(0)]*d for _ in range(d)]
for i in range(3):
    for j in range(3): PhiF[1+i][1+j]=Phi[i][j]
def ap(M,x): return [sum(M[i][j]*x[j] for j in range(d)) for i in range(d)]
ok2=all(pair_sym(cphi,x,y)==trphi*q(x,y)+2*q(ap(PhiF,x),y) for x in e[1:] for y in e[1:])
print("(2) int c_phi x y = tr(phi) q(x,y) + 2 q(phi x, y):",ok2)
# (4) threshold: min n with a partition having t distinct parts
print("(4) t(t+1)/2 for t=21:",21*22//2)
