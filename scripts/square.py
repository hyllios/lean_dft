import sympy as sp, itertools
# square graph 1-2-3-4-1 (0-based 0..3), hopping -1, two spinless fermions, basis e_a^e_b, a<b
M=4; edges=[(0,1),(1,2),(2,3),(3,0)]
h=sp.zeros(M); 
for a,b in edges: h[a,b]=h[b,a]=-1
basis=list(itertools.combinations(range(M),2))
def wedge(a,b):  # returns (sign, sorted pair) or None
    if a==b: return None
    return (1,(a,b)) if a<b else (-1,(b,a))
H1=sp.zeros(6)   # hopping part only
for col,(c,d) in enumerate(basis):
    for k in range(M):   # (h e_c) ^ e_d  and  e_c ^ (h e_d)
        for (x,y,coef) in [(k,d,h[k,c]),(c,k,h[k,d])]:
            if coef==0: continue
            w=wedge(x,y)
            if w: H1[basis.index(w[1]),col]+=w[0]*coef
occ=[[1 if i in cfg else 0 for cfg in basis] for i in range(M)]
s=sp.Rational(3,4)
def Hfull(t):
    v=[s+t,-s+t,-s-t,s-t]
    return 4*sp.eye(6)+H1+sp.diag(*[sum(v[i]*occ[i][c] for i in range(M)) for c in range(6)])
print('basis',basis); print('hopping part H1 ='); sp.pprint(H1)
psi=sp.Matrix([0,2,1,4,2,0]); E=sp.Rational(3,2)
for t in (0,sp.Rational(1,2)):
    H=Hfull(t)
    print(f't={t}: H psi - E psi =',list(H*psi-E*psi),' eigenvalues:',sorted([sp.nsimplify(x) for x in H.eigenvals()],key=lambda z:float(z)))
    # LDL^T of H - E I (psd, 1-dim kernel)
    A=H-E*sp.eye(6); L=sp.eye(6); D=[]
    A=A.copy()
    for k in range(6):
        piv=A[k,k]; D.append(piv)
        if piv==0: 
            assert all(A[k,j]==0 for j in range(k,6)), 'zero pivot with nonzero row'
            continue
        for i in range(k+1,6):
            L[i,k]=A[i,k]/piv
        for i in range(k+1,6):
            for j in range(k+1,6):
                A[i,j]-=L[i,k]*A[k,j]
    print('  D =',D)
    phi=sp.symbols('p0:6'); pv=sp.Matrix(phi)
    lhs=sp.expand((pv.T*(H-E*sp.eye(6))*pv)[0])
    rhs=sp.expand(sum(D[k]*(sum(L[i,k]*phi[i] for i in range(6)))**2 for k in range(6)))
    print('  SOS identity holds:', sp.simplify(lhs-rhs)==0)
    print('  squares:',[ (D[k], sum(L[i,k]*phi[i] for i in range(6))) for k in range(6) if D[k]!=0])
