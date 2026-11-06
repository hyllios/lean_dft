import sympy as sp, itertools
exec(open('square.py').read().split("s=sp.Rational(3,4)")[0])   # reuse H1, basis, occ
phi=sp.symbols('p0:6'); v=sp.symbols('v0:4')
qf=sum((4+sum(v[i]*occ[i][c] for i in range(4)))*phi[c]**2 for c in range(6)) \
   + sum(2*H1[c,d]*phi[c]*phi[d] for c in range(6) for d in range(c+1,6))
def lean(e):
    s=sp.sstr(sp.expand(e))
    for k in range(6): s=s.replace(f'p{k}',f'φ {k}')
    for k in range(4): s=s.replace(f'v{k}',f'v {k}')
    return s.replace('**','^')
rows=lambda M: '; '.join(', '.join(str(M[i,j]) for j in range(6)) for i in range(6))
H0=4*sp.eye(6)+H1
occ_str='![' + ', '.join('![' + ', '.join(str(x) for x in occ[i]) + ']' for i in range(4)) + ']'
def squares(t):
    s_=sp.Rational(3,4); vv=[s_+t,-s_+t,-s_-t,s_-t]
    H=4*sp.eye(6)+H1+sp.diag(*[sum(vv[i]*occ[i][c] for i in range(4)) for c in range(6)])
    A=(H-sp.Rational(3,2)*sp.eye(6)).copy(); L=sp.eye(6); D=[]
    for k in range(6):
        piv=A[k,k]; D.append(piv)
        if piv==0: continue
        for i in range(k+1,6): L[i,k]=A[i,k]/piv
        for i in range(k+1,6):
            for j in range(k+1,6): A[i,j]-=L[i,k]*A[k,j]
    return vv,[lean(sum(L[i,k]*phi[i] for i in range(6))) for k in range(6) if D[k]!=0]
out=f"""
/-! ### Counterexample 2 (PvL Sect. III.3, Eqs. 45–51): two spinless fermions on a square.
Sites 0–1–2–3–0, hopping −1; basis {{01, 02, 03, 12, 13, 23}}. Potentials v(t) = (s+t, −s+t, −s−t, s−t), s = 3/4.
For |t| < s the ground state is Ψ_A ∝ (0, 2, 1, 4, 2, 0), energy 3/2, NON-DEGENERATE, density (1,4,4,1)/5:
no empty and no full site. Yet t = 0 and t = 1/2 give the same ground state: HK fails non-trivially.
Ground-state proofs via exact sum-of-squares (LDLᵀ) certificates of H − 3/2 (one zero pivot = the ground state). -/

def occ4 : Fin 4 → Fin 6 → ℝ := {occ_str}

def H0sq : Matrix (Fin 6) (Fin 6) ℝ := !![{rows(H0)}]

lemma qf_sq (v : Fin 4 → ℝ) (φ : Fin 6 → ℝ) :
    qf (hamN H0sq occ4 v) φ = {lean(qf)} := by
  rw [qf_hamN]
  simp [qf, dens, H0sq, occ4, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring
"""
for name,t in (('ground_sq0',0),('ground_sq1',sp.Rational(1,2))):
    vv,sq=squares(t)
    vstr='![' + ', '.join(str(x) for x in vv) + ']'
    hints=', '.join(f'sq_nonneg ({q})' for q in sq)
    out+=f"""
lemma {name} : IsGroundState (hamN H0sq occ4 {vstr}) ![0, 2, 1, 4, 2, 0] := by
  refine ⟨fun h => by simpa using congrFun h 1, fun φ => ?_⟩
  rw [qf_sq, qf_sq]
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [{hints}]
"""
out+="""
/-- Non-trivial failure of strong HK: non-degenerate ground state, density strictly between 0 and 1. -/
theorem hk_fails_square :
    IsGroundState (hamN H0sq occ4 ![3/4, -3/4, -3/4, 3/4]) ![0, 2, 1, 4, 2, 0] ∧
    IsGroundState (hamN H0sq occ4 ![5/4, -1/4, -5/4, 1/4]) ![0, 2, 1, 4, 2, 0] ∧
    ¬ ∃ k : ℝ, ∀ i, (![3/4, -3/4, -3/4, 3/4] : Fin 4 → ℝ) i - (![5/4, -1/4, -5/4, 1/4] : Fin 4 → ℝ) i = k := by
  refine ⟨ground_sq0, ground_sq1, ?_⟩
  rintro ⟨k, hk⟩
  have h0 := hk 0; have h2 := hk 2
  simp at h0 h2
  norm_num at h0 h2
  linarith
"""
open('data/square_snippet.lean','w').write(out); print(out)
