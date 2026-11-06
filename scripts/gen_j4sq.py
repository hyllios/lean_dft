import sympy as sp
H0 = sp.Matrix([[4,-1,0,0,1,0],[-1,4,-1,-1,0,1],[0,-1,4,0,-1,0],[0,-1,0,4,-1,0],[1,0,-1,-1,4,-1],[0,1,0,0,-1,4]])
occ = [[1,1,1,0,0,0],[1,0,0,1,1,0],[0,1,0,1,0,1],[0,0,1,0,1,1]]
v = [-3,-3,-2,0]
H = H0 + sp.diag(*[sum(v[i]*occ[i][c] for i in range(4)) for c in range(6)])
def lm(M): return "!![" + "; ".join(", ".join(str(x) for x in M.row(i)) for i in range(M.rows)) + "]"
P = [sp.eye(6)] + [H**k for k in range(1,6)]
out = ["-- generated snippet; the checked version lives in DFT/Lattice/Generic/SquareCertificate.lean", "",
       "namespace DFT", "", "open Matrix MvPolynomial", ""]
out.append("def vsq : Fin 4 → ℝ := ![-3, -3, -2, 0]")
out.append(f"def Hsq1 : Matrix (Fin 6) (Fin 6) ℝ := {lm(H)}")
out.append("lemma hamN_vsq : hamN H0sq occ4 vsq = Hsq1 := by\n  ext i j; fin_cases i <;> fin_cases j <;> simp [hamN, H0sq, occ4, vsq, Hsq1, Fin.sum_univ_succ] <;> norm_num")
for k in range(2,6):
    out.append(f"def Hsq{k} : Matrix (Fin 6) (Fin 6) ℝ := {lm(P[k])}")
    out.append(f"lemma Hsq_pow{k} : Hsq1 ^ {k} = Hsq{k} := by\n  rw [pow_succ{', Hsq_pow'+str(k-1) if k>2 else ', pow_one'}]\n  ext i j; fin_cases i <;> fin_cases j <;> simp [Hsq1, Hsq{k}{', Hsq'+str(k-1) if k>2 else ''}, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num")
out.append("lemma pow_cases (k : ℕ) (hk : k < 6) : Hsq1 ^ k = ![1, Hsq1, Hsq2, Hsq3, Hsq4, Hsq5] ⟨k, hk⟩ := by\n  interval_cases k\n  · simp\n  · simp\n  all_goals simp [Hsq_pow2, Hsq_pow3, Hsq_pow4, Hsq_pow5]")
for c in range(6):
    K = sp.Matrix(6,6,lambda i,j: P[j][i,c]); d = K.det()
    out.append(f"def Ksq{c} : Matrix (Fin 6) (Fin 6) ℝ := {lm(K)}")
    out.append(f"lemma kry_sq{c} : kry Hsq1 {c} Fin.val = Ksq{c} := by\n  ext i j\n  rw [kry, pow_cases j.val j.isLt]\n  fin_cases i <;> fin_cases j <;> simp [Hsq1, Hsq2, Hsq3, Hsq4, Hsq5, Ksq{c}]")
    out.append(f"lemma det_Ksq{c} : Ksq{c}.det = {d} := by\n  simp [Ksq{c}, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]\n  norm_num")
open('data/square_certificate_snippet.lean','w').write("\n".join(out) + "\n")
