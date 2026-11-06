"""Generate DFT/Lattice/Spin/HubbardCertificates.lean.

Exact certificates of the sector-wise Krylov condition for small Hubbard models with one spin-up and one
spin-down electron (total density, spin-independent potential).

Configuration (a, b) = (site of the up electron, site of the down electron) has index a*M + b.
H0 = -t (hopping of either electron along an edge) + U [a = b];  n_i(a, b) = [a = i] + [b = i].
Sectors: singlet (basis e_aa and e_ab + e_ba, a < b) and triplet (basis e_ab - e_ba, a < b).
For each model the script finds an integer potential v0 at which every sector Krylov determinant
det(B^T K_c) (columns of K_c: H(v0)^k P e_c, k < d) is nonzero, and writes Lean proofs by norm_num.
"""
import itertools, random, sympy as sp

R = sp.Rational


def model(M, edges, t, U):
    n = M * M
    H0 = sp.zeros(n, n)
    for a, b in itertools.product(range(M), repeat=2):
        c = a * M + b
        if a == b:
            H0[c, c] += U
        for (p, q) in edges:
            for (x, y) in ((p, q), (q, p)):
                if a == x:
                    H0[c, y * M + b] += -t          # up electron hops
                if b == x:
                    H0[c, a * M + y] += -t          # down electron hops
    occ = [[(1 if a == i else 0) + (1 if b == i else 0) for a in range(M) for b in range(M)]
           for i in range(M)]
    pairs = [(a, b) for a in range(M) for b in range(M) if a < b]
    BS = sp.zeros(n, M + len(pairs)); GS = sp.zeros(M + len(pairs), M + len(pairs))
    for k in range(M):
        BS[k * M + k, k] = 1; GS[k, k] = 1
    for j, (a, b) in enumerate(pairs):
        BS[a * M + b, M + j] = 1; BS[b * M + a, M + j] = 1; GS[M + j, M + j] = R(1, 2)
    BT = sp.zeros(n, len(pairs)); GT = sp.zeros(len(pairs), len(pairs))
    for j, (a, b) in enumerate(pairs):
        BT[a * M + b, j] = 1; BT[b * M + a, j] = -1; GT[j, j] = R(1, 2)
    PS = BS * GS * BS.T; PT = BT * GT * BT.T
    assert PS + PT == sp.eye(n) and PS * PS == PS and PT * PT == PT
    for P in (PS, PT):
        assert H0 * P == P * H0
        for i in range(M):
            D = sp.diag(*occ[i]); assert D * P == P * D
    return dict(M=M, n=n, H0=H0, occ=occ, sectors=[('S', PS, BS, GS), ('T', PT, BT, GT)])


def hamN(m, v):
    return m['H0'] + sp.diag(*[sum(v[i] * m['occ'][i][c] for i in range(m['M'])) for c in range(m['n'])])


def krylov_mats(m, v):
    H = hamN(m, v); out = {}
    for (name, P, B, G) in m['sectors']:
        d = B.shape[1]
        HP = [P]
        for k in range(1, d):
            HP.append(H * HP[-1])
        mats = {}
        for c in range(m['n']):
            if P[c, c] == 0:
                continue
            K = sp.Matrix(m['n'], d, lambda i, k: HP[k][i, c])
            mats[c] = B.T * K
        out[name] = (HP, mats)
    return H, out


def find_v0(m, rng=range(-3, 4), seed=1):
    random.seed(seed)
    cands = list(itertools.product(rng, repeat=m['M']))
    random.shuffle(cands)
    for v in cands:
        if v[0] != 0:
            continue
        H, km = krylov_mats(m, v)
        if all(M_.det() != 0 for (_, mats) in km.values() for M_ in mats.values()):
            return list(v)
    raise ValueError('no point found')


def num(x):
    x = sp.nsimplify(x)
    if x.q == 1:
        return f'{x.p}'
    return f'({x.p}/{x.q})'


def mat(A):
    rows = '; '.join(', '.join(num(A[i, j]) for j in range(A.shape[1])) for i in range(A.shape[0]))
    return f'!![{rows}]'


def vec(xs):
    return '![' + ', '.join(num(x) for x in xs) + ']'


EXT = 'ext i j; fin_cases i <;> fin_cases j <;> simp [{defs}, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num'


def emit(m, pre, title, v0, nogs=None):
    M, n = m['M'], m['n']
    H, km = krylov_mats(m, v0)
    L = []
    w = L.append
    w(f'/-! ### {title} -/\n')
    w(f'def H0{pre} : Matrix (Fin {n}) (Fin {n}) ℝ := {mat(m["H0"])}\n')
    w(f'def occ{pre} : Fin {M} → Fin {n} → ℝ := ![' + ', '.join(vec(r) for r in m['occ']) + ']\n')
    secs = m['sectors']
    for (name, P, B, G) in secs:
        w(f'def P{name}{pre} : Matrix (Fin {n}) (Fin {n}) ℝ := {mat(P)}\n')
        w(f'def B{name}{pre} : Matrix (Fin {n}) (Fin {B.shape[1]}) ℝ := {mat(B)}\n')
        w(f'def G{name}{pre} : Matrix (Fin {B.shape[1]}) (Fin {B.shape[1]}) ℝ := {mat(G)}\n')
    dS, dT = secs[0][2].shape[1], secs[1][2].shape[1]
    w(f'/-- Sector dimensions: singlet (`true`) and triplet (`false`). -/\n'
      f'def d{pre} : Bool → ℕ\n  | true => {dS}\n  | false => {dT}\n')
    w(f'/-- Sector projections: singlet (`true`) and triplet (`false`). -/\n'
      f'def P{pre} : Bool → Matrix (Fin {n}) (Fin {n}) ℝ\n  | true => PS{pre}\n  | false => PT{pre}\n')
    w(f'def B{pre} : (s : Bool) → Matrix (Fin {n}) (Fin (d{pre} s)) ℝ\n  | true => BS{pre}\n'
      f'  | false => BT{pre}\n')
    w(f'def G{pre} : (s : Bool) → Matrix (Fin (d{pre} s)) (Fin (d{pre} s)) ℝ\n  | true => GS{pre}\n'
      f'  | false => GT{pre}\n')
    allP = f'P{pre}, PS{pre}, PT{pre}'
    w(f'lemma H0{pre}_symm : (H0{pre}).IsSymm := by\n'
      f'  apply Matrix.IsSymm.ext; intro i j\n'
      f'  fin_cases i <;> fin_cases j <;> simp [H0{pre}]\n')
    w(f'lemma P{pre}_symm : ∀ s, (P{pre} s).IsSymm := by\n'
      f'  intro s; cases s <;> apply Matrix.IsSymm.ext <;> intro i j <;>\n'
      f'    fin_cases i <;> fin_cases j <;> simp [{allP}]\n')
    w(f'lemma P{pre}_idem : ∀ s, P{pre} s * P{pre} s = P{pre} s := by\n'
      f'  intro s; cases s <;> ({EXT.format(defs=allP)})\n')
    w(f'lemma P{pre}_sum : ∑ s, P{pre} s = 1 := by\n'
      f'  rw [Fintype.sum_bool]\n'
      f'  ext i j; fin_cases i <;> fin_cases j <;> simp [{allP}, Matrix.one_apply] <;> norm_num\n')
    w(f'lemma P{pre}_comm0 : ∀ s, H0{pre} * P{pre} s = P{pre} s * H0{pre} := by\n'
      f'  intro s; cases s <;> ({EXT.format(defs="H0"+pre+", "+allP)})\n')
    w(f'lemma P{pre}_commn : ∀ s i, diagonal (occ{pre} i) * P{pre} s = P{pre} s * diagonal (occ{pre} i) := by\n'
      f'  intro s i; cases s <;> fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;>\n'
      f'    simp [occ{pre}, {allP}] <;> norm_num)\n')
    for nm in ('S', 'T'):
        w(f'lemma P{nm}{pre}_B : P{nm}{pre} = B{nm}{pre} * G{nm}{pre} * (B{nm}{pre})ᵀ := by\n'
          f'  {EXT.format(defs="P"+nm+pre+", B"+nm+pre+", G"+nm+pre)}\n')
    w(f'lemma P{pre}_B : ∀ s, P{pre} s = B{pre} s * G{pre} s * (B{pre} s)ᵀ := by\n'
      f'  intro s; cases s\n  · exact PT{pre}_B\n  · exact PS{pre}_B\n')
    # potential and powers
    w(f'def v{pre} : Fin {M} → ℝ := {vec(v0)}\n')
    w(f'def H{pre} : Matrix (Fin {n}) (Fin {n}) ℝ := {mat(H)}\n')
    w(f'lemma hamN_v{pre} : hamN H0{pre} occ{pre} v{pre} = H{pre} := by\n'
      f'  ext i j; fin_cases i <;> fin_cases j <;> simp [hamN, H0{pre}, occ{pre}, v{pre}, H{pre},\n'
      f'    Fin.sum_univ_succ] <;> norm_num\n')
    for (name, P, B, G) in secs:
        HP, mats = km[name]
        d = B.shape[1]
        for k in range(d):
            if k == 0:
                w(f'def HP{name}{pre}0 : Matrix (Fin {n}) (Fin {n}) ℝ := {mat(HP[0])}\n')
                w(f'lemma hp{name}{pre}0 : H{pre} ^ 0 * P{name}{pre} = HP{name}{pre}0 := by\n'
                  f'  rw [pow_zero, Matrix.one_mul]; rfl\n')
            else:
                w(f'def HP{name}{pre}{k} : Matrix (Fin {n}) (Fin {n}) ℝ := {mat(HP[k])}\n')
                w(f'lemma hp{name}{pre}{k} : H{pre} ^ {k} * P{name}{pre} = HP{name}{pre}{k} := by\n'
                  f'  rw [pow_succ\', Matrix.mul_assoc, hp{name}{pre}{k-1}]\n'
                  f'  {EXT.format(defs=f"H{pre}, HP{name}{pre}{k-1}, HP{name}{pre}{k}")}\n')
        hps = ', '.join(f'HP{name}{pre}{k}' for k in range(d))
        w(f'lemma hp{name}{pre} (k : Fin {d}) : H{pre} ^ (k : ℕ) * P{name}{pre} = ![{hps}] k := by\n'
          f'  fin_cases k\n' + ''.join(f'  · exact hp{name}{pre}{k}\n' for k in range(d)))
        # Bᵀ K matrices
        Ms = []
        for c in range(n):
            Mc = mats.get(c, sp.zeros(d, d))
            w(f'def K{name}{pre}{c} : Matrix (Fin {d}) (Fin {d}) ℝ := {mat(Mc)}\n')
            Ms.append(f'K{name}{pre}{c}')
        w(f'def K{name}{pre} : Fin {n} → Matrix (Fin {d}) (Fin {d}) ℝ := ![{", ".join(Ms)}]\n')
        w(f'lemma kry{name}{pre} (c : Fin {n}) (hc : P{name}{pre} c c ≠ 0) :\n'
          f'    (B{name}{pre})ᵀ * symKry (d := {d}) H{pre} P{name}{pre} c = K{name}{pre} c := by\n'
          f'  ext a k\n'
          f'  rw [Matrix.mul_apply]\n'
          f'  simp only [Matrix.transpose_apply, symKry, hp{name}{pre}]\n'
          f'  fin_cases c <;> simp [P{name}{pre}] at hc <;> fin_cases a <;> fin_cases k <;>\n'
          f'    simp [B{name}{pre}, K{name}{pre}, {", ".join(Ms)}, {hps}, P{name}{pre}, Fin.sum_univ_succ] <;> norm_num\n')
        w(f'lemma det{name}{pre} (c : Fin {n}) (hc : P{name}{pre} c c ≠ 0) : (K{name}{pre} c).det ≠ 0 := by\n'
          f'  fin_cases c <;> simp [P{name}{pre}] at hc <;>\n'
          f'    simp [K{name}{pre}, {", ".join(Ms)}, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove] <;> norm_num\n')
    w(f'lemma hstar{pre} : ∀ s c, P{pre} s c c ≠ 0 → symKrylovPoly H0{pre} occ{pre} (P{pre} s) (B{pre} s) c ≠ 0 := by\n'
      f'  intro s c hc h\n'
      f'  have := congrArg (eval v{pre}) h\n'
      f'  rw [eval_symKrylovPoly, map_zero, hamN_v{pre}] at this\n'
      f'  cases s\n'
      f'  · exact detT{pre} c hc (by rw [← kryT{pre} c hc]; exact this)\n'
      f'  · exact detS{pre} c hc (by rw [← kryS{pre} c hc]; exact this)\n')
    L = [x.replace('lemma ', '-- Exact arithmetic on explicit matrices by `norm_num` needs a larger budget.\nset_option maxHeartbeats 4000000 in\nlemma ', 1) if x.startswith('lemma ') else x for x in L]
    return '\n'.join(L), v0


dimer = model(2, [(0, 1)], 1, 4)
tri = model(3, [(0, 1), (1, 2), (0, 2)], 1, 4)
vd = find_v0(dimer); vt = find_v0(tri)
print('dimer v0', vd, 'triangle v0', vt)
for nm, m, v in (('dimer', dimer, vd), ('triangle', tri, vt)):
    H, km = krylov_mats(m, v)
    for s, (_, mats) in km.items():
        print(nm, s, {c: M_.det() for c, M_ in mats.items()})
code_d, _ = emit(dimer, 'D', 'Hubbard dimer, one up and one down electron (half filling), t = 1, U = 4', vd)
code_t, _ = emit(tri, 'Tr', 'Hubbard triangle, one up and one down electron, t = 1, U = 4', vt)
MANUAL_D = r"""
lemma rigidS_D : RigidOn PSD occD := by
  intro w κ h
  have e0 := h 0 (by simp [PSD])
  have e3 := h 3 (by simp [PSD])
  simp [occD, Fin.sum_univ_succ] at e0 e3
  exact ⟨w 0, fun i => by fin_cases i <;> simp <;> linarith⟩

/-- **The polarised half-filled state is never a ground state.** The triplet has energy `v₀ + v₁`;
the trial state `(1, 2, 2, 1)` has energy `v₀ + v₁ - 8/10`. -/
lemma noGS_D : NoGS H0D occD PTD := by
  intro v ψ hψ
  by_contra hne
  have hE := isGroundState_eigen (hamN_isSymm H0D_symm occD v) hψ
  set E := qf (hamN H0D occD v) ψ / (ψ ⬝ᵥ ψ)
  have hT : hamN H0D occD v *ᵥ (PTD *ᵥ ψ) = (v 0 + v 1) • (PTD *ᵥ ψ) := by
    funext i
    fin_cases i <;> simp [hamN, H0D, occD, PTD, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
  have hE' : hamN H0D occD v *ᵥ (PTD *ᵥ ψ) = E • (PTD *ᵥ ψ) := by
    rw [mulVec_mulVec, hamN_comm (P := PTD) (PD_comm0 false) (PD_commn false) v, ← mulVec_mulVec,
      hE, mulVec_smul]
  have hEq : E = v 0 + v 1 := by
    have h0 : (E - (v 0 + v 1)) • (PTD *ᵥ ψ) = 0 := by rw [sub_smul, ← hE', ← hT, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · linarith
    · exact absurd h hne
  have hψψ : 0 < ψ ⬝ᵥ ψ := lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg (ψ i)))
    (fun h => hψ.1 (dotProduct_self_eq_zero.mp h.symm))
  have hqψ : qf (hamN H0D occD v) ψ = E * (ψ ⬝ᵥ ψ) := by
    simp only [E]; field_simp
  have hq : qf (hamN H0D occD v) ![1, 2, 2, 1] = 10 * (v 0 + v 1) - 8 := by
    simp [qf, hamN, H0D, occD, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]; ring
  have hφφ : (![1, 2, 2, 1] : Fin 4 → ℝ) ⬝ᵥ ![1, 2, 2, 1] = 10 := by
    simp [dotProduct, Fin.sum_univ_succ]; norm_num
  have := hψ.2 ![1, 2, 2, 1]
  rw [hqψ, hq, hφφ, hEq] at this
  nlinarith

lemma RD : ∀ s, RigidOn (PD s) occD ∨ NoGS H0D occD (PD s) := by
  intro s; cases s
  · exact Or.inr noGS_D
  · exact Or.inl rigidS_D

/-- **Hubbard dimer at half filling: total-density HK for almost every potential.** One up and one
down electron, `t = 1`, `U = 4`, spin-independent potential. -/
theorem hubbard_dimer_generic_hk_ae :
    ∃ Z : Set (Fin 2 → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      {v | NonUV H0D occD v} ⊆ Z :=
  generic_hk_sym H0D_symm PD_symm PD_idem PD_sum PD_comm0 PD_commn PD_B RD hstarD
"""
MANUAL_T = r"""
lemma rigidS_Tr : RigidOn PSTr occTr := by
  intro w κ h
  have e0 := h 0 (by simp [PSTr])
  have e4 := h 4 (by simp [PSTr])
  have e8 := h 8 (by simp [PSTr])
  simp [occTr, Fin.sum_univ_succ] at e0 e4 e8
  exact ⟨w 0, fun i => by fin_cases i <;> simp <;> linarith⟩

lemma rigidT_Tr : RigidOn PTTr occTr := by
  intro w κ h
  have e1 := h 1 (by simp [PTTr])
  have e2 := h 2 (by simp [PTTr])
  have e5 := h 5 (by simp [PTTr])
  simp [occTr, Fin.sum_univ_succ] at e1 e2 e5
  exact ⟨w 0, fun i => by fin_cases i <;> simp <;> linarith⟩

lemma RTr : ∀ s, RigidOn (PTr s) occTr ∨ NoGS H0Tr occTr (PTr s) := by
  intro s; cases s
  · exact Or.inl rigidT_Tr
  · exact Or.inl rigidS_Tr

/-- **Hubbard triangle: total-density HK for almost every potential.** One up and one down electron,
`t = 1`, `U = 4`, spin-independent potential. -/
theorem hubbard_triangle_generic_hk_ae :
    ∃ Z : Set (Fin 3 → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      {v | NonUV H0Tr occTr v} ⊆ Z :=
  generic_hk_sym H0Tr_symm PTr_symm PTr_idem PTr_sum PTr_comm0 PTr_commn PTr_B RTr hstarTr
"""
HEADER = """/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.Spin.Symmetric

/-!
# Total-density Hohenberg–Kohn for small Hubbard models (exact certificates)

Generated by `scripts/gen_hubbard_sym_lean.py`. One spin-up and one spin-down electron, hopping
`t = 1` on every bond, Hubbard `U = 4`, spin-INDEPENDENT potential coupled to the total density.
Configuration `(a, b)` (up electron on `a`, down electron on `b`) has index `a * M + b`. The sectors
are the singlet (`true`) and the triplet (`false`); every triplet state vanishes on doubly occupied
configurations, so the plain Krylov condition (H*) fails, and `generic_hk_sym` is used instead.

* `hubbard_dimer_generic_hk_ae`: two sites (half filling). The triplet sector is not rigid (its
  density is `(1, 1)` for every potential), but it never carries a ground state (`noGS_D`).
* `hubbard_triangle_generic_hk_ae`: three sites; both sectors are rigid.

Each sector Krylov determinant is evaluated exactly at one integer potential.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false

namespace DFT

open Matrix MvPolynomial MeasureTheory

noncomputable section

"""
FOOTER = """
end

end DFT
"""
open('../DFT/Lattice/Spin/HubbardCertificates.lean', 'w').write(
    HEADER + code_d + MANUAL_D + chr(10) + code_t + MANUAL_T + FOOTER)
