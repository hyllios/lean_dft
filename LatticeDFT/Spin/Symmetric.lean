/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.Generic.NullSets

/-!
# Generic Hohenberg–Kohn with a symmetry

Spinful electrons with a spin-independent potential have a symmetry for every potential: total spin.
Eigenstates of spin `S` vanish on some configurations for every `v` (a triplet never doubly occupies a
site), so the Krylov condition (H*) fails. This file proves the generic Hohenberg–Kohn theorem from a
sector-wise condition.

The symmetry is given abstractly by orthogonal projections `P s` (the sectors) with `Σ_s P s = 1`,
commuting with `H0` and with every occupation `diag(n_i)`, hence with `H(v)` for every `v`.

* `symKrylovPoly`: `det(Bᵀ K)`, where the columns of `K` are `H(v)^k P e_c` (`k < d`) and the columns
  of `B` span the sector (`P = B G Bᵀ`). It vanishes when some nonzero `φ` in the sector is orthogonal to
  all of them.
* `nonUV_sym_imp`: a shared ground state splits into sector components, each of them shared; a component
  with full support on its sector forces `v - v'` constant (sector rigidity); otherwise it vanishes at a
  configuration of the sector, and a sector Krylov polynomial vanishes at `v`.
* `generic_hk_sym`: if every sector Krylov polynomial is nonzero, and every sector is rigid or never
  carries a ground state, the non-uniquely v-representable potentials lie in a closed, nowhere dense,
  Lebesgue-null set.
-/

namespace LatticeDFT

open Matrix MvPolynomial MeasureTheory

variable {C V ι : Type*} [Fintype C] [DecidableEq C] [Fintype V] [Fintype ι]

/-- The sector Krylov matrix: column `k` is `H^k P e_c`, for `k < d`. -/
noncomputable def symKry {R : Type*} [CommRing R] {d : ℕ} (H P : Matrix C C R) (c : C) :
    Matrix C (Fin d) R :=
  fun i k => (H ^ (k : ℕ) * P) i c

/-- The sector Krylov polynomial `det(Bᵀ K)`, for a matrix `B` whose columns span the sector
(`P = B G Bᵀ`). -/
noncomputable def symKrylovPoly {d : ℕ} (H0 : Matrix C C ℝ) (n : V → C → ℝ) (P : Matrix C C ℝ)
    (B : Matrix C (Fin d) ℝ) (c : C) : MvPolynomial V ℝ :=
  ((B.map MvPolynomial.C)ᵀ * symKry (hamP H0 n) (P.map MvPolynomial.C) c).det

lemma eval_symKrylovPoly {d : ℕ} (H0 : Matrix C C ℝ) (n : V → C → ℝ) (P : Matrix C C ℝ)
    (B : Matrix C (Fin d) ℝ) (c : C) (v : V → ℝ) :
    eval v (symKrylovPoly H0 n P B c) = (Bᵀ * symKry (hamN H0 n v) P c).det := by
  rw [symKrylovPoly, RingHom.map_det]
  congr 1
  have hp : ∀ k, ((hamP H0 n) ^ k).map (eval v) = hamN H0 n v ^ k := by
    intro k
    rw [← hamP_eval, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
  ext i k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul,
    Matrix.transpose_apply, symKry, eval_C]
  apply Finset.sum_congr rfl; intro j _
  congr 1
  rw [← hp]
  simp

/-- If `P = B G Bᵀ` and a nonzero `φ` with `P φ = φ` is orthogonal to every column of the sector
Krylov matrix, then `det(Bᵀ K) = 0`. -/
lemma det_symKry_eq_zero {d : ℕ} {H P : Matrix C C ℝ} {B : Matrix C (Fin d) ℝ}
    {G : Matrix (Fin d) (Fin d) ℝ} (hB : P = B * G * Bᵀ) {c : C} {φ : C → ℝ} (hφ : φ ≠ 0)
    (hP : P *ᵥ φ = φ) (horth : φ ᵥ* symKry (d := d) H P c = 0) :
    (Bᵀ * symKry H P c).det = 0 := by
  rw [← exists_vecMul_eq_zero_iff]
  set z := G *ᵥ (Bᵀ *ᵥ φ)
  have hz : B *ᵥ z = φ := by
    rw [mulVec_mulVec, mulVec_mulVec, ← hB, hP]
  refine ⟨z, fun h0 => hφ (by rw [← hz, h0, mulVec_zero]), ?_⟩
  rw [← vecMul_vecMul, vecMul_transpose, hz, horth]

/-- `H(v)` commutes with every sector projection. -/
lemma hamN_comm {H0 : Matrix C C ℝ} {n : V → C → ℝ} {P : Matrix C C ℝ} (h0 : H0 * P = P * H0)
    (hn : ∀ i, diagonal (n i) * P = P * diagonal (n i)) (v : V → ℝ) :
    hamN H0 n v * P = P * hamN H0 n v := by
  have hd : diagonal (fun c => ∑ i, v i * n i c) = ∑ i, v i • diagonal (n i) := by
    ext a b
    simp only [diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hamN, hd, add_mul, mul_add, h0, Finset.sum_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [smul_mul_assoc, mul_smul_comm, hn i]

/-- Rigidity on a sector: `Σ_i w_i n_i(c)` constant on the support of `P` forces `w` constant. -/
def RigidOn (P : Matrix C C ℝ) (n : V → C → ℝ) : Prop :=
  ∀ (w : V → ℝ) (κ : ℝ), (∀ c, P c c ≠ 0 → ∑ i, w i * n i c = κ) → ∃ k, ∀ i, w i = k

/-- A sector that never carries a ground state. -/
def NoGS (H0 : Matrix C C ℝ) (n : V → C → ℝ) (P : Matrix C C ℝ) : Prop :=
  ∀ (v : V → ℝ) (ψ : C → ℝ), IsGroundState (hamN H0 n v) ψ → P *ᵥ ψ = 0

variable {H0 : Matrix C C ℝ} {n : V → C → ℝ} {P : ι → Matrix C C ℝ} {d : ι → ℕ}
  {B : ∀ s, Matrix C (Fin (d s)) ℝ} {G : ∀ s, Matrix (Fin (d s)) (Fin (d s)) ℝ}

/-- **Non-uniqueness forces a zero of a sector Krylov polynomial.** -/
theorem nonUV_sym_imp (hH0 : H0.IsSymm) (hS : ∀ s, (P s).IsSymm) (hI : ∀ s, P s * P s = P s)
    (hsum : ∑ s, P s = 1) (h0 : ∀ s, H0 * P s = P s * H0)
    (hn : ∀ s i, diagonal (n i) * P s = P s * diagonal (n i))
    (hB : ∀ s, P s = B s * G s * (B s)ᵀ)
    (hR : ∀ s, RigidOn (P s) n ∨ NoGS H0 n (P s)) {v : V → ℝ} (h : NonUV H0 n v) :
    ∃ s c, P s c c ≠ 0 ∧ eval v (symKrylovPoly H0 n (P s) (B s) c) = 0 := by
  obtain ⟨ψ, v', hψ, hψ', hne⟩ := h
  have hE := isGroundState_eigen (hamN_isSymm hH0 n v) hψ
  have hE' := isGroundState_eigen (hamN_isSymm hH0 n v') hψ'
  set E := qf (hamN H0 n v) ψ / (ψ ⬝ᵥ ψ)
  set E' := qf (hamN H0 n v') ψ / (ψ ⬝ᵥ ψ)
  -- some sector component is nonzero
  obtain ⟨s, hs⟩ : ∃ s, P s *ᵥ ψ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hψ.1
    rw [← one_mulVec ψ, ← hsum, sum_mulVec]
    exact Finset.sum_eq_zero (fun s _ => hall s)
  have hRs : RigidOn (P s) n := by
    rcases hR s with h | h
    · exact h
    · exact absurd (h v ψ hψ) hs
  set φ := P s *ᵥ ψ
  have hφE : hamN H0 n v *ᵥ φ = E • φ := by
    change hamN H0 n v *ᵥ (P s *ᵥ ψ) = E • (P s *ᵥ ψ)
    rw [mulVec_mulVec, hamN_comm (h0 s) (hn s) v, ← mulVec_mulVec, hE, mulVec_smul]
  have hφE' : hamN H0 n v' *ᵥ φ = E' • φ := by
    change hamN H0 n v' *ᵥ (P s *ᵥ ψ) = E' • (P s *ᵥ ψ)
    rw [mulVec_mulVec, hamN_comm (h0 s) (hn s) v', ← mulVec_mulVec, hE', mulVec_smul]
  have hPφ : P s *ᵥ φ = φ := by simp only [φ, mulVec_mulVec, hI s]
  by_cases hall : ∀ c, P s c c ≠ 0 → φ c ≠ 0
  · exfalso
    apply hne
    apply hRs (fun i => v i - v' i) (E - E')
    intro c hc
    have e1 := congrFun hφE c
    have e2 := congrFun hφE' c
    rw [hamN_mulVec_apply] at e1 e2
    simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
    have : (∑ i, (v i - v' i) * n i c) * φ c = (E - E') * φ c := by
      simp only [sub_mul, Finset.sum_sub_distrib]; linarith
    exact mul_right_cancel₀ (hall c hc) this
  · push Not at hall
    obtain ⟨c, hc, hφc⟩ := hall
    refine ⟨s, c, hc, ?_⟩
    rw [eval_symKrylovPoly]
    apply det_symKry_eq_zero (hB s) hs hPφ
    -- φ ⬝ (H^k P e_c) = E^k (P φ)_c = E^k φ_c = 0
    have hpow : ∀ k : ℕ, φ ᵥ* (hamN H0 n v ^ k) = E ^ k • φ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← vecMul_vecMul, ih, smul_vecMul]
        have : φ ᵥ* hamN H0 n v = E • φ := by
          rw [← (hamN_isSymm hH0 n v).eq, vecMul_transpose, hφE]
        rw [this, smul_smul, pow_succ]
    have hsymm : φ ᵥ* P s = P s *ᵥ φ := by
      conv_lhs => rw [← (hS s).eq]
      rw [vecMul_transpose]
    funext k
    have key : (φ ᵥ* symKry (d := d s) (hamN H0 n v) (P s) c) k =
        (φ ᵥ* (hamN H0 n v ^ (k : ℕ) * P s)) c := by
      simp only [symKry, vecMul, dotProduct]
    rw [key, ← vecMul_vecMul, hpow, smul_vecMul, hsymm, hPφ, Pi.smul_apply, hφc, smul_zero,
      Pi.zero_apply]

/-- **Generic Hohenberg–Kohn theorem with a symmetry.** -/
theorem generic_hk_sym (hH0 : H0.IsSymm) (hS : ∀ s, (P s).IsSymm) (hI : ∀ s, P s * P s = P s)
    (hsum : ∑ s, P s = 1) (h0 : ∀ s, H0 * P s = P s * H0)
    (hn : ∀ s i, diagonal (n i) * P s = P s * diagonal (n i))
    (hB : ∀ s, P s = B s * G s * (B s)ᵀ) (hR : ∀ s, RigidOn (P s) n ∨ NoGS H0 n (P s))
    (hstar : ∀ s c, P s c c ≠ 0 → symKrylovPoly H0 n (P s) (B s) c ≠ 0) :
    ∃ Z : Set (V → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧ {v | NonUV H0 n v} ⊆ Z := by
  classical
  set Q := ∏ s, ∏ c ∈ Finset.univ.filter (fun c => P s c c ≠ 0), symKrylovPoly H0 n (P s) (B s) c
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun s _ => Finset.prod_ne_zero_iff.mpr
    (fun c hc => hstar s c (Finset.mem_filter.mp hc).2))
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hQ
  refine ⟨_, hcl, hint, volume_zeroSet hQ, fun v hv => ?_⟩
  obtain ⟨s, c, hc, hz⟩ := nonUV_sym_imp hH0 hS hI hsum h0 hn hB hR hv
  change eval v Q = 0
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ s)
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩) hz

end LatticeDFT
