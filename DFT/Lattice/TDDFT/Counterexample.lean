/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.TDDFT.KohnSham

/-!
# Theorem 2 of Farzanehpour–Tokatly is false

Farzanehpour and Tokatly (PRB 86, 125130 (2012)), Theorem 2, assert that on a connected lattice
every ground state lies in the v-representability set `Ω`, so that every density consistent with it
is produced by some potential. `square_kMat_degenerate` showed that their proof breaks down. Here
the conclusion itself fails.

Two fermions on the square at `v₀ = (3/4, -3/4, -3/4, 3/4)`, ground state `ψ₀ = (0, 2, 1, 4, 2, 0)`.
With `w = (1, 1, -1, -1)` the force-balance matrix `K = K(ψ₀, 0)` has `K w = 0`. The density
`n(t) = ρ₀ + (t - t₀)²/2 · (q - w)` is consistent with `ψ₀` (right initial density and current,
`Σ n̈ = 0`, smooth), but any trajectory producing it would satisfy `q - w = q - K v(t₀)` at `t₀`,
and the dot product with `w` gives `|w|² = 0`.

* `kfb_transpose`: `K(ψ)` is symmetric (for symmetric `H₀`).
* `mulVec_eq_zero_of_psd`: a symmetric positive semidefinite matrix annihilates the vectors on
  which its quadratic form vanishes.
* `kfb_sq_w`: `K(ψ₀, 0) w = 0`.
* `ft_theorem2_false`: **the counterexample.**
* `square_not_mem_omega`: `(ψ₀, 0) ∉ Ω`.
-/

namespace DFT

open Matrix Filter Topology

section general

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The force-balance matrix is symmetric. -/
lemma kfb_transpose {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ)
    (ψ : (C → ℝ) × (C → ℝ)) : (kfb H0 n ψ)ᵀ = kfb H0 n ψ := by
  ext i j
  simp only [transpose_apply, kfb]
  congr 1
  rw [Qf_sub, Qf_sub]
  have h1 : H0 * Nmat n j * Nmat n i = H0 * Nmat n i * Nmat n j := by
    rw [mul_assoc, Nmat_comm, ← mul_assoc]
  have h2 : Qf (Nmat n i * H0 * Nmat n j) ψ = Qf (Nmat n j * H0 * Nmat n i) ψ := by
    rw [← Qf_transpose (Nmat n i * H0 * Nmat n j), transpose_mul, transpose_mul,
      Nmat_transpose, Nmat_transpose, hH0.eq, mul_assoc]
  rw [h1, h2]

/-- A symmetric positive semidefinite matrix annihilates every vector on which its quadratic
form vanishes. -/
lemma mulVec_eq_zero_of_psd {K : Matrix V V ℝ} (hS : Kᵀ = K)
    (hpsd : ∀ u, 0 ≤ u ⬝ᵥ (K *ᵥ u)) {w : V → ℝ} (hw : w ⬝ᵥ (K *ᵥ w) = 0) : K *ᵥ w = 0 := by
  funext i
  set e : V → ℝ := Pi.single i 1
  have hwK : w ⬝ᵥ (K *ᵥ e) = (K *ᵥ w) i := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hS]
    simp [e, dotProduct, Pi.single_apply]
  have heK : e ⬝ᵥ (K *ᵥ w) = (K *ᵥ w) i := by simp [e, dotProduct, Pi.single_apply]
  have hee : e ⬝ᵥ (K *ᵥ e) = K i i := by
    simp [e, dotProduct, mulVec, Pi.single_apply]
  have key : ∀ s : ℝ, 0 ≤ (2 * (K *ᵥ w) i) * s + K i i * s ^ 2 := by
    intro s
    have h := hpsd (w + s • e)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hw, hwK, heK, hee] at h
    nlinarith [h]
  have := lin_coeff_zero key
  simp only [Pi.zero_apply]
  linarith

end general

/-- The ground state of two fermions on the square. -/
def ψsq : Fin 6 → ℝ := ![0, 2, 1, 4, 2, 0]

/-- The potential at which `ψsq` is a ground state. -/
noncomputable def vsq0 : Fin 4 → ℝ := ![3/4, -3/4, -3/4, 3/4]

/-- The zero mode of the force-balance matrix. -/
def wsq : Fin 4 → ℝ := ![1, 1, -1, -1]

lemma sum_occ4 (c : Fin 6) : ∑ i, occ4 i c = 2 := by
  fin_cases c <;> simp [occ4, Fin.sum_univ_four] <;> norm_num

lemma ground_sq : IsGroundState (hamN H0sq occ4 vsq0) ψsq := hk_fails_square.1

/-- `kMat(ψ₀) w = 0`. -/
lemma kMat_sq_w : kMat H0sq occ4 ψsq *ᵥ wsq = 0 := by
  obtain ⟨h0, h1, -⟩ := hk_fails_square
  have h := kMat_shared H0sq_isSymm h0 h1
  have hw : (fun i => (![3/4, -3/4, -3/4, 3/4] : Fin 4 → ℝ) i -
      (![5/4, -1/4, -5/4, 1/4] : Fin 4 → ℝ) i) = (-1 / 2 : ℝ) • wsq := by
    funext i; fin_cases i <;> simp [wsq] <;> norm_num
  rw [hw, mulVec_smul] at h
  have := congrArg (fun u => (-2 : ℝ) • u) h
  simpa [ψsq, smul_smul] using this

/-- **`K(ψ₀, 0) w = 0`.** -/
lemma kfb_sq_w : kfb H0sq occ4 (ψsq, 0) *ᵥ wsq = 0 := by
  refine mulVec_eq_zero_of_psd (kfb_transpose H0sq_isSymm occ4 _) (fun u => ?_) ?_
  · rw [kfb_quad_real H0sq_isSymm]
    linarith [kMat_nonpos H0sq_isSymm ground_sq u]
  · rw [kfb_quad_real H0sq_isSymm, kMat_sq_w, dotProduct_zero, neg_zero]

/-- The acceleration of the counterexample density: `q(ψ₀, 0) - w`. -/
noncomputable def ftAcc : Fin 4 → ℝ := fun i => qsrc H0sq occ4 (ψsq, 0) i - wsq i

/-- The counterexample density `n(t) = ρ₀ + (t - t₀)²/2 · (q - w)`. -/
noncomputable def ftDens (t0 t : ℝ) : Fin 4 → ℝ :=
  fun i => tdens occ4 (ψsq, 0) i + (t - t0) ^ 2 / 2 * ftAcc i

lemma sum_ftAcc : ∑ i, ftAcc i = 0 := by
  simp only [ftAcc, Finset.sum_sub_distrib, qsrc_sum H0sq sum_occ4]
  simp [wsq, Fin.sum_univ_four]

lemma hasDerivAt_ftDens (t0 t : ℝ) :
    HasDerivAt (ftDens t0) (fun i => (t - t0) * ftAcc i) t := by
  refine hasDerivAt_pi.2 fun i => ?_
  have h := ((((hasDerivAt_id t).sub_const t0).pow 2).div_const 2).mul_const (ftAcc i)
  have h2 := h.const_add (tdens occ4 (ψsq, 0) i)
  exact h2.congr_deriv (by simp)

lemma hasDerivAt_ftVel (t0 t : ℝ) :
    HasDerivAt (fun s => fun i => (s - t0) * ftAcc i) ftAcc t := by
  refine hasDerivAt_pi.2 fun i => ?_
  simpa using ((hasDerivAt_id t).sub_const t0).mul_const (ftAcc i)

/-- **Theorem 2 of Farzanehpour–Tokatly is false.** The ground state `ψ₀` of two fermions on the
square (at the potential `v₀`) admits a consistent density — smooth, with the right initial density
and current and `Σ n̈ = 0`, exactly the hypotheses of `td_existence` apart from `ψ₀ ∈ Ω` — that no
potential produces: there is no trajectory from `(ψ₀, 0)`, driven by any potential `v(t)`, whose
density equals `n(t)` near `t₀`. So Theorem 2 of Farzanehpour–Tokatly, PRB 86, 125130 (2012), is
false. -/
theorem ft_theorem2_false (t0 : ℝ) :
    IsGroundState (hamN H0sq occ4 vsq0) ψsq ∧
    (∀ t, HasDerivAt (ftDens t0) (fun i => (t - t0) * ftAcc i) t) ∧
    (∀ t, HasDerivAt (fun s => fun i => (s - t0) * ftAcc i) ftAcc t) ∧
    Continuous (fun _ : ℝ => ftAcc) ∧ (∑ i, ftAcc i = 0) ∧
    (∀ i, ftDens t0 t0 i = tdens occ4 (ψsq, 0) i) ∧
    (∀ i, tcur H0sq occ4 (ψsq, 0) i = (t0 - t0) * ftAcc i) ∧
    ∀ (v : ℝ → Fin 4 → ℝ) (ψ : ℝ → (Fin 6 → ℝ) × (Fin 6 → ℝ)), ψ t0 = (ψsq, 0) →
      ¬ ∀ᶠ t in 𝓝 t0, HasDerivAt ψ (schr H0sq occ4 (v t) (ψ t)) t ∧
        ∀ i, tdens occ4 (ψ t) i = ftDens t0 t i := by
  refine ⟨ground_sq, hasDerivAt_ftDens t0, hasDerivAt_ftVel t0, continuous_const, sum_ftAcc,
    fun i => by simp [ftDens], fun i => by rw [tcur_real]; ring, fun v ψ h0 hev => ?_⟩
  have hH := H0sq_isSymm
  -- the current equals `ṅ` near `t₀`
  have hcur : ∀ᶠ t in 𝓝 t0, ∀ i, tcur H0sq occ4 (ψ t) i = (t - t0) * ftAcc i := by
    filter_upwards [hev.eventually_nhds] with t ht
    intro i
    have hd := tdens_hasDerivAt hH ht.self_of_nhds.1 i
    have heq : (fun s => tdens occ4 (ψ s) i) =ᶠ[𝓝 t] (fun s => ftDens t0 s i) :=
      ht.mono fun s hs => hs.2 i
    exact hd.unique ((hasDerivAt_pi.1 (hasDerivAt_ftDens t0 t) i).congr_of_eventuallyEq heq)
  -- force balance at `t₀`: `q - w = q - K v(t₀)`
  have hK : ∀ i, ftAcc i = qsrc H0sq occ4 (ψsq, 0) i -
      ∑ j, kfb H0sq occ4 (ψsq, 0) i j * v t0 j := by
    intro i
    have hd := tcur_hasDerivAt hH hev.self_of_nhds.1 i
    rw [h0] at hd
    have heq : (fun s => tcur H0sq occ4 (ψ s) i) =ᶠ[𝓝 t0] (fun s => (s - t0) * ftAcc i) :=
      hcur.mono fun s hs => hs i
    have h2 := (hasDerivAt_pi.1 (hasDerivAt_ftVel t0 t0) i).congr_of_eventuallyEq heq
    exact (hd.unique h2).symm
  -- dot with `w`
  set K := kfb H0sq occ4 (ψsq, 0)
  have hKw : ∀ j, ∑ i, wsq i * K i j = 0 := by
    intro j
    have h1 := congrFun kfb_sq_w j
    have hsym : ∀ i, K i j = K j i := fun i => by
      have := congrFun (congrFun (kfb_transpose hH occ4 (ψsq, 0)) j) i
      simpa [K, transpose_apply] using this
    simp only [mulVec, dotProduct, Pi.zero_apply] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hsym i, mul_comm]
  have hA : ∑ i, wsq i * ftAcc i = ∑ i, wsq i * qsrc H0sq occ4 (ψsq, 0) i := by
    simp only [hK, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∑ j, ∑ i, wsq i * (K i j * v t0 j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      calc ∑ i, wsq i * (K i j * v t0 j) = (∑ i, wsq i * K i j) * v t0 j := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hKw j, zero_mul]
    rw [this, sub_zero]
  have hB : ∑ i, wsq i * ftAcc i = ∑ i, wsq i * qsrc H0sq occ4 (ψsq, 0) i - 4 := by
    simp only [ftAcc, mul_sub, Finset.sum_sub_distrib]
    simp [wsq, Fin.sum_univ_four]
    norm_num
  linarith

/-- **The square ground state lies outside `Ω`.** `w` is a nonzero vector in the kernel of
`K(ψ₀, 0) + 𝟙𝟙ᵀ`. -/
theorem square_not_mem_omega : ((ψsq, 0) : (Fin 6 → ℝ) × (Fin 6 → ℝ)) ∉ omega H0sq occ4 := by
  intro h
  apply h
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨wsq, fun h0 => by simpa [wsq] using congrFun h0 0, ?_⟩
  rw [kJ, add_mulVec, kfb_sq_w, onesM_mulVec, zero_add]
  funext i
  simp [wsq, Fin.sum_univ_four]

end DFT
