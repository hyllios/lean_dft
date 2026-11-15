/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.TDDFT.Counterexample
import DFT.Lattice.HK.SquarePlane

/-!
# The force-balance counterexample in its general and normalized forms

`ft_theorem2_counterexample` is stated for the unnormalized ground state
`ψsq = (0, 2, 1, 4, 2, 0)` and the change `u = w` of the acceleration, `w = (1, 1, −1, −1)`. Here:
the same for any rescaled ground state `a·ψsq` (`a ≠ 0`) and any change `u` with `⟨w, u⟩ ≠ 0`
and `Σ u = 0` (`prop9_general`), and the statement for the normalized ground state
`Ψ₀ = ψsq / 5` (`prop9_paper`). Two ingredients beyond the library's proof: a rescaled ground
state is a ground state (`isGroundState_smul`, in `HK.SquarePlane`), and `K` at `a·ψsq` is `a²·K`
at `ψsq` (`kfb_smul_real`), so `w` stays its zero mode.
-/

namespace DFT

open Matrix Filter Topology

/-- The density's acceleration for the state a·ψsq: q(a·ψsq) − u. -/
noncomputable def ftAccU (a : ℝ) (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => qsrc H0sq occ4 (a • ψsq, 0) i - u i

/-- The density ρ(a·ψsq) + (t − t₀)²/2 · (q(a·ψsq) − u). -/
noncomputable def ftDensU (a : ℝ) (u : Fin 4 → ℝ) (t0 t : ℝ) : Fin 4 → ℝ :=
  fun i => tdens occ4 (a • ψsq, 0) i + (t - t0) ^ 2 / 2 * ftAccU a u i

/-- `K` is quadratic in a real state: `K(a x, 0) = a² K(x, 0)`. -/
lemma kfb_smul_real {C V : Type*} [Fintype C] [DecidableEq C] (H0 : Matrix C C ℝ)
    (n : V → C → ℝ) (x : C → ℝ) (a : ℝ) : kfb H0 n (a • x, 0) = a ^ 2 • kfb H0 n (x, 0) := by
  ext i j
  simp only [kfb, Qf, Matrix.smul_apply, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, Matrix.mulVec_zero, dotProduct_zero, add_zero]
  ring

/-- `w` is a zero mode of `K` at every multiple of `ψsq`. -/
lemma kfb_scaled_w (a : ℝ) : kfb H0sq occ4 (a • ψsq, 0) *ᵥ wsq = 0 := by
  rw [kfb_smul_real, Matrix.smul_mulVec, kfb_sq_w, smul_zero]

/-- The derivative of the density path `ftDensU`. -/
lemma hasDerivAt_ftDensU (a : ℝ) (u : Fin 4 → ℝ) (t0 t : ℝ) :
    HasDerivAt (ftDensU a u t0) (fun i => (t - t0) * ftAccU a u i) t := by
  refine hasDerivAt_pi.2 fun i => ?_
  have h := ((((hasDerivAt_id t).sub_const t0).pow 2).div_const 2).mul_const (ftAccU a u i)
  have h2 := h.const_add (tdens occ4 (a • ψsq, 0) i)
  exact h2.congr_deriv (by simp)

/-- The derivative of the velocity `(t − t₀) · ftAccU`. -/
lemma hasDerivAt_ftVelU (a : ℝ) (u : Fin 4 → ℝ) (t0 t : ℝ) :
    HasDerivAt (fun s => fun i => (s - t0) * ftAccU a u i) (ftAccU a u) t := by
  refine hasDerivAt_pi.2 fun i => ?_
  simpa using ((hasDerivAt_id t).sub_const t0).mul_const (ftAccU a u i)

/-- The acceleration has zero sum when `u` has zero sum. -/
lemma sum_ftAccU (a : ℝ) {u : Fin 4 → ℝ} (hu : ∑ i, u i = 0) : ∑ i, ftAccU a u i = 0 := by
  simp only [ftAccU, Finset.sum_sub_distrib, qsrc_sum H0sq sum_occ4, hu, sub_zero]

/-- **The counterexample, general form**, with every conjunct of the library's
`ft_theorem2_counterexample`: a·ψsq is a ground state; the density `ftDensU a u t0` is
differentiable with continuous second derivative `ftAccU a u`, Σ ρ̈ = 0, and it has the density
and the current of a·ψsq at t₀; yet no potential produces it from a·ψsq in any neighbourhood of
t₀. -/
theorem prop9_general (a : ℝ) (u : Fin 4 → ℝ) (ha : a ≠ 0) (hu : ∑ i, u i = 0)
    (hw : ∑ i, wsq i * u i ≠ 0) (t0 : ℝ) :
    IsGroundState (hamN H0sq occ4 vsq0) (a • ψsq) ∧
    (∀ t, HasDerivAt (ftDensU a u t0) (fun i => (t - t0) * ftAccU a u i) t) ∧
    (∀ t, HasDerivAt (fun s => fun i => (s - t0) * ftAccU a u i) (ftAccU a u) t) ∧
    Continuous (fun _ : ℝ => ftAccU a u) ∧ (∑ i, ftAccU a u i = 0) ∧
    (∀ i, ftDensU a u t0 t0 i = tdens occ4 (a • ψsq, 0) i) ∧
    (∀ i, tcur H0sq occ4 (a • ψsq, 0) i = (t0 - t0) * ftAccU a u i) ∧
    ∀ (v : ℝ → Fin 4 → ℝ) (ψ : ℝ → (Fin 6 → ℝ) × (Fin 6 → ℝ)), ψ t0 = (a • ψsq, 0) →
      ¬ ∀ᶠ t in 𝓝 t0, HasDerivAt ψ (schr H0sq occ4 (v t) (ψ t)) t ∧
        ∀ i, tdens occ4 (ψ t) i = ftDensU a u t0 t i := by
  refine ⟨isGroundState_smul ground_sq ha, hasDerivAt_ftDensU a u t0, hasDerivAt_ftVelU a u t0,
    continuous_const, sum_ftAccU a hu, fun i => by simp [ftDensU], fun i => by rw [tcur_real]; ring,
    fun v ψ h0 hev => ?_⟩
  have hH := H0sq_isSymm
  -- the current equals the derivative of the target density near t₀
  have hcur : ∀ᶠ t in 𝓝 t0, ∀ i, tcur H0sq occ4 (ψ t) i = (t - t0) * ftAccU a u i := by
    filter_upwards [hev.eventually_nhds] with t ht
    intro i
    have hd := tdens_hasDerivAt hH ht.self_of_nhds.1 i
    have heq : (fun s => tdens occ4 (ψ s) i) =ᶠ[𝓝 t] (fun s => ftDensU a u t0 s i) :=
      ht.mono fun s hs => hs.2 i
    exact hd.unique ((hasDerivAt_pi.1 (hasDerivAt_ftDensU a u t0 t) i).congr_of_eventuallyEq heq)
  -- force balance at t₀
  have hK : ∀ i, ftAccU a u i = qsrc H0sq occ4 (a • ψsq, 0) i -
      ∑ j, kfb H0sq occ4 (a • ψsq, 0) i j * v t0 j := by
    intro i
    have hd := tcur_hasDerivAt hH hev.self_of_nhds.1 i
    rw [h0] at hd
    have heq : (fun s => tcur H0sq occ4 (ψ s) i) =ᶠ[𝓝 t0] (fun s => (s - t0) * ftAccU a u i) :=
      hcur.mono fun s hs => hs i
    have h2 := (hasDerivAt_pi.1 (hasDerivAt_ftVelU a u t0 t0) i).congr_of_eventuallyEq heq
    exact (hd.unique h2).symm
  -- project on w: K w = 0 and K is symmetric
  set K := kfb H0sq occ4 (a • ψsq, 0)
  have hKw : ∀ j, ∑ i, wsq i * K i j = 0 := by
    intro j
    have h1 := congrFun (kfb_scaled_w a) j
    have hsym : ∀ i, K i j = K j i := fun i => by
      have := congrFun (congrFun (kfb_transpose hH occ4 (a • ψsq, 0)) j) i
      simpa [K, transpose_apply] using this
    simp only [mulVec, dotProduct, Pi.zero_apply] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hsym i, mul_comm]
  have hA : ∑ i, wsq i * ftAccU a u i = ∑ i, wsq i * qsrc H0sq occ4 (a • ψsq, 0) i := by
    simp only [hK, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∑ j, ∑ i, wsq i * (K i j * v t0 j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      calc ∑ i, wsq i * (K i j * v t0 j) = (∑ i, wsq i * K i j) * v t0 j := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hKw j, zero_mul]
    rw [this, sub_zero]
  have hB : ∑ i, wsq i * ftAccU a u i =
      ∑ i, wsq i * qsrc H0sq occ4 (a • ψsq, 0) i - ∑ i, wsq i * u i := by
    simp only [ftAccU, mul_sub, Finset.sum_sub_distrib]
  exact hw (by linarith)

/-- **The counterexample for the normalized ground state**: the normalized ground state Ψ₀ = ψsq/5,
with density (1, 4, 4, 1)/5, and w = (1, 1, −1, −1); every conjunct of the library theorem. -/
theorem prop9_paper (t0 : ℝ) :
    ((1 / 5 : ℝ) • ψsq) ⬝ᵥ ((1 / 5 : ℝ) • ψsq) = 1 ∧
    (fun i => tdens occ4 ((1 / 5 : ℝ) • ψsq, 0) i) = ![1 / 5, 4 / 5, 4 / 5, 1 / 5] ∧
    IsGroundState (hamN H0sq occ4 vsq0) ((1 / 5 : ℝ) • ψsq) ∧
    (∀ t, HasDerivAt (ftDensU (1 / 5) wsq t0) (fun i => (t - t0) * ftAccU (1 / 5) wsq i) t) ∧
    (∀ t, HasDerivAt (fun s => fun i => (s - t0) * ftAccU (1 / 5) wsq i) (ftAccU (1 / 5) wsq) t) ∧
    Continuous (fun _ : ℝ => ftAccU (1 / 5) wsq) ∧ (∑ i, ftAccU (1 / 5) wsq i = 0) ∧
    (∀ i, ftDensU (1 / 5) wsq t0 t0 i = tdens occ4 ((1 / 5 : ℝ) • ψsq, 0) i) ∧
    (∀ i, tcur H0sq occ4 ((1 / 5 : ℝ) • ψsq, 0) i = (t0 - t0) * ftAccU (1 / 5) wsq i) ∧
    ∀ (v : ℝ → Fin 4 → ℝ) (ψ : ℝ → (Fin 6 → ℝ) × (Fin 6 → ℝ)), ψ t0 = ((1 / 5 : ℝ) • ψsq, 0) →
      ¬ ∀ᶠ t in 𝓝 t0, HasDerivAt ψ (schr H0sq occ4 (v t) (ψ t)) t ∧
        ∀ i, tdens occ4 (ψ t) i = ftDensU (1 / 5) wsq t0 t i := by
  have hsum : ∑ i, wsq i = 0 := by simp [wsq, Fin.sum_univ_four]
  have hww : ∑ i, wsq i * wsq i ≠ 0 := by simp [wsq, Fin.sum_univ_four]; norm_num
  refine ⟨?_, ?_, prop9_general (1 / 5) wsq (by norm_num) hsum hww t0⟩
  · simp [ψsq, dotProduct, Fin.sum_univ_succ]; norm_num
  · ext i; fin_cases i <;>
      simp [tdens, Qf, Nmat, occ4, ψsq, Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
        Fin.sum_univ_succ] <;> norm_num

/-- The library's `ft_theorem2_counterexample` is the instance a = 1, u = w: the same density and
the same acceleration (and the same list of conjuncts, compare the statements). -/
theorem prop9_library_case (t0 t : ℝ) :
    ftDensU 1 wsq t0 t = ftDens t0 t ∧ ftAccU 1 wsq = ftAcc := by
  constructor
  · ext i; simp [ftDensU, ftAccU, ftDens, ftAcc]
  · ext i; simp [ftAccU, ftAcc]

/-- The library's `ft_theorem2_counterexample`, statement copied verbatim, derived from
`prop9_general` with a = 1, u = w. -/
theorem library_statement_from_general (t0 : ℝ) :
    IsGroundState (hamN H0sq occ4 vsq0) ψsq ∧
    (∀ t, HasDerivAt (ftDens t0) (fun i => (t - t0) * ftAcc i) t) ∧
    (∀ t, HasDerivAt (fun s => fun i => (s - t0) * ftAcc i) ftAcc t) ∧
    Continuous (fun _ : ℝ => ftAcc) ∧ (∑ i, ftAcc i = 0) ∧
    (∀ i, ftDens t0 t0 i = tdens occ4 (ψsq, 0) i) ∧
    (∀ i, tcur H0sq occ4 (ψsq, 0) i = (t0 - t0) * ftAcc i) ∧
    ∀ (v : ℝ → Fin 4 → ℝ) (ψ : ℝ → (Fin 6 → ℝ) × (Fin 6 → ℝ)), ψ t0 = (ψsq, 0) →
      ¬ ∀ᶠ t in 𝓝 t0, HasDerivAt ψ (schr H0sq occ4 (v t) (ψ t)) t ∧
        ∀ i, tdens occ4 (ψ t) i = ftDens t0 t i := by
  have hsum : ∑ i, wsq i = 0 := by simp [wsq, Fin.sum_univ_four]
  have hww : ∑ i, wsq i * wsq i ≠ 0 := by simp [wsq, Fin.sum_univ_four]; norm_num
  have hD : ftDensU 1 wsq t0 = ftDens t0 := funext fun t => (prop9_library_case t0 t).1
  have hA : ftAccU 1 wsq = ftAcc := (prop9_library_case t0 t0).2
  have h := prop9_general 1 wsq one_ne_zero hsum hww t0
  rw [hD, hA, one_smul] at h
  exact h

/-- Why the counterexample needs ⟨w, u⟩ ≠ 0: for u = (1, −1, 1, −1), with ⟨w, u⟩ = 0 and Σu = 0, the
force balance at ψsq is no obstruction, because u is in the range of K(ψsq) (K v = u for v = (1/20,
0, 1/20, 0)). The argument projects the force balance on w, the zero mode of K; a change u without a
component along w escapes it. -/
theorem orthogonal_u_in_range :
    ∃ v : Fin 4 → ℝ, kfb H0sq occ4 (ψsq, 0) *ᵥ v = ![1, -1, 1, -1] := by
  refine ⟨![1 / 20, 0, 1 / 20, 0], ?_⟩
  ext i; fin_cases i <;>
    simp [kfb, Qf, Nmat, H0sq, occ4, ψsq, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ] <;> norm_num

end DFT
