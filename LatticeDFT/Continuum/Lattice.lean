/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.Continuum.HK
import LatticeDFT.TDDFT.ForceBalance
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The lattice as an instance of the general Hohenberg–Kohn setting

A finite configuration space with the counting measure. The form domain is everything, the
separation property is automatic (test with indicator functions), rigidity of the coupling is the
lattice `Rigid`, and unique continuation is "the ground state has no zero amplitude", which the
Krylov condition (H*) guarantees. The general theorem `hk_of_ucp` then gives back lattice
Hohenberg–Kohn at every potential satisfying (H*).

* `latticeSetting`, `isGS_lattice_iff`: the general ground-state notion is the lattice one.
* `sep_lattice`, `rigidL_lattice`, `ucp_lattice_iff`.
* `lattice_hk_of_hstar`: Hohenberg–Kohn at (H*) potentials, derived from the general theorem.
-/

namespace LatticeDFT

namespace Continuum

open MeasureTheory Matrix

variable {C V : Type*} [Fintype C] [DecidableEq C] [MeasurableSpace C]
  [MeasurableSingletonClass C] [Fintype V]

/-- The energy form of a matrix. -/
def matForm (H0 : Matrix C C ℝ) : (C → ℝ) →ₗ[ℝ] (C → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun ψ φ => ψ ⬝ᵥ (H0 *ᵥ φ))
    (fun a b c => by simp [add_dotProduct])
    (fun r a b => by simp [smul_dotProduct])
    (fun a b c => by simp [mulVec_add, dotProduct_add])
    (fun r a b => by simp [mulVec_smul, dotProduct_smul])

/-- The coupling `L w (c) = Σᵢ wᵢ nᵢ(c)`. -/
def latticeL (n : V → C → ℝ) : (V → ℝ) →ₗ[ℝ] (C → ℝ) where
  toFun w := fun c => ∑ i, w i * n i c
  map_add' a b := by funext c; simp [add_mul, Finset.sum_add_distrib]
  map_smul' r a := by funext c; simp [Finset.mul_sum, mul_assoc]

/-- The lattice as a general Hohenberg–Kohn setting (counting measure). -/
noncomputable def latticeSetting (H0 : Matrix C C ℝ) (hH0 : H0.IsSymm) (n : V → C → ℝ) :
    Setting (Measure.count : Measure C) (V → ℝ) where
  D := ⊤
  h0 := matForm H0
  h0_symm ψ _ φ _ := by
    simp only [matForm, LinearMap.mk₂_apply]
    rw [dotProduct_mulVec, ← mulVec_transpose, hH0.eq, dotProduct_comm]
  L := latticeL n
  int_L _ _ _ _ _ := Integrable.of_finite
  int_sq _ _ _ _ := Integrable.of_finite

variable {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}

omit [DecidableEq C] in
lemma ip_lattice (ψ φ : C → ℝ) : ip (μ := Measure.count) ψ φ = ψ ⬝ᵥ φ := by
  simp [ip, dotProduct]

include hH0 in
lemma Q_lattice (w : V → ℝ) (ψ : C → ℝ) :
    Q (latticeSetting H0 hH0 n) w ψ = qf (hamN H0 n w) ψ := by
  simp only [Q, pf, latticeSetting, matForm, LinearMap.mk₂_apply, latticeL, LinearMap.coe_mk,
    AddHom.coe_mk, integral_count, qf, hamN, add_mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro c _
  simp only [Pi.add_apply, mulVec_diagonal]
  ring

include hH0 in
/-- The general ground-state notion is the lattice one. -/
theorem isGS_lattice_iff (w : V → ℝ) (ψ : C → ℝ) :
    IsGS (latticeSetting H0 hH0 n) w ψ ↔ IsGroundState (hamN H0 n w) ψ := by
  have hpos : 0 < ψ ⬝ᵥ ψ ↔ ψ ≠ 0 := by
    constructor
    · intro h h0; rw [h0, dotProduct_zero] at h; exact lt_irrefl _ h
    · intro h
      exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (ψ i))
        (fun h' => h (dotProduct_self_eq_zero.mp h'.symm))
  unfold IsGS
  simp only [ip_lattice, Q_lattice, hpos]
  have hD : (latticeSetting H0 hH0 n).D = ⊤ := rfl
  simp only [hD, Submodule.mem_top, true_and, forall_const, IsGroundState]

include hH0 in
/-- Separation holds on a finite configuration space. -/
theorem sep_lattice : Sep (latticeSetting H0 hH0 n) := by
  intro g _ h
  rw [Filter.EventuallyEq, Measure.ae_count_iff]
  intro c
  have := h (Pi.single c 1) (Submodule.mem_top)
  simpa [integral_count, Pi.single_apply] using this

omit [DecidableEq C] in
include hH0 in
/-- Rigidity of the coupling is lattice rigidity. -/
theorem rigidL_lattice (hR : Rigid n) : RigidL (latticeSetting H0 hH0 n) (fun _ => 1) := by
  intro w c h
  rw [Filter.EventuallyEq, Measure.ae_count_iff] at h
  obtain ⟨k, hk⟩ := hR w c fun x => h x
  exact ⟨k, funext fun i => by simp [hk i]⟩

omit [Fintype C] [DecidableEq C] [MeasurableSingletonClass C] in
/-- Unique continuation on the lattice: no zero amplitude. -/
lemma ucp_lattice_iff (ψ : C → ℝ) :
    (∀ᵐ c ∂(Measure.count : Measure C), ψ c ≠ 0) ↔ ∀ c, ψ c ≠ 0 :=
  Measure.ae_count_iff

include hH0 in
/-- **Lattice Hohenberg–Kohn from the general theorem.** At a potential `v` satisfying (H*) (all
Krylov determinants nonzero), with rigid occupations: if a ground state of `v'` has the same norm and
density as a ground state of `v`, then `v - v'` is constant. Unique continuation is supplied by
(H*): ground states have no zero amplitude. -/
theorem lattice_hk_of_hstar (hR : Rigid n) {v v' : V → ℝ} {ord : C → ℕ}
    (hv : ∀ c, (kry (hamN H0 n v) c ord).det ≠ 0) {ψ ψ' : C → ℝ}
    (hψ : IsGroundState (hamN H0 n v) ψ) (hψ' : IsGroundState (hamN H0 n v') ψ')
    (hn : ψ ⬝ᵥ ψ = ψ' ⬝ᵥ ψ')
    (hd : ∀ i, ∑ c, n i c * ψ c ^ 2 = ∑ c, n i c * ψ' c ^ 2) :
    ∃ k : ℝ, ∀ i, v i - v' i = k := by
  have hS := hamN_isSymm hH0 n v
  have hfull := (eigen_unique_of_hstar hS hv hψ.1 (isGroundState_eigen hS hψ)
    (isGroundState_eigen hS hψ)).1
  have hdens : dens (latticeSetting H0 hH0 n) ψ = dens (latticeSetting H0 hH0 n) ψ' := by
    funext w
    simp only [dens, pf, latticeSetting, latticeL, LinearMap.coe_mk, AddHom.coe_mk,
      integral_count, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun c i => w i * n i c * (ψ' c * ψ' c))]
    apply Finset.sum_congr rfl; intro i _
    have := hd i
    simp only [mul_assoc, ← Finset.mul_sum, sq] at this ⊢
    rw [this]
  obtain ⟨k, hk⟩ := hk_of_ucp (sep_lattice hH0) (rigidL_lattice hH0 hR)
    ((isGS_lattice_iff hH0 v ψ).2 hψ) ((isGS_lattice_iff hH0 v' ψ').2 hψ')
    (by rw [ip_lattice, ip_lattice, hn]) hdens ((ucp_lattice_iff ψ).2 hfull)
  exact ⟨k, fun i => by simpa using congrFun hk i⟩

end Continuum

end LatticeDFT
