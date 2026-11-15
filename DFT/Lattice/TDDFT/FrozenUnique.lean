/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.TDDFT.Frozen

/-!
# Uniqueness for the linear Schrödinger equation; frozen densities never change

`frozenPath_hasDerivAt` and `tdens_frozenPath` (`Frozen.lean`) show that, for a continuous
potential, the frozen trajectory solves the Schrödinger equation with constant density. This file
shows that it is the only solution through `(x, 0)`, so every solution through a frozen eigenvector
has constant density.

The uniqueness theorems need only a symmetric `H0`; no regularity of the potential path `v` is
assumed. Solutions are classical (differentiable at every time of the interval). For a fixed time
the generator `ψ ↦ (H ψ₂, -H ψ₁)` is skew, so the squared distance `Qf 1 (ψ - φ)` of two
solutions has zero derivative.

* `schr_sub`, `Qf_one_hasDerivAt_schr`, `eq_zero_of_Qf_one_eq_zero`: linearity, norm
  conservation, `Qf 1` definite.
* `schr_unique_Ioo`, `schr_unique`, `schr_unique_eventually`: uniqueness on an open interval,
  on `ℝ`, and near `t0`.
* `frozenPath_unique`, `tdens_of_frozen`, `tdens_of_frozen_Ioo`: for a symmetric `H0` and a
  continuous potential, every solution through a frozen eigenvector (on `ℝ`, resp. on an open
  interval) is the frozen path, and its density is constant.
* `hubbard_triplet_frozen_unique`: the Hubbard-dimer triplet.
-/

namespace DFT

open Matrix Set Filter Topology

section unique

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]
  {H0 : Matrix C C ℝ} {n : V → C → ℝ}

/-- `schr` is linear in the state. -/
lemma schr_sub (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) (ψ φ : (C → ℝ) × (C → ℝ)) :
    schr H0 n v (ψ - φ) = schr H0 n v ψ - schr H0 n v φ := by
  refine Prod.ext ?_ ?_ <;> simp [schr, mulVec_sub]
  abel

/-- The squared norm `Qf 1` is conserved along any solution, for any value of the potential. -/
lemma Qf_one_hasDerivAt_schr (hH0 : H0.IsSymm) {v : V → ℝ} {ψ : ℝ → (C → ℝ) × (C → ℝ)} {t : ℝ}
    (hψ : HasDerivAt ψ (schr H0 n v (ψ t)) t) : HasDerivAt (fun s => Qf 1 (ψ s)) 0 t := by
  have := Qf_hasDerivAt hH0 hψ 1
  simpa [Wf] using this

omit [Fintype V] in
/-- `Qf 1 ψ = 0` only for `ψ = 0`. -/
lemma eq_zero_of_Qf_one_eq_zero {ψ : (C → ℝ) × (C → ℝ)} (h : Qf 1 ψ = 0) : ψ = 0 := by
  have h' : ψ.1 ⬝ᵥ ψ.1 + ψ.2 ⬝ᵥ ψ.2 = 0 := by simpa [Qf] using h
  have h1 : 0 ≤ ψ.1 ⬝ᵥ ψ.1 := Finset.sum_nonneg fun c _ => mul_self_nonneg _
  have h2 : 0 ≤ ψ.2 ⬝ᵥ ψ.2 := Finset.sum_nonneg fun c _ => mul_self_nonneg _
  have e1 : ψ.1 = 0 := dotProduct_self_eq_zero.mp (by linarith)
  have e2 : ψ.2 = 0 := dotProduct_self_eq_zero.mp (by linarith)
  exact Prod.ext e1 e2

/-- **Uniqueness on an open interval.** Two solutions of the linear Schrödinger equation with the
same potential path that agree at `t0` agree on the whole interval. Only `H0` symmetric is used;
no regularity of `v` is assumed (the solutions are differentiable at every time of the interval). -/
theorem schr_unique_Ioo (hH0 : H0.IsSymm) {v : ℝ → V → ℝ} {a b t0 : ℝ} (ht0 : t0 ∈ Ioo a b)
    {ψ φ : ℝ → (C → ℝ) × (C → ℝ)}
    (hψ : ∀ t ∈ Ioo a b, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t)
    (hφ : ∀ t ∈ Ioo a b, HasDerivAt φ (schr H0 n (v t) (φ t)) t)
    (h0 : ψ t0 = φ t0) : EqOn ψ φ (Ioo a b) := by
  intro t ht
  have hf : ∀ s ∈ Ioo a b, HasDerivAt (fun s => Qf 1 (ψ s - φ s)) 0 s := by
    intro s hs
    have hδ : HasDerivAt (fun s => ψ s - φ s) (schr H0 n (v s) (ψ s - φ s)) s := by
      rw [schr_sub]; exact (hψ s hs).sub (hφ s hs)
    exact Qf_one_hasDerivAt_schr (ψ := fun s => ψ s - φ s) hH0 hδ
  have hc : Qf 1 (ψ t - φ t) = Qf 1 (ψ t0 - φ t0) := const_of_hasDerivAt_zero hf ht ht0
  rw [h0, sub_self] at hc
  have hz : Qf 1 (0 : (C → ℝ) × (C → ℝ)) = 0 := by simp [Qf]
  exact sub_eq_zero.mp (eq_zero_of_Qf_one_eq_zero (hc.trans hz))

/-- **Uniqueness on `ℝ`.** Two solutions on `ℝ` with the same potential path that agree at `t0`
are equal; no regularity of `v` is assumed. -/
theorem schr_unique (hH0 : H0.IsSymm) {v : ℝ → V → ℝ} {t0 : ℝ} {ψ φ : ℝ → (C → ℝ) × (C → ℝ)}
    (hψ : ∀ t, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t)
    (hφ : ∀ t, HasDerivAt φ (schr H0 n (v t) (φ t)) t) (h0 : ψ t0 = φ t0) : ψ = φ := by
  funext t
  refine schr_unique_Ioo (a := min t t0 - 1) (b := max t t0 + 1) hH0 ?_
    (fun s _ => hψ s) (fun s _ => hφ s) h0 ?_
  · exact ⟨by linarith [min_le_right t t0], by linarith [le_max_right t t0]⟩
  · exact ⟨by linarith [min_le_left t t0], by linarith [le_max_left t t0]⟩

/-- **Uniqueness near `t0`**, in the form of `td_uniqueness`. -/
theorem schr_unique_eventually (hH0 : H0.IsSymm) {v : ℝ → V → ℝ} {t0 : ℝ}
    {ψ φ : ℝ → (C → ℝ) × (C → ℝ)}
    (hψ : ∀ᶠ t in 𝓝 t0, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t)
    (hφ : ∀ᶠ t in 𝓝 t0, HasDerivAt φ (schr H0 n (v t) (φ t)) t) (h0 : ψ t0 = φ t0) :
    ψ =ᶠ[𝓝 t0] φ := by
  obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hψ.and hφ)
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with t ht
  exact schr_unique_Ioo hH0 hmem (fun s hs => (hsub hs).1) (fun s hs => (hsub hs).2) h0 ht

end unique

section frozen

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]
  {H0 : Matrix C C ℝ} {n : V → C → ℝ} {x : C → ℝ} {E : ℝ} {ν : V → ℝ}

/-- **The frozen path is the only solution.** For a symmetric `H0` and a continuous potential,
every solution defined on `ℝ` through the frozen eigenvector `(x, 0)` at `t0` is the frozen
path. -/
theorem frozenPath_unique (hH0 : H0.IsSymm) (hx : H0 *ᵥ x = E • x)
    (hν : ∀ c, x c ≠ 0 → ∀ i, n i c = ν i) {v : ℝ → V → ℝ} (hv : Continuous v) {t0 : ℝ}
    {ψ : ℝ → (C → ℝ) × (C → ℝ)} (hψ : ∀ t, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t)
    (h0 : ψ t0 = (x, 0)) : ψ = frozenPath x (frozenPhase E ν v t0) :=
  schr_unique hH0 hψ (fun t => frozenPath_hasDerivAt hx hν hv t0 t)
    (h0.trans (frozenPath_zero (frozenPhase_self v t0)).symm)

/-- **Frozen densities never change.** For a symmetric `H0` and a continuous potential, the
density of every solution defined on `ℝ` through the frozen eigenvector `(x, 0)` equals that of
`x` at all times. -/
theorem tdens_of_frozen (hH0 : H0.IsSymm) (hx : H0 *ᵥ x = E • x)
    (hν : ∀ c, x c ≠ 0 → ∀ i, n i c = ν i) {v : ℝ → V → ℝ} (hv : Continuous v) {t0 : ℝ}
    {ψ : ℝ → (C → ℝ) × (C → ℝ)} (hψ : ∀ t, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t)
    (h0 : ψ t0 = (x, 0)) : ∀ t i, tdens n (ψ t) i = tdens n (x, 0) i := by
  intro t i
  rw [frozenPath_unique hH0 hx hν hv hψ h0]
  exact tdens_frozenPath _ t i

/-- **Frozen densities on an interval.** The same for a solution defined only on an open interval
containing `t0`: its density equals that of `x` on the whole interval. -/
theorem tdens_of_frozen_Ioo (hH0 : H0.IsSymm) (hx : H0 *ᵥ x = E • x)
    (hν : ∀ c, x c ≠ 0 → ∀ i, n i c = ν i) {v : ℝ → V → ℝ} (hv : Continuous v) {a b t0 : ℝ}
    (ht0 : t0 ∈ Ioo a b) {ψ : ℝ → (C → ℝ) × (C → ℝ)}
    (hψ : ∀ t ∈ Ioo a b, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t) (h0 : ψ t0 = (x, 0)) :
    ∀ t ∈ Ioo a b, ∀ i, tdens n (ψ t) i = tdens n (x, 0) i := by
  intro t ht i
  rw [schr_unique_Ioo hH0 ht0 hψ (fun s _ => frozenPath_hasDerivAt hx hν hv t0 s)
    (h0.trans (frozenPath_zero (frozenPhase_self v t0)).symm) ht]
  exact tdens_frozenPath _ t i

end frozen

section hubbard

/-- **The frozen triplet, uniquely.** For every hopping `t`, every `U` and every continuous
spin-independent potential, every solution on `ℝ` through the triplet at `t0` is the frozen path,
and its density is `(2, 2)` at all times (`tripD` has norm `√2`). -/
theorem hubbard_triplet_frozen_unique (t U : ℝ) {v : ℝ → Fin 2 → ℝ} (hv : Continuous v) {t0 : ℝ}
    {ψ : ℝ → (Fin 4 → ℝ) × (Fin 4 → ℝ)}
    (hψ : ∀ s, HasDerivAt ψ (schr (hubD t U) occD (v s) (ψ s)) s) (h0 : ψ t0 = (tripD, 0)) :
    ψ = frozenPath tripD (frozenPhase 0 (fun _ => 1) v t0) ∧ ∀ s i, tdens occD (ψ s) i = 2 := by
  have h := frozenPath_unique (hubD_isSymm t U) (hubD_triplet t U) triplet_occ hv hψ h0
  exact ⟨h, fun s i => by rw [h]; exact (hubbard_triplet_frozen t U hv t0 s).2 i⟩

end hubbard

end DFT
