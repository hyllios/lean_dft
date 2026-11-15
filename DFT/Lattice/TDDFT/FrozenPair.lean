/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.TDDFT.FrozenUnique

/-!
# Frozen densities for complex eigenstates

`Frozen.lean` and `FrozenUnique.lean` treat a real frozen eigenvector `(x, 0)`. This file
generalizes them to a complex eigenstate `x + i y` of a real symmetric `H0`, i.e. a pair `(x, y)`
with `H0 x = E x` and `H0 y = E y` (for a degenerate `E`, `x` and `y` need not be parallel), all of
whose configurations (those where `x` or `y` is nonzero) have the same occupations `ν`. The
evolution is the rotation `e^{-iθ(t)} (x + i y)`, `θ̇ = E + Σ_i v_i(t) ν_i`, and the density never
changes.

* `frozenPath₂`, `frozenPath₂_zero_right`, `frozenPath₂_zero`: the trajectory
  `(cos θ x + sin θ y, cos θ y - sin θ x)`; for `y = 0` it is `frozenPath x θ`.
* `frozenPath₂_hasDerivAt`, `tdens_frozenPath₂`: it solves the Schrödinger equation for every
  continuous `v(t)`, with constant density.
* `frozenPath₂_unique`, `tdens_of_frozen₂`: for a symmetric `H0` and a continuous potential, every
  solution on `ℝ` through `(x, y)` is the frozen path, and its density is constant.
* `kfb_eq_zero_of_occ_const`, `not_mem_omega_of_occ_const`: such a state lies outside `Ω` as soon
  as there are two sites. More generally, if all configurations of `(x, y)` have the same
  occupations, then `K(x, y) = 0` (no eigenstate condition, no symmetry of `H0`), so
  `K + 𝟙𝟙ᵀ = 𝟙𝟙ᵀ` is singular with two or more sites.
-/

namespace DFT

open Matrix Set Filter Topology

section frozen

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
  {H0 : Matrix C C ℝ} {n : V → C → ℝ} {x y : C → ℝ} {E : ℝ} {ν : V → ℝ}

/-- The frozen trajectory of `x + i y`: `e^{-iθ} (x + i y)` in real coordinates,
`(cos θ · x + sin θ · y, cos θ · y - sin θ · x)`. -/
noncomputable def frozenPath₂ (x y : C → ℝ) (θ : ℝ → ℝ) (t : ℝ) : (C → ℝ) × (C → ℝ) :=
  (Real.cos (θ t) • x + Real.sin (θ t) • y, Real.cos (θ t) • y - Real.sin (θ t) • x)

omit [Fintype C] [DecidableEq C] in
/-- For a real state (`y = 0`) the trajectory is `frozenPath`. -/
lemma frozenPath₂_zero_right (x : C → ℝ) (θ : ℝ → ℝ) : frozenPath₂ x 0 θ = frozenPath x θ := by
  funext t
  simp only [frozenPath₂, smul_zero, add_zero, zero_sub, frozenPath]

omit [Fintype C] [DecidableEq C] in
/-- At a time where the phase vanishes, the trajectory is at `(x, y)`. -/
lemma frozenPath₂_zero {θ : ℝ → ℝ} {t0 : ℝ} (h : θ t0 = 0) : frozenPath₂ x y θ t0 = (x, y) := by
  simp only [frozenPath₂, h, Real.cos_zero, one_smul, Real.sin_zero, zero_smul, add_zero,
    sub_zero]

omit [DecidableEq V] in
/-- **The frozen trajectory of a complex eigenstate solves the Schrödinger equation for every
continuous potential.** -/
theorem frozenPath₂_hasDerivAt (hx : H0 *ᵥ x = E • x) (hy : H0 *ᵥ y = E • y)
    (hν : ∀ c, (x c ≠ 0 ∨ y c ≠ 0) → ∀ i, n i c = ν i)
    {v : ℝ → V → ℝ} (hv : Continuous v) (t0 t : ℝ) :
    HasDerivAt (frozenPath₂ x y (frozenPhase E ν v t0))
      (schr H0 n (v t) (frozenPath₂ x y (frozenPhase E ν v t0) t)) t := by
  set θ := frozenPhase E ν v t0
  set lam := E + ∑ i, v t i * ν i
  have hf : Continuous fun s => E + ∑ i, v s i * ν i :=
    continuous_const.add (continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hv).mul continuous_const)
  have hθ : HasDerivAt θ lam t := (hf.integral_hasStrictDerivAt t0 t).hasDerivAt
  have hc := (Real.hasDerivAt_cos (θ t)).comp t hθ
  have hs := (Real.hasDerivAt_sin (θ t)).comp t hθ
  have h1 := (hc.smul_const x).add (hs.smul_const y)
  have h2 := (hc.smul_const y).sub (hs.smul_const x)
  have h : HasDerivAt (frozenPath₂ x y θ) _ t := h1.prodMk h2
  convert h using 1
  simp only [schr, frozenPath₂, mulVec_add, mulVec_sub, mulVec_smul,
    hamN_mulVec_frozen hx (fun c hc => hν c (Or.inl hc)),
    hamN_mulVec_frozen hy (fun c hc => hν c (Or.inr hc)), smul_smul, Prod.mk.injEq, lam]
  refine ⟨?_, ?_⟩ <;> (funext c; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]; ring)

omit [Fintype V] [DecidableEq V] in
/-- The density along the frozen trajectory never changes. -/
lemma tdens_frozenPath₂ (θ : ℝ → ℝ) (t : ℝ) (i : V) :
    tdens n (frozenPath₂ x y θ t) i = tdens n (x, y) i := by
  simp only [tdens, Qf, dotProduct, frozenPath₂, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nmat,
    mulVec_diagonal, Pi.sub_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  linear_combination (n i c * (x c ^ 2 + y c ^ 2)) * Real.cos_sq_add_sin_sq (θ t)

end frozen

section unique

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]
  {H0 : Matrix C C ℝ} {n : V → C → ℝ} {x y : C → ℝ} {E : ℝ} {ν : V → ℝ}

/-- **The frozen path is the only solution.** For a symmetric `H0` and a continuous potential,
every solution defined on `ℝ` through the frozen complex eigenstate `(x, y)` at `t0` is the
frozen path. -/
theorem frozenPath₂_unique (hH0 : H0.IsSymm) (hx : H0 *ᵥ x = E • x) (hy : H0 *ᵥ y = E • y)
    (hν : ∀ c, (x c ≠ 0 ∨ y c ≠ 0) → ∀ i, n i c = ν i) {v : ℝ → V → ℝ} (hv : Continuous v)
    {t0 : ℝ} {ψ : ℝ → (C → ℝ) × (C → ℝ)} (hψ : ∀ t, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t)
    (h0 : ψ t0 = (x, y)) : ψ = frozenPath₂ x y (frozenPhase E ν v t0) :=
  schr_unique hH0 hψ (fun t => frozenPath₂_hasDerivAt hx hy hν hv t0 t)
    (h0.trans (frozenPath₂_zero (frozenPhase_self v t0)).symm)

/-- **Frozen densities of complex eigenstates never change.** For a symmetric `H0` and a
continuous potential, the density of every solution defined on `ℝ` through the frozen complex
eigenstate `(x, y)` equals that of `(x, y)` at all times. -/
theorem tdens_of_frozen₂ (hH0 : H0.IsSymm) (hx : H0 *ᵥ x = E • x) (hy : H0 *ᵥ y = E • y)
    (hν : ∀ c, (x c ≠ 0 ∨ y c ≠ 0) → ∀ i, n i c = ν i) {v : ℝ → V → ℝ} (hv : Continuous v)
    {t0 : ℝ} {ψ : ℝ → (C → ℝ) × (C → ℝ)} (hψ : ∀ t, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t)
    (h0 : ψ t0 = (x, y)) : ∀ t i, tdens n (ψ t) i = tdens n (x, y) i := by
  intro t i
  rw [frozenPath₂_unique hH0 hx hy hν hv hψ h0]
  exact tdens_frozenPath₂ _ t i

end unique

section occ

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
  {H0 : Matrix C C ℝ} {n : V → C → ℝ} {x y : C → ℝ} {ν : V → ℝ}

omit [Fintype V] [DecidableEq V] in
/-- If all configurations of `z` have the occupations `ν`, then `z` is annihilated (in
expectation) by `H0 N_i N_j - N_j H0 N_i`, for every `H0`. -/
lemma dotProduct_comm_occ_const {z : C → ℝ} (hz : ∀ c, z c ≠ 0 → ∀ i, n i c = ν i) (i j : V) :
    z ⬝ᵥ ((H0 * Nmat n i * Nmat n j - Nmat n j * H0 * Nmat n i) *ᵥ z) = 0 := by
  have hN : ∀ k, Nmat n k *ᵥ z = ν k • z := by
    intro k; funext c
    simp only [Nmat, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases h : z c = 0
    · rw [h, mul_zero, mul_zero]
    · rw [hz c h k]
  have hNv : z ᵥ* Nmat n j = ν j • z := by
    funext c
    simp only [Nmat, vecMul_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases h : z c = 0
    · rw [h, zero_mul, mul_zero]
    · rw [hz c h j, mul_comm]
  rw [sub_mulVec, dotProduct_sub]
  simp only [← mulVec_mulVec, hN, mulVec_smul, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_mulVec z (Nmat n j), hNv, smul_dotProduct, smul_eq_mul]
  ring

omit [Fintype V] [DecidableEq V] in
/-- **Equal occupations kill `K`.** If all configurations of `(x, y)` (those where `x` or `y` is
nonzero) have the same occupations `ν`, then `K(x, y) = 0`. No eigenstate condition and no
symmetry of `H0` are needed. -/
theorem kfb_eq_zero_of_occ_const (hν : ∀ c, (x c ≠ 0 ∨ y c ≠ 0) → ∀ i, n i c = ν i) :
    kfb H0 n (x, y) = 0 := by
  ext i j
  simp only [kfb, Qf,
    dotProduct_comm_occ_const (fun c hc => hν c (Or.inl hc)) i j,
    dotProduct_comm_occ_const (fun c hc => hν c (Or.inr hc)) i j, add_zero, mul_zero]
  rfl

/-- **Equal occupations lie outside `Ω`.** On a lattice with at least two sites, every state all
of whose configurations have the same occupations is outside `Ω`: `K + 𝟙𝟙ᵀ = 𝟙𝟙ᵀ` has two equal
rows. -/
theorem not_mem_omega_of_occ_const (hν : ∀ c, (x c ≠ 0 ∨ y c ≠ 0) → ∀ i, n i c = ν i)
    {i j : V} (hij : i ≠ j) : ((x, y) : (C → ℝ) × (C → ℝ)) ∉ omega H0 n := by
  intro hΩ
  apply hΩ
  rw [kJ, kfb_eq_zero_of_occ_const hν, zero_add]
  exact det_zero_of_row_eq hij (funext fun _ => rfl)

end occ

end DFT
