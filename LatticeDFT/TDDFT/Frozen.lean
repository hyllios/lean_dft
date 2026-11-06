/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.TDDFT.Existence
import LatticeDFT.Spin.HubbardCertificates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Frozen densities: a total failure of TDDFT uniqueness

If an eigenvector `x` of `H0` has all of its configurations at the same occupations `ν`, then `x`
is an eigenvector of `H0 + v·n` for *every* potential, the evolution only changes a global phase,
and the density stays `ν`-weighted forever, whatever `v(t)` is. The potential is then completely
undetermined by the density, not just up to a constant.

* `hamN_mulVec_frozen`, `frozenPath_hasDerivAt`, `tdens_frozenPath`: the explicit trajectory
  `ψ(t) = (cos θ(t) x, -sin θ(t) x)`, `θ̇ = E + Σ_i v_i(t) ν_i`, for every continuous `v(t)`.
* `not_mem_omega_of_frozen`: such a state lies outside `Ω` (proved from `td_uniqueness`: two
  different gauge-fixed potentials give the same density).
* `hubbard_triplet_frozen`, `hubbard_triplet_not_mem_omega`: the Hubbard dimer at half filling.
  The `S_z = 0` triplet `|↑,↓⟩ - |↓,↑⟩` has no double occupancy, is annihilated by the hopping for
  every `t` and `U`, and has density `(1, 1)` under every time-dependent spin-independent potential.

Farzanehpour and Tokatly (PRB 86, 125130 (2012), appendix) remark that "the dynamics of a triplet
state on two sites is trivial" and restrict to singlets; here this is made precise as a failure of
TDDFT uniqueness. On a general lattice the same is expected for every maximal-spin state at half
filling (by SU(2) symmetry, hopping cannot create double occupancy in it), but that is not proved
here.
-/

namespace LatticeDFT

open Matrix Set Filter Topology

section frozen

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
  {H0 : Matrix C C ℝ} {n : V → C → ℝ} {x : C → ℝ} {E : ℝ} {ν : V → ℝ}

omit [DecidableEq V] in
/-- A frozen eigenvector is an eigenvector of `H0 + v·n` for every `v`. -/
lemma hamN_mulVec_frozen (hx : H0 *ᵥ x = E • x) (hν : ∀ c, x c ≠ 0 → ∀ i, n i c = ν i)
    (w : V → ℝ) : hamN H0 n w *ᵥ x = (E + ∑ i, w i * ν i) • x := by
  funext c
  simp only [hamN, add_mulVec, Pi.add_apply, hx, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : x c = 0
  · simp [h]
  · simp only [hν c h]; ring

/-- The accumulated phase `θ(t) = ∫_{t₀}^t (E + Σ_i v_i ν_i)`. -/
noncomputable def frozenPhase (E : ℝ) (ν : V → ℝ) (v : ℝ → V → ℝ) (t0 t : ℝ) : ℝ :=
  ∫ s in t0..t, (E + ∑ i, v s i * ν i)

/-- The frozen trajectory `(cos θ · x, -sin θ · x)`. -/
noncomputable def frozenPath (x : C → ℝ) (θ : ℝ → ℝ) (t : ℝ) : (C → ℝ) × (C → ℝ) :=
  (Real.cos (θ t) • x, -(Real.sin (θ t) • x))

omit [DecidableEq V] in
/-- **The frozen trajectory solves the Schrödinger equation for every continuous potential.** -/
theorem frozenPath_hasDerivAt (hx : H0 *ᵥ x = E • x) (hν : ∀ c, x c ≠ 0 → ∀ i, n i c = ν i)
    {v : ℝ → V → ℝ} (hv : Continuous v) (t0 t : ℝ) :
    HasDerivAt (frozenPath x (frozenPhase E ν v t0))
      (schr H0 n (v t) (frozenPath x (frozenPhase E ν v t0) t)) t := by
  set θ := frozenPhase E ν v t0
  set lam := E + ∑ i, v t i * ν i
  have hf : Continuous fun s => E + ∑ i, v s i * ν i :=
    continuous_const.add (continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hv).mul continuous_const)
  have hθ : HasDerivAt θ lam t := (hf.integral_hasStrictDerivAt t0 t).hasDerivAt
  have hc := (Real.hasDerivAt_cos (θ t)).comp t hθ
  have hs := (Real.hasDerivAt_sin (θ t)).comp t hθ
  have h1 := hc.smul_const x
  have h2 := (hs.smul_const x).neg
  have h : HasDerivAt (frozenPath x θ) _ t := h1.prodMk h2
  convert h using 1
  simp only [schr, frozenPath, mulVec_neg, mulVec_smul, hamN_mulVec_frozen hx hν, smul_smul,
    Prod.mk.injEq, lam]
  refine ⟨?_, ?_⟩ <;>
    first | trivial | (funext c; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring)

omit [Fintype V] [DecidableEq V] in
/-- The density along the frozen trajectory never changes. -/
lemma tdens_frozenPath (θ : ℝ → ℝ) (t : ℝ) (i : V) :
    tdens n (frozenPath x θ t) i = tdens n (x, 0) i := by
  simp only [tdens, Qf, frozenPath, mulVec_neg, mulVec_smul, dotProduct_neg, neg_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, mulVec_zero, dotProduct_zero,
    add_zero]
  have := Real.cos_sq_add_sin_sq (θ t)
  linear_combination (x ⬝ᵥ (Nmat n i *ᵥ x)) * this

omit [Fintype C] [DecidableEq C] in
lemma frozenPath_zero {θ : ℝ → ℝ} {t0 : ℝ} (h : θ t0 = 0) : frozenPath x θ t0 = (x, 0) := by
  simp [frozenPath, h]

omit [DecidableEq V] in
lemma frozenPhase_self (v : ℝ → V → ℝ) (t0 : ℝ) : frozenPhase E ν v t0 t0 = 0 := by
  simp [frozenPhase]

/-- **Frozen states lie outside `Ω`.** Two different gauge-fixed potentials (`0` and a constant
`e_i - e_j`) drive the frozen state with the same density; if the state were in `Ω`,
`td_uniqueness` would force the potentials to agree. -/
theorem not_mem_omega_of_frozen (hH0 : H0.IsSymm) (hx : H0 *ᵥ x = E • x)
    (hν : ∀ c, x c ≠ 0 → ∀ i, n i c = ν i) {i j : V} (hij : i ≠ j) :
    ((x, 0) : (C → ℝ) × (C → ℝ)) ∉ omega H0 n := by
  intro hΩ
  set w : V → ℝ := fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)
  have hw : ∑ k, w k = 0 := by simp [w, Finset.sum_sub_distrib]
  set v1 : ℝ → V → ℝ := fun _ => 0
  set v2 : ℝ → V → ℝ := fun _ => w
  have hpath : ∀ v : ℝ → V → ℝ, Continuous v → (∑ k, v 0 k = 0) → (∀ s, v s = v 0) →
      ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (frozenPath x (frozenPhase E ν v 0))
        (schr H0 n (v t) (frozenPath x (frozenPhase E ν v 0) t)) t ∧ ∑ k, v t k = 0 ∧
        ∀ k, tdens n (frozenPath x (frozenPhase E ν v 0) t) k = tdens n (x, 0) k := by
    intro v hv h0 hconst
    exact Eventually.of_forall fun t =>
      ⟨frozenPath_hasDerivAt hx hν hv 0 t, by rw [hconst t]; exact h0,
        fun k => tdens_frozenPath _ t k⟩
  have hu := td_uniqueness (nn := fun _ k => tdens n ((x, 0) : (C → ℝ) × (C → ℝ)) k)
    (nd := fun _ _ => 0) (ndd := fun _ _ => 0) hH0 (fun _ => hasDerivAt_const _ _)
    (fun _ => hasDerivAt_const _ _) continuous_const hΩ
    (hpath v1 continuous_const (by simp [v1]) fun _ => rfl)
    (hpath v2 continuous_const hw fun _ => rfl)
    (frozenPath_zero (frozenPhase_self _ _)) (frozenPath_zero (frozenPhase_self _ _))
  have h0 : v1 0 = v2 0 := hu.2.self_of_nhds
  have := congrFun h0 i
  simp [v1, v2, w, hij] at this

end frozen

section hubbard

/-- The Hubbard dimer with one up and one down electron, hopping `t` and on-site `U`.
Configuration `(a, b)` (up on `a`, down on `b`) has index `2a + b`. -/
def hubD (t U : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![U, -t, -t, 0; -t, 0, 0, -t; -t, 0, 0, -t; 0, -t, -t, U]

/-- The `S_z = 0` triplet `|↑₀↓₁⟩ - |↓₀↑₁⟩`. -/
def tripD : Fin 4 → ℝ := ![0, 1, -1, 0]

lemma hubD_isSymm (t U : ℝ) : (hubD t U).IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hubD]

lemma hubD_triplet (t U : ℝ) : hubD t U *ᵥ tripD = (0 : ℝ) • tripD := by
  ext i; fin_cases i <;> simp [hubD, tripD, mulVec, dotProduct, Fin.sum_univ_four]

lemma triplet_occ (c : Fin 4) (hc : tripD c ≠ 0) (i : Fin 2) : occD i c = 1 := by
  fin_cases c <;> fin_cases i <;> simp_all [tripD, occD]

/-- **The frozen triplet.** For every hopping `t`, every `U` and every continuous time-dependent
spin-independent potential `v(t)`, the triplet evolves only by a phase and its density stays
`(2, 2)` (that is `(1, 1)` per unit norm: `tripD` has norm `√2`). -/
theorem hubbard_triplet_frozen (t U : ℝ) {v : ℝ → Fin 2 → ℝ} (hv : Continuous v) (t0 s : ℝ) :
    HasDerivAt (frozenPath tripD (frozenPhase 0 (fun _ => 1) v t0))
      (schr (hubD t U) occD (v s) (frozenPath tripD (frozenPhase 0 (fun _ => 1) v t0) s)) s ∧
      ∀ i, tdens occD (frozenPath tripD (frozenPhase 0 (fun _ => 1) v t0) s) i = 2 := by
  refine ⟨frozenPath_hasDerivAt (hubD_triplet t U) triplet_occ hv t0 s, fun i => ?_⟩
  rw [tdens_frozenPath]
  fin_cases i <;> simp [tdens, Qf, Nmat, occD, tripD, dotProduct, mulVec, Matrix.diagonal,
    Fin.sum_univ_four] <;> norm_num

/-- **The triplet is outside `Ω`** for every `t` and `U`: its density cannot determine the
potential. -/
theorem hubbard_triplet_not_mem_omega (t U : ℝ) :
    ((tripD, 0) : (Fin 4 → ℝ) × (Fin 4 → ℝ)) ∉ omega (hubD t U) occD :=
  not_mem_omega_of_frozen (hubD_isSymm t U) (hubD_triplet t U) triplet_occ
    (i := 0) (j := 1) (by decide)

end hubbard

end LatticeDFT
