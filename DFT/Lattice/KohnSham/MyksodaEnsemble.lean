/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.KohnSham.RegularizedKS
import DFT.Lattice.KohnSham.Representability

/-!
# The limit densities of the regularized Kohn–Sham scheme are ground-state-ensemble densities

`lattice_myksoda` (the regularized Kohn–Sham iteration) concludes that the limit densities minimize
the Lieb energy, `F(ρ) + v·ρ = E(v)` with `ρ` in the density domain. `lieb` is the Legendre form
`sup_v [E(v) − v·ρ]`, so this says that `v` maximizes `E(·) − (·)·ρ`; a maximizer gives a
ground-state ensemble (the second half of `ensemble_v_representable`, whose argument is copied here:
separation from the compact convex set of ensemble densities, `exists_gs_below`).

* `ens_of_maximiser`, `maximiser_of_lieb_eq`, `ens_of_lieb_eq`.
* `lattice_myksoda_ensemble`: for every accumulation point `z`, `ρ = z + εv` is the density of a
  ground-state ensemble of the interacting `H(v)` and `ρ_KS = z + εv_KS` of the reference `H(v_KS)`
  (occupations nonnegative, fixed particle number).
-/

namespace DFT

open Matrix Filter Topology RealInnerProductSpace

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [Nonempty C]

/-- A maximizer of v ↦ E(v) − v·ρ makes ρ the density of a ground-state ensemble. -/
theorem ens_of_maximiser {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}
    (hn0 : ∀ i c, 0 ≤ n i c) {Nr : ℝ} (hN : ∀ c, ∑ i, n i c = Nr) {ρ vs : V → ℝ}
    (hmax : ∀ v, Egs H0 n v - v ⬝ᵥ ρ ≤ Egs H0 n vs - vs ⬝ᵥ ρ) :
    ∃ Γ ∈ Ens H0 n vs, ensDens n Γ = ρ := by
  classical
  by_contra hno
  push Not at hno
  have hρt : ρ ∉ Set.image (ensDens n) (Ens H0 n vs) := fun ⟨Γ, hΓ, h⟩ => hno Γ hΓ h
  have hconv : Convex ℝ (Set.image (ensDens n) (Ens H0 n vs)) := by
    apply (convex_Ens H0 n vs).is_linear_image
    refine ⟨fun Γ1 Γ2 => ?_, fun a Γ => ?_⟩
    · funext i; simp [ensDens, mul_add, Finset.sum_add_distrib]
    · funext i
      simp only [ensDens, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro c _; ring
  have hclosed : IsClosed (Set.image (ensDens n) (Ens H0 n vs)) :=
    ((isCompact_Ens H0 n vs).image (continuous_ensDens n)).isClosed
  obtain ⟨f, u, hfρ, hft⟩ := geometric_hahn_banach_point_closed hconv hclosed hρt
  set w : V → ℝ := fun i => f (fun j => if i = j then 1 else 0)
  have hf : ∀ x, f x = w ⬝ᵥ x := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (V → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this, dotProduct]; apply Finset.sum_congr rfl; intro i _; ring
  obtain ⟨ψ, hψ, hn, hle⟩ := exists_gs_below hH0 hn0 hN hmax w
  have hin : dens n ψ ∈ Set.image (ensDens n) (Ens H0 n vs) :=
    ⟨vecMulVec ψ ψ, pure_mem_Ens hH0 n hψ hn, ensDens_vecMulVec n ψ⟩
  have h1 := hft _ hin
  rw [hf] at h1 hfρ
  linarith

/-- On the density domain, the Lieb equality makes v a maximizer of v' ↦ E(v') − v'·ρ. -/
theorem maximiser_of_lieb_eq {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} {ρ v : V → ℝ}
    (hρ : ρ ∈ DensDomain n) (heq : lieb H0 n ρ + v ⬝ᵥ ρ = Egs H0 n v) :
    ∀ v', Egs H0 n v' - v' ⬝ᵥ ρ ≤ Egs H0 n v - v ⬝ᵥ ρ := by
  intro v'
  have := le_lieb hH0 n hρ v'
  linarith

/-- A density in the domain that minimizes the Lieb energy in v is a ground-state-ensemble density
of H(v). -/
theorem ens_of_lieb_eq {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}
    (hn0 : ∀ i c, 0 ≤ n i c) {Nr : ℝ} (hN : ∀ c, ∑ i, n i c = Nr) {ρ v : V → ℝ}
    (hρ : ρ ∈ DensDomain n) (heq : lieb H0 n ρ + v ⬝ᵥ ρ = Egs H0 n v) :
    ∃ Γ ∈ Ens H0 n v, ensDens n Γ = ρ :=
  ens_of_maximiser hH0 hn0 hN (maximiser_of_lieb_eq hH0 hρ heq)

/-- `lattice_myksoda` with its Lieb-energy conclusions read as ground-state ensembles. -/
theorem lattice_myksoda_ensemble {ε : ℝ} {H0 H0' : Matrix C C ℝ} {n : V → C → ℝ} (hε : 0 < ε)
    (hH0 : H0.IsSymm) (hH0' : H0'.IsSymm) (hn0 : ∀ i c, 0 ≤ n i c) {Nr : ℝ}
    (hN : ∀ c, ∑ i, n i c = Nr)
    (v : EuclideanSpace ℝ V) {x x' : ℕ → EuclideanSpace ℝ V}
    (hb : ∀ i, gFreg H0' n ε (x' i) = -(v + gFreg H0 n ε (x i) - gFreg H0' n ε (x i)))
    (hc : ∀ i, x (i + 1) = x i + ksStep ε (gFreg H0 n ε (x i) + v) (x' i - x i) • (x' i - x i))
    (z : EuclideanSpace ℝ V) (φ : ℕ → ℕ) (hφ : StrictMono φ) (hz : Tendsto (x ∘ φ) atTop (𝓝 z)) :
    (∃ Γ ∈ Ens H0 n (WithLp.ofLp v), ensDens n Γ = WithLp.ofLp (z + ε • v)) ∧
      ∃ vKS : EuclideanSpace ℝ V,
        Tendsto (fun i => v + gFreg H0 n ε (x (φ i)) - gFreg H0' n ε (x (φ i))) atTop (𝓝 vKS) ∧
        ∃ Γ' ∈ Ens H0' n (WithLp.ofLp vKS), ensDens n Γ' = WithLp.ofLp (z + ε • vKS) := by
  obtain ⟨-, -, hlim⟩ := lattice_myksoda hε hH0 hH0' v hb hc
  obtain ⟨-, -, ⟨hdom, heq⟩, vKS, hvKS, hdom', heq'⟩ := hlim z φ hφ hz
  exact ⟨ens_of_lieb_eq hH0 hn0 hN hdom heq, vKS, hvKS, ens_of_lieb_eq hH0' hn0 hN hdom' heq'⟩

end DFT
