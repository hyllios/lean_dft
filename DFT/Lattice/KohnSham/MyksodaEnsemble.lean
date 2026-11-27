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
`sup_v [E(v) − v·ρ]`, so this says that `v` maximizes `E(·) − (·)·ρ`, and a maximizer gives a
ground-state ensemble (`ens_of_maximiser`, from the scope framework).

* `maximiser_of_lieb_eq`, `ens_of_lieb_eq`.
* `lattice_myksoda_ensemble`: for every accumulation point `z`, `ρ = z + εv` is the density of a
  ground-state ensemble of the interacting `H(v)` and `ρ_KS = z + εv_KS` of the reference `H(v_KS)`.
-/

namespace DFT

open Matrix Filter Topology RealInnerProductSpace

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [Nonempty C]

/-- On the density domain, the Lieb equality makes v a maximizer of v' ↦ E(v') − v'·ρ. -/
theorem maximiser_of_lieb_eq {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} {ρ v : V → ℝ}
    (hρ : ρ ∈ DensDomain n) (heq : lieb H0 n ρ + v ⬝ᵥ ρ = Egs H0 n v) :
    ∀ v', Egs H0 n v' - v' ⬝ᵥ ρ ≤ Egs H0 n v - v ⬝ᵥ ρ := by
  intro v'
  have := le_lieb hH0 n hρ v'
  linarith

/-- A density in the domain that minimizes the Lieb energy in v is a ground-state-ensemble density
of H(v). -/
theorem ens_of_lieb_eq {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} {ρ v : V → ℝ}
    (hρ : ρ ∈ DensDomain n) (heq : lieb H0 n ρ + v ⬝ᵥ ρ = Egs H0 n v) :
    ∃ Γ ∈ Ens H0 n v, ensDens n Γ = ρ :=
  ens_of_maximiser hH0 (maximiser_of_lieb_eq hH0 hρ heq)

/-- `lattice_myksoda` with its Lieb-energy conclusions read as ground-state ensembles. -/
theorem lattice_myksoda_ensemble {ε : ℝ} {H0 H0' : Matrix C C ℝ} {n : V → C → ℝ} (hε : 0 < ε)
    (hH0 : H0.IsSymm) (hH0' : H0'.IsSymm)
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
  exact ⟨ens_of_lieb_eq hH0 hdom heq, vKS, hvKS, ens_of_lieb_eq hH0' hdom' heq'⟩

end DFT
