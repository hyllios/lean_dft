/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.KohnSham.Duality

/-!
# Ensemble v-representability

* `Ens H0 n v`: ground-state ensembles (density matrices supported on the ground-state space of
  `H(v)`), and their densities `ensDens`.
* `latticeScope_dens`, `mem_Ens_of_isEnsGS`: the ensemble ground states of the lattice scope
  (`latticeScope`) are the ground-state ensembles `Ens`, with the same densities.
* `ens_of_maximiser`: a maximiser `v` of `E(v) − v·ρ` makes `ρ` the density of a ground-state
  ensemble of `H(v)` (the scope's `exists_isEnsGS_of_isMax`).
* `ensemble_v_representable`: every strictly positive mixture of configuration densities is the
  density of a ground-state ensemble of some `H(v)` (the scope's `ensemble_vrep_of_extend`). With
  `H0` non-interacting this is the existence of a Kohn–Sham potential.
-/

namespace DFT

open Matrix

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [Nonempty C]

/-- Ground-state ensembles of `H(v)`: density matrices supported on the ground-state space. -/
def Ens (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : Set (Matrix C C ℝ) :=
  {Γ | Γᵀ = Γ ∧ (∀ x : C → ℝ, 0 ≤ x ⬝ᵥ (Γ *ᵥ x)) ∧ Γ.trace = 1 ∧ hamN H0 n v * Γ = Egs H0 n v • Γ}

/-- Density of an ensemble. -/
def ensDens (n : V → C → ℝ) (Γ : Matrix C C ℝ) : V → ℝ := fun i => ∑ c, n i c * Γ c c

omit [DecidableEq C] [Fintype V] [Nonempty C] in
lemma ensDens_vecMulVec (n : V → C → ℝ) (ψ : C → ℝ) : ensDens n (vecMulVec ψ ψ) = dens n ψ := by
  funext i; simp [ensDens, dens, vecMulVec, sq]

lemma pure_mem_Ens {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) {v : V → ℝ} {ψ : C → ℝ}
    (hψ : IsGroundState (hamN H0 n v) ψ) (hn : ψ ⬝ᵥ ψ = 1) : vecMulVec ψ ψ ∈ Ens H0 n v := by
  have heig : hamN H0 n v *ᵥ ψ = Egs H0 n v • ψ := by
    have := isGroundState_eigen (hamN_isSymm hH0 n v) hψ
    rw [hn, div_one, qf_groundState_eq (hamN_isSymm hH0 n v) hψ hn] at this
    exact this
  refine ⟨?_, fun x => ?_, ?_, ?_⟩
  · ext a b; simp [vecMulVec, mul_comm]
  · have : x ⬝ᵥ (vecMulVec ψ ψ *ᵥ x) = (ψ ⬝ᵥ x) * (ψ ⬝ᵥ x) := by
      simp only [vecMulVec, mulVec, dotProduct, of_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
    rw [this]; exact mul_self_nonneg _
  · simpa [Matrix.trace, vecMulVec, dotProduct] using hn
  · rw [mul_vecMulVec, heig]; ext a b; simp [vecMulVec, mul_assoc]

/-! ### The lattice scope -/

variable {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}

omit [Fintype V] [Nonempty C] in
lemma latticeScope_dens (Γ : Matrix C C ℝ) : (latticeScope H0 hH0 n).dens Γ = ensDens n Γ := by
  funext i
  simp [Scope.dens, Scope.trv, latticeScope, trace, ensDens, mul_comm]

lemma mem_Ens_of_isEnsGS {v : V → ℝ} {Γ : Matrix C C ℝ} (h : (latticeScope H0 hH0 n).IsEnsGS v Γ) :
    Γ ∈ Ens H0 n v := by
  have hP := h.1.1
  refine ⟨?_, fun x => ?_, h.1.2, ?_⟩
  · have := hP.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  · simpa using hP.dotProduct_mulVec_nonneg x
  · have := Scope.IsEnsGS.ham_mul _ h
    rwa [latticeScope_ham, latticeScope_E] at this

include hH0 in
/-- A maximiser of `v ↦ E(v) − v·ρ` makes `ρ` the density of a ground-state ensemble of `H(v)`. -/
theorem ens_of_maximiser {ρ vs : V → ℝ}
    (hmax : ∀ v, Egs H0 n v - v ⬝ᵥ ρ ≤ Egs H0 n vs - vs ⬝ᵥ ρ) :
    ∃ Γ ∈ Ens H0 n vs, ensDens n Γ = ρ := by
  obtain ⟨Γ, hΓ, hρ, -⟩ := (latticeScope H0 hH0 n).exists_isEnsGS_of_isMax (ρ := ρ) (v := vs)
    fun v => by simpa only [latticeScope_E, dotProduct_comm ρ] using hmax v
  exact ⟨Γ, mem_Ens_of_isEnsGS hH0 hΓ, (latticeScope_dens hH0 Γ).symm.trans hρ⟩

include hH0 in
/-- **Ensemble v-representability.** A strictly positive mixture of configuration densities is the
density of a ground-state ensemble of `H(v)` for some potential `v`. -/
theorem ensemble_v_representable {ρ : V → ℝ} {lam : C → ℝ} (hlam : ∀ c, 0 < lam c)
    (hsum : ∑ c, lam c = 1) (hρ : ρ = fun i => ∑ c, lam c * n i c) :
    ∃ v : V → ℝ, ∃ Γ ∈ Ens H0 n v, ensDens n Γ = ρ := by
  -- the smallest weight
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
  have hext : ∀ ρ' ∈ (latticeScope H0 hH0 n).Be, ∃ ε > (0 : ℝ),
      ρ + ε • (ρ - ρ') ∈ (latticeScope H0 hH0 n).Be := by
    intro ρ' hρ'
    rw [latticeScope_Be] at hρ' ⊢
    obtain ⟨μ, hμ0, hμ1, rfl⟩ := hρ'
    have hμle : ∀ c, μ c ≤ 1 := fun c => hμ1 ▸ Finset.single_le_sum (fun c _ => hμ0 c)
      (Finset.mem_univ c)
    refine ⟨lam c₀, hlam c₀, fun c => lam c + lam c₀ * (lam c - μ c), fun c => ?_, ?_, ?_⟩
    · have := hc₀ c (Finset.mem_univ c)
      nlinarith [hlam c, hlam c₀, hμ0 c, hμle c]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hsum, hμ1]
    · subst hρ
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
  obtain ⟨v, Γ, hΓ, hρΓ, -⟩ := (latticeScope H0 hH0 n).ensemble_vrep_of_extend hext
  exact ⟨v, Γ, mem_Ens_of_isEnsGS hH0 hΓ, (latticeScope_dens hH0 Γ).symm.trans hρΓ⟩

end DFT
