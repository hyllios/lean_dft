/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Convex.Function
import DFT.Lattice.Basic.Spectral
import DFT.Lattice.HK.Basic
import DFT.Scope.Representability

/-!
# Lieb's functional and convex duality

Setting: configurations `C`, sites `V`, symmetric `H0`, occupations `n`; `E(v)` is the ground-state
energy of `H(v) = hamN H0 n v`.
* `DensDomain n`: densities `ρ = Σ_c λ_c n(c)` with `λ` a probability vector (ensemble densities of
  configurations).
* `lieb ρ = sup_v [E(v) − v·ρ]`: Lieb's universal functional (Legendre transform of `E`).
* `lieb_duality`: `E(v) = min_{ρ ∈ DensDomain} [F(ρ) + v·ρ]`, the minimum being attained at the
  density of any ground state of `H(v)`.
* `lieb_convexOn`: `F` is convex on the density domain.

Lattice DFT as a scope (`latticeScope`, the observables being the occupations `n_i`, after
Wang–Liebert–Penz–Schilling): `latticeScope_E` (same ground-state energy),
`latticeScope_Bp`, `latticeScope_Be` (both ranges are the density domain, the hypersimplex for
spinless fermions), and `lieb_eq_Fe` (Lieb's functional is the scope's ensemble functional).
`lieb_convexOn` is derived from the scope's `convexOn_Fe`.
-/

namespace DFT

open Matrix

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [Nonempty C]

/-- Ground-state energy as a function of the potential. -/
noncomputable def Egs (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : ℝ := gsEnergy (hamN H0 n v)

/-- Ensemble densities of configurations. -/
def DensDomain (n : V → C → ℝ) : Set (V → ℝ) :=
  {ρ | ∃ lam : C → ℝ, (∀ c, 0 ≤ lam c) ∧ ∑ c, lam c = 1 ∧ ρ = fun i => ∑ c, lam c * n i c}

/-- **Lieb's universal functional.** -/
noncomputable def lieb (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ρ : V → ℝ) : ℝ :=
  sSup (Set.range fun v : V → ℝ => Egs H0 n v - v ⬝ᵥ ρ)

lemma Egs_le_config {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) (v : V → ℝ) (c : C) :
    Egs H0 n v ≤ H0 c c + ∑ i, v i * n i c := by
  have h := gsEnergy_le (hamN_isSymm hH0 n v) (φ := Pi.single c 1) (by simp)
  unfold Egs
  refine h.trans (le_of_eq ?_)
  rw [qf_hamN]
  simp [qf, dens, Pi.single_apply, mulVec, dotProduct]

lemma lieb_bdd {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) {ρ : V → ℝ}
    (hρ : ρ ∈ DensDomain n) : BddAbove (Set.range fun v : V → ℝ => Egs H0 n v - v ⬝ᵥ ρ) := by
  obtain ⟨lam, hl0, hl1, rfl⟩ := hρ
  refine ⟨∑ c, lam c * H0 c c, ?_⟩
  rintro _ ⟨v, rfl⟩
  have : Egs H0 n v = ∑ c, lam c * Egs H0 n v := by rw [← Finset.sum_mul, hl1, one_mul]
  have hdot : v ⬝ᵥ (fun i => ∑ c, lam c * n i c) = ∑ c, lam c * ∑ i, v i * n i c := by
    simp only [dotProduct, Finset.mul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro i _; ring
  simp only
  rw [this, hdot, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum; intro c _
  have := Egs_le_config hH0 n v c
  nlinarith [hl0 c]

lemma le_lieb {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) {ρ : V → ℝ}
    (hρ : ρ ∈ DensDomain n) (v : V → ℝ) : Egs H0 n v - v ⬝ᵥ ρ ≤ lieb H0 n ρ :=
  le_csSup (lieb_bdd hH0 n hρ) ⟨v, rfl⟩

omit [DecidableEq C] [Fintype V] [Nonempty C] in
lemma dens_mem_domain (n : V → C → ℝ) {ψ : C → ℝ} (hn : ψ ⬝ᵥ ψ = 1) : dens n ψ ∈ DensDomain n := by
  refine ⟨fun c => ψ c ^ 2, fun c => sq_nonneg _, by simpa [dotProduct, sq] using hn, ?_⟩
  funext i; simp [dens, mul_comm]

/-- **Lieb duality.** `E(v) ≤ F(ρ) + v·ρ` on the density domain, with equality at ground-state
densities. -/
theorem lieb_duality {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) (v : V → ℝ) :
    (∀ ρ ∈ DensDomain n, Egs H0 n v ≤ lieb H0 n ρ + v ⬝ᵥ ρ) ∧
    ∀ ψ, IsGroundState (hamN H0 n v) ψ → ψ ⬝ᵥ ψ = 1 →
      Egs H0 n v = lieb H0 n (dens n ψ) + v ⬝ᵥ dens n ψ := by
  refine ⟨fun ρ hρ => by linarith [le_lieb hH0 n hρ v], fun ψ hψ hn => ?_⟩
  have hdom := dens_mem_domain n hn
  have hE : Egs H0 n v = qf H0 ψ + v ⬝ᵥ dens n ψ := by
    unfold Egs
    rw [← qf_groundState_eq (hamN_isSymm hH0 n v) hψ hn, qf_hamN]
    simp [dotProduct]
  have hle : lieb H0 n (dens n ψ) ≤ qf H0 ψ := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨v', rfl⟩
    have := gsEnergy_le (hamN_isSymm hH0 n v') hn
    rw [qf_hamN] at this
    unfold Egs
    have hd : ∑ i, v' i * dens n ψ i = v' ⬝ᵥ dens n ψ := rfl
    linarith
  have hge := le_lieb hH0 n hdom v
  linarith

/-! ### Lattice DFT as a scope -/

/-- **Lattice DFT as a scope**: the observables are the occupations `n_i`. -/
noncomputable def latticeScope (H0 : Matrix C C ℝ) (hH0 : H0.IsSymm) (n : V → C → ℝ) :
    Scope ℝ C V where
  H0 := H0
  B i := diagonal (n i)
  isHermitian_H0 := by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hH0
  isHermitian_B i := isHermitian_diagonal _

variable {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ)

omit [DecidableEq C] [Fintype V] [Nonempty C] in
lemma expv_eq_qf (A : Matrix C C ℝ) (ψ : C → ℝ) : Scope.expv A ψ = qf A ψ := by
  simp [Scope.expv, qf]

omit [DecidableEq C] [Fintype V] [Nonempty C] in
lemma mem_unitVecs_iff {ψ : C → ℝ} : ψ ∈ Scope.unitVecs ↔ ψ ⬝ᵥ ψ = 1 := by
  simp [Scope.unitVecs]

omit [Fintype C] [Nonempty C] in
lemma latticeScope_ham (v : V → ℝ) : (latticeScope H0 hH0 n).ham v = hamN H0 n v := by
  simp only [Scope.ham, Scope.pot, latticeScope, hamN]
  congr 1
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

omit [Fintype V] [Nonempty C] in
lemma latticeScope_densPure (ψ : C → ℝ) : (latticeScope H0 hH0 n).densPure ψ = dens n ψ := by
  funext i
  simp only [Scope.densPure, latticeScope, expv_eq_qf, qf, mulVec_diagonal, dotProduct, dens]
  exact Finset.sum_congr rfl fun c _ => by ring

lemma latticeScope_E (v : V → ℝ) : (latticeScope H0 hH0 n).E v = Egs H0 n v := by
  have hS := hamN_isSymm hH0 n v
  refine le_antisymm ?_ ?_
  · obtain ⟨hg, hn⟩ := Classical.choose_spec (exists_groundState hS)
    have h := (latticeScope H0 hH0 n).E_le v (mem_unitVecs_iff.2 hn)
    rwa [latticeScope_ham, expv_eq_qf, qf_groundState_eq hS hg hn] at h
  · obtain ⟨ψ, hψ, hE⟩ := (latticeScope H0 hH0 n).exists_isGS v
    rw [← hE, latticeScope_ham, expv_eq_qf]
    exact gsEnergy_le hS (mem_unitVecs_iff.1 hψ)

omit [Fintype V] [Nonempty C] in
/-- The pure range is the density domain. -/
lemma latticeScope_Bp : (latticeScope H0 hH0 n).Bp = DensDomain n := by
  ext ρ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    rw [latticeScope_densPure]
    exact dens_mem_domain n (mem_unitVecs_iff.1 hψ)
  · rintro ⟨lam, hl0, hl1, rfl⟩
    refine ⟨fun c => Real.sqrt (lam c), mem_unitVecs_iff.2 ?_, ?_⟩
    · simp only [dotProduct]
      rw [← hl1]
      exact Finset.sum_congr rfl fun c _ => Real.mul_self_sqrt (hl0 c)
    · rw [latticeScope_densPure]
      funext i
      simp only [dens]
      exact Finset.sum_congr rfl fun c _ => by rw [Real.sq_sqrt (hl0 c), mul_comm]

omit [DecidableEq C] [Fintype V] [Nonempty C] in
lemma convex_densDomain : Convex ℝ (DensDomain n) := by
  rintro ρ ⟨l1, h10, h11, rfl⟩ ρ' ⟨l2, h20, h21, rfl⟩ a b ha hb hab
  refine ⟨fun c => a * l1 c + b * l2 c, fun c => by nlinarith [h10 c, h20 c], ?_, ?_⟩
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, h11, h21, hab]
  · funext i; simp [Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_assoc]

omit [Fintype V] [Nonempty C] in
/-- The ensemble range is the density domain. -/
lemma latticeScope_Be : (latticeScope H0 hH0 n).Be = DensDomain n := by
  rw [Scope.Be_eq_convexHull_Bp, latticeScope_Bp, (convex_densDomain n).convexHull_eq]

/-- **Lieb's functional is the ensemble functional of the lattice scope.** -/
theorem lieb_eq_Fe {ρ : V → ℝ} (hρ : ρ ∈ DensDomain n) :
    lieb H0 n ρ = ((latticeScope H0 hH0 n).Fe ρ).toReal := by
  have hρB : ρ ∈ (latticeScope H0 hH0 n).Be := (latticeScope_Be hH0 n).symm ▸ hρ
  refine le_antisymm (csSup_le (Set.range_nonempty _) ?_) ?_
  · rintro _ ⟨v, rfl⟩
    have := (latticeScope H0 hH0 n).E_sub_le_Fe hρB v
    rwa [latticeScope_E, dotProduct_comm] at this
  · have h := (latticeScope H0 hH0 n).Fe_eq_iSup hρB
    rw [(latticeScope H0 hH0 n).Fe_eq_toReal hρB] at h
    refine EReal.coe_le_coe_iff.1 (h ▸ iSup_le fun v => EReal.coe_le_coe_iff.2 ?_)
    rw [latticeScope_E, dotProduct_comm]
    exact le_lieb hH0 n hρ v

include hH0 in
/-- **Convexity of Lieb's functional**, from the convexity of the scope's ensemble functional. -/
theorem lieb_convexOn : ConvexOn ℝ (DensDomain n) (lieb H0 n) := by
  have h := (latticeScope H0 hH0 n).convexOn_Fe
  rw [latticeScope_Be] at h
  exact h.congr fun ρ hρ => (lieb_eq_Fe hH0 n hρ).symm

end DFT
