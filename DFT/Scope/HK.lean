/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import ForMathlib.Analysis.Matrix.RealGram
import DFT.Scope.Basic

/-!
# Critical states and the Hohenberg–Kohn theorems for a scope

* `IsGS.mulVec_eq`: a ground state is an eigenvector, `H(v) ψ = E(v) ψ`.
* `isCritical_iff`, `isCritical_iff_det`: for a non-redundant scope, `ψ` is critical iff
  `ψ, B_1 ψ, …, B_m ψ` are linearly dependent over `ℝ`, iff their real Gram determinant vanishes.
* `weak_hk`, `weak_hk_ens`: if ground states of `H(v₁)` and `H(v₂)` have the same density, each is
  a ground state of the other Hamiltonian (pure states and ensembles).
* `strong_hk`: if a regular value `ρ ∈ B_r` is the density of a pure ground state of `H(v)` and of
  `H(v')`, then `ι(v - v') ∈ ℝ·1`; `strong_hk_eq`: for a non-redundant scope, `v = v'`.
-/

namespace DFT.Scope

open Matrix RCLike Set
open scoped ComplexOrder

variable {𝕜 d m : Type*} [RCLike 𝕜] [Fintype d] [Fintype m] (S : Scope 𝕜 d m)

/-- A ground state is an eigenvector of `H(v)` with eigenvalue `E(v)`. -/
lemma IsGS.mulVec_eq {S : Scope 𝕜 d m} {v : m → ℝ} {ψ : d → 𝕜} (h : S.IsGS v ψ) :
    S.ham v *ᵥ ψ = (S.E v : 𝕜) • ψ :=
  (S.isHermitian_ham v).mulVec_eq_of_le (fun _ hφ => S.E_le v hφ) h.1 h.2

/-! ### Critical states -/

omit [Fintype m] in
lemma ne_zero_of_mem_unitVecs {ψ : d → 𝕜} (hψ : ψ ∈ unitVecs) : ψ ≠ 0 := by
  rintro rfl
  simp [unitVecs] at hψ

omit [Fintype d] in
/-- In a non-redundant scope, `ι v ∈ ℝ·1` only for `v = 0`. -/
lemma eq_zero_of_pot_eq_smul_one [DecidableEq d] (hS : S.NoRedundancy) {v : m → ℝ} {c : ℝ}
    (h : S.pot v = (c : 𝕜) • 1) : v = 0 := by
  by_cases hc : c = 0
  · subst hc
    exact hS.1 (by rw [h, pot_zero]; simp)
  · refine absurd ?_ (hS.2 (c⁻¹ • v))
    rw [pot_smul, h, RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul, ← ofReal_mul,
      inv_mul_cancel₀ hc, ofReal_one, one_smul]

/-- **Critical states** of a non-redundant scope: `ψ` is critical iff `ψ, B_1 ψ, …, B_m ψ` are
linearly dependent over `ℝ`. -/
theorem isCritical_iff [DecidableEq d] (hS : S.NoRedundancy) {ψ : d → 𝕜} (hψ : ψ ∈ unitVecs) :
    S.IsCritical ψ ↔
      ¬LinearIndependent ℝ fun o : Option m => o.elim ψ fun i => S.B i *ᵥ ψ := by
  rw [Fintype.not_linearIndependent_iff]
  constructor
  · rintro ⟨v, hv, μ, hμ⟩
    -- the eigenvalue of a Hermitian matrix is real
    have hψ' : star ψ ⬝ᵥ ψ = 1 := hψ
    have hμr : μ = (re μ : 𝕜) := by
      have h := congrArg (fun x => star ψ ⬝ᵥ x) hμ
      simp only [dotProduct_smul, hψ', smul_eq_mul, mul_one] at h
      have him := (S.isHermitian_pot v).im_star_dotProduct_mulVec_self ψ
      rw [h] at him
      apply RCLike.ext <;> simp [him]
    set r := re μ
    rw [hμr] at hμ
    refine ⟨fun o => o.elim (-r) v, ?_, ?_⟩
    · rw [Fintype.sum_option]
      simp only [Option.elim]
      rw [← S.pot_mulVec, hμ, neg_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜), neg_add_cancel]
    · by_contra h0
      push Not at h0
      have : v = 0 := funext fun i => h0 (some i)
      exact hv 0 (by rw [this, pot_zero]; simp)
  · rintro ⟨g, hg, o, ho⟩
    rw [Fintype.sum_option] at hg
    simp only [Option.elim] at hg
    set v : m → ℝ := fun i => g (some i)
    have hpot : S.pot v *ᵥ ψ = ((-g none : ℝ) : 𝕜) • ψ := by
      rw [S.pot_mulVec, ← RCLike.real_smul_eq_coe_smul (K := 𝕜), neg_smul]
      exact eq_neg_of_add_eq_zero_right hg
    refine ⟨v, fun c hc => ?_, _, hpot⟩
    have hv := S.eq_zero_of_pot_eq_smul_one hS hc
    rw [hv, pot_zero, zero_mulVec] at hpot
    have hg0 : g none = 0 := by
      by_contra hne
      have := congrArg (fun x => (((-g none)⁻¹ : ℝ) : 𝕜) • x) hpot
      simp only [smul_zero, smul_smul, ← ofReal_mul,
        inv_mul_cancel₀ (neg_ne_zero.2 hne), ofReal_one, one_smul] at this
      exact ne_zero_of_mem_unitVecs hψ this.symm
    cases o with
    | none => exact ho hg0
    | some i => exact ho (congrFun hv i)

/-- **Critical states** of a non-redundant scope: `ψ` is critical iff the real Gram determinant
of `ψ, B_1 ψ, …, B_m ψ` vanishes. -/
theorem isCritical_iff_det [DecidableEq d] [DecidableEq m] (hS : S.NoRedundancy) {ψ : d → 𝕜}
    (hψ : ψ ∈ unitVecs) :
    S.IsCritical ψ ↔ (reGram fun o : Option m => o.elim ψ fun i => S.B i *ᵥ ψ).det = 0 := by
  rw [det_reGram_eq_zero_iff, S.isCritical_iff hS hψ]

/-! ### Hohenberg–Kohn -/

/-- **Weak Hohenberg–Kohn theorem** (pure states). -/
theorem weak_hk {v₁ v₂ : m → ℝ} {ψ₁ ψ₂ : d → 𝕜} (h₁ : S.IsGS v₁ ψ₁) (h₂ : S.IsGS v₂ ψ₂)
    (hρ : S.densPure ψ₁ = S.densPure ψ₂) : S.IsGS v₂ ψ₁ ∧ S.IsGS v₁ ψ₂ := by
  have e₁ := S.E_le v₁ h₂.1
  have e₂ := S.E_le v₂ h₁.1
  rw [← h₁.2] at e₁
  rw [← h₂.2] at e₂
  rw [expv_ham, expv_ham, hρ] at e₁ e₂
  refine ⟨⟨h₁.1, ?_⟩, ⟨h₂.1, ?_⟩⟩
  · rw [← h₂.2, expv_ham, expv_ham, hρ]; linarith
  · rw [← h₁.2, expv_ham, expv_ham, hρ]; linarith

/-- **Weak Hohenberg–Kohn theorem** (ensembles). -/
theorem weak_hk_ens {v₁ v₂ : m → ℝ} {Γ₁ Γ₂ : Matrix d d 𝕜} (h₁ : S.IsEnsGS v₁ Γ₁)
    (h₂ : S.IsEnsGS v₂ Γ₂) (hρ : S.dens Γ₁ = S.dens Γ₂) :
    S.IsEnsGS v₂ Γ₁ ∧ S.IsEnsGS v₁ Γ₂ := by
  have e₁ := S.E_le_trv v₁ h₂.1
  have e₂ := S.E_le_trv v₂ h₁.1
  rw [← h₁.2] at e₁
  rw [← h₂.2] at e₂
  rw [trv_ham, trv_ham, hρ] at e₁ e₂
  refine ⟨⟨h₁.1, ?_⟩, ⟨h₂.1, ?_⟩⟩
  · rw [← h₂.2, trv_ham, trv_ham, hρ]; linarith
  · rw [← h₁.2, trv_ham, trv_ham, hρ]; linarith

/-- **Strong Hohenberg–Kohn theorem**: if a regular value is the density of a pure ground state
of `H(v)` and of `H(v')`, the potentials differ by a multiple of the identity. -/
theorem strong_hk [DecidableEq d] {ρ : m → ℝ} (hρ : ρ ∈ S.Br) {v v' : m → ℝ} {ψ ψ' : d → 𝕜}
    (h : S.IsGS v ψ) (h' : S.IsGS v' ψ') (hψ : S.densPure ψ = ρ) (hψ' : S.densPure ψ' = ρ) :
    ∃ c : ℝ, S.pot (v - v') = (c : 𝕜) • 1 := by
  have hv' : S.IsGS v' ψ := (S.weak_hk h h' (hψ.trans hψ'.symm)).1
  by_contra hne
  push Not at hne
  refine hρ.2 ⟨ψ, ⟨h.1, v - v', hne, ((S.E v - S.E v' : ℝ) : 𝕜), ?_⟩, hψ⟩
  have e := h.mulVec_eq
  have e' := hv'.mulVec_eq
  simp only [ham, add_mulVec] at e e'
  rw [pot_sub, sub_mulVec, ofReal_sub, sub_smul]
  rw [← e, ← e']
  abel

/-- **Strong Hohenberg–Kohn theorem** for a non-redundant scope: `v = v'`. -/
theorem strong_hk_eq [DecidableEq d] (hS : S.NoRedundancy) {ρ : m → ℝ} (hρ : ρ ∈ S.Br)
    {v v' : m → ℝ} {ψ ψ' : d → 𝕜} (h : S.IsGS v ψ) (h' : S.IsGS v' ψ')
    (hψ : S.densPure ψ = ρ) (hψ' : S.densPure ψ' = ρ) : v = v' := by
  obtain ⟨c, hc⟩ := S.strong_hk hρ h h' hψ hψ'
  exact sub_eq_zero.1 (S.eq_zero_of_pot_eq_smul_one hS hc)

end DFT.Scope
