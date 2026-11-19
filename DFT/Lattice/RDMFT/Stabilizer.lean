/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.RDMFT.Basic

/-!
# The one-body stabilizer decides the RDMFT Hohenberg–Kohn theorem

Gilbert's step (`gilbert_weak`) reduces the question "does `γ` determine `h`?" to a question about
the ground state alone. If `ψ` is a ground state of both `H(h)` and `H(h')`, subtracting the two
eigenvalue equations gives `Γ(h' - h) ψ = c ψ`. So `h` is determined up to a constant as soon as
`ψ` is an eigenvector of no non-scalar one-body operator (`rdmDetermines_of_trivialStab`).

The converse holds for gapped ground states. If `Γ(d) ψ = c ψ` with `d` not scalar, the orthogonal
complement of `ψ` is invariant under `Γ(d)`, and the gap protects `ψ` against the small perturbation
`ε Γ(d)` (`persist_of_eigen`). So `ψ` stays the ground state of `H(h + ε d)` and `γ` does not
determine `h` (`not_rdmDetermines_of_stab`).

Lattice DFT asks the same question with `d` restricted to diagonal matrices. In RDMFT every one-body
operator is allowed, which is why failures are much more frequent (`RDMFT/Counting`).

* `TrivialStab ψ`: every symmetric `d` with `Γ(d) ψ ∈ ℝ ψ` is a multiple of the identity.
* `RDMDetermines W h`: `γ` determines `h` up to a constant.
* `rdmDetermines_of_trivialStab`: **trivial stabilizer ⇒ HK**.
* `abs_qf_le`, `persist_of_eigen`: a gapped ground state survives perturbations it is an
  eigenvector of.
* `not_rdmDetermines_of_stab`: **nontrivial stabilizer of a gapped ground state ⇒ no HK**.
-/

namespace DFT

section

open Matrix

variable {M N : ℕ}

/-- `ψ` is an eigenvector of no non-scalar symmetric one-body operator. -/
def TrivialStab (ψ : Conf M N → ℝ) : Prop :=
  ∀ d : Matrix (Fin M) (Fin M) ℝ, d.IsSymm → ∀ c : ℝ,
    (Γ d : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ ψ = c • ψ → ∃ c' : ℝ, d = c' • 1

/-- The one-body reduced density matrix of the ground state determines `h` up to a constant. -/
def RDMDetermines (W : Matrix (Conf M N) (Conf M N) ℝ) (h : Matrix (Fin M) (Fin M) ℝ) : Prop :=
  ∀ h' : Matrix (Fin M) (Fin M) ℝ, h'.IsSymm → ∀ ψ ψ' : Conf M N → ℝ,
    IsGroundState (hamR W h) ψ → IsGroundState (hamR W h') ψ' →
    ψ ⬝ᵥ ψ = 1 → ψ' ⬝ᵥ ψ' = 1 → rdm ψ = rdm ψ' → ∃ c : ℝ, h' = h + c • 1

/-- **Trivial one-body stabilizer ⇒ Hohenberg–Kohn for RDMFT.** -/
theorem rdmDetermines_of_trivialStab {W : Matrix (Conf M N) (Conf M N) ℝ} (hW : W.IsSymm)
    {h : Matrix (Fin M) (Fin M) ℝ} (hh : h.IsSymm)
    (hstab : ∀ ψ, IsGroundState (hamR W h) ψ → TrivialStab ψ) : RDMDetermines W h := by
  intro h' hh' ψ ψ' hψ hψ' hN hN' hd
  have hψ2 := (gilbert_weak hψ hψ' hN hN' hd).1
  have e1 := isGroundState_eigen (hamR_isSymm hW hh) hψ
  have e2 := isGroundState_eigen (hamR_isSymm hW hh') hψ2
  have key : (Γ (h' - h) : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ ψ =
      (qf (hamR W h') ψ / (ψ ⬝ᵥ ψ) - qf (hamR W h) ψ / (ψ ⬝ᵥ ψ)) • ψ := by
    have : (Γ (h' - h) : Matrix (Conf M N) (Conf M N) ℝ) = hamR W h' - hamR W h := by
      rw [gamma_sub, hamR, hamR]; abel
    rw [this, Matrix.sub_mulVec, e1, e2, sub_smul]
  obtain ⟨c', hc'⟩ := hstab ψ hψ (h' - h) (hh'.sub hh) _ key
  exact ⟨c', sub_eq_iff_eq_add'.mp hc'⟩

variable {C : Type*} [Fintype C]

/-- `|⟨χ, P χ⟩| ≤ (Σ |P_ss'|) ‖χ‖²`. -/
lemma abs_qf_le (P : Matrix C C ℝ) (χ : C → ℝ) :
    |qf P χ| ≤ (∑ s, ∑ s', |P s s'|) * (χ ⬝ᵥ χ) := by
  have hsq : ∀ s, χ s * χ s ≤ χ ⬝ᵥ χ := fun s =>
    Finset.single_le_sum (f := fun j => χ j * χ j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ s)
  have hb : ∀ s s', |χ s| * |χ s'| ≤ χ ⬝ᵥ χ := by
    intro s s'
    have h1 := hsq s; have h2 := hsq s'
    nlinarith [abs_mul_abs_self (χ s), abs_mul_abs_self (χ s'), sq_nonneg (|χ s| - |χ s'|)]
  have hqf : qf P χ = ∑ s, ∑ s', χ s * (P s s' * χ s') := by
    simp only [qf, dotProduct, mulVec, Finset.mul_sum]
  rw [hqf, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s' _ => ?_)
  rw [abs_mul, abs_mul]
  calc |χ s| * (|P s s'| * |χ s'|) = |P s s'| * (|χ s| * |χ s'|) := by ring
    _ ≤ |P s s'| * (χ ⬝ᵥ χ) := mul_le_mul_of_nonneg_left (hb s s') (abs_nonneg _)

/-- A ground state with gap `g` remains the ground state of `H + ε P` when it is an eigenvector of
the symmetric perturbation `P` and `|ε| (m + |c|) ≤ g`, where `m` bounds `|⟨χ, P χ⟩| / ‖χ‖²`. -/
theorem persist_of_eigen {H P : Matrix C C ℝ} (hH : H.IsSymm) (hP : P.IsSymm) {ψ : C → ℝ}
    (hψ : IsGroundState H ψ) (hN : ψ ⬝ᵥ ψ = 1) {g c m ε : ℝ}
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf H ψ + g) * (χ ⬝ᵥ χ) ≤ qf H χ)
    (hPψ : P *ᵥ ψ = c • ψ) (hm : ∀ χ, |qf P χ| ≤ m * (χ ⬝ᵥ χ)) (hε : |ε| * (m + |c|) ≤ g) :
    IsGroundState (H + ε • P) ψ := by
  classical
  have hS : (H + ε • P).IsSymm := hH.add (hP.smul ε)
  have hE : H *ᵥ ψ = (qf H ψ) • ψ := by
    have := isGroundState_eigen hH hψ; rwa [hN, div_one] at this
  have hqP : qf P ψ = c := by rw [qf, hPψ, dotProduct_smul, hN, smul_eq_mul, mul_one]
  have hE' : (H + ε • P) *ᵥ ψ = (qf (H + ε • P) ψ) • ψ := by
    rw [qf_add_smul, hqP, Matrix.add_mulVec, Matrix.smul_mulVec, hE, hPψ, smul_smul, add_smul]
  refine ⟨hψ.1, fun φ => ?_⟩
  obtain ⟨h0, hn, hq⟩ := decomp hS hN hE' φ
  set a := ψ ⬝ᵥ φ
  set χ := φ - a • ψ
  have hg := hgap χ h0
  have hb := abs_le.mp (hm χ)
  have hεP : -(|ε| * m * (χ ⬝ᵥ χ)) ≤ ε * qf P χ := by
    rcases le_total 0 ε with he | he
    · rw [abs_of_nonneg he]; nlinarith [hb.1, dot_self_nonneg χ]
    · rw [abs_of_nonpos he]; nlinarith [hb.2, dot_self_nonneg χ]
  have hεc : ε * c ≤ |ε| * |c| := by rw [← abs_mul]; exact le_abs_self _
  rw [hn, hq, hN, mul_one, qf_add_smul (A := H) (B := P) (ψ := χ), qf_add_smul, hqP]
  nlinarith [dot_self_nonneg χ, mul_le_mul_of_nonneg_right hε (dot_self_nonneg χ),
    mul_le_mul_of_nonneg_right hεc (dot_self_nonneg χ)]

/-- **A nontrivial one-body stabilizer of a gapped ground state defeats Hohenberg–Kohn for RDMFT.**
If `Γ(d) ψ = c ψ` with `d` symmetric and not scalar, then `ψ` is also the ground state of
`H(h + ε d)` for some `ε > 0`, so `γ` does not determine `h`. -/
theorem not_rdmDetermines_of_stab {W : Matrix (Conf M N) (Conf M N) ℝ} (hW : W.IsSymm)
    {h : Matrix (Fin M) (Fin M) ℝ} (hh : h.IsSymm) {ψ : Conf M N → ℝ}
    (hψ : IsGroundState (hamR W h) ψ) (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf (hamR W h) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (hamR W h) χ)
    {d : Matrix (Fin M) (Fin M) ℝ} (hd : d.IsSymm) (hns : ∀ c : ℝ, d ≠ c • 1) {c : ℝ}
    (hdψ : (Γ d : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ ψ = c • ψ) : ¬ RDMDetermines W h := by
  intro hdet
  set P : Matrix (Conf M N) (Conf M N) ℝ := Γ d
  set m := ∑ s, ∑ s', |P s s'|
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hpos : 0 < m + |c| + 1 := by positivity
  set ε := g / (m + |c| + 1)
  have hε : 0 < ε := div_pos hg hpos
  have hεg : |ε| * (m + |c|) ≤ g := by
    rw [abs_of_pos hε, div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [abs_nonneg c]
  have hψ' : IsGroundState (hamR W (h + ε • d)) ψ := by
    rw [hamR_add_smul]
    exact persist_of_eigen (hamR_isSymm hW hh) (gamma_isSymm hd) hψ hN hgap hdψ
      (abs_qf_le P) hεg
  obtain ⟨c', hc'⟩ := hdet (h + ε • d) (hh.add (hd.smul ε)) ψ ψ hψ hψ' hN hN rfl
  have heq : ε • d = c' • (1 : Matrix (Fin M) (Fin M) ℝ) := add_left_cancel hc'
  apply hns (ε⁻¹ * c')
  rw [← inv_smul_smul₀ hε.ne' d, heq, smul_smul]

end

end DFT
