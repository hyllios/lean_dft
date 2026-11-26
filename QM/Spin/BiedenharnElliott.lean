/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.Spin.NineJ

/-!
# The Biedenharn–Elliott identity

The overlap of `|((j₁ j₂) j₁₂ j₃) j₁₂₃ j₄; J M⟩` with `|j₁, (j₂ (j₃ j₄) j₃₄) j₂₃₄; J M⟩` is computed
in two ways. Through `|(j₁ j₂) j₁₂, (j₃ j₄) j₃₄; J M⟩` it is a product of two recoupling
coefficients. Through `|(j₁ (j₂ j₃) j₂₃) j₁₂₃, j₄; J M⟩` and `|j₁, ((j₂ j₃) j₂₃ j₄) j₂₃₄; J M⟩` it
is a sum over `j₂₃` of three. In terms of 6j symbols this is the Biedenharn–Elliott identity.
-/

namespace QM

open Finset

/-- Overlaps of states that share the coupled pair `(j₃ j₄) j₃₄`. -/
lemma sum4_pair34 {n₁ n₂ n₃ n₄ c c' : ℕ} (hc : c ≤ min n₃ n₄) (hc' : c' ≤ min n₃ n₄)
    (F G : ℕ → ℕ → ℕ → ℝ) :
    sum4 n₁ n₂ n₃ n₄ (fun x₁ x₂ x₃ x₄ =>
      (∑ v ∈ range (n₃ + n₄ - 2 * c + 1), cgCoeff n₃ n₄ c v x₃ x₄ * F x₁ x₂ v) *
        ∑ v ∈ range (n₃ + n₄ - 2 * c' + 1), cgCoeff n₃ n₄ c' v x₃ x₄ * G x₁ x₂ v) =
      if c = c' then ∑ x₁ ∈ range (n₁ + 1), ∑ x₂ ∈ range (n₂ + 1),
        ∑ v ∈ range (n₃ + n₄ - 2 * c + 1), F x₁ x₂ v * G x₁ x₂ v else 0 := by
  have inner : ∀ x₁ x₂, ∑ x₃ ∈ range (n₃ + 1), ∑ x₄ ∈ range (n₄ + 1),
      (∑ v ∈ range (n₃ + n₄ - 2 * c + 1), cgCoeff n₃ n₄ c v x₃ x₄ * F x₁ x₂ v) *
        (∑ v ∈ range (n₃ + n₄ - 2 * c' + 1), cgCoeff n₃ n₄ c' v x₃ x₄ * G x₁ x₂ v) =
      if c = c' then ∑ v ∈ range (n₃ + n₄ - 2 * c + 1), F x₁ x₂ v * G x₁ x₂ v else 0 := by
    intro x₁ x₂
    simp only [Finset.sum_mul_sum]
    rw [sum4_rotate, sum4_rotate]
    rw [Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun v' _ => (show
      ∑ x₃ ∈ range (n₃ + 1), ∑ x₄ ∈ range (n₄ + 1),
        cgCoeff n₃ n₄ c v x₃ x₄ * F x₁ x₂ v * (cgCoeff n₃ n₄ c' v' x₃ x₄ * G x₁ x₂ v') =
      F x₁ x₂ v * G x₁ x₂ v' * (if c = c' ∧ v = v' then 1 else 0) by
        rw [← cg_orthogonal_left hc (Nat.lt_succ_iff.mp (Finset.mem_range.mp hv)) hc',
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]
                                                 exact Finset.sum_congr rfl fun _ _ => by ring)]
    split_ifs with hcc
    · subst hcc
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [Finset.sum_eq_single v]
      · simp
      · intro v' _ hne; simp [Ne.symm hne]
      · intro h; exact absurd hv h
    · simp [hcc]
  unfold sum4
  rw [Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ => inner x₁ x₂]
  split_ifs <;> simp

/-! ### The coupling schemes -/

/-- `|((j₁ j₂) j₁₂ j₃) j₁₂₃, j₄; J M⟩` with `j₁₂ = j₁ + j₂ - a`, `j₁₂₃ = j₁₂ + j₃ - S`,
`J = j₁₂₃ + j₄ - R`. -/
noncomputable def stC (n₁ n₂ n₃ n₄ a S R K x₁ x₂ x₃ x₄ : ℕ) : ℝ :=
  ∑ z ∈ range (n₁ + n₂ - 2 * a + n₃ - 2 * S + 1),
    cgCoeff (n₁ + n₂ - 2 * a + n₃ - 2 * S) n₄ R K z x₄ * cU n₁ n₂ n₃ a S z (x₁, x₂, x₃)

/-- `|(j₁ (j₂ j₃) j₂₃) j₁₂₃', j₄; J M⟩` with `j₂₃ = j₂ + j₃ - b`, `j₁₂₃' = j₁ + j₂₃ - Q`. -/
noncomputable def stF (n₁ n₂ n₃ n₄ b Q R K x₁ x₂ x₃ x₄ : ℕ) : ℝ :=
  ∑ z ∈ range (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + 1),
    cgCoeff (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q) n₄ R K z x₄ * cV n₁ n₂ n₃ b Q z (x₁, x₂, x₃)

/-- `|j₁, ((j₂ j₃) j₂₃ j₄) j₂₃₄; J M⟩` with `j₂₃₄ = j₂₃ + j₄ - f`, `J = j₁ + j₂₃₄ - R`. -/
noncomputable def stG (n₁ n₂ n₃ n₄ b f R K x₁ x₂ x₃ x₄ : ℕ) : ℝ :=
  ∑ u ∈ range (n₂ + n₃ - 2 * b + 1),
    cgCoeff n₂ n₃ b u x₂ x₃ * cV n₁ (n₂ + n₃ - 2 * b) n₄ f R K (x₁, u, x₄)

lemma stC_eq_w (n₁ n₂ n₃ n₄ a S R K x₁ x₂ x₃ x₄ : ℕ) :
    stC n₁ n₂ n₃ n₄ a S R K x₁ x₂ x₃ x₄ = ∑ w ∈ range (n₁ + n₂ - 2 * a + 1),
      cgCoeff n₁ n₂ a w x₁ x₂ * cU (n₁ + n₂ - 2 * a) n₃ n₄ S R K (w, x₃, x₄) := by
  simp only [stC, cU, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma st1234_eq_w (n₁ n₂ n₃ n₄ a c P K x₁ x₂ x₃ x₄ : ℕ) :
    st1234 n₁ n₂ n₃ n₄ a c P K x₁ x₂ x₃ x₄ = ∑ w ∈ range (n₁ + n₂ - 2 * a + 1),
      cgCoeff n₁ n₂ a w x₁ x₂ * cV (n₁ + n₂ - 2 * a) n₃ n₄ c P K (w, x₃, x₄) := by
  simp only [st1234, cU, cV, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma stF_eq_u (n₁ n₂ n₃ n₄ b Q R K x₁ x₂ x₃ x₄ : ℕ) :
    stF n₁ n₂ n₃ n₄ b Q R K x₁ x₂ x₃ x₄ = ∑ u ∈ range (n₂ + n₃ - 2 * b + 1),
      cgCoeff n₂ n₃ b u x₂ x₃ * cU n₁ (n₂ + n₃ - 2 * b) n₄ Q R K (x₁, u, x₄) := by
  simp only [stF, cU, cV, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma stG_eq_y (n₁ n₂ n₃ n₄ b f R K x₁ x₂ x₃ x₄ : ℕ) :
    stG n₁ n₂ n₃ n₄ b f R K x₁ x₂ x₃ x₄ =
      ∑ y ∈ range (n₂ + n₃ - 2 * b + n₄ - 2 * f + 1),
        cgCoeff n₁ (n₂ + n₃ - 2 * b + n₄ - 2 * f) R K x₁ y * cU n₂ n₃ n₄ b f y (x₂, x₃, x₄) := by
  simp only [stG, cU, cV, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma stE1_eq_y (n₁ n₂ n₃ n₄ c b R K x₁ x₂ x₃ x₄ : ℕ) :
    stE1 n₁ n₂ n₃ n₄ c b R K x₁ x₂ x₃ x₄ =
      ∑ y ∈ range (n₂ + (n₃ + n₄ - 2 * c) - 2 * b + 1),
        cgCoeff n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) R K x₁ y * cV n₂ n₃ n₄ c b y (x₂, x₃, x₄) := by
  rw [stE1_eq]
  simp only [cV]

/-! ### First path: through `(j₁ j₂) j₁₂, (j₃ j₄) j₃₄` -/

/-- The coefficient of `|(j₁ j₂) j₁₂, (j₃ j₄) j₃₄⟩` in `|((j₁ j₂) j₁₂ j₃) j₁₂₃, j₄⟩`. -/
noncomputable def coefCD (n₁ n₂ n₃ n₄ a S R K c : ℕ) : ℝ :=
  if Triad (n₁ + n₂ - 2 * a) (n₃ + n₄ - 2 * c) (n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R) then
    recoup3 (n₁ + n₂ - 2 * a) n₃ n₄ S c R ((n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) -
      (n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R)) / 2) K else 0

lemma stC_expandD {n₁ n₂ n₃ n₄ a S R K x₁ x₂ x₃ x₄ : ℕ}
    (hS : S ≤ min (n₁ + n₂ - 2 * a) n₃) (hR : R ≤ min (n₁ + n₂ - 2 * a + n₃ - 2 * S) n₄)
    (hK : K ≤ n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R) (hx₃ : x₃ ≤ n₃) (hx₄ : x₄ ≤ n₄) :
    stC n₁ n₂ n₃ n₄ a S R K x₁ x₂ x₃ x₄ = ∑ c ∈ range (min n₃ n₄ + 1),
      coefCD n₁ n₂ n₃ n₄ a S R K c * st1234 n₁ n₂ n₃ n₄ a c ((n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) -
        (n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R)) / 2) K x₁ x₂ x₃ x₄ := by
  rw [stC_eq_w, Finset.sum_congr rfl fun w hw => by
    rw [cU_expand hS hR hK (mem_idx3.mpr ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hw), hx₃, hx₄⟩),
      Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [st1234_eq_w, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [coefCD]
  split_ifs <;> ring

/-- **First path**: a product of two recoupling coefficients. -/
theorem path_D {n₁ n₂ n₃ n₄ a S R K c b R' : ℕ} (hc : c ≤ min n₃ n₄)
    (hS : S ≤ min (n₁ + n₂ - 2 * a) n₃) (hR : R ≤ min (n₁ + n₂ - 2 * a + n₃ - 2 * S) n₄)
    (hK : K ≤ n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R) :
    sum4 n₁ n₂ n₃ n₄ (fun x₁ x₂ x₃ x₄ =>
      stC n₁ n₂ n₃ n₄ a S R K x₁ x₂ x₃ x₄ * stE1 n₁ n₂ n₃ n₄ c b R' K x₁ x₂ x₃ x₄) =
      coefCD n₁ n₂ n₃ n₄ a S R K c * recoup3 n₁ n₂ (n₃ + n₄ - 2 * c) a b
        ((n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - (n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R)) / 2)
        R' K := by
  rw [sum4_congr fun x₁ _ x₂ _ x₃ h₃ x₄ h₄ => by
    rw [stC_expandD hS hR hK h₃ h₄, Finset.sum_mul]]
  rw [sum4_sum]
  simp_rw [mul_assoc, sum4_mul_left]
  rw [Finset.sum_eq_single c]
  · unfold st1234 stE1
    rw [sum4_pair34 hc hc, ite_eq_left rfl]
    congr 1
    unfold recoup3
    rw [show ∑ i ∈ idx3 n₁ n₂ (n₃ + n₄ - 2 * c),
        cU n₁ n₂ (n₃ + n₄ - 2 * c) a ((n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) -
          (n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R)) / 2) K i *
        cV n₁ n₂ (n₃ + n₄ - 2 * c) b R' K i =
      ∑ i ∈ idx3 n₁ n₂ (n₃ + n₄ - 2 * c), (fun t s r =>
        cU n₁ n₂ (n₃ + n₄ - 2 * c) a ((n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) -
          (n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R)) / 2) K (t, s, r) *
        cV n₁ n₂ (n₃ + n₄ - 2 * c) b R' K (t, s, r)) i.1 i.2.1 i.2.2 from rfl]
    exact (sum_idx3 n₁ n₂ (n₃ + n₄ - 2 * c) (fun t s r =>
        cU n₁ n₂ (n₃ + n₄ - 2 * c) a ((n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) -
          (n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R)) / 2) K (t, s, r) *
        cV n₁ n₂ (n₃ + n₄ - 2 * c) b R' K (t, s, r))).symm
  · intro c' hc' hne
    unfold st1234 stE1
    rw [sum4_pair34 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc')) hc, ite_eq_right hne, mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hc)) h

/-! ### Second path: through `(j₁ (j₂ j₃) j₂₃), j₄` and `j₁, ((j₂ j₃) j₂₃ j₄)` -/

/-- The coefficient of `|(j₁ (j₂ j₃) j₂₃) j₁₂₃, j₄⟩` in `|((j₁ j₂) j₁₂ j₃) j₁₂₃, j₄⟩`. -/
noncomputable def coefCF (n₁ n₂ n₃ a S b : ℕ) : ℝ :=
  if Triad n₁ (n₂ + n₃ - 2 * b) (n₁ + n₂ - 2 * a + n₃ - 2 * S) then
    recoup3 n₁ n₂ n₃ a b S ((n₁ + (n₂ + n₃ - 2 * b) - (n₁ + n₂ - 2 * a + n₃ - 2 * S)) / 2) 0
  else 0

/-- The coefficient of `|j₁, ((j₂ j₃) j₂₃ j₄) j₂₃₄⟩` in `|(j₁ (j₂ j₃) j₂₃) j₁₂₃, j₄⟩`. -/
noncomputable def coefFG (n₁ n₂ n₃ n₄ b Q R K f : ℕ) : ℝ :=
  if Triad n₁ (n₂ + n₃ - 2 * b + n₄ - 2 * f) (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + n₄ - 2 * R) then
    recoup3 n₁ (n₂ + n₃ - 2 * b) n₄ Q f R ((n₁ + (n₂ + n₃ - 2 * b + n₄ - 2 * f) -
      (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + n₄ - 2 * R)) / 2) K else 0

lemma stC_expandF {n₁ n₂ n₃ n₄ a S R K x₁ x₂ x₃ x₄ : ℕ} (ha : a ≤ min n₁ n₂)
    (hS : S ≤ min (n₁ + n₂ - 2 * a) n₃) (hx₁ : x₁ ≤ n₁) (hx₂ : x₂ ≤ n₂) (hx₃ : x₃ ≤ n₃) :
    stC n₁ n₂ n₃ n₄ a S R K x₁ x₂ x₃ x₄ = ∑ b ∈ range (min n₂ n₃ + 1),
      coefCF n₁ n₂ n₃ a S b * stF n₁ n₂ n₃ n₄ b
        ((n₁ + (n₂ + n₃ - 2 * b) - (n₁ + n₂ - 2 * a + n₃ - 2 * S)) / 2) R K x₁ x₂ x₃ x₄ := by
  unfold stC
  rw [Finset.sum_congr rfl fun z hz => by
    rw [cU_expand ha hS (Nat.lt_succ_iff.mp (Finset.mem_range.mp hz))
      (mem_idx3.mpr ⟨hx₁, hx₂, hx₃⟩), Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  unfold coefCF stF
  split_ifs with hT
  · obtain ⟨t1, t2, t3, r, hr⟩ := hT
    have hQ : (n₁ + (n₂ + n₃ - 2 * b) - (n₁ + n₂ - 2 * a + n₃ - 2 * S)) / 2 ≤
        min n₁ (n₂ + n₃ - 2 * b) := le_min (by omega) (by omega)
    have hN : n₁ + n₂ - 2 * a + n₃ - 2 * S = n₁ + (n₂ + n₃ - 2 * b) -
        2 * ((n₁ + (n₂ + n₃ - 2 * b) - (n₁ + n₂ - 2 * a + n₃ - 2 * S)) / 2) := by omega
    rw [← hN, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [recoup3_const ha hb' hS hQ hN (Nat.lt_succ_iff.mp (Finset.mem_range.mp hz))]
    ring
  · simp

lemma stF_expandG {n₁ n₂ n₃ n₄ b Q R K x₁ x₂ x₃ x₄ : ℕ} (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b))
    (hR : R ≤ min (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q) n₄)
    (hK : K ≤ n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + n₄ - 2 * R) (hx₁ : x₁ ≤ n₁) (hx₄ : x₄ ≤ n₄) :
    stF n₁ n₂ n₃ n₄ b Q R K x₁ x₂ x₃ x₄ = ∑ f ∈ range (min (n₂ + n₃ - 2 * b) n₄ + 1),
      coefFG n₁ n₂ n₃ n₄ b Q R K f * stG n₁ n₂ n₃ n₄ b f ((n₁ + (n₂ + n₃ - 2 * b + n₄ - 2 * f) -
        (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + n₄ - 2 * R)) / 2) K x₁ x₂ x₃ x₄ := by
  rw [stF_eq_u, Finset.sum_congr rfl fun u hu => by
    rw [cU_expand hQ hR hK (mem_idx3.mpr ⟨hx₁, Nat.lt_succ_iff.mp (Finset.mem_range.mp hu), hx₄⟩),
      Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  unfold stG coefFG
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> ring

lemma idx3_inner {n₂ n₃ n₄ b c f e y y' : ℕ} (hb : b ≤ min n₂ n₃) (hc : c ≤ min n₃ n₄)
    (hf : f ≤ min (n₂ + n₃ - 2 * b) n₄) (he : e ≤ min n₂ (n₃ + n₄ - 2 * c))
    (hy : y ≤ n₂ + n₃ - 2 * b + n₄ - 2 * f) (hy' : y' ≤ n₂ + (n₃ + n₄ - 2 * c) - 2 * e) :
    ∑ x₂ ∈ range (n₂ + 1), ∑ x₃ ∈ range (n₃ + 1), ∑ x₄ ∈ range (n₄ + 1),
      cU n₂ n₃ n₄ b f y (x₂, x₃, x₄) * cV n₂ n₃ n₄ c e y' (x₂, x₃, x₄) =
      if n₂ + n₃ - 2 * b + n₄ - 2 * f = n₂ + (n₃ + n₄ - 2 * c) - 2 * e ∧ y = y' then
        recoup3 n₂ n₃ n₄ b c f e 0 else 0 := by
  rw [← sum_idx3 n₂ n₃ n₄ (fun t s r => cU n₂ n₃ n₄ b f y (t, s, r) * cV n₂ n₃ n₄ c e y' (t, s, r))]
  split_ifs with h
  · obtain ⟨hN, rfl⟩ := h
    change recoup3 n₂ n₃ n₄ b c f e y = _
    exact recoup3_const hb hc hf he hN hy
  · exact cU_cV_eq_zero hb hc hf he hy hy' h

/-- The overlap of `|j₁, ((j₂ j₃) j₂₃ j₄) x⟩` with `|j₁, (j₂ (j₃ j₄) j₃₄) x'⟩`. -/
lemma overlap_GE {n₁ n₂ n₃ n₄ b₂₃ f R'' c b R' K : ℕ} (hb₂₃ : b₂₃ ≤ min n₂ n₃)
    (hf : f ≤ min (n₂ + n₃ - 2 * b₂₃) n₄) (hc : c ≤ min n₃ n₄) (hb : b ≤ min n₂ (n₃ + n₄ - 2 * c))
    (hR'' : R'' ≤ min n₁ (n₂ + n₃ - 2 * b₂₃ + n₄ - 2 * f))
    (hK : K ≤ n₁ + (n₂ + n₃ - 2 * b₂₃ + n₄ - 2 * f) - 2 * R'')
    (hR' : R' ≤ min n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b))
    (hRR : n₁ + (n₂ + n₃ - 2 * b₂₃ + n₄ - 2 * f) - 2 * R'' =
      n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) - 2 * R') :
    sum4 n₁ n₂ n₃ n₄ (fun x₁ x₂ x₃ x₄ =>
      stG n₁ n₂ n₃ n₄ b₂₃ f R'' K x₁ x₂ x₃ x₄ * stE1 n₁ n₂ n₃ n₄ c b R' K x₁ x₂ x₃ x₄) =
      if n₂ + n₃ - 2 * b₂₃ + n₄ - 2 * f = n₂ + (n₃ + n₄ - 2 * c) - 2 * b then
        recoup3 n₂ n₃ n₄ b₂₃ c f b 0 else 0 := by
  set j := n₂ + n₃ - 2 * b₂₃ + n₄ - 2 * f with hj
  set j' := n₂ + (n₃ + n₄ - 2 * c) - 2 * b with hj'
  have step : ∀ x₁, ∑ x₂ ∈ range (n₂ + 1), ∑ x₃ ∈ range (n₃ + 1), ∑ x₄ ∈ range (n₄ + 1),
      stG n₁ n₂ n₃ n₄ b₂₃ f R'' K x₁ x₂ x₃ x₄ * stE1 n₁ n₂ n₃ n₄ c b R' K x₁ x₂ x₃ x₄ =
      ∑ y ∈ range (j + 1), ∑ y' ∈ range (j' + 1),
        cgCoeff n₁ j R'' K x₁ y * cgCoeff n₁ j' R' K x₁ y' *
          (if j = j' ∧ y = y' then recoup3 n₂ n₃ n₄ b₂₃ c f b 0 else 0) := by
    intro x₁
    simp only [stG_eq_y, stE1_eq_y, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun x₂ _ => Finset.sum_congr rfl fun x₃ _ => sum3_rotate _ _ _ _]
    rw [sum4_rotate, sum4_rotate]
    refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun y' hy' => ?_
    rw [← idx3_inner hb₂₃ hc hf hb (Nat.lt_succ_iff.mp (Finset.mem_range.mp hy))
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hy')), Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  unfold sum4
  rw [Finset.sum_congr rfl fun x₁ _ => step x₁]
  split_ifs with hcond
  · have r1 := le_trans hR'' (min_le_left _ _)
    have r2 := le_trans hR'' (min_le_right _ _)
    have r3 := le_trans hR' (min_le_left _ _)
    have r4 := le_trans hR' (min_le_right _ _)
    have hRe : R'' = R' := by omega
    rw [← hcond, ← hRe]
    rw [Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun y hy => (show
      ∑ y' ∈ range (j + 1), cgCoeff n₁ j R'' K x₁ y * cgCoeff n₁ j R'' K x₁ y' *
        (if j = j ∧ y = y' then recoup3 n₂ n₃ n₄ b₂₃ c f b 0 else 0) =
      recoup3 n₂ n₃ n₄ b₂₃ c f b 0 * (cgCoeff n₁ j R'' K x₁ y * cgCoeff n₁ j R'' K x₁ y) by
        rw [Finset.sum_eq_single y]
        · rw [ite_eq_left ⟨rfl, rfl⟩]; ring
        · intro y' _ hne; rw [ite_eq_right (fun h => hne h.2.symm)]; ring
        · intro h; exact absurd hy h)]
    simp only [← Finset.mul_sum]
    rw [cg_orthogonal_left hR'' hK hR'']
    simp
  · simp only [mul_ite, mul_zero]
    exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun u _ =>
      Finset.sum_eq_zero fun u' _ => ite_eq_right (fun h => hcond h.1)

lemma path_f {n₁ n₂ n₃ n₄ b₂₃ Q R K c b R' f : ℕ} (hb₂₃ : b₂₃ ≤ min n₂ n₃)
    (hf : f ≤ min (n₂ + n₃ - 2 * b₂₃) n₄) (hc : c ≤ min n₃ n₄)
    (hK : K ≤ n₁ + (n₂ + n₃ - 2 * b₂₃) - 2 * Q + n₄ - 2 * R)
    (hb : b ≤ min n₂ (n₃ + n₄ - 2 * c)) (hR' : R' ≤ min n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b))
    (hJ : n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) - 2 * R' =
      n₁ + (n₂ + n₃ - 2 * b₂₃) - 2 * Q + n₄ - 2 * R) :
    coefFG n₁ n₂ n₃ n₄ b₂₃ Q R K f *
      sum4 n₁ n₂ n₃ n₄ (fun x₁ x₂ x₃ x₄ =>
        stG n₁ n₂ n₃ n₄ b₂₃ f ((n₁ + (n₂ + n₃ - 2 * b₂₃ + n₄ - 2 * f) -
        (n₁ + (n₂ + n₃ - 2 * b₂₃) - 2 * Q + n₄ - 2 * R)) / 2) K x₁ x₂ x₃ x₄ *
        stE1 n₁ n₂ n₃ n₄ c b R' K x₁ x₂ x₃ x₄) =
      if n₂ + n₃ - 2 * b₂₃ + n₄ - 2 * f = n₂ + (n₃ + n₄ - 2 * c) - 2 * b then
        coefFG n₁ n₂ n₃ n₄ b₂₃ Q R K f * recoup3 n₂ n₃ n₄ b₂₃ c f b 0 else 0 := by
  by_cases hF : Triad n₁ (n₂ + n₃ - 2 * b₂₃ + n₄ - 2 * f)
      (n₁ + (n₂ + n₃ - 2 * b₂₃) - 2 * Q + n₄ - 2 * R)
  swap
  · simp [coefFG, hF]
  obtain ⟨f1, f2, f3, rf, hrf⟩ := hF
  have r1 := le_trans hR' (min_le_left _ _)
  have r2 := le_trans hR' (min_le_right _ _)
  clear hR'
  rw [overlap_GE hb₂₃ hf hc hb (le_min (by omega) (by omega)) (by omega) (le_min r1 r2)
    (by omega), mul_ite, mul_zero]

lemma path_FG_inner {n₁ n₂ n₃ n₄ b₂₃ Q R K c b R' : ℕ} (hb₂₃ : b₂₃ ≤ min n₂ n₃)
    (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b₂₃)) (hR : R ≤ min (n₁ + (n₂ + n₃ - 2 * b₂₃) - 2 * Q) n₄)
    (hK : K ≤ n₁ + (n₂ + n₃ - 2 * b₂₃) - 2 * Q + n₄ - 2 * R) (hc : c ≤ min n₃ n₄)
    (hb : b ≤ min n₂ (n₃ + n₄ - 2 * c)) (hR' : R' ≤ min n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b))
    (hJ : n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) - 2 * R' =
      n₁ + (n₂ + n₃ - 2 * b₂₃) - 2 * Q + n₄ - 2 * R) :
    sum4 n₁ n₂ n₃ n₄ (fun x₁ x₂ x₃ x₄ =>
      stF n₁ n₂ n₃ n₄ b₂₃ Q R K x₁ x₂ x₃ x₄ * stE1 n₁ n₂ n₃ n₄ c b R' K x₁ x₂ x₃ x₄) =
      if Triad (n₂ + n₃ - 2 * b₂₃) n₄ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) then
        coefFG n₁ n₂ n₃ n₄ b₂₃ Q R K
            ((n₂ + n₃ - 2 * b₂₃ + n₄ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2) *
          recoup3 n₂ n₃ n₄ b₂₃ c ((n₂ + n₃ - 2 * b₂₃ + n₄ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2)
            b 0
      else 0 := by
  rw [sum4_congr fun x₁ h₁ x₂ _ x₃ _ x₄ h₄ => by
    rw [stF_expandG hQ hR hK h₁ h₄, Finset.sum_mul]]
  rw [sum4_sum]
  simp_rw [mul_assoc]
  rw [Finset.sum_congr rfl fun f _ => sum4_mul_left _ _ _ _ _ _]
  rw [Finset.sum_congr rfl fun f hf =>
    path_f hb₂₃ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hf)) hc hK hb hR' hJ]
  exact sum_P_single (n₂ + n₃ - 2 * b₂₃) n₄ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) _

/-- **Second path**: a sum over `j₂₃` of three recoupling coefficients. -/
theorem path_FG {n₁ n₂ n₃ n₄ a S R K c b R' : ℕ} (ha : a ≤ min n₁ n₂)
    (hS : S ≤ min (n₁ + n₂ - 2 * a) n₃) (hR : R ≤ min (n₁ + n₂ - 2 * a + n₃ - 2 * S) n₄)
    (hK : K ≤ n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R) (hc : c ≤ min n₃ n₄)
    (hb : b ≤ min n₂ (n₃ + n₄ - 2 * c)) (hR' : R' ≤ min n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b))
    (hJ : n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) - 2 * R' =
      n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R) :
    sum4 n₁ n₂ n₃ n₄ (fun x₁ x₂ x₃ x₄ =>
      stC n₁ n₂ n₃ n₄ a S R K x₁ x₂ x₃ x₄ * stE1 n₁ n₂ n₃ n₄ c b R' K x₁ x₂ x₃ x₄) =
      ∑ b₂₃ ∈ range (min n₂ n₃ + 1), coefCF n₁ n₂ n₃ a S b₂₃ *
        (if Triad (n₂ + n₃ - 2 * b₂₃) n₄ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) then
          coefFG n₁ n₂ n₃ n₄ b₂₃
            ((n₁ + (n₂ + n₃ - 2 * b₂₃) - (n₁ + n₂ - 2 * a + n₃ - 2 * S)) / 2) R K
            ((n₂ + n₃ - 2 * b₂₃ + n₄ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2) *
          recoup3 n₂ n₃ n₄ b₂₃ c ((n₂ + n₃ - 2 * b₂₃ + n₄ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2)
            b 0
        else 0) := by
  rw [sum4_congr fun x₁ h₁ x₂ h₂ x₃ h₃ x₄ _ => by
    rw [stC_expandF ha hS h₁ h₂ h₃, Finset.sum_mul]]
  rw [sum4_sum]
  refine Finset.sum_congr rfl fun b₂₃ hb₂₃ => ?_
  have hb₂₃' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₂₃)
  simp_rw [mul_assoc]
  rw [sum4_mul_left]
  by_cases hT : Triad n₁ (n₂ + n₃ - 2 * b₂₃) (n₁ + n₂ - 2 * a + n₃ - 2 * S)
  swap
  · simp [coefCF, hT]
  obtain ⟨t1, t2, t3, r, hr⟩ := hT
  have hE : n₁ + (n₂ + n₃ - 2 * b₂₃) -
      2 * ((n₁ + (n₂ + n₃ - 2 * b₂₃) - (n₁ + n₂ - 2 * a + n₃ - 2 * S)) / 2) =
      n₁ + n₂ - 2 * a + n₃ - 2 * S := by omega
  rw [path_FG_inner hb₂₃' (le_min (by omega) (by omega)) (by rw [hE]; exact hR)
    (by rw [hE]; exact hK) hc hb hR' (by rw [hE]; exact hJ)]

/-! ### Conversion to 6j symbols -/

lemma sixJ_eq_zero_of_not_triad₃ {n₁ n₂ n₃ n₄ n₅ n₆ : ℕ} (h : ¬Triad n₄ n₂ n₆) :
    sixJ n₁ n₂ n₃ n₄ n₅ n₆ = 0 := by
  unfold sixJ sixJTerm
  simp [threeJ_of_not (show ¬(Triad n₄ n₂ n₆ ∧ _) from fun h' => h h'.1)]

lemma coefCF_eq {n₁ n₂ n₃ a S b : ℕ} (ha : a ≤ min n₁ n₂) (hS : S ≤ min (n₁ + n₂ - 2 * a) n₃)
    (hb : b ≤ min n₂ n₃) :
    coefCF n₁ n₂ n₃ a S b = (-1) ^ ((n₁ + n₂ + n₃ + (n₁ + n₂ - 2 * a + n₃ - 2 * S)) / 2) *
      √((((n₁ + n₂ - 2 * a : ℕ) : ℝ) + 1) * (((n₂ + n₃ - 2 * b : ℕ) : ℝ) + 1)) *
      sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₃ (n₁ + n₂ - 2 * a + n₃ - 2 * S) (n₂ + n₃ - 2 * b) := by
  unfold coefCF
  split_ifs with hT
  · obtain ⟨t1, t2, t3, r, hr⟩ := hT
    exact recoup3_eq_sixJ ha hb hS (le_min (by omega) (by omega)) (by omega) (Nat.zero_le _)
  · rw [sixJ_eq_zero_of_not_triad₂ (fun h => hT (triad_swap23.mp h))]; ring

lemma coefFG_eq {n₁ n₂ n₃ n₄ b Q R K f : ℕ} (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b))
    (hR : R ≤ min (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q) n₄) (hf : f ≤ min (n₂ + n₃ - 2 * b) n₄)
    (hK : K ≤ n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + n₄ - 2 * R) :
    coefFG n₁ n₂ n₃ n₄ b Q R K f =
      (-1) ^ ((n₁ + (n₂ + n₃ - 2 * b) + n₄ + (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + n₄ - 2 * R)) / 2) *
      √((((n₁ + (n₂ + n₃ - 2 * b) - 2 * Q : ℕ) : ℝ) + 1) *
        (((n₂ + n₃ - 2 * b + n₄ - 2 * f : ℕ) : ℝ) + 1)) *
      sixJ n₁ (n₂ + n₃ - 2 * b) (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q) n₄
        (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + n₄ - 2 * R) (n₂ + n₃ - 2 * b + n₄ - 2 * f) := by
  unfold coefFG
  split_ifs with hT
  · obtain ⟨t1, t2, t3, r, hr⟩ := hT
    exact recoup3_eq_sixJ hQ hf hR (le_min (by omega) (by omega)) (by omega) hK
  · rw [sixJ_eq_zero_of_not_triad₂ (fun h => hT (triad_swap23.mp h))]; ring

lemma coefCD_eq {n₁ n₂ n₃ n₄ a S R K c : ℕ} (hS : S ≤ min (n₁ + n₂ - 2 * a) n₃)
    (hR : R ≤ min (n₁ + n₂ - 2 * a + n₃ - 2 * S) n₄) (hc : c ≤ min n₃ n₄)
    (hK : K ≤ n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R) :
    coefCD n₁ n₂ n₃ n₄ a S R K c =
      (-1) ^ ((n₁ + n₂ - 2 * a + n₃ + n₄ + (n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R)) / 2) *
      √((((n₁ + n₂ - 2 * a + n₃ - 2 * S : ℕ) : ℝ) + 1) * (((n₃ + n₄ - 2 * c : ℕ) : ℝ) + 1)) *
      sixJ (n₁ + n₂ - 2 * a) n₃ (n₁ + n₂ - 2 * a + n₃ - 2 * S) n₄
        (n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R) (n₃ + n₄ - 2 * c) := by
  unfold coefCD
  split_ifs with hT
  · obtain ⟨t1, t2, t3, r, hr⟩ := hT
    exact recoup3_eq_sixJ hS hc hR (le_min (by omega) (by omega)) (by omega) hK
  · rw [sixJ_eq_zero_of_not_triad₂ (fun h => hT (triad_swap23.mp h))]; ring

/-! ### The identity -/

/-- The two paths, with the coupling labels as variables. -/
lemma be_paths {n₁ n₂ n₃ n₄ a S R c b R' : ℕ} (ha : a ≤ min n₁ n₂)
    (hS : S ≤ min (n₁ + n₂ - 2 * a) n₃) (hR : R ≤ min (n₁ + n₂ - 2 * a + n₃ - 2 * S) n₄)
    (hc : c ≤ min n₃ n₄) (hb : b ≤ min n₂ (n₃ + n₄ - 2 * c))
    (hR' : R' ≤ min n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b))
    (hJ : n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) - 2 * R' =
      n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R) :
    coefCD n₁ n₂ n₃ n₄ a S R 0 c * recoup3 n₁ n₂ (n₃ + n₄ - 2 * c) a b
        ((n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - (n₁ + n₂ - 2 * a + n₃ - 2 * S + n₄ - 2 * R)) / 2)
        R' 0 =
      ∑ b₂₃ ∈ range (min n₂ n₃ + 1), coefCF n₁ n₂ n₃ a S b₂₃ *
        (if Triad (n₂ + n₃ - 2 * b₂₃) n₄ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) then
          coefFG n₁ n₂ n₃ n₄ b₂₃
            ((n₁ + (n₂ + n₃ - 2 * b₂₃) - (n₁ + n₂ - 2 * a + n₃ - 2 * S)) / 2) R 0
            ((n₂ + n₃ - 2 * b₂₃ + n₄ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2) *
          recoup3 n₂ n₃ n₄ b₂₃ c ((n₂ + n₃ - 2 * b₂₃ + n₄ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2)
            b 0
        else 0) := by
  rw [← path_D hc hS hR (Nat.zero_le _), path_FG ha hS hR (Nat.zero_le _) hc hb hR' hJ]

lemma be_alg (A B D s₁ s₂ s₃ P X C E R : ℝ) (hP : 0 ≤ P) (hX : 0 ≤ X) (hC : 0 ≤ C)
    (hE : 0 ≤ E) :
    s₁ * √(P * X) * A * (s₂ * √(C * E) * B * (s₃ * √(X * R) * D)) =
      s₁ * s₂ * s₃ * √(P * C * E * R) * (X * A * B * D) := by
  rw [Real.sqrt_mul hP, Real.sqrt_mul hC, Real.sqrt_mul hX, Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_mul hP]
  have := Real.mul_self_sqrt hX
  linear_combination (s₁ * s₂ * s₃ * A * B * D * √P * √C * √E * √R) * this

/-- One term of the second path in terms of 6j symbols. -/
lemma be_term {a b c d e f p q r aL Sl Rl cL bL b₂₃ : ℕ}
    (hA : p + 2 * aL = d + a) (hSl : c + 2 * Sl = p + b) (hRl : q + 2 * Rl = c + f)
    (hcL : r + 2 * cL = b + f) (hbL : e + 2 * bL = a + r)
    (aL₁ : aL ≤ d) (aL₂ : aL ≤ a) (Sl₁ : Sl ≤ p) (Sl₂ : Sl ≤ b) (Rl₁ : Rl ≤ c) (Rl₂ : Rl ≤ f)
    (cL₁ : cL ≤ b) (cL₂ : cL ≤ f) (bL₁ : bL ≤ a) (bL₂ : bL ≤ r) (h₆ : Triad d e q)
    (hb₂₃ : b₂₃ ≤ min a b) :
    coefCF d a b aL Sl b₂₃ *
      (if Triad (a + b - 2 * b₂₃) f (a + (b + f - 2 * cL) - 2 * bL) then
        coefFG d a b f b₂₃ ((d + (a + b - 2 * b₂₃) - (d + a - 2 * aL + b - 2 * Sl)) / 2) Rl 0
          ((a + b - 2 * b₂₃ + f - (a + (b + f - 2 * cL) - 2 * bL)) / 2) *
        recoup3 a b f b₂₃ cL ((a + b - 2 * b₂₃ + f - (a + (b + f - 2 * cL) - 2 * bL)) / 2) bL 0
      else 0) =
      (-1) ^ ((d + a + b + c) / 2 + (d + (a + b - 2 * b₂₃) + f + q) / 2 + (a + b + f + e) / 2) *
        √((((p : ℕ) : ℝ) + 1) * ((c : ℝ) + 1) * ((e : ℝ) + 1) * ((r : ℝ) + 1)) *
        ((((a + b - 2 * b₂₃ : ℕ) : ℝ) + 1) * sixJ d a p b c (a + b - 2 * b₂₃) *
          sixJ d (a + b - 2 * b₂₃) c f q e * sixJ a b (a + b - 2 * b₂₃) f e r) := by
  have e₁ : d + a - 2 * aL = p := by omega
  have e₂ : p + b - 2 * Sl = c := by omega
  have e₃ : b + f - 2 * cL = r := by omega
  have e₄ : a + r - 2 * bL = e := by omega
  have b1 := le_trans hb₂₃ (min_le_left _ _)
  have b2 := le_trans hb₂₃ (min_le_right _ _)
  rw [coefCF_eq (le_min aL₁ aL₂) (by rw [e₁]; exact le_min Sl₁ Sl₂) hb₂₃]
  simp only [e₁, e₂, e₃, e₄]
  by_cases hX : Triad d (a + b - 2 * b₂₃) c
  swap
  · rw [sixJ_eq_zero_of_not_triad₂ (fun h => hX (triad_swap23.mp h))]; ring
  by_cases hY : Triad (a + b - 2 * b₂₃) f e
  swap
  · rw [ite_eq_right hY, sixJ_eq_zero_of_not_triad₄ (n₁ := a) (n₂ := b) (n₆ := r)
      (fun h => hY (triad_cyclic.mp h))]
    ring
  rw [ite_eq_left hY]
  obtain ⟨x1, x2, x3, rx, hrx⟩ := hX
  obtain ⟨y1, y2, y3, ry, hry⟩ := hY
  obtain ⟨z1, z2, z3, rz, hrz⟩ := h₆
  have hQe : d + (a + b - 2 * b₂₃) - 2 * ((d + (a + b - 2 * b₂₃) - c) / 2) = c := by omega
  have hF : a + b - 2 * b₂₃ + f - 2 * ((a + b - 2 * b₂₃ + f - e) / 2) = e := by omega
  rw [coefFG_eq (le_min (by omega) (by omega)) (by rw [hQe]; exact le_min Rl₁ Rl₂)
      (le_min (by omega) (by omega)) (by rw [hQe]; omega),
    recoup3_eq_sixJ hb₂₃ (le_min cL₁ cL₂) (le_min (by omega) (by omega))
      (le_min (by omega) (by omega)) (by rw [e₃, hF]; omega) (Nat.zero_le _)]
  rw [hQe, hF, e₃, show c + f - 2 * Rl = q by omega]
  rw [pow_add, pow_add]
  exact be_alg _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity)
    (by positivity)

lemma be_alg2 (A B s₁ s₂ C R P E : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P) (hE : 0 ≤ E) :
    s₁ * √(C * R) * A * (s₂ * √(P * E) * B) = s₁ * s₂ * √(P * C * E * R) * (A * B) := by
  rw [Real.sqrt_mul hC, Real.sqrt_mul hP, Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_mul hP]
  ring

/-- The first path in terms of 6j symbols. -/
lemma be_lhs {a b c d e f p q r aL Sl Rl cL bL R'l : ℕ}
    (hA : p + 2 * aL = d + a) (hSl : c + 2 * Sl = p + b) (hRl : q + 2 * Rl = c + f)
    (hcL : r + 2 * cL = b + f) (hbL : e + 2 * bL = a + r) (hR'l : q + 2 * R'l = d + e)
    (aL₁ : aL ≤ d) (aL₂ : aL ≤ a) (Sl₁ : Sl ≤ p) (Sl₂ : Sl ≤ b) (Rl₁ : Rl ≤ c) (Rl₂ : Rl ≤ f)
    (cL₁ : cL ≤ b) (cL₂ : cL ≤ f) (bL₁ : bL ≤ a) (bL₂ : bL ≤ r) (R'l₁ : R'l ≤ d)
    (R'l₂ : R'l ≤ e) :
    coefCD d a b f aL Sl Rl 0 cL * recoup3 d a (b + f - 2 * cL) aL bL
        ((d + a - 2 * aL + (b + f - 2 * cL) - (d + a - 2 * aL + b - 2 * Sl + f - 2 * Rl)) / 2)
        R'l 0 =
      (-1) ^ ((p + b + f + q) / 2) * (-1) ^ ((d + a + r + q) / 2) *
        √((((p : ℕ) : ℝ) + 1) * ((c : ℝ) + 1) * ((e : ℝ) + 1) * ((r : ℝ) + 1)) *
        (sixJ p b c f q r * sixJ d a p r q e) := by
  have e₁ : d + a - 2 * aL = p := by omega
  have e₂ : p + b - 2 * Sl = c := by omega
  have e₃ : b + f - 2 * cL = r := by omega
  have e₅ : c + f - 2 * Rl = q := by omega
  rw [coefCD_eq (by rw [e₁]; exact le_min Sl₁ Sl₂) (by rw [e₁, e₂]; exact le_min Rl₁ Rl₂)
    (le_min cL₁ cL₂) (Nat.zero_le _)]
  simp only [e₁, e₂, e₃, e₅]
  by_cases hT : Triad p r q
  swap
  · rw [sixJ_eq_zero_of_not_triad₂ (fun h => hT (triad_swap23.mp h))]; ring
  obtain ⟨t1, t2, t3, rt, hrt⟩ := hT
  have hP : p + r - 2 * ((p + r - q) / 2) = q := by omega
  have hPm : (p + r - q) / 2 ≤ min p r := le_min (by omega) (by omega)
  have hRm : R'l ≤ min d (a + r - 2 * bL) := le_min R'l₁ (by omega)
  rw [recoup3_eq_sixJ (le_min aL₁ aL₂) (le_min bL₁ bL₂) (by rw [e₁]; exact hPm) hRm
    (by rw [e₁]; omega) (Nat.zero_le _)]
  rw [e₁, hP, show a + r - 2 * bL = e by omega]
  exact be_alg2 _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity)

/-- The phases of the two paths against the phase `(-1)^(S + x)` of the identity. -/
lemma be_sign {a b c d e f p q r aL Sl Rl cL bL R'l b₂₃ : ℕ}
    (hA : p + 2 * aL = d + a) (hSl : c + 2 * Sl = p + b) (hRl : q + 2 * Rl = c + f)
    (hcL : r + 2 * cL = b + f) (hbL : e + 2 * bL = a + r) (hR'l : q + 2 * R'l = d + e) :
    (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r + (a + b - 2 * b₂₃)) / 2) =
      (-1) ^ ((p + b + f + q) / 2) * (-1) ^ ((d + a + r + q) / 2) *
        (-1) ^ ((d + a + b + c) / 2 + (d + (a + b - 2 * b₂₃) + f + q) / 2 +
          (a + b + f + e) / 2) := by
  rw [← pow_add, ← pow_add]
  exact neg_one_pow_eq_of_even (Nat.even_iff.mpr (by omega))

lemma be_alg3 (W s t u v w z : ℝ) (hs : s * s = 1) :
    W * s * (s * t * u * v * w * z) = t * W * (u * v * w * z) := by
  linear_combination (W * t * u * v * w * z) * hs

/-- Exchange of upper and lower entries in the first and third columns:
`{j₄ j₂ j₆; j₁ j₅ j₃} = {j₁ j₂ j₃; j₄ j₅ j₆}`. -/
lemma sixJ_flip13 (n₁ n₂ n₃ n₄ n₅ n₆ : ℕ) :
    sixJ n₄ n₂ n₆ n₁ n₅ n₃ = sixJ n₁ n₂ n₃ n₄ n₅ n₆ :=
  (sixJ_swap23 n₄ n₆ n₂ n₁ n₃ n₅).trans
    ((sixJ_flip n₁ n₃ n₂ n₄ n₆ n₅).trans (sixJ_swap23 n₁ n₂ n₃ n₄ n₅ n₆))

/-- Exchange of upper and lower entries in the last two columns:
`{j₁ j₅ j₆; j₄ j₂ j₃} = {j₁ j₂ j₃; j₄ j₅ j₆}`. -/
lemma sixJ_flip23 (n₁ n₂ n₃ n₄ n₅ n₆ : ℕ) :
    sixJ n₁ n₅ n₆ n₄ n₂ n₃ = sixJ n₁ n₂ n₃ n₄ n₅ n₆ :=
  (sixJ_swap12 n₅ n₁ n₆ n₂ n₄ n₃).trans
    ((sixJ_flip13 n₂ n₁ n₃ n₅ n₄ n₆).trans (sixJ_swap12 n₁ n₂ n₃ n₄ n₅ n₆))

/-- **Biedenharn–Elliott identity** with `nᵢ = 2jᵢ`:
`Σ_x (-1)^(S + x) (2x + 1) {a b x; c d p} {c d x; e f q} {e f x; b a r} =
{p q r; e a d} {p q r; f b c}` with `S = a + b + c + d + e + f + p + q + r`. The sum runs over all
`x` (the terms vanish beyond `a + b`). -/
theorem biedenharn_elliott (a b c d e f p q r : ℕ) :
    ∑ x ∈ range (a + b + 1), (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r + x) / 2) *
      ((x : ℝ) + 1) * sixJ a b x c d p * sixJ c d x e f q * sixJ e f x b a r =
      sixJ p q r e a d * sixJ p q r f b c := by
  -- bring the symbols to the form produced by the recoupling
  have s1 : ∀ x, sixJ a b x c d p = sixJ d a p b c x := fun x =>
    ((sixJ_flip13 b a x d c p).trans (sixJ_swap12 b a x d c p).symm).symm
  have s2 : ∀ x, sixJ c d x e f q = sixJ d x c f q e := fun x =>
    ((sixJ_swap23 d c x f e q).trans (sixJ_swap12 c d x e f q)).symm
  have s3 : ∀ x, sixJ e f x b a r = sixJ a b x f e r := fun x =>
    ((sixJ_flip a b x f e r).symm.trans (sixJ_swap12 e f x b a r)).symm
  have s4 : sixJ p q r f b c = sixJ p b c f q r := (sixJ_flip23 p q r f b c).symm
  have s5 : sixJ p q r e a d = sixJ d a p r q e :=
    ((sixJ_flip d a p r q e).symm.trans ((sixJ_swap23 r p q d e a).trans
      ((sixJ_swap12 p r q e d a).trans (sixJ_swap23 p q r e a d)))).symm
  simp only [s1, s2, s3, s4, s5]
  -- both sides vanish unless the six triads of the coupling scheme hold
  by_cases h₁ : Triad d a p
  swap
  · have z : ∀ n₄ n₅ n₆, sixJ d a p n₄ n₅ n₆ = 0 := fun _ _ _ => sixJ_eq_zero_of_not_triad₁ h₁
    simp [z]
  by_cases h₂ : Triad p b c
  swap
  · have z₁ : ∀ n₄ n₅ n₆, sixJ p b c n₄ n₅ n₆ = 0 := fun _ _ _ => sixJ_eq_zero_of_not_triad₁ h₂
    have z₂ : ∀ x, sixJ d a p b c x = 0 := fun _ =>
      sixJ_eq_zero_of_not_triad₄ (n₄ := b) (n₅ := c) (n₃ := p) fun h => h₂ (triad_cyclic.mp h)
    simp [z₁, z₂]
  by_cases h₃ : Triad c f q
  swap
  · have z₁ : ∀ x, sixJ d x c f q e = 0 := fun _ =>
      sixJ_eq_zero_of_not_triad₄ (n₄ := f) (n₅ := q) (n₃ := c) fun h => h₃ (triad_cyclic.mp h)
    have z₂ : sixJ p b c f q r = 0 :=
      sixJ_eq_zero_of_not_triad₄ (n₄ := f) (n₅ := q) (n₃ := c) fun h => h₃ (triad_cyclic.mp h)
    simp [z₁, z₂]
  by_cases h₄ : Triad b f r
  swap
  · have z₁ : ∀ x, sixJ a b x f e r = 0 := fun _ =>
      sixJ_eq_zero_of_not_triad₃ (n₄ := f) (n₂ := b) (n₆ := r) fun h => h₄ (triad_swap12.mp h)
    have z₂ : sixJ p b c f q r = 0 :=
      sixJ_eq_zero_of_not_triad₃ (n₄ := f) (n₂ := b) (n₆ := r) fun h => h₄ (triad_swap12.mp h)
    simp [z₁, z₂]
  by_cases h₅ : Triad a r e
  swap
  · have z₁ : ∀ x, sixJ a b x f e r = 0 := fun _ =>
      sixJ_eq_zero_of_not_triad₂ (n₁ := a) (n₅ := e) (n₆ := r) fun h => h₅ (triad_swap23.mp h)
    have z₂ : sixJ d a p r q e = 0 :=
      sixJ_eq_zero_of_not_triad₃ (n₄ := r) (n₂ := a) (n₆ := e) fun h => h₅ (triad_swap12.mp h)
    simp [z₁, z₂]
  by_cases h₆ : Triad d e q
  swap
  · have z₁ : ∀ x, sixJ d x c f q e = 0 := fun _ =>
      sixJ_eq_zero_of_not_triad₂ (n₁ := d) (n₅ := q) (n₆ := e) fun h => h₆ (triad_swap23.mp h)
    have z₂ : sixJ d a p r q e = 0 :=
      sixJ_eq_zero_of_not_triad₂ (n₁ := d) (n₅ := q) (n₆ := e) fun h => h₆ (triad_swap23.mp h)
    simp [z₁, z₂]
  -- the coupling labels
  have h₆' := h₆
  obtain ⟨u₁, u₂, u₃, k₁, hk₁⟩ := h₁
  obtain ⟨v₁, v₂, v₃, k₂, hk₂⟩ := h₂
  obtain ⟨w₁, w₂, w₃, k₃, hk₃⟩ := h₃
  obtain ⟨x₁, x₂, x₃, k₄, hk₄⟩ := h₄
  obtain ⟨y₁, y₂, y₃, k₅, hk₅⟩ := h₅
  obtain ⟨z₁, z₂, z₃, k₆, hk₆⟩ := h₆
  obtain ⟨aL, hA⟩ : ∃ aL, p + 2 * aL = d + a := ⟨(d + a - p) / 2, by omega⟩
  obtain ⟨Sl, hSl⟩ : ∃ Sl, c + 2 * Sl = p + b := ⟨(p + b - c) / 2, by omega⟩
  obtain ⟨Rl, hRl⟩ : ∃ Rl, q + 2 * Rl = c + f := ⟨(c + f - q) / 2, by omega⟩
  obtain ⟨cL, hcL⟩ : ∃ cL, r + 2 * cL = b + f := ⟨(b + f - r) / 2, by omega⟩
  obtain ⟨bL, hbL⟩ : ∃ bL, e + 2 * bL = a + r := ⟨(a + r - e) / 2, by omega⟩
  obtain ⟨R'l, hR'l⟩ : ∃ R'l, q + 2 * R'l = d + e := ⟨(d + e - q) / 2, by omega⟩
  -- the two paths
  have hP := be_paths (n₁ := d) (n₂ := a) (n₃ := b) (n₄ := f) (a := aL) (S := Sl) (R := Rl)
    (c := cL) (b := bL) (R' := R'l) (le_min (by omega) (by omega))
    (le_min (by omega) (by omega)) (le_min (by omega) (by omega)) (le_min (by omega) (by omega))
    (le_min (by omega) (by omega)) (le_min (by omega) (by omega)) (by omega)
  rw [be_lhs hA hSl hRl hcL hbL hR'l (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)] at hP
  rw [Finset.sum_congr rfl fun b₂₃ hb => be_term hA hSl hRl hcL hbL (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h₆'
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))] at hP
  -- compare with the identity term by term
  rw [sum_triad_reindex a b _ fun x hx => by rw [sixJ_eq_zero_of_not_triad₁ hx]; ring]
  have hW : (0 : ℝ) < √(((p : ℝ) + 1) * ((c : ℝ) + 1) * ((e : ℝ) + 1) * ((r : ℝ) + 1)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hσ : ((-1 : ℝ) ^ ((p + b + f + q) / 2) * (-1) ^ ((d + a + r + q) / 2)) *
      ((-1 : ℝ) ^ ((p + b + f + q) / 2) * (-1) ^ ((d + a + r + q) / 2)) = 1 := by
    rw [mul_mul_mul_comm, ← pow_add, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩,
      Even.neg_one_pow ⟨_, rfl⟩, one_mul]
  rw [← mul_right_inj' (mul_ne_zero hW.ne' (left_ne_zero_of_mul_eq_one hσ)), Finset.mul_sum,
    show √(((p : ℝ) + 1) * ((c : ℝ) + 1) * ((e : ℝ) + 1) * ((r : ℝ) + 1)) *
        ((-1 : ℝ) ^ ((p + b + f + q) / 2) * (-1) ^ ((d + a + r + q) / 2)) *
        (sixJ d a p r q e * sixJ p b c f q r) =
      (-1 : ℝ) ^ ((p + b + f + q) / 2) * (-1) ^ ((d + a + r + q) / 2) *
        √(((p : ℝ) + 1) * ((c : ℝ) + 1) * ((e : ℝ) + 1) * ((r : ℝ) + 1)) *
        (sixJ p b c f q r * sixJ d a p r q e) by ring, hP]
  refine Finset.sum_congr rfl fun b₂₃ _ => ?_
  rw [be_sign (b₂₃ := b₂₃) hA hSl hRl hcL hbL hR'l]
  exact be_alg3 _ _ _ _ _ _ _ hσ

end QM
