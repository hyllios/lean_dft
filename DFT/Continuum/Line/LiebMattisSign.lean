/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.YoungPos

/-!
# Signs of mixed-symmetry ground states at configurations with cross-group collisions

* `NoSame a x`: no two particles of the same group meet.
* `SY_eventually`: `SY a` is locally constant where `NoSame a`.
* `exists_injective_near`: collision-free configurations are dense in the cube.
* `SY_pm'`: `SY a (x ∘ σ) = sgn σ · SY a x` for `σ` in the Young subgroup, whenever `NoSame a x`
  (cross-group collisions allowed).
* `gs_SY_pos`: a ground state `g` of mixed symmetry satisfies `0 < s₀ · SY(x) · g(x)` at every
  point of the cube without same-group collisions, for a fixed sign `s₀`.
* `SY_mul_SY_succ`: `SY a · SY (a+1)` is the product of the signs of the pairs containing
  particle `a`: `Π_{i<a} sign(x_a - x_i) · Π_{j>a} sign(x_j - x_a)`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ} {a : ℕ}

/-- No two particles of the same group meet. -/
def NoSame (a : ℕ) (x : Cfg n) : Prop := ∀ i j, i ≠ j → SameB a i j → x i ≠ x j

lemma NoSame.pm {x : Cfg n} (hx : NoSame a x) {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) :
    NoSame a (pm σ x) := fun i j hij hs => by
  simp only [pm_apply]
  exact hx (σ i) (σ j) (fun h => hij (σ.injective h)) ((YG_sameB hσ i j).2 hs)

lemma NoSame.of_injective {x : Cfg n} (hx : Function.Injective x) : NoSame a x :=
  fun _ _ hij _ h => hij (hx h)

lemma NoSame.of_RY {x : Cfg n} (hx : x ∈ RY a n) : NoSame a x := fun i j hij hs => by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (hx.2 i j h hs).ne
  · exact (hx.2 j i h (sameB_comm.1 hs)).ne'

/-- `SY a` is locally constant away from same-group collisions. -/
lemma SY_eventually {x : Cfg n} (hx : NoSame a x) : ∀ᶠ y in 𝓝 x, SY a y = SY a x := by
  have hf : ∀ i j : Fin (n + 1), ∀ᶠ y in 𝓝 x,
      (if i < j ∧ SameB a i j then Real.sign (y j - y i) else 1) =
        (if i < j ∧ SameB a i j then Real.sign (x j - x i) else 1) := by
    intro i j
    split_ifs with h
    · have hne : x j - x i ≠ 0 := sub_ne_zero.2 (hx j i (ne_of_lt h.1).symm (sameB_comm.1 h.2))
      have hcd : Continuous fun y : Cfg n => y j - y i :=
        (continuous_apply j).sub (continuous_apply i)
      rcases hne.lt_or_gt with hl | hl
      · filter_upwards [hcd.continuousAt.eventually (gt_mem_nhds hl)] with y hy
        rw [Real.sign_of_neg hy, Real.sign_of_neg hl]
      · filter_upwards [hcd.continuousAt.eventually (lt_mem_nhds hl)] with y hy
        rw [Real.sign_of_pos hy, Real.sign_of_pos hl]
    · exact Eventually.of_forall fun _ => rfl
  have hall : ∀ᶠ y in 𝓝 x, ∀ i j : Fin (n + 1),
      (if i < j ∧ SameB a i j then Real.sign (y j - y i) else 1) =
        (if i < j ∧ SameB a i j then Real.sign (x j - x i) else 1) :=
    eventually_all.2 fun i => eventually_all.2 fun j => hf i j
  filter_upwards [hall] with y hy
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hy i j

/-- **Collision-free configurations are dense in the cube.** -/
lemma exists_injective_near {x : Cfg n} (hx : x ∈ Cube n) {U : Set (Cfg n)} (hU : U ∈ 𝓝 x) :
    ∃ y ∈ U, y ∈ Cube n ∧ Function.Injective y := by
  obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.1 (inter_mem hU (isOpen_cube.mem_nhds hx))
  by_contra hno
  push Not at hno
  have hsub : V ⊆ {y : Cfg n | ¬ Function.Injective y} := fun y hy =>
    hno y (hVU hy).1 (hVU hy).2
  have h0 : μN n {y : Cfg n | ¬ Function.Injective y} = 0 := ae_iff.1 ae_injective
  have hpos : 0 < μN n V := by
    rw [Measure.restrict_apply hVo.measurableSet,
      Set.inter_eq_left.2 fun y hy => (hVU hy).2]
    exact hVo.measure_pos volume ⟨x, hxV⟩
  exact hpos.ne' (measure_mono_null hsub h0)

/-- **The ordering sign is antisymmetric under the Young subgroup** away from same-group
collisions. -/
lemma SY_pm' {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) {x : Cfg n} (hx : x ∈ Cube n)
    (hns : NoSame a x) : SY a (pm σ x) = sgn σ * SY a x := by
  have h1 := SY_eventually hns
  have h2 : ∀ᶠ y in 𝓝 x, SY a (pm σ y) = SY a (pm σ x) :=
    (continuous_pm σ).continuousAt.eventually (SY_eventually (hns.pm hσ))
  obtain ⟨y, ⟨hy1, hy2⟩, -, hinj⟩ := exists_injective_near hx (h1.and h2)
  rw [← hy1, ← hy2, SY_pm hσ hinj]

lemma sgn_mul_self' (σ : Equiv.Perm (Fin (n + 1))) : sgn σ * sgn σ = 1 := sgn_mul_self σ

section gs

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} (hws : ∀ σ x, w (pm σ x) = w x)
  {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
  (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x)
include hws hF hVF

/-- **The sign of a ground state of mixed symmetry** at every point of the cube without
same-group collisions. -/
theorem gs_SY_pos {g : Cfg n → ℝ} (hg : IsGS (settingS (ymix a) w hw) v g) :
    ∃ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) ∧
      ∀ y ∈ Cube n, NoSame a y → 0 < s₀ * (SY a y * g y) := by
  have hD : g ∈ DomY a n := hg.1
  have key : ∀ s₀ : ℝ, (∀ x ∈ RY a n, 0 < s₀ * g x) →
      ∀ y ∈ Cube n, NoSame a y → 0 < s₀ * (SY a y * g y) := by
    intro s₀ hs y hy hns
    obtain ⟨ρ, hρ, hR⟩ := exists_YG_mem_RY (a := a) hy hns
    have h1 := hs _ hR
    have h2 : g (pm ρ y) = sgn ρ * g y := hD.2.1 ρ hρ y
    have h3 : SY a (pm ρ y) = sgn ρ * SY a y := SY_pm' hρ hy hns
    rw [SY_RY hR] at h3
    -- `SY a y = sgn ρ`
    have h4 : SY a y = sgn ρ := by
      have := congrArg (fun t => sgn ρ * t) h3
      simp only [mul_one, ← mul_assoc, sgn_mul_self, one_mul] at this
      exact this.symm
    rw [h4, ← h2]
    exact h1
  rcases gs_sign_RY hws hF hVF hg with h | h
  · exact ⟨1, Or.inl rfl, key 1 fun x hx => by rw [one_mul]; exact h x hx⟩
  · exact ⟨-1, Or.inr rfl, key (-1) fun x hx => by have := h x hx; linarith⟩

end gs

/-! ### The two groupings `a` and `a + 1` -/

/-- `Π_{i<a} sign(x_a - x_i)`, with `p` the particle of index `a`. -/
noncomputable def Rlow (a : ℕ) (p : Fin (n + 1)) (x : Cfg n) : ℝ :=
  ∏ i : Fin (n + 1), if (i : ℕ) < a then Real.sign (x p - x i) else 1

/-- `Π_{j>a} sign(x_j - x_a)`. -/
noncomputable def Rhigh (a : ℕ) (p : Fin (n + 1)) (x : Cfg n) : ℝ :=
  ∏ j : Fin (n + 1), if a < (j : ℕ) then Real.sign (x j - x p) else 1

lemma SY_mul_SY_succ {p : Fin (n + 1)} (hp : (p : ℕ) = a) {x : Cfg n} (hx : NoSame a x) :
    SY a x * SY (a + 1) x = Rlow a p x * Rhigh a p x := by
  -- both sides as double products over pairs
  have hlow : Rlow a p x = ∏ i : Fin (n + 1), ∏ j : Fin (n + 1),
      if i < j ∧ j = p then Real.sign (x j - x i) else 1 := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_eq_single p (fun j _ hj => by simp [hj]) (by simp)]
    have : i < p ↔ (i : ℕ) < a := by rw [Fin.lt_def, hp]
    simp only [this, and_true]
  have hhigh : Rhigh a p x = ∏ i : Fin (n + 1), ∏ j : Fin (n + 1),
      if i < j ∧ i = p then Real.sign (x j - x i) else 1 := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Finset.prod_eq_single p (fun i _ hi => by simp [hi]) (by simp)]
    have : p < j ↔ a < (j : ℕ) := by rw [Fin.lt_def, hp]
    simp only [this, and_true]
  rw [hlow, hhigh, SY, SY, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hpv : (p : ℕ) = a := hp
  by_cases hij : i < j
  · have hijv : (i : ℕ) < j := hij
    by_cases h1 : SameB a i j <;> by_cases h2 : SameB (a + 1) i j
    · -- same in both groupings: the square of a sign
      have hjp : j ≠ p := fun e => by
        subst e; simp only [SameB] at h1 h2; omega
      have hip : i ≠ p := fun e => by
        subst e; simp only [SameB] at h1 h2; omega
      have hne : x j - x i ≠ 0 := sub_ne_zero.2 (hx j i (ne_of_lt hij).symm (sameB_comm.1 h1))
      simp only [hij, h1, h2, true_and, hjp, hip, ite_false, mul_one]
      rcases Real.sign_apply_eq_of_ne_zero _ hne with h | h <;> rw [h] <;> norm_num
    · -- the pair `(a, j)`
      have hip : i = p := Fin.ext (by simp only [SameB] at h1 h2; omega)
      have hjp : j ≠ p := fun e => (ne_of_lt hij) (hip.trans e.symm)
      subst hip
      simp [hij, h1, h2, hjp]
    · -- the pair `(i, a)`
      have hjp : j = p := Fin.ext (by simp only [SameB] at h1 h2; omega)
      have hip : i ≠ p := fun e => (ne_of_lt hij) (e.trans hjp.symm)
      subst hjp
      simp [hij, h1, h2, hip]
    · have hjp : j ≠ p := fun e => by subst e; simp only [SameB] at h1 h2; omega
      have hip : i ≠ p := fun e => by subst e; simp only [SameB] at h1 h2; omega
      simp [hij, h1, h2, hip, hjp]
  · simp [hij]

end DFT.Continuum.Line
