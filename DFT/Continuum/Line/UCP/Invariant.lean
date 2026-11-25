/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.UCP.ZeroSet

/-!
# Translation-invariant sets are null or conull

A measurable set `Z` that is, up to null sets, invariant under small coordinate translations
inside every sub-cube `[a, 1 - a]ᴺ` is null or conull in the cube (`null_or_conull`).

* `invariant_all`: invariance under coordinate translations of either sign;
* `invariant_vec`: invariance under all vector translations (composing coordinate moves; the
  intermediate points stay in the box);
* `const_on_box`: on an open box, the indicator agrees a.e. with `F / c`, `F = φ ⋆ χ` for a
  continuous tent kernel `φ` of mass `c` (Fubini); `F` is continuous and `{0, c}`-valued, hence
  constant on the (connected) box;
* `null_or_conull`: exhaust the cube by boxes.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology
open scoped ContDiff ENNReal

variable {n : ℕ}

section invariance

variable {Z : Set (Cfg n)} {a : ℝ}

/-- Invariance under coordinate translations of either sign, inside any set `P`. -/
lemma invariant_all_gen {P : Set (Cfg n)}
    (hinv : ∀ k (h : ℝ), 0 ≤ h → ∀ᵐ x ∂volume, x ∈ SP P h k → (x ∈ Z ↔ x + h • ek k ∈ Z))
    (k : Fin (n + 1)) (h : ℝ) :
    ∀ᵐ x ∂volume, x ∈ P → x + h • ek k ∈ P → (x ∈ Z ↔ x + h • ek k ∈ Z) := by
  rcases le_or_gt 0 h with hh | hh
  · filter_upwards [hinv k h hh] with x hx h1 h2
    exact hx ⟨h1, h2⟩
  · have H := (measurePreserving_add_right volume (h • ek k)).quasiMeasurePreserving.ae
      (hinv k (-h) (by linarith))
    filter_upwards [H] with x hx h1 h2
    have e : x + h • ek k + -h • ek k = x := by rw [neg_smul, add_neg_cancel_right]
    have := hx ⟨h2, by rw [e]; exact h1⟩
    rw [e] at this
    exact this.symm

/-- Invariance under coordinate translations of either sign. -/
lemma invariant_all
    (hinv : ∀ k (h : ℝ), 0 ≤ h → ∀ᵐ x ∂volume, x ∈ Sa n a h k → (x ∈ Z ↔ x + h • ek k ∈ Z))
    (k : Fin (n + 1)) (h : ℝ) :
    ∀ᵐ x ∂volume, x ∈ Qa n a → x + h • ek k ∈ Qa n a → (x ∈ Z ↔ x + h • ek k ∈ Z) :=
  invariant_all_gen hinv k h

/-- The partial translation by the coordinates in `s`. -/
def trS (t : Cfg n) (s : Finset (Fin (n + 1))) : Cfg n := fun j => if j ∈ s then t j else 0

lemma trS_insert (t : Cfg n) {s : Finset (Fin (n + 1))} {k : Fin (n + 1)} (hk : k ∉ s) :
    trS t (insert k s) = trS t s + t k • ek k := by
  funext j
  simp only [trS, Finset.mem_insert, Pi.add_apply, Pi.smul_apply, ek, smul_eq_mul]
  by_cases hj : j = k
  · subst hj; simp [hk]
  · simp [hj]

/-- Invariance under all vector translations, inside a product set `Π_j I_j`. -/
lemma invariant_vec_gen {I : Fin (n + 1) → Set ℝ}
    (hA : ∀ k (h : ℝ), ∀ᵐ x ∂volume, x ∈ univ.pi I → x + h • ek k ∈ univ.pi I →
      (x ∈ Z ↔ x + h • ek k ∈ Z)) (t : Cfg n) :
    ∀ᵐ x ∂volume, x ∈ univ.pi I → x + t ∈ univ.pi I → (x ∈ Z ↔ x + t ∈ Z) := by
  classical
  suffices H : ∀ s : Finset (Fin (n + 1)), ∀ᵐ x ∂volume, x ∈ univ.pi I →
      x + trS t s ∈ univ.pi I → (x ∈ Z ↔ x + trS t s ∈ Z) by
    have e : trS t Finset.univ = t := by funext j; simp [trS]
    simpa [e] using H Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    have e : trS t (∅ : Finset (Fin (n + 1))) = 0 := by funext j; simp [trS]
    simp [e]
  | insert k s hk ih =>
    have h2 := (measurePreserving_add_right volume (trS t s)).quasiMeasurePreserving.ae
      (hA k (t k))
    filter_upwards [ih, h2] with x h1 h2 hx hxt
    rw [trS_insert t hk, ← add_assoc] at hxt ⊢
    have hmid : x + trS t s ∈ univ.pi I := Set.mem_univ_pi.2 fun j => by
      have a1 := Set.mem_univ_pi.1 hx j
      have a2 := Set.mem_univ_pi.1 hxt j
      simp only [Pi.add_apply, Pi.smul_apply, ek, smul_eq_mul, trS] at a2 ⊢
      by_cases hj : j ∈ s
      · have hjk : j ≠ k := fun h => hk (h ▸ hj)
        simp only [hj, ↓reduceIte, Pi.single_eq_of_ne hjk, mul_zero, add_zero] at a2 ⊢
        exact a2
      · simp only [hj, ↓reduceIte, add_zero]; exact a1
    exact (h1 hx hmid).trans (h2 hmid hxt)

/-- Invariance under all vector translations. -/
lemma invariant_vec
    (hA : ∀ k (h : ℝ), ∀ᵐ x ∂volume, x ∈ Qa n a → x + h • ek k ∈ Qa n a →
      (x ∈ Z ↔ x + h • ek k ∈ Z)) (t : Cfg n) :
    ∀ᵐ x ∂volume, x ∈ Qa n a → x + t ∈ Qa n a → (x ∈ Z ↔ x + t ∈ Z) :=
  invariant_vec_gen (I := fun _ => Icc a (1 - a)) hA t

end invariance

/-! ### Constancy on a box -/

/-- The open box `(a + r, 1 - a - r)ᴺ`. -/
def Bx (n : ℕ) (a r : ℝ) : Set (Cfg n) := univ.pi fun _ => Ioo (a + r) (1 - a - r)

lemma isOpen_Bx (a r : ℝ) : IsOpen (Bx n a r) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

lemma measurableSet_Bx (a r : ℝ) : MeasurableSet (Bx n a r) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-- The tent kernel `Π_k max(0, r - |t_k|)`. -/
noncomputable def tent (r : ℝ) (t : Cfg n) : ℝ := ∏ k, max 0 (r - |t k|)

lemma continuous_tent (r : ℝ) : Continuous (tent (n := n) r) :=
  continuous_finsetProd _ fun k _ =>
    continuous_const.max (continuous_const.sub (continuous_abs.comp (continuous_apply k)))

lemma tent_nonneg (r : ℝ) (t : Cfg n) : 0 ≤ tent r t :=
  Finset.prod_nonneg fun _ _ => le_max_left _ _

lemma tent_eq_zero {r : ℝ} {t : Cfg n} {k : Fin (n + 1)} (h : r ≤ |t k|) : tent r t = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ k) (max_eq_left (by linarith))

lemma hasCompactSupport_tent (r : ℝ) : HasCompactSupport (tent (n := n) r) := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun _ => isCompact_Icc (a := -r) (b := r))
    fun t ht => ?_
  obtain ⟨k, hk⟩ : ∃ k, t k ∉ Icc (-r) r := by
    by_contra h; push Not at h; exact ht (Set.mem_univ_pi.2 h)
  refine tent_eq_zero (k := k) ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hk
  rcases hk with hk | hk
  · linarith [neg_le_abs (t k)]
  · linarith [le_abs_self (t k)]

lemma tent_pos {r : ℝ} (hr : 0 < r) : 0 < ∫ t, tent (n := n) r t :=
  (continuous_tent r).integral_pos_of_hasCompactSupport_nonneg_ne_zero (hasCompactSupport_tent r)
    (tent_nonneg r) (x := 0) (by
      simp only [tent, Pi.zero_apply, abs_zero, sub_zero]
      exact (Finset.prod_pos fun _ _ => lt_max_of_lt_right hr).ne')

/-- **Constancy on a connected open set.** If `Z` is invariant under translations inside `P`, and
`B - [-r, r]ᴺ ⊆ P` with `B` open and connected, then `Z` is null or conull in `B`. -/
theorem const_on_set {Z : Set (Cfg n)} (hZ : MeasurableSet Z) {P B : Set (Cfg n)}
    (hQc : P ⊆ Cube n) (hBo : IsOpen B) (hpre : IsPreconnected B) {r : ℝ} (hr : 0 < r)
    (hBK : ∀ x ∈ B, ∀ t ∈ univ.pi (fun _ : Fin (n + 1) => Icc (-r) r), x - t ∈ P)
    (hV : ∀ t : Cfg n, ∀ᵐ x ∂volume, x ∈ P → x + t ∈ P → (x ∈ Z ↔ x + t ∈ Z)) :
    (∀ᵐ x ∂volume.restrict B, x ∈ Z) ∨ (∀ᵐ x ∂volume.restrict B, x ∉ Z) := by
  have hBm : MeasurableSet B := hBo.measurableSet
  have hBQ : B ⊆ P := fun x hx => by
    simpa using hBK x hx 0 (Set.mem_univ_pi.2 fun _ =>
      ⟨by simp only [Pi.zero_apply]; linarith, by simp only [Pi.zero_apply]; linarith⟩)
  set Z' := Z ∩ Cube n
  have hZ' : MeasurableSet Z' := hZ.inter measurableSet_cube
  set χ : Cfg n → ℝ := Z'.indicator fun _ => 1
  have hχm : Measurable χ := measurable_const.indicator hZ'
  have hχi : Integrable χ := by
    refine (integrable_indicator_iff hZ').2 (integrableOn_const ?_)
    exact ne_top_of_le_ne_top (by rw [volume_cube]; exact ENNReal.one_ne_top)
      (measure_mono inter_subset_right)
  have hχ01 : ∀ x, χ x = 0 ∨ χ x = 1 := fun x => by
    by_cases hx : x ∈ Z' <;> simp [χ, hx]
  set c := ∫ t, tent (n := n) r t
  have hc : 0 < c := tent_pos hr
  set F : Cfg n → ℝ := fun x => ∫ t, tent r t * χ (x - t)
  have hFc : Continuous F := by
    have h := (hasCompactSupport_tent (n := n) r).continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (continuous_tent r) hχi.locallyIntegrable (μ := volume)
    convert h using 1
    funext x
    simp [convolution_def, F, smul_eq_mul]
  -- Fubini: for a.e. `x ∈ B`, `χ (x - t) = χ x` for a.e. `t` in the support of the kernel
  set K : Set (Cfg n) := univ.pi fun _ => Icc (-r) r
  set E : Set (Cfg n × Cfg n) := {p | p.1 ∈ B ∧ p.2 ∈ K ∧ χ (p.1 - p.2) ≠ χ p.1}
  have hE : MeasurableSet E :=
    (measurable_fst (hBm)).inter ((measurable_snd
      (MeasurableSet.univ_pi fun _ => measurableSet_Icc)).inter
      (measurableSet_eq_fun (hχm.comp (measurable_fst.sub measurable_snd))
        (hχm.comp measurable_fst)).compl)
  have hslice : ∀ t : Cfg n, volume ((fun x => (x, t)) ⁻¹' E) = 0 := fun t => by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hV (-t)] with x hx ⟨hxB, htK, hne⟩
    have hxQ := hBQ hxB
    have hxt : x + -t ∈ P := by rw [← sub_eq_add_neg]; exact hBK x hxB t htK
    have hiff := hx hxQ hxt
    apply hne
    simp only [χ, Z', ← sub_eq_add_neg] at hiff ⊢
    rw [← sub_eq_add_neg] at hxt
    by_cases hz : x ∈ Z
    · rw [indicator_of_mem (show x - t ∈ Z ∩ Cube n from ⟨hiff.1 hz, hQc hxt⟩),
        indicator_of_mem (show x ∈ Z ∩ Cube n from ⟨hz, hQc hxQ⟩)]
    · rw [indicator_of_notMem (fun h : x - t ∈ Z ∩ Cube n => hz (hiff.2 h.1)),
        indicator_of_notMem (fun h : x ∈ Z ∩ Cube n => hz h.1)]
  have hprod : (volume.prod volume) E = 0 := by
    rw [Measure.prod_apply_symm hE]
    simp [hslice]
  have hae := (Measure.measure_prod_null hE).1 hprod
  have hFx : ∀ᵐ x ∂volume.restrict B, F x = c * χ x := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem (hBm)] with x hx hxB
    simp only [Pi.zero_apply] at hx
    have h1 : ∀ᵐ t ∂volume, tent r t * χ (x - t) = tent r t * χ x := by
      rw [measure_eq_zero_iff_ae_notMem] at hx
      filter_upwards [hx] with t ht
      by_cases htK : t ∈ K
      · have : χ (x - t) = χ x := by
          by_contra hne; exact ht ⟨hxB, htK, hne⟩
        rw [this]
      · obtain ⟨k, hk⟩ : ∃ k, t k ∉ Icc (-r) r := by
          by_contra h; push Not at h; exact htK (Set.mem_univ_pi.2 h)
        have : tent r t = 0 := by
          refine tent_eq_zero (k := k) ?_
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hk
          rcases hk with hk | hk
          · linarith [neg_le_abs (t k)]
          · linarith [le_abs_self (t k)]
        simp [this]
    simp only [F]
    rw [integral_congr_ae h1, integral_mul_const]
  -- `F` takes only the values `0` and `c` on `B`
  set O := B ∩ {x | F x ≠ 0 ∧ F x ≠ c}
  have hO : IsOpen O := hBo.inter ((isOpen_ne_fun hFc continuous_const).inter
    (isOpen_ne_fun hFc continuous_const))
  have hO0 : volume O = 0 := by
    have h := (ae_restrict_iff' (hBm)).1 hFx
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with x hx ⟨hxB, h1, h2⟩
    rcases hχ01 x with h | h <;> simp [hx hxB, h] at h1 h2
  have hOe : O = ∅ := (hO.measure_eq_zero_iff volume).1 hO0
  have hval : ∀ x ∈ B, F x = 0 ∨ F x = c := fun x hx => by
    by_contra h; push Not at h
    have : x ∈ O := ⟨hx, h⟩
    rw [hOe] at this; exact this
  -- intermediate values
  by_cases hall : ∀ x ∈ B, F x = c
  · left
    filter_upwards [hFx, ae_restrict_mem (hBm)] with x hx hxB
    rw [hall x hxB] at hx
    have : χ x = 1 := by
      have := hc.ne'; field_simp at hx ⊢; linarith
    by_contra hz
    simp [χ, Z', hz] at this
  · right
    push Not at hall
    obtain ⟨x1, hx1B, hx1⟩ := hall
    have hF1 : F x1 = 0 := (hval x1 hx1B).resolve_right hx1
    have hzero : ∀ x ∈ B, F x = 0 := fun x hxB => by
      rcases hval x hxB with h | h
      · exact h
      · obtain ⟨y, hyB, hy⟩ := hpre.intermediate_value hx1B hxB hFc.continuousOn
          (show c / 2 ∈ Icc (F x1) (F x) by rw [hF1, h]; constructor <;> linarith)
        rcases hval y hyB with h' | h' <;> rw [h'] at hy <;> linarith
    filter_upwards [hFx, ae_restrict_mem (hBm)] with x hx hxB hz
    rw [hzero x hxB] at hx
    have : χ x = 0 := by
      rcases mul_eq_zero.1 hx.symm with h | h
      · linarith
      · exact h
    simp [χ, Z', hz, hQc (hBQ hxB)] at this

/-- **On an open box, an invariant set is null or conull.** -/
theorem const_on_box {Z : Set (Cfg n)} (hZ : MeasurableSet Z) {a r : ℝ} (ha : 0 < a)
    (hr : 0 < r)
    (hV : ∀ t : Cfg n, ∀ᵐ x ∂volume, x ∈ Qa n a → x + t ∈ Qa n a → (x ∈ Z ↔ x + t ∈ Z)) :
    (∀ᵐ x ∂volume.restrict (Bx n a r), x ∈ Z) ∨ (∀ᵐ x ∂volume.restrict (Bx n a r), x ∉ Z) :=
  const_on_set hZ (Qa_sub_cube ha) (isOpen_Bx a r)
    (convex_pi fun _ _ => convex_Ioo (a + r) (1 - a - r)).isPreconnected hr
    (fun x hx t ht => Set.mem_univ_pi.2 fun j => by
      have h1 := Set.mem_univ_pi.1 hx j
      have h2 := Set.mem_univ_pi.1 ht j
      simp only [Pi.sub_apply]
      exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩) hV

/-! ### Exhausting the cube -/

lemma Bx_sub_cube {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : Bx n a r ⊆ Cube n := fun x hx =>
  Set.mem_univ_pi.2 fun j => by
    have := Set.mem_univ_pi.1 hx j; exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The boxes `Bₘ = (2/(m+5), 1 - 2/(m+5))ᴺ`. -/
noncomputable def bm (m : ℕ) : ℝ := 1 / ((m : ℝ) + 5)

lemma bm_pos (m : ℕ) : 0 < bm m := by unfold bm; positivity

lemma bm_le (m : ℕ) : bm m ≤ 1 / 5 := by
  unfold bm
  exact one_div_le_one_div_of_le (by norm_num) (by linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])

lemma B0_sub (m : ℕ) : Bx n (bm 0) (bm 0) ⊆ Bx n (bm m) (bm m) := fun x hx =>
  Set.mem_univ_pi.2 fun j => by
    have h := Set.mem_univ_pi.1 hx j
    have h0 : bm 0 = 1 / 5 := by simp [bm]
    rw [h0] at h
    have := bm_le m
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

lemma cube_sub_iUnion : Cube n ⊆ ⋃ m, Bx n (bm m) (bm m) := by
  intro x hx
  have hj : ∀ j, ∃ m : ℕ, 2 * bm m < x j ∧ 2 * bm m < 1 - x j := fun j => by
    have h := Set.mem_univ_pi.1 hx j
    have hd : 0 < min (x j) (1 - x j) := lt_min h.1 (by linarith [h.2])
    obtain ⟨m, hm⟩ := exists_nat_gt (2 / min (x j) (1 - x j))
    refine ⟨m, ?_⟩
    have hm' : 2 * bm m < min (x j) (1 - x j) := by
      unfold bm
      rw [div_lt_iff₀ hd] at hm
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      nlinarith
    exact ⟨hm'.trans_le (min_le_left _ _), hm'.trans_le (min_le_right _ _)⟩
  choose m hm using hj
  set M := Finset.univ.sup m
  refine Set.mem_iUnion.2 ⟨M, Set.mem_univ_pi.2 fun j => ?_⟩
  have hle : bm M ≤ bm (m j) := by
    unfold bm
    exact one_div_le_one_div_of_le (by positivity)
      (by have := Finset.le_sup (f := m) (Finset.mem_univ j); exact_mod_cast by omega)
  exact ⟨by linarith [(hm j).1], by linarith [(hm j).2]⟩

lemma volume_B0_pos : 0 < volume (Bx n (bm 0) (bm 0)) := by
  refine (isOpen_Bx _ _).measure_pos volume ⟨fun _ => 1 / 2, Set.mem_univ_pi.2 fun _ => ?_⟩
  simp only [bm, Nat.cast_zero, zero_add]
  constructor <;> norm_num

/-- **A translation-invariant measurable set is null or conull in the cube.** -/
theorem null_or_conull {Z : Set (Cfg n)} (hZ : MeasurableSet Z)
    (hinv : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → ∀ k (h : ℝ), 0 ≤ h →
      ∀ᵐ x ∂volume, x ∈ Sa n a h k → (x ∈ Z ↔ x + h • ek k ∈ Z)) :
    (∀ᵐ x ∂μN n, x ∈ Z) ∨ (∀ᵐ x ∂μN n, x ∉ Z) := by
  have hP : ∀ m : ℕ, (∀ᵐ x ∂volume.restrict (Bx n (bm m) (bm m)), x ∈ Z) ∨
      (∀ᵐ x ∂volume.restrict (Bx n (bm m) (bm m)), x ∉ Z) := fun m =>
    const_on_box hZ (bm_pos m) (bm_pos m) (invariant_vec (invariant_all
      (hinv (bm m) (bm_pos m) ((bm_le m).trans (by norm_num)))))
  have hB0 := volume_B0_pos (n := n)
  have hcube : ∀ (p : Cfg n → Prop), (∀ m, ∀ᵐ x ∂volume.restrict (Bx n (bm m) (bm m)), p x) →
      ∀ᵐ x ∂μN n, p x := fun p h =>
    ae_restrict_of_ae_restrict_of_subset cube_sub_iUnion ((ae_restrict_iUnion_iff _ _).2 h)
  have hclash : ∀ m, (∀ᵐ x ∂volume.restrict (Bx n (bm m) (bm m)), x ∈ Z) →
      (∀ᵐ x ∂volume.restrict (Bx n (bm m) (bm m)), x ∉ Z) → False := fun m h1 h2 => by
    have h1' := ae_restrict_of_ae_restrict_of_subset (B0_sub m) h1
    have h2' := ae_restrict_of_ae_restrict_of_subset (B0_sub m) h2
    have : ∀ᵐ x ∂volume.restrict (Bx n (bm 0) (bm 0)), False := by
      filter_upwards [h1', h2'] with x a b using b a
    rw [ae_iff, Measure.restrict_apply' (measurableSet_Bx _ _)] at this
    simp only [not_false_eq_true, ofPred_true, univ_inter] at this
    exact hB0.ne' this
  rcases hP 0 with h0 | h0
  · left
    refine hcube _ fun m => ?_
    rcases hP m with hm | hm
    · exact hm
    · exact (hclash 0 h0 (ae_restrict_of_ae_restrict_of_subset (B0_sub m) hm)).elim
  · right
    refine hcube _ fun m => ?_
    rcases hP m with hm | hm
    · exact (hclash 0 (ae_restrict_of_ae_restrict_of_subset (B0_sub m) hm) h0).elim
    · exact hm

/-! ### Locally null or conull sets -/

/-- **Local constancy propagates through a connected set.** If every point of the preconnected
set `U` has an open neighbourhood in `U` on which `Z` is null or conull, then `Z` is
null or conull in `U`. -/
theorem null_or_conull_of_local {Z U : Set (Cfg n)} (hUc : IsPreconnected U)
    (hloc : ∀ x ∈ U, ∃ B, IsOpen B ∧ x ∈ B ∧ B ⊆ U ∧
      ((∀ᵐ y ∂volume.restrict B, y ∈ Z) ∨ (∀ᵐ y ∂volume.restrict B, y ∉ Z))) :
    (∀ᵐ y ∂volume.restrict U, y ∈ Z) ∨ (∀ᵐ y ∂volume.restrict U, y ∉ Z) := by
  -- the union of the open subsets of `U` on which `p` holds a.e.
  let A : (Cfg n → Prop) → Set (Cfg n) := fun p =>
    ⋃ i : {B : Set (Cfg n) // IsOpen B ∧ B ⊆ U ∧ ∀ᵐ y ∂volume.restrict B, p y}, i.1
  have hAo : ∀ p, IsOpen (A p) := fun p => isOpen_iUnion fun i => i.2.1
  have hAU : ∀ p, A p ⊆ U := fun p => iUnion_subset fun i => i.2.2.1
  have hAae : ∀ p, ∀ᵐ y ∂volume.restrict (A p), p y := fun p => by
    obtain ⟨T, hT, hTe⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : {B : Set (Cfg n) // IsOpen B ∧ B ⊆ U ∧ ∀ᵐ y ∂volume.restrict B, p y} => i.1)
      fun i => i.2.1
    change ∀ᵐ y ∂volume.restrict (⋃ i, _), p y
    rw [← hTe]
    exact (ae_restrict_biUnion_iff _ hT p).2 fun i _ => i.2.2.2
  have hmem : ∀ (p : Cfg n → Prop) (x : Cfg n) (B : Set (Cfg n)), IsOpen B → x ∈ B → B ⊆ U →
      (∀ᵐ y ∂volume.restrict B, p y) → x ∈ A p := fun p x B hB hx hBU h =>
    mem_iUnion.2 ⟨⟨B, hB, hBU, h⟩, hx⟩
  set A1 := A fun y => y ∈ Z
  set A0 := A fun y => y ∉ Z
  have hdisj : Disjoint A1 A0 := by
    rw [Set.disjoint_iff]
    intro x ⟨h1, h0⟩
    have hO : IsOpen (A1 ∩ A0) := (hAo _).inter (hAo _)
    have hpos : 0 < volume (A1 ∩ A0) := hO.measure_pos volume ⟨x, h1, h0⟩
    have hae : ∀ᵐ y ∂volume.restrict (A1 ∩ A0), False := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left (hAae _),
        ae_restrict_of_ae_restrict_of_subset inter_subset_right (hAae _)] with y a b using b a
    rw [ae_iff, Measure.restrict_apply' hO.measurableSet] at hae
    simp only [not_false_eq_true, ofPred_true, univ_inter] at hae
    exact hpos.ne' hae
  have hcov : U ⊆ A1 ∪ A0 := fun x hx => by
    obtain ⟨B, hB, hxB, hBU, h | h⟩ := hloc x hx
    · exact Or.inl (hmem _ x B hB hxB hBU h)
    · exact Or.inr (hmem _ x B hB hxB hBU h)
  by_cases h1 : (U ∩ A1).Nonempty
  · left
    exact ae_restrict_of_ae_restrict_of_subset
      (hUc.subset_left_of_subset_union (hAo _) (hAo _) hdisj hcov h1) (hAae _)
  · right
    have hsub : U ⊆ A0 := fun x hx => by
      rcases hcov hx with h | h
      · exact absurd ⟨x, hx, h⟩ h1
      · exact h
    exact ae_restrict_of_ae_restrict_of_subset hsub (hAae _)

end DFT.Continuum.Line
