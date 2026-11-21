/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.YoungStrong
import DFT.Continuum.Line.HardCore
import DFT.Continuum.Line.WeakRep

/-!
# The ordering sign within groups, and the competitor `S·|Φ|`

For a state `Φ` of mixed symmetry, `S(x) = Π_{i<j, same group} sign(x_j - x_i)` is the sign of
the ordering within the two groups, and `Φ̃ = S · |Φ|` is a candidate state that is nonnegative
on the ordered region `RY`.

* `SY`, `SY_RY`, `abs_SY_le`, `SY_pm_ae`: the sign, equal to `1` on `RY`, of modulus at most `1`,
  and antisymmetric under the Young subgroup away from collisions (via the Vandermonde sign
  `gA = SY · SC`, where the cross-group factor `SC` is invariant).
* `tl Φ = SY · |Φ|`: continuous (`continuous_tl`), vanishing on the walls, `tl² = Φ²`.
* `lipschitzOn_line`: along a coordinate line, `S · |g|` is Lipschitz whenever `S` changes only
  where `g` vanishes.
* `isWD_tl`: **`Φ̃` has weak derivatives with zero boundary values**, bounded by `|∂ₖΦ|`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine
open scoped NNReal

variable {n : ℕ} {a : ℕ}

/-! ### The sign of a product -/

lemma sign_mul' (x y : ℝ) : Real.sign (x * y) = Real.sign x * Real.sign y := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [Real.sign_of_neg hx, Real.sign_of_neg hy, Real.sign_of_pos (mul_pos_of_neg_of_neg hx hy)]
      norm_num
    · subst hy; simp
    · rw [Real.sign_of_neg hx, Real.sign_of_pos hy, Real.sign_of_neg (mul_neg_of_neg_of_pos hx hy)]
      norm_num
  · subst hx; simp
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [Real.sign_of_pos hx, Real.sign_of_neg hy, Real.sign_of_neg (mul_neg_of_pos_of_neg hx hy)]
      norm_num
    · subst hy; simp
    · rw [Real.sign_of_pos hx, Real.sign_of_pos hy, Real.sign_of_pos (mul_pos hx hy)]; norm_num

lemma sign_prod' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    Real.sign (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.sign_one]
  | insert b s hb ih => rw [Finset.prod_insert hb, Finset.prod_insert hb, sign_mul', ih]

/-! ### The ordering sign within groups -/

/-- `Π_{i<j, same group} sign(x_j - x_i)`. -/
noncomputable def SY (a : ℕ) (x : Cfg n) : ℝ :=
  ∏ i, ∏ j, if i < j ∧ SameB a i j then Real.sign (x j - x i) else 1

/-- `Π_{i<j, different groups} sign(x_j - x_i)`. -/
noncomputable def SC (a : ℕ) (x : Cfg n) : ℝ :=
  ∏ i, ∏ j, if i < j ∧ ¬ SameB a i j then Real.sign (x j - x i) else 1

lemma abs_SY_le (x : Cfg n) : |SY a x| ≤ 1 := by
  rw [SY, Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
  rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => ?_
  split_ifs
  · rcases Real.sign_apply_eq (x j - x i) with h | h | h <;> simp [h]
  · simp

lemma SY_RY {x : Cfg n} (hx : x ∈ RY a n) : SY a x = 1 := by
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs with h
  · exact Real.sign_of_pos (sub_pos.2 (hx.2 i j h.1 h.2))
  · rfl

lemma sameB_comm {i j : Fin (n + 1)} : SameB a i j ↔ SameB a j i := Iff.comm

lemma gA_eq_SY_mul_SC (x : Cfg n) : gA x = SY a x * SC a x := by
  rw [gA, vdm, Matrix.det_vandermonde, sign_prod', SY, SC, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sign_prod', ← Finset.prod_mul_distrib]
  have e : Finset.Ioi i = Finset.univ.filter fun j => i < j := by ext j; simp
  rw [e, Finset.prod_filter]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hij : i < j <;> by_cases hs : SameB a i j <;> simp [hij, hs]

lemma SC_eq (x : Cfg n) :
    SC a x = ∏ i : Fin (n + 1), ∏ j : Fin (n + 1),
      if (i : ℕ) < a ∧ a ≤ (j : ℕ) then Real.sign (x j - x i) else 1 := by
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  have hiff : (i < j ∧ ¬ SameB a i j) ↔ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
    simp only [SameB, Fin.lt_def]; omega
  simp only [hiff]

lemma SC_pm {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) (x : Cfg n) :
    SC a (pm σ x) = SC a x := by
  rw [SC_eq, SC_eq]
  set F : Fin (n + 1) → Fin (n + 1) → ℝ := fun i' j' =>
    if (i' : ℕ) < a ∧ a ≤ (j' : ℕ) then Real.sign (x j' - x i') else 1
  have h1 : ∀ i j : Fin (n + 1), ((i : ℕ) < a ∧ a ≤ (j : ℕ)) ↔
      ((σ i : ℕ) < a ∧ a ≤ (σ j : ℕ)) := fun i j => by
    rw [hσ i, ← not_lt, ← not_lt, hσ j]
  calc (∏ i : Fin (n + 1), ∏ j : Fin (n + 1),
        if (i : ℕ) < a ∧ a ≤ (j : ℕ) then Real.sign (pm σ x j - pm σ x i) else 1)
      = ∏ i, ∏ j, F (σ i) (σ j) := by
        refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
        simp only [F, pm_apply]
        exact if_congr (h1 i j) rfl rfl
    _ = ∏ i, ∏ j', F (σ i) j' :=
        Finset.prod_congr rfl fun i _ => Equiv.prod_comp σ (F (σ i))
    _ = ∏ i', ∏ j', F i' j' := Equiv.prod_comp σ (fun i' => ∏ j', F i' j')

lemma SC_ne_zero {x : Cfg n} (hx : Function.Injective x) : SC a x ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  split_ifs with h
  · rw [Ne, Real.sign_eq_zero_iff, sub_eq_zero]
    exact fun e => (ne_of_gt h.1) (hx e)
  · exact one_ne_zero

/-- **The ordering sign is antisymmetric under the Young subgroup**, away from collisions. -/
lemma SY_pm {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) {x : Cfg n}
    (hx : Function.Injective x) : SY a (pm σ x) = sgn σ * SY a x := by
  have h := gA_pm σ x
  rw [gA_eq_SY_mul_SC (a := a), gA_eq_SY_mul_SC (a := a), SC_pm hσ] at h
  exact mul_right_cancel₀ (SC_ne_zero hx) (by rw [h]; ring)

/-- Along a coordinate line, the sign changes only where particle `k` meets a partner. -/
lemma SY_update_ne {x : Cfg n} {k : Fin (n + 1)} {u v : ℝ} (huv : u ≤ v)
    (h : SY a (Function.update x k u) ≠ SY a (Function.update x k v)) :
    ∃ j, j ≠ k ∧ SameB a k j ∧ x j ∈ Icc u v := by
  by_contra hno
  push Not at hno
  apply h
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  split_ifs with hij
  · have hne : i ≠ j := ne_of_lt hij.1
    by_cases hik : i = k
    · subst hik
      have hj : j ≠ i := hne.symm
      simp only [Function.update_self, Function.update_of_ne hj]
      have hx := hno j hj hij.2
      rcases lt_or_gt_of_ne (show x j ≠ u from fun e => hx (by rw [← e]; exact ⟨le_rfl, e ▸ huv⟩))
        with h1 | h1
      · rw [Real.sign_of_neg (by linarith), Real.sign_of_neg (by linarith)]
      · by_cases h2 : x j ≤ v
        · exact absurd ⟨h1.le, h2⟩ hx
        · rw [Real.sign_of_pos (by linarith), Real.sign_of_pos (by push Not at h2; linarith)]
    by_cases hjk : j = k
    · subst hjk
      simp only [Function.update_self, Function.update_of_ne hik]
      have hx := hno i hik (sameB_comm.1 hij.2)
      rcases lt_or_gt_of_ne (show x i ≠ u from fun e => hx (by rw [e]; exact ⟨le_rfl, huv⟩))
        with h1 | h1
      · rw [Real.sign_of_pos (by linarith), Real.sign_of_pos (by linarith)]
      · by_cases h2 : x i ≤ v
        · exact absurd ⟨h1.le, h2⟩ hx
        · rw [Real.sign_of_neg (by linarith), Real.sign_of_neg (by push Not at h2; linarith)]
    · simp only [Function.update_of_ne hik, Function.update_of_ne hjk]
  · rfl

/-! ### The competitor `S · |Φ|` -/

/-- `Φ̃ = S · |Φ|`. -/
noncomputable def tl (a : ℕ) (Φ : Cfg n → ℝ) (x : Cfg n) : ℝ := SY a x * |Φ x|

lemma abs_tl_le (Φ : Cfg n → ℝ) (x : Cfg n) : |tl a Φ x| ≤ |Φ x| := by
  rw [tl, abs_mul, abs_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_SY_le x)

lemma tl_RY {Φ : Cfg n → ℝ} {x : Cfg n} (hx : x ∈ RY a n) : tl a Φ x = |Φ x| := by
  rw [tl, SY_RY hx, one_mul]

section dom

variable {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomY a n)
include hΦ

lemma tl_sq (x : Cfg n) : tl a Φ x ^ 2 = Φ x ^ 2 := by
  by_cases hc : ∃ i j, i ≠ j ∧ SameB a i j ∧ x i = x j
  · obtain ⟨i, j, hij, hs, he⟩ := hc
    have h0 := eq_zero_of_collisionY hΦ hij hs he
    simp [tl, h0]
  · push Not at hc
    have h1 : SY a x ^ 2 = 1 := by
      rw [SY, ← Finset.prod_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun j _ => ?_
      split_ifs with h
      · have hne : x j - x i ≠ 0 := sub_ne_zero.2 fun e => hc i j (ne_of_lt h.1) h.2 e.symm
        rcases Real.sign_apply_eq_of_ne_zero _ hne with h' | h' <;> rw [h'] <;> norm_num
      · simp
    rw [tl, mul_pow, h1, one_mul, sq_abs]

lemma tl_wall (x : Cfg n) (k : Fin (n + 1)) (hk : x k = 0 ∨ x k = 1) : tl a Φ x = 0 := by
  simp [tl, hΦ.2.2 x k hk]

lemma continuous_tl : Continuous (tl a Φ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hc : ∃ i j, i ≠ j ∧ SameB a i j ∧ x i = x j
  · obtain ⟨i, j, hij, hs, he⟩ := hc
    have h0 := eq_zero_of_collisionY hΦ hij hs he
    have hx0 : tl a Φ x = 0 := by simp [tl, h0]
    rw [ContinuousAt, hx0]
    have hΦt : Tendsto Φ (𝓝 x) (𝓝 0) := h0 ▸ hΦ.1.continuous.continuousAt
    exact squeeze_zero_norm (fun y => by simpa using abs_tl_le (a := a) Φ y)
      (by simpa using hΦt.norm)
  · push Not at hc
    have hS : ContinuousAt (SY a) x := by
      refine tendsto_finsetProd _ fun i _ => tendsto_finsetProd _ fun j _ => ?_
      split_ifs with h
      · have hne : x j - x i ≠ 0 := sub_ne_zero.2 fun e => hc i j (ne_of_lt h.1) h.2 e.symm
        have hev : (fun y : Cfg n => Real.sign (y j - y i)) =ᶠ[𝓝 x]
            fun _ => Real.sign (x j - x i) := by
          have hcd : Continuous fun y : Cfg n => y j - y i :=
            (continuous_apply j).sub (continuous_apply i)
          rcases hne.lt_or_gt with hl | hl
          · filter_upwards [hcd.continuousAt.eventually (gt_mem_nhds hl)] with y hy
            rw [Real.sign_of_neg hy, Real.sign_of_neg hl]
          · filter_upwards [hcd.continuousAt.eventually (lt_mem_nhds hl)] with y hy
            rw [Real.sign_of_pos hy, Real.sign_of_pos hl]
        exact tendsto_const_nhds.congr' hev.symm
      · exact tendsto_const_nhds
    exact hS.mul hΦ.1.continuous.continuousAt.abs

/-- **`Φ̃` is antisymmetric under the Young subgroup**, away from collisions. -/
lemma tl_pm {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) {x : Cfg n}
    (hx : Function.Injective x) : tl a Φ (pm σ x) = sgn σ * tl a Φ x := by
  rw [tl, tl, SY_pm hσ hx, hΦ.2.1 σ hσ x, abs_mul]
  have : |(ymix (n := n) a).χ σ| = 1 := by
    change |sgn σ| = 1
    rcases sgn_eq_or σ with h | h <;> simp [h]
  rw [this, one_mul]; ring

end dom

/-! ### Lipschitz along lines -/

/-- `s · |g|` is Lipschitz if `g` is and `s` (of modulus `≤ 1`) changes only where `g` vanishes. -/
lemma abs_sub_line {g s : ℝ → ℝ} {p q C : ℝ}
    (hg : ∀ u ∈ Icc p q, ∀ v ∈ Icc p q, |g u - g v| ≤ C * |u - v|) (hs : ∀ t, |s t| ≤ 1)
    (hjump : ∀ u ∈ Icc p q, ∀ v ∈ Icc p q, u ≤ v → s u ≠ s v → ∃ c ∈ Icc u v, g c = 0) :
    ∀ u ∈ Icc p q, ∀ v ∈ Icc p q, abs (s u * |g u| - s v * |g v|) ≤ C * |u - v| := by
  have key : ∀ u ∈ Icc p q, ∀ v ∈ Icc p q, u ≤ v →
      abs (s u * |g u| - s v * |g v|) ≤ C * |u - v| := by
    intro u hu v hv huv
    by_cases he : s u = s v
    · rw [he, ← mul_sub, abs_mul]
      calc |s v| * abs (|g u| - |g v|) ≤ 1 * |g u - g v| :=
            mul_le_mul (hs v) (abs_abs_sub_abs_le_abs_sub _ _) (abs_nonneg _) zero_le_one
        _ ≤ C * |u - v| := by rw [one_mul]; exact hg u hu v hv
    · obtain ⟨c, hc, hgc⟩ := hjump u hu v hv huv he
      have hcI : c ∈ Icc p q := ⟨hu.1.trans hc.1, hc.2.trans hv.2⟩
      have h1 := hg u hu c hcI
      have h2 := hg v hv c hcI
      rw [hgc, sub_zero] at h1 h2
      have h3 : abs (s u * |g u| - s v * |g v|) ≤ |g u| + |g v| := by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;>
          (rw [abs_mul, abs_abs]; exact mul_le_of_le_one_left (abs_nonneg _) (hs _))
      have hcu : |u - c| = c - u := by rw [abs_sub_comm, abs_of_nonneg (by linarith [hc.1])]
      have hcv : |v - c| = v - c := abs_of_nonneg (by linarith [hc.2])
      have huv' : |u - v| = v - u := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      rw [hcu] at h1; rw [hcv] at h2; rw [huv']
      nlinarith
  intro u hu v hv
  rcases le_total u v with h | h
  · exact key u hu v hv h
  · rw [abs_sub_comm, abs_sub_comm u v]; exact key v hv u hu h

section line

variable {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomY a n)
include hΦ

lemma jump_line (x : Cfg n) (k : Fin (n + 1)) {u v : ℝ} (huv : u ≤ v)
    (h : SY a (Function.update x k u) ≠ SY a (Function.update x k v)) :
    ∃ c ∈ Icc u v, Φ (Function.update x k c) = 0 := by
  obtain ⟨j, hjk, hs, hj⟩ := SY_update_ne huv h
  refine ⟨x j, hj, eq_zero_of_collisionY hΦ hjk.symm hs ?_⟩
  simp [Function.update_of_ne hjk]

/-- A bound for `|∂ₖΦ|` on the closed cube. -/
lemma exists_dk_bound (k : Fin (n + 1)) : ∃ C, 0 ≤ C ∧ ∀ x ∈ CubeC n, |dk k Φ x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_cubeC.exists_bound_of_continuousOn
    (contDiff_dk hΦ.1 k).continuous.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => (by simpa using hC x hx : |dk k Φ x| ≤ C).trans
    (le_max_left _ _)⟩

/-- The line through `x` in direction `k`. -/
lemma hasDerivAt_line (x : Cfg n) (k : Fin (n + 1)) (t : ℝ) :
    HasDerivAt (fun s => Φ (Function.update x k s)) (dk k Φ (Function.update x k t)) t :=
  hasDerivAt_slice (hΦ.1.differentiable (by norm_num)) x k t

/-- Mean value along a line, with a bound on a convex set of parameters. -/
lemma line_mvt (x : Cfg n) (k : Fin (n + 1)) {I : Set ℝ} (hI : Convex ℝ I) {C : ℝ}
    (hC : ∀ t ∈ I, |dk k Φ (Function.update x k t)| ≤ C) :
    ∀ u ∈ I, ∀ v ∈ I, |Φ (Function.update x k u) - Φ (Function.update x k v)| ≤ C * |u - v| := by
  intro u hu v hv
  have := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => Φ (Function.update x k s)) (f' := fun t => dk k Φ (Function.update x k t))
    (fun t _ => (hasDerivAt_line hΦ x k t).hasDerivWithinAt) (fun t ht => by
      simpa using hC t ht) hv hu
  simpa [Real.norm_eq_abs] using this

/-- `Φ̃` is Lipschitz along lines. -/
lemma lip_tl_line (x : Cfg n) (k : Fin (n + 1)) {p q C : ℝ}
    (hC : ∀ t ∈ Icc p q, |dk k Φ (Function.update x k t)| ≤ C) :
    ∀ u ∈ Icc p q, ∀ v ∈ Icc p q,
      |tl a Φ (Function.update x k u) - tl a Φ (Function.update x k v)| ≤ C * |u - v| :=
  abs_sub_line (g := fun s => Φ (Function.update x k s))
    (s := fun s => SY a (Function.update x k s)) (line_mvt hΦ x k (convex_Icc p q) hC)
    (fun _ => abs_SY_le _) (fun _ _ _ _ huv h => jump_line hΦ x k huv h)

end line

/-! ### Weak derivatives of `Φ̃` -/

/-- Line derivatives of a continuous function are measurable. -/
lemma measurable_line_deriv {G : Cfg n → ℝ} (hG : Continuous G) (k : Fin (n + 1)) :
    Measurable fun x : Cfg n => deriv (fun s => G (Function.update x k s)) (x k) := by
  have hF : Continuous (Function.uncurry fun (x : Cfg n) (s : ℝ) => G (Function.update x k s)) :=
    hG.comp (continuous_fst.update k continuous_snd)
  exact (measurable_deriv_with_param (𝕜 := ℝ) hF).comp
    (measurable_id.prodMk (measurable_pi_apply k))

/-- The derivative of `Φ̃` along coordinate `k`. -/
noncomputable def Gt (a : ℕ) (Φ : Cfg n → ℝ) (k : Fin (n + 1)) (x : Cfg n) : ℝ :=
  deriv (fun s => tl a Φ (Function.update x k s)) (x k)

section wd

variable {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomY a n)
include hΦ

lemma measurable_Gt (k : Fin (n + 1)) : Measurable (Gt a Φ k) :=
  measurable_line_deriv (continuous_tl hΦ) k

/-- `|∂ₖΦ̃| ≤ |∂ₖΦ|` in the cube. -/
lemma abs_Gt_le (k : Fin (n + 1)) (x : Cfg n) : |Gt a Φ k x| ≤ |dk k Φ x| := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set t := x k
  have hcd : Continuous fun s => dk k Φ (Function.update x k s) :=
    (contDiff_dk hΦ.1 k).continuous.comp (continuous_const.update k continuous_id)
  have hev : ∀ᶠ s in 𝓝 t, |dk k Φ (Function.update x k s)| < |dk k Φ x| + ε := by
    have := (hcd.abs.continuousAt (x := t)).eventually (gt_mem_nhds (a := |dk k Φ x| + ε)
      (by simp only [t, Function.update_eq_self]; linarith))
    exact this
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hsub : Icc (t - δ / 2) (t + δ / 2) ⊆ {s | dist s t < δ} := fun s hs => by
    simp only [mem_ofPred_eq, Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
  have hlip := lip_tl_line hΦ x k (p := t - δ / 2) (q := t + δ / 2) (C := |dk k Φ x| + ε)
    (fun s hs => (hball (hsub hs)).le)
  have hL : LipschitzOnWith (Real.toNNReal (|dk k Φ x| + ε))
      (fun s => tl a Φ (Function.update x k s)) (Icc (t - δ / 2) (t + δ / 2)) :=
    LipschitzOnWith.of_dist_le_mul fun u hu v hv => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
      exact hlip u hu v hv
  have hnhds : Icc (t - δ / 2) (t + δ / 2) ∈ 𝓝 t :=
    Icc_mem_nhds (by linarith) (by linarith)
  have := norm_deriv_le_of_lipschitzOn hnhds hL
  rw [Real.norm_eq_abs, Real.coe_toNNReal _ (by positivity)] at this
  exact this

lemma memLp_Gt (k : Fin (n + 1)) : MemLp (Gt a Φ k) 2 (μN n) := by
  obtain ⟨C, hC0, hC⟩ := exists_dk_bound hΦ k
  refine MemLp.of_bound (measurable_Gt hΦ k).aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
  rw [Real.norm_eq_abs]
  exact (abs_Gt_le hΦ k x).trans (hC x (cube_subset hx))

/-- **`Φ̃` has weak derivatives with zero boundary values.** -/
theorem isWD_tl (k : Fin (n + 1)) : IsWD k (tl a Φ) (Gt a Φ k) := by
  obtain ⟨C, hC0, hC⟩ := exists_dk_bound hΦ k
  refine ⟨memLp_Gt hΦ k, fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ k
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have htc := continuous_tl hΦ
  rw [integral_cube_ins (F := fun x => tl a Φ x * dk k φ x) k (integrableN (htc.mul hd)),
    integral_cube_ins (F := fun x => Gt a Φ k x * φ x) k
      (int_mul_cont (memLp_Gt hΦ k) hφ.continuous),
    ← integral_neg]
  refine setIntegral_congr_fun measurableSet_cube' fun y hy => ?_
  simp only [integral_Ioo_eq_interval]
  set f : ℝ → ℝ := fun t => tl a Φ (Fin.insertNth k t y)
  set u : ℝ → ℝ := fun t => φ (Fin.insertNth k t y)
  have hline : ∀ s, Function.update (Fin.insertNth k 0 y : Cfg n) k s = Fin.insertNth k s y :=
    fun s => by simp [Fin.update_insertNth]
  -- `f` is Lipschitz on `[0, 1]`
  have hlip := lip_tl_line hΦ (Fin.insertNth k 0 y) k (p := 0) (q := 1) (C := C) fun t ht => by
    rw [hline]
    refine hC _ fun i _ => ?_
    rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
    · simpa using ht
    · simpa using Ioo_subset_Icc_self (hy j (mem_univ j))
  simp only [hline] at hlip
  have hL : LipschitzOnWith (Real.toNNReal C) f (uIcc 0 1) :=
    LipschitzOnWith.of_dist_le_mul fun s hs t ht => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC0]
      rw [uIcc01] at hs ht
      exact hlip s hs t ht
  have hfAC : AbsolutelyContinuousOnInterval f 0 1 := hL.absolutelyContinuousOnInterval
  have huAC : AbsolutelyContinuousOnInterval u 0 1 :=
    ContDiffOn.absolutelyContinuousOnInterval (hφ.comp (contDiff_ins k y)).contDiffOn
  have hu : ∀ t, HasDerivAt u (dk k φ (Fin.insertNth k t y)) t := hasDerivAt_ins hφd k y
  have hf0 : f 0 = 0 := tl_wall hΦ _ k (Or.inl (by simp))
  have hf1 : f 1 = 0 := tl_wall hΦ _ k (Or.inr (by simp))
  have ibp := hfAC.integral_mul_deriv_eq_deriv_mul huAC
  rw [hf0, hf1, zero_mul, zero_mul, sub_zero, zero_sub] at ibp
  have hGt : ∀ t, Gt a Φ k (Fin.insertNth k t y) = deriv f t := fun t => by
    simp only [Gt, f, Fin.insertNth_apply_same, Fin.update_insertNth]
  have e1 : ∫ t in (0 : ℝ)..1, tl a Φ (Fin.insertNth k t y) * dk k φ (Fin.insertNth k t y) =
      ∫ t in (0 : ℝ)..1, f t * deriv u t := by
    congr 1; funext t; rw [(hu t).deriv]
  have e2 : ∫ t in (0 : ℝ)..1, Gt a Φ k (Fin.insertNth k t y) * φ (Fin.insertNth k t y) =
      ∫ t in (0 : ℝ)..1, deriv f t * u t := by
    congr 1; funext t; rw [hGt]
  rw [e1, e2, ibp]

end wd

end DFT.Continuum.Line
