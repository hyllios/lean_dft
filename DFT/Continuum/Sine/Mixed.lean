/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Exists

/-!
# Regularity of the minimiser under polynomial decay of the potential

`Sine/Regular` needs `Σ_l b_l (1 + |l|)^s < ∞` for every `s`. A smooth potential whose even
reflection across the walls is not smooth (for instance a pair interaction `u(x_i - x_j)`) has
cosine coefficients decaying only like `Π_j (1 + l_j)^{-2}`. This file runs the bootstrap with the
product weights

  `ω_r(m) = Π_j (m_j + 1)^r`,

which satisfy `ω_r(m') ≤ ω_r(m) ω_r(l)` for admissible `l`. The kernel is bounded on
`ℓ²(ω_r)` when `Σ_l b_l ω_r(l) < ∞`; the Euler–Lagrange equation gains `λ_m ≥ ω_δ(m)` for
`δ (n + 1) ≤ 2`; so after `n + 1` steps the minimiser lies in `ℓ²(ω_r λ)` for the given `r`. For
`r > 1/2`, Cauchy–Schwarz with `Σ_m ω_r(m)^{-2} < ∞` gives `Σ_m W(m)² |c_m| < ∞`, which is enough
for a `C²` sine series.

* `om`, `om_le_of_adm`, `om_le_lam`: the weights.
* `nW_Kc_le`: the kernel on `ℓ²(ω_r)`.
* `nW_lam_ne_top`, `summable_wt_sq_mul`: **the bootstrap**.
* `contDiff_ser2`: a sine series with `Σ W² |c_m| < ∞` is `C²`.
* `ser_min2`: the minimiser is a function in the domain.
* `exists_isGS_kernel`, `hk_line_kernel`, `lieb_line_kernel`: **existence, Hohenberg–Kohn and
  Lieb** under a kernel bound `|K(m', m)| ≤ Σ_l b_l [adm m' l m]` with
  `Σ_l b_l Π_j (1 + l_j)^r < ∞` for some `r ∈ (1/2, 2]`.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real
open scoped ENNReal

variable {n : ℕ}

/-! ### Product weights -/

/-- The product weight `ω_r(m) = Π_j (m_j + 1)^r`. -/
noncomputable def om (r : ℝ) (m : Fin (n + 1) → ℕ) : ℝ := ∏ j, ((m j : ℝ) + 1) ^ r

lemma om_pos (r : ℝ) (m : Fin (n + 1) → ℕ) : 0 < om r m :=
  Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (by positivity) r

lemma om_zero (m : Fin (n + 1) → ℕ) : om 0 m = 1 := by simp [om]

lemma om_add (r δ : ℝ) (m : Fin (n + 1) → ℕ) : om (r + δ) m = om r m * om δ m := by
  simp only [om, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => Real.rpow_add (by positivity) r δ

lemma om_mono {r s : ℝ} (hrs : r ≤ s) (m : Fin (n + 1) → ℕ) : om r m ≤ om s m :=
  Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ =>
    Real.rpow_le_rpow_of_exponent_le (by have : (0 : ℝ) ≤ m j := Nat.cast_nonneg _; linarith) hrs

/-- For admissible `l`, `ω_r(m') ≤ ω_r(m) ω_r(l)`. -/
lemma om_le_of_adm {r : ℝ} (hr : 0 ≤ r) {m' l m : Fin (n + 1) → ℕ} (h : adm m' l m) :
    om r m' ≤ om r m * om r l := by
  simp only [om, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ hr
  have h1 : m' j + 1 ≤ (m j + 1) + l j := adm1_le (h j)
  have h2 : ((m' j : ℝ) + 1) ≤ ((m j : ℝ) + 1) + l j := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ m j := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ l j := Nat.cast_nonneg _
  nlinarith

/-- The Euler–Lagrange gain: `ω_δ(m) ≤ λ_m` when `δ (n + 1) ≤ 2`. -/
lemma om_le_lam {δ : ℝ} (hδ : 0 ≤ δ) (hδn : δ * (n + 1) ≤ 2) (m : Fin (n + 1) → ℕ) :
    om δ m ≤ lam m := by
  set S := Real.sqrt (ksq m : ℝ)
  have hk : ∀ j, (m j : ℝ) + 1 ≤ S := fun j => by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have : (m j + 1) ^ 2 ≤ ksq m := Finset.single_le_sum (f := fun j => (m j + 1) ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact_mod_cast this
  have hS1 : 1 ≤ S := le_trans (by have : (0 : ℝ) ≤ m 0 := Nat.cast_nonneg _; linarith) (hk 0)
  calc om δ m ≤ ∏ _j : Fin (n + 1), S ^ δ :=
        Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ =>
          Real.rpow_le_rpow (by positivity) (hk j) hδ
    _ = S ^ (δ * (n + 1)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity)]
        push_cast; ring_nf
    _ ≤ S ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hS1 hδn
    _ = ksq m := by rw [Real.rpow_two, Real.sq_sqrt (by positivity)]
    _ ≤ lam m := by
        rw [lam]
        have : 1 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
        nlinarith [(Nat.cast_nonneg (ksq m) : (0 : ℝ) ≤ ksq m)]

/-! ### The kernel on `ℓ²(ω_r)` -/

section schur

variable {V : Cfg n → ℝ} {b : (Fin (n + 1) → ℕ) → ℝ} (hb0 : ∀ l, 0 ≤ b l) (hbS : Summable b)
  (hK : ∀ m' m, |Ker V m' m| ≤ ∑' l, b l * (if adm m' l m then 1 else 0))

/-- `Γ_r = Σ_l b_l ω_r(l)`. -/
noncomputable def GamW (b : (Fin (n + 1) → ℕ) → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∑' l, ENNReal.ofReal (b l * om r l)

/-- The majorant `A_r(m', m) = Σ_l b_l ω_r(l) [adm m' l m]`. -/
noncomputable def AmajW (b : (Fin (n + 1) → ℕ) → ℝ) (r : ℝ) (m' m : Fin (n + 1) → ℕ) : ℝ≥0∞ :=
  ∑' l, ENNReal.ofReal (b l * om r l) * (if adm m' l m then 1 else 0)

lemma AmajW_row (r : ℝ) (m' : Fin (n + 1) → ℕ) :
    ∑' m, AmajW b r m' m ≤ 3 ^ (n + 1) * GamW b r := by
  simp only [AmajW]
  rw [tsum_comm]
  simp only [ENNReal.tsum_mul_left]
  rw [GamW, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun l => ?_
  rw [mul_comm]; exact mul_le_mul_left (tsum_adm_le m' l) _

lemma AmajW_col (r : ℝ) (m : Fin (n + 1) → ℕ) :
    ∑' m', AmajW b r m' m ≤ 3 ^ (n + 1) * GamW b r := by
  simp only [AmajW]
  rw [tsum_comm]
  simp only [ENNReal.tsum_mul_left]
  rw [GamW, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun l => ?_
  rw [mul_comm]; exact mul_le_mul_left (tsum_adm_le' l m) _

include hb0 hbS hK in
lemma ofReal_om_Ker_le {r : ℝ} (hr : 0 ≤ r) (m' m : Fin (n + 1) → ℕ) :
    ENNReal.ofReal (om r m' * |Ker V m' m|) ≤ AmajW b r m' m * ENNReal.ofReal (om r m) := by
  have hs : Summable fun l => b l * (if adm m' l m then 1 else 0) :=
    Summable.of_nonneg_of_le (fun l => mul_nonneg (hb0 l) (by split_ifs <;> norm_num))
      (fun l => by split_ifs <;> simp [hb0 l]) hbS
  calc ENNReal.ofReal (om r m' * |Ker V m' m|)
      ≤ ENNReal.ofReal (om r m' * ∑' l, b l * (if adm m' l m then 1 else 0)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hK m' m) (om_pos r m').le)
    _ = ∑' l, ENNReal.ofReal (om r m' * (b l * (if adm m' l m then 1 else 0))) := by
        rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun l => mul_nonneg (om_pos r m').le
          (mul_nonneg (hb0 l) (by split_ifs <;> norm_num))) (hs.mul_left _)]
    _ ≤ ∑' l, ENNReal.ofReal (b l * om r l) * (if adm m' l m then 1 else 0) *
          ENNReal.ofReal (om r m) := by
        refine tsum_le_tsum fun l => ?_
        split_ifs with h
        · rw [mul_one, mul_one, ← ENNReal.ofReal_mul (mul_nonneg (hb0 l) (om_pos r l).le)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_le_mul_of_nonneg_left (om_le_of_adm hr h) (hb0 l)
          nlinarith
        · simp
    _ = AmajW b r m' m * ENNReal.ofReal (om r m) := by rw [AmajW, ENNReal.tsum_mul_right]

/-- The weighted norm `Σ_m (ω(m) |c_m|)²`. -/
noncomputable def nW (ω : (Fin (n + 1) → ℕ) → ℝ) (c : (Fin (n + 1) → ℕ) → ℝ) : ℝ≥0∞ :=
  ∑' m, ENNReal.ofReal (ω m * |c m|) ^ 2

include hb0 hbS hK in
/-- **The kernel on `ℓ²(ω_r)`**: `‖Kc‖_{ω_r} ≤ 3^{n+1} Γ_r ‖c‖_{ω_r}`. -/
theorem nW_Kc_le {r : ℝ} (hr : 0 ≤ r) (c : (Fin (n + 1) → ℕ) → ℝ) :
    nW (om r) (Kc V c) ≤ (3 ^ (n + 1) * GamW b r) ^ 2 * nW (om r) c := by
  have hpt : ∀ m', ENNReal.ofReal (om r m' * |Kc V c m'|) ≤
      ∑' m, AmajW b r m' m * ENNReal.ofReal (om r m * |c m|) := by
    intro m'
    calc ENNReal.ofReal (om r m' * |Kc V c m'|)
        = ENNReal.ofReal (om r m') * ENNReal.ofReal |Kc V c m'| :=
          ENNReal.ofReal_mul (om_pos r m').le
      _ ≤ ENNReal.ofReal (om r m') * ∑' m, ENNReal.ofReal |Ker V m' m * c m| :=
          by gcongr; exact ofReal_abs_tsum_le _
      _ = ∑' m, ENNReal.ofReal (om r m' * |Ker V m' m|) * ENNReal.ofReal |c m| := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun m => ?_
          rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), ← mul_assoc,
            ← ENNReal.ofReal_mul (om_pos r m').le]
      _ ≤ ∑' m, AmajW b r m' m * ENNReal.ofReal (om r m) * ENNReal.ofReal |c m| :=
          tsum_le_tsum fun m => by gcongr; exact ofReal_om_Ker_le hb0 hbS hK hr m' m
      _ = _ := by
          refine tsum_congr fun m => ?_
          rw [mul_assoc, ← ENNReal.ofReal_mul (om_pos r m).le]
  calc nW (om r) (Kc V c)
      ≤ ∑' m', (∑' m, AmajW b r m' m * ENNReal.ofReal (om r m * |c m|)) ^ 2 :=
        tsum_le_tsum fun m' => pow_le_pow_left' (hpt m') 2
    _ ≤ 3 ^ (n + 1) * GamW b r * (3 ^ (n + 1) * GamW b r) * nW (om r) c :=
        schur _ _ (AmajW_row r) (AmajW_col r)
    _ = _ := by ring

end schur

/-! ### The bootstrap -/

section boot

variable {V : Cfg n → ℝ} {b : (Fin (n + 1) → ℕ) → ℝ} (hb0 : ∀ l, 0 ≤ b l) (hbS : Summable b)
  (hK : ∀ m' m, |Ker V m' m| ≤ ∑' l, b l * (if adm m' l m then 1 else 0))

lemma nW_zero_ne_top {c : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2) :
    nW (om 0) c ≠ ⊤ := by
  have := nw_zero_ne_top hc
  rw [nw_eq] at this
  simpa [nW, om_zero] using this

include hb0 hbS hK in
/-- **One step**: from `ℓ²(ω_r)` to `ℓ²(ω_r λ)`. -/
lemma nW_step {c : (Fin (n + 1) → ℕ) → ℝ} {E : ℝ} (hEL : ∀ m, lam m * c m + Kc V c m = E * c m)
    {r : ℝ} (hr : 0 ≤ r) (hG : GamW b r ≠ ⊤) (hc : nW (om r) c ≠ ⊤) :
    nW (fun m => om r m * lam m) c ≠ ⊤ := by
  have hpt : ∀ m, ENNReal.ofReal (om r m * lam m * |c m|) ^ 2 ≤
      ENNReal.ofReal (2 * E ^ 2) * ENNReal.ofReal (om r m * |c m|) ^ 2 +
      ENNReal.ofReal 2 * ENNReal.ofReal (om r m * |Kc V c m|) ^ 2 := by
    intro m
    have hL : lam m * c m = E * c m - Kc V c m := by linarith [hEL m]
    have hQ : (lam m * c m) ^ 2 ≤ 2 * (E ^ 2 * c m ^ 2) + 2 * Kc V c m ^ 2 := by
      rw [hL]; nlinarith [sq_nonneg (E * c m + Kc V c m)]
    have ho := om_pos r m
    have hlam : 0 ≤ lam m := by unfold lam; positivity
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : (om r m * lam m * |c m|) ^ 2 = om r m ^ 2 * (lam m * c m) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring
    have r1 : (om r m * |c m|) ^ 2 = om r m ^ 2 * c m ^ 2 := by rw [mul_pow, sq_abs]
    have r2 : (om r m * |Kc V c m|) ^ 2 = om r m ^ 2 * Kc V c m ^ 2 := by rw [mul_pow, sq_abs]
    rw [e1]
    have := mul_le_mul_of_nonneg_left hQ (sq_nonneg (om r m))
    nlinarith [this, r1, r2]
  have hKc := nW_Kc_le hb0 hbS hK hr c
  refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hpt)
  rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ?_ hKc)⟩
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by simp) hG)) hc

/-- Trading the gain `λ` for a larger product weight. -/
lemma nW_raise {c : (Fin (n + 1) → ℕ) → ℝ} {r δ : ℝ} (hδ : 0 ≤ δ) (hδn : δ * (n + 1) ≤ 2)
    (h : nW (fun m => om r m * lam m) c ≠ ⊤) : nW (om (r + δ)) c ≠ ⊤ := by
  refine ne_top_of_le_ne_top h (tsum_le_tsum fun m => ?_)
  refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) 2
  rw [om_add]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (om_le_lam hδ hδn m) (om_pos r m).le) (abs_nonneg _)

include hb0 hbS hK in
/-- **The bootstrap**: a square-summable solution of `λ c + Kc = E c` lies in `ℓ²(ω_r λ)` when
`Σ_l b_l ω_r(l) < ∞`. -/
theorem nW_lam_ne_top {c : (Fin (n + 1) → ℕ) → ℝ} {E : ℝ}
    (hEL : ∀ m, lam m * c m + Kc V c m = E * c m) (hc : Summable fun m => c m ^ 2) {r : ℝ}
    (hr : 0 ≤ r) (hr2 : r ≤ 2) (hG : Summable fun l => b l * om r l) :
    nW (fun m => om r m * lam m) c ≠ ⊤ := by
  have hGs : ∀ s, s ≤ r → GamW b s ≠ ⊤ := fun s hsr => by
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum fun l => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (om_mono hsr l) (hb0 l)))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => mul_nonneg (hb0 l) (om_pos r l).le) hG]
    exact ENNReal.ofReal_ne_top
  have hN : (0 : ℝ) < n + 1 := by positivity
  have key : ∀ i : ℕ, nW (om (min (2 * (i : ℝ) / (n + 1)) r)) c ≠ ⊤ := by
    intro i
    induction i with
    | zero =>
      have : min (2 * ((0 : ℕ) : ℝ) / (n + 1)) r = 0 := by simp [hr]
      rw [this]; exact nW_zero_ne_top hc
    | succ i ih =>
      set a := 2 * (i : ℝ) / (n + 1)
      set a' := 2 * ((i + 1 : ℕ) : ℝ) / (n + 1)
      have haa : a' - a = 2 / (n + 1) := by
        simp only [a, a']; push_cast; field_simp; ring
      have hpos : 0 ≤ a' - a := by rw [haa]; positivity
      have hs0 : 0 ≤ min a r := le_min (by positivity) hr
      have hdiff : min a' r - min a r ≤ a' - a := by
        rcases min_choice a r with h | h <;> rw [h]
        · linarith [min_le_left a' r]
        · linarith [min_le_right a' r]
      have hle : min a r ≤ min a' r := min_le_min_right _ (by linarith)
      have hδn : (min a' r - min a r) * (n + 1) ≤ 2 := by
        calc (min a' r - min a r) * (n + 1) ≤ (a' - a) * (n + 1) :=
              mul_le_mul_of_nonneg_right hdiff hN.le
          _ = 2 := by rw [haa]; field_simp
      have h1 := nW_step hb0 hbS hK hEL hs0 (hGs _ (min_le_right _ _)) ih
      have h2 := nW_raise (r := min a r) (δ := min a' r - min a r) (by linarith) hδn h1
      rwa [add_sub_cancel] at h2
  have hfin : min (2 * ((n + 1 : ℕ) : ℝ) / (n + 1)) r = r := by
    rw [min_eq_right]
    push_cast
    rw [mul_div_assoc, div_self hN.ne', mul_one]
    exact hr2
  have h := key (n + 1)
  rw [hfin] at h
  exact nW_step hb0 hbS hK hEL hr (hGs r le_rfl) h

/-- `Σ_m ω_r(m)^{-2} < ∞` for `r > 1/2`. -/
lemma tsum_om_inv_ne_top {r : ℝ} (hr : 1 / 2 < r) :
    ∑' m : Fin (n + 1) → ℕ, ENNReal.ofReal ((om r m)⁻¹) ^ 2 ≠ ⊤ := by
  have hs : Summable fun k : ℕ => ((k : ℝ) + 1) ^ (-(2 * r)) := by
    have h1 := (Real.summable_nat_rpow_inv (p := 2 * r)).2 (by linarith)
    have h2 := (summable_nat_add_iff 1).2 h1
    refine h2.congr fun k => ?_
    push_cast
    rw [Real.rpow_neg (by positivity)]
  have hpt : ∀ m : Fin (n + 1) → ℕ, ENNReal.ofReal ((om r m)⁻¹) ^ 2 =
      ∏ j, ENNReal.ofReal (((m j : ℝ) + 1) ^ (-(2 * r))) := by
    intro m
    have ho := om_pos r m
    rw [← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_prod_of_nonneg (fun j _ => by positivity)]
    congr 1
    rw [om, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Real.rpow_neg (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  simp only [hpt]
  rw [tsum_pi_prod (n + 1) (fun _ k => ENNReal.ofReal (((k : ℝ) + 1) ^ (-(2 * r)))),
    ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
  simp

include hb0 hbS hK in
/-- **`Σ_m W(m)² |c_m| < ∞`** for a square-summable solution, when `Σ_l b_l ω_r(l) < ∞` for some
`r ∈ (1/2, 2]`. -/
theorem summable_wt_sq_mul {c : (Fin (n + 1) → ℕ) → ℝ} {E : ℝ}
    (hEL : ∀ m, lam m * c m + Kc V c m = E * c m) (hc : Summable fun m => c m ^ 2) {r : ℝ}
    (hr : 1 / 2 < r) (hr2 : r ≤ 2) (hG : Summable fun l => b l * om r l) :
    Summable fun m => (wt m : ℝ) ^ 2 * |c m| := by
  have hN := nW_lam_ne_top hb0 hbS hK hEL hc (by linarith) hr2 hG
  have hL : Summable fun m => lam m * |c m| := by
    refine summable_of_ofReal_abs ?_
    have hpt : ∀ m, ENNReal.ofReal (abs (lam m * |c m|)) =
        ENNReal.ofReal (om r m * lam m * |c m|) * ENNReal.ofReal ((om r m)⁻¹) := fun m => by
      have ho := om_pos r m
      have hl : 0 ≤ lam m := by unfold lam; positivity
      rw [abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; field_simp
    simp only [hpt]
    have h := tsum_mul_le_sq (fun m => ENNReal.ofReal (om r m * lam m * |c m|))
      (fun m => ENNReal.ofReal ((om r m)⁻¹))
    have hR := ENNReal.mul_ne_top hN (tsum_om_inv_ne_top (n := n) hr)
    exact (ENNReal.pow_ne_top_iff.1 (ne_top_of_le_ne_top hR h)).resolve_right two_ne_zero
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    (hL.mul_left ((n + 1) / π ^ 2))
  have := wt_sq_le_lam m
  calc (wt m : ℝ) ^ 2 * |c m| ≤ (n + 1) / π ^ 2 * lam m * |c m| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = _ := by ring

end boot

/-! ### A `C²` sine series -/

/-- **`‖D^i s_m‖ ≤ D_i (1 + π W)^i`** on all of `ℝ^{n+1}`. -/
lemma norm_iteratedFDeriv_smd_le' (m : Fin (n + 1) → ℕ) (i : ℕ) (x : Cfg n) :
    ‖iteratedFDeriv ℝ i (smd m) x‖ ≤ Dc n i * (1 + π * wt m) ^ i := by
  classical
  have hf : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))),
      ContDiff ℝ ⊤ (fun y : Cfg n => sn (m j + 1) (y j)) := fun j _ =>
    (contDiff_sn _).comp (by fun_prop)
  have h := norm_iteratedFDeriv_prod_le (u := Finset.univ)
    (f := fun j (y : Cfg n) => sn (m j + 1) (y j)) hf (x := x) (n := i) (by exact_mod_cast le_top)
  have e : smd m = fun y : Cfg n => ∏ j ∈ Finset.univ, sn (m j + 1) (y j) := rfl
  rw [e]
  refine h.trans ?_
  have hW1 : (1 : ℝ) ≤ 1 + π * wt m := by
    have : 0 ≤ π * (wt m : ℝ) := by positivity
    linarith
  have hfac : ∀ p ∈ (Finset.univ : Finset (Fin (n + 1))).sym i, ∀ j ∈ (Finset.univ : Finset _),
      ‖iteratedFDeriv ℝ ((p : Multiset (Fin (n + 1))).count j)
        (fun y : Cfg n => sn (m j + 1) (y j)) x‖ ≤
        √2 * (1 + π * wt m) ^ ((p : Multiset (Fin (n + 1))).count j) := by
    intro p _ j _
    refine (norm_iteratedFDeriv_factor_le _ _ j x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
    have hk : ((m j + 1 : ℕ) : ℝ) ≤ wt m := by
      exact_mod_cast Finset.single_le_sum (f := fun j => m j + 1) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ j)
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [pi_pos]) _
  rw [Dc, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∏ j ∈ Finset.univ, ‖iteratedFDeriv ℝ ((p : Multiset (Fin (n + 1))).count j)
        (fun y : Cfg n => sn (m j + 1) (y j)) x‖
      ≤ ∏ j ∈ (Finset.univ : Finset (Fin (n + 1))),
          √2 * (1 + π * wt m) ^ ((p : Multiset (Fin (n + 1))).count j) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (hfac p hp)
    _ = √2 ^ (n + 1) * (1 + π * wt m) ^ i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_pow_eq_pow_sum, Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
        simp

/-- **A sine series with `Σ W² |c_m| < ∞` is `C²`.** -/
theorem contDiff_ser2 {c : (Fin (n + 1) → ℕ) → ℝ}
    (hc : Summable fun m => (wt m : ℝ) ^ 2 * |c m|) : ContDiff ℝ 2 (ser c) := by
  have hf : ∀ m, ContDiff ℝ 2 fun x => c m * smd m x := fun m =>
    contDiff_const.mul ((contDiff_smd_top m).of_le le_top)
  refine contDiff_tsum (v := fun k m => |c m| * Dc n k * (1 + π * wt m) ^ k) hf
    (fun k hk => ?_) fun k m x hk => ?_
  · have hk2 : k ≤ 2 := by exact_mod_cast hk
    refine Summable.of_norm_bounded (hc.mul_left ((1 + π) ^ 2 * |Dc n k|)) fun m => ?_
    have hW : (1 : ℝ) ≤ wt m := by exact_mod_cast one_le_wt m
    have h0 : (1 : ℝ) ≤ 1 + π * wt m := by nlinarith [pi_pos]
    have h1 : 1 + π * wt m ≤ (1 + π) * wt m := by nlinarith [pi_pos]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs,
      abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + π * wt m) k)]
    calc |c m| * |Dc n k| * (1 + π * wt m) ^ k ≤ |c m| * |Dc n k| * ((1 + π) * wt m) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (pow_le_pow_right₀ h0 hk2).trans (pow_le_pow_left₀ (by linarith) h1 2)
      _ = _ := by ring
  · have e : (fun x => c m * smd m x) = c m • smd m := rfl
    rw [e, iteratedFDeriv_const_smul_apply ((contDiff_smd_top m).of_le le_top).contDiffAt,
      norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smd_le' m k x) (abs_nonneg _)

/-! ### The minimiser and the ground state -/

section minimiser

variable {V : Cfg n → ℝ} {b : (Fin (n + 1) → ℕ) → ℝ} (hb0 : ∀ l, 0 ≤ b l) (hbS : Summable b)
  (hK : ∀ m' m, |Ker V m' m| ≤ ∑' l, b l * (if adm m' l m then 1 else 0))
include hb0 hbS hK

/-- **The minimiser is a function in the domain**, under polynomial decay. -/
theorem ser_min2 (hVs : ∀ σ x, V (pm σ x) = V x) {τ : Stat} {a : (Fin (n + 1) → ℕ) → ℝ}
    (ha : Adm τ.toSym a) (hmin : Fn V a = E0 V τ.toSym) {r : ℝ} (hr : 1 / 2 < r) (hr2 : r ≤ 2)
    (hG : Summable fun l => b l * om r l) :
    ser a ∈ Dom τ n ∧ ∀ m, cN m (ser a) = a m := by
  have hEL := (kBd_of_kernel hb0 hbS hK).euler_lagrange hVs ha hmin
  have hq := summable_wt_sq_mul hb0 hbS hK hEL ha.sq hr hr2 hG
  have h0 : Summable fun m => |a m| := Summable.of_nonneg_of_le (fun m => abs_nonneg _)
    (fun m => le_mul_of_one_le_left (abs_nonneg _)
      (one_le_pow₀ (by exact_mod_cast one_le_wt m))) hq
  exact ⟨⟨contDiff_ser2 hq, fun σ x => ser_pm ha.sym σ trivial x, ser_face a⟩, cN_ser h0⟩

end minimiser

section existence

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {b : (Fin (n + 1) → ℕ) → ℝ}

/-- **Interacting ground states on a line exist** under a kernel bound with polynomial decay:
`|K(m', m)| ≤ Σ_l b_l [adm m' l m]` for the potential `Σ_k v(x_k) + w(x)`, with
`Σ_l b_l Π_j (1 + l_j)^r < ∞` for some `r ∈ (1/2, 2]`. -/
theorem exists_isGS_kernel {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x) (hb0 : ∀ l, 0 ≤ b l)
    (hbS : Summable b)
    (hK : ∀ m' m, |Ker (fun x => LN n v x + w x) m' m| ≤
      ∑' l, b l * (if adm m' l m then 1 else 0))
    {r : ℝ} (hr : 1 / 2 < r) (hr2 : r ≤ 2) (hG : Summable fun l => b l * om r l) :
    ∃ Φ, IsGS (setting τ n w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 := by
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hVs : ∀ σ x, V (pm σ x) = V x := fun σ x => by simp only [V, LN_pm, hws]
  obtain ⟨a, ha, hmin⟩ := (kBd_of_kernel hb0 hbS hK).exists_min (exists_adm τ)
  obtain ⟨hΦ, hcoef⟩ := ser_min2 hb0 hbS hK hVs ha hmin hr hr2 hG
  have hcoef' : (fun m => cN m (ser a)) = a := funext hcoef
  have hip : ip (μ := μN n) (ser a) (ser a) = 1 := by
    rw [ip_eq_tsum hΦ.1.continuous]; simp only [hcoef]; exact ha.norm
  have hQ : Q (setting τ n w hw) v (ser a) = E0 V τ.toSym := by
    rw [Q_eq_Fn hw v hΦ, hcoef', hmin]
  refine ⟨ser a, ⟨hΦ, hip ▸ one_pos, fun φ hφ => ?_⟩, hip⟩
  rw [hQ, hip, mul_one, Q_eq_Fn hw v hφ, ip_eq_tsum hφ.1.continuous]
  exact (kBd_of_kernel hb0 hbS hK).Fn_ge (Dir_cN hφ)

end existence

end DFT.Continuum.Sine
