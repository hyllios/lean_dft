/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.HK.YoungGS

/-!
# The Young antisymmetrisation on `L²` and `H¹₀`

`altY a f = Σ_{σ ∈ YG a} sgn σ · f ∘ σ` (`Line/YoungStrong`). Here, on states of finite kinetic
energy:

* `altY_altY`: `altY a ∘ altY a = |YG a| · altY a`;
* `integral_altY_mul`: `altY a` is self-adjoint in `L²(cube)`; `integral_mul_altY_self_nonneg`:
  `⟨χ, altY a χ⟩ ≥ 0`;
* `AntiY a χ`: antisymmetry under `YG a`, a.e.; for such `χ` and any `H¹` function `φ`, every term
  of the energy form is multiplied by `|YG a|` when `φ` is replaced by `altY a φ`
  (`integral_mul_altY_of_antiY`, `kin_mul_altY`, `h0W_altY`);
* **`el_all`**: the weak Schrödinger equation of a ground state of mixed symmetry holds against
  all `H¹` test functions, not only those of its symmetry;
* **`Q_altY_W`**: the Young antisymmetrisation of a ground state of type `c` is an eigenstate of
  type `a` with the same energy (for a relabelling-invariant interaction).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ} {a : ℕ}

/-! ### Algebra -/

open Classical in
/-- `|YG a|`. -/
noncomputable def cardY (n a : ℕ) : ℝ :=
  ((Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => YG a σ).card : ℝ)

lemma cardY_pos : 0 < cardY n a := by
  classical
  have : (1 : Equiv.Perm (Fin (n + 1))) ∈ Finset.univ.filter fun σ => YG a σ :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, YG_one a⟩
  unfold cardY
  exact_mod_cast Finset.card_pos.2 ⟨_, this⟩

/-- `altY a ∘ altY a = |YG a| · altY a`. -/
lemma altY_altY (f : Cfg n → ℝ) (x : Cfg n) : altY a (altY a f) x = cardY n a * altY a f x := by
  classical
  have h1 : ∀ σ, YG a σ → sgn σ * altY a f (pm σ x) = altY a f x := fun σ hσ => by
    rw [altY_pm f hσ, ← mul_assoc, sgn_mul_self, one_mul]
  have e : altY a (altY a f) x =
      ∑ σ : Equiv.Perm (Fin (n + 1)), if YG a σ then sgn σ * altY a f (pm σ x) else 0 := rfl
  rw [e, Finset.sum_congr rfl fun σ _ => show (if YG a σ then sgn σ * altY a f (pm σ x) else 0) =
      if YG a σ then altY a f x else 0 by
        by_cases h : YG a σ
        · simp only [h, ↓reduceIte, h1 σ h]
        · simp only [h, ↓reduceIte]]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

/-! ### `L²` -/

lemma memLp_altY {f : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) : MemLp (altY a f) 2 (μN n) := by
  classical
  have : altY a f = fun x => ∑ σ, (if YG a σ then sgn σ else 0) * f (pm σ x) := by
    funext x; simp only [altY]; exact Finset.sum_congr rfl fun σ _ => by split_ifs <;> simp
  rw [this]
  exact memLp_finsetSum _ fun σ _ => (memLp_comp_pm hf σ).const_mul _

/-- **`altY a` is self-adjoint in `L²`.** -/
lemma integral_altY_mul {f h : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) (hh : MemLp h 2 (μN n)) :
    ∫ x, altY a f x * h x ∂μN n = ∫ x, f x * altY a h x ∂μN n := by
  classical
  have e1 : (fun x => altY a f x * h x) = fun x =>
      ∑ σ, (if YG a σ then sgn σ else 0) * (f (pm σ x) * h x) := by
    funext x; simp only [altY, Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by split_ifs <;> ring
  have e2 : (fun x => f x * altY a h x) = fun x =>
      ∑ σ, (if YG a σ then sgn σ else 0) * (f x * h (pm σ x)) := by
    funext x; simp only [altY, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by split_ifs <;> ring
  rw [e1, e2, integral_finsetSum _ fun σ _ =>
      (int_mul_L2 (memLp_comp_pm hf σ) hh).const_mul _,
    integral_finsetSum _ fun σ _ => (int_mul_L2 hf (memLp_comp_pm hh σ)).const_mul _]
  simp only [integral_const_mul]
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin (n + 1))))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.inv_apply]
  have hY : YG a σ⁻¹ ↔ YG a σ := ⟨fun h => by simpa using YG_inv h, YG_inv⟩
  rw [sgn_inv]
  simp only [hY]
  congr 1
  have := integral_pm σ (fun y => f (pm σ⁻¹ y) * h y)
  simp only [pm_inv_pm] at this
  rw [this]

lemma integral_mul_altY_self_nonneg {χ : Cfg n → ℝ} (hχ : MemLp χ 2 (μN n)) :
    0 ≤ ∫ x, χ x * altY a χ x ∂μN n := by
  have hA := memLp_altY (a := a) hχ
  have key : ∫ x, altY a χ x * altY a χ x ∂μN n = cardY n a * ∫ x, χ x * altY a χ x ∂μN n := by
    rw [integral_altY_mul hχ hA, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by beta_reduce; rw [altY_altY]; ring)
  have hsq : 0 ≤ ∫ x, altY a χ x * altY a χ x ∂μN n := integral_nonneg fun x => mul_self_nonneg _
  have hc := cardY_pos (n := n) (a := a)
  nlinarith

/-! ### Antisymmetric states -/

/-- Antisymmetry under `YG a`, almost everywhere. -/
def AntiY (a : ℕ) (χ : Cfg n → ℝ) : Prop :=
  ∀ σ, YG a σ → ∀ᵐ x ∂μN n, χ (pm σ x) = sgn σ * χ x

lemma antiY_of_mem {χ : Cfg n → ℝ} (hχ : χ ∈ DomWS (ymix (n := n) a)) : AntiY a χ :=
  fun σ hσ => hχ.2.2 σ hσ

lemma AntiY.mul_sym {χ W : Cfg n → ℝ} (hχ : AntiY a χ) (hW : ∀ σ x, W (pm σ x) = W x) :
    AntiY a fun x => W x * χ x := fun σ hσ => by
  filter_upwards [hχ σ hσ] with x hx
  simp only [hW, hx]; ring

lemma altY_ae_of_antiY {χ : Cfg n → ℝ} (hχ : AntiY a χ) :
    altY a χ =ᵐ[μN n] fun x => cardY n a * χ x := by
  classical
  have h : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), YG a σ → χ (pm σ x) = sgn σ * χ x := by
    rw [ae_all_iff]; intro σ
    by_cases hσ : YG a σ
    · filter_upwards [hχ σ hσ] with x hx _ using hx
    · exact ae_of_all _ fun _ h => absurd h hσ
  filter_upwards [h] with x hx
  simp only [altY]
  rw [Finset.sum_congr rfl fun σ _ => show (if YG a σ then sgn σ * χ (pm σ x) else 0) =
      if YG a σ then χ x else 0 by
        by_cases h : YG a σ
        · simp only [h, ↓reduceIte, hx σ h, ← mul_assoc, sgn_mul_self, one_mul]
        · simp only [h, ↓reduceIte]]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- **Pairing with `altY a φ`** multiplies by `|YG a|`. -/
lemma integral_mul_altY_of_antiY {χ φ : Cfg n → ℝ} (hχ : MemLp χ 2 (μN n)) (hanti : AntiY a χ)
    (hφ : MemLp φ 2 (μN n)) :
    ∫ x, χ x * altY a φ x ∂μN n = cardY n a * ∫ x, χ x * φ x ∂μN n := by
  rw [← integral_altY_mul hχ hφ, ← integral_const_mul]
  exact integral_congr_ae (by filter_upwards [altY_ae_of_antiY hanti] with x hx; rw [hx]; ring)

/-! ### Derivatives -/

lemma isWD_altY {φ : Cfg n → ℝ} (hφ : H1W φ) (k : Fin (n + 1)) :
    IsWD k (altY a φ) (sumY a sgn fun σ => dW (σ⁻¹ k) φ) := by
  rw [altY_eq_sumY]
  exact (isWD_sumY sgn (fun _ _ => hφ.1) (fun σ _ => dW_spec (hφ.2 (σ⁻¹ k)))).2

lemma h1W_altY {φ : Cfg n → ℝ} (hφ : H1W φ) : H1W (altY a φ) :=
  ⟨memLp_altY hφ.1, fun k => ⟨_, isWD_altY hφ k⟩⟩

lemma altY_memWS {φ : Cfg n → ℝ} (hφ : H1W φ) : altY a φ ∈ DomWS (ymix (n := n) a) :=
  ⟨memLp_altY hφ.1, fun k => ⟨_, isWD_altY hφ k⟩, fun _ hσ => ae_of_all _ fun x =>
    altY_pm φ hσ x⟩

/-- Derivatives of an antisymmetric state under relabelling. -/
lemma ae_dW_pm_antiY {χ : Cfg n → ℝ} (hχ : χ ∈ DomWS (ymix (n := n) a)) :
    ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), YG a σ → ∀ k : Fin (n + 1),
      dW (σ⁻¹ k) χ (pm σ x) = sgn σ * dW k χ x := by
  rw [ae_all_iff]; intro σ
  by_cases hσ : YG a σ
  · have H : ∀ k : Fin (n + 1), ∀ᵐ x ∂μN n, dW (σ⁻¹ k) χ (pm σ x) = sgn σ * dW k χ x :=
      fun k => by
        have h1 := (dW_spec (hχ.2.1 (σ⁻¹ k))).comp_pm σ
        have h2 : IsWD k (fun x => sgn σ * χ x) (fun x => sgn σ * dW k χ x) :=
          (dW_spec (hχ.2.1 k)).const_mul _
        exact IsWD.unique (h1.congr (hχ.2.2 σ hσ)) h2
    filter_upwards [ae_all_iff.2 H] with x hx _ k using hx k
  · exact ae_of_all _ fun _ h => absurd h hσ

/-- **The kinetic form with `altY a φ`** is multiplied by `|YG a|`. -/
lemma kin_mul_altY {χ φ : Cfg n → ℝ} (hχ : χ ∈ DomWS (ymix (n := n) a)) (hφ : H1W φ) :
    ∑ k, ∫ x, dW k χ x * dW k (altY a φ) x ∂μN n =
      cardY n a * ∑ k, ∫ x, dW k χ x * dW k φ x ∂μN n := by
  classical
  have hdχ : ∀ k, MemLp (dW k χ) 2 (μN n) := fun k => memLp_dW hχ k
  have hdφ : ∀ k, MemLp (dW k φ) 2 (μN n) := fun k => memLp_dW_H hφ k
  -- expand `∂ₖ(altY a φ)`
  have e1 : ∀ k, ∫ x, dW k χ x * dW k (altY a φ) x ∂μN n =
      ∑ σ, (if YG a σ then sgn σ else 0) *
        ∫ x, dW k χ x * dW (σ⁻¹ k) φ (pm σ x) ∂μN n := fun k => by
    rw [integral_congr_ae (by
      filter_upwards [dW_ae_eq (isWD_altY (a := a) hφ k)] with x hx; rw [hx])]
    have : (fun x => dW k χ x * sumY a sgn (fun σ => dW (σ⁻¹ k) φ) x) = fun x =>
        ∑ σ, (if YG a σ then sgn σ else 0) * (dW k χ x * dW (σ⁻¹ k) φ (pm σ x)) := by
      funext x; simp only [sumY, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by split_ifs <;> ring
    rw [this, integral_finsetSum _ fun σ _ =>
      (int_mul_L2 (hdχ k) (memLp_comp_pm (hdφ _) σ)).const_mul _]
    simp only [integral_const_mul]
  -- each relabelling contributes the same
  have e2 : ∀ σ, YG a σ → ∑ k, ∫ x, dW k χ x * dW (σ⁻¹ k) φ (pm σ x) ∂μN n =
      sgn σ * ∑ k, ∫ x, dW k χ x * dW k φ x ∂μN n := fun σ hσ => by
    have hd := ae_dW_pm_antiY hχ
    have step : ∀ k, ∫ x, dW k χ x * dW (σ⁻¹ k) φ (pm σ x) ∂μN n =
        sgn σ * ∫ x, dW (σ⁻¹ k) χ x * dW (σ⁻¹ k) φ x ∂μN n := fun k => by
      have hc := integral_pm σ (fun y => dW k χ (pm σ⁻¹ y) * dW (σ⁻¹ k) φ y)
      simp only [pm_inv_pm] at hc
      rw [hc, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hd] with y hy
      have := hy σ⁻¹ (YG_inv hσ) (σ⁻¹ k)
      have hk : σ (σ⁻¹ k) = k := by simp
      rw [inv_inv, hk, sgn_inv] at this
      rw [this]; ring
    rw [Finset.sum_congr rfl fun k _ => step k, ← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp σ⁻¹ (fun j => ∫ x, dW j χ x * dW j φ x ∂μN n)
  simp only [e1]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun σ _ => show
      ∑ k, (if YG a σ then sgn σ else 0) * ∫ x, dW k χ x * dW (σ⁻¹ k) φ (pm σ x) ∂μN n =
        if YG a σ then ∑ k, ∫ x, dW k χ x * dW k φ x ∂μN n else 0 by
    rw [← Finset.mul_sum]
    split_ifs with h
    · rw [e2 σ h, ← mul_assoc, sgn_mul_self, one_mul]
    · simp]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

/-! ### The energy form -/

section form

variable {w : Cfg n → ℝ} (hw : Continuous w) (hws : ∀ σ x, w (pm σ x) = w x)
include hw hws

/-- **The energy form with `altY a φ`** is multiplied by `|YG a|`. -/
lemma h0W_altY {χ φ : Cfg n → ℝ} (hχ : χ ∈ DomWS (ymix (n := n) a)) (hφ : H1W φ) :
    h0W n w χ (altY a φ) = cardY n a * h0W n w χ φ := by
  have hwχ : MemLp (fun x => w x * χ x) 2 (μN n) := by
    simpa only [mul_comm] using memLp_mul_cont hw hχ.1
  have h2 := integral_mul_altY_of_antiY hwχ ((antiY_of_mem hχ).mul_sym hws) hφ.1
  have hw2 : ∫ x, w x * (χ x * altY a φ x) ∂μN n = cardY n a * ∫ x, w x * (χ x * φ x) ∂μN n := by
    have e1 : ∫ x, w x * (χ x * altY a φ x) ∂μN n = ∫ x, w x * χ x * altY a φ x ∂μN n :=
      integral_congr_ae (ae_of_all _ fun x => by ring)
    have e2 : ∫ x, w x * (χ x * φ x) ∂μN n = ∫ x, w x * χ x * φ x ∂μN n :=
      integral_congr_ae (ae_of_all _ fun x => by ring)
    rw [e1, h2, e2]
  simp only [h0W, kin_mul_altY hχ hφ, hw2]
  ring

omit hw hws in
lemma LN_altY (v : Pot) {χ φ : Cfg n → ℝ} (hχ : χ ∈ DomWS (ymix (n := n) a))
    (hφ : MemLp φ 2 (μN n)) :
    ∫ x, LN n v x * (χ x * altY a φ x) ∂μN n = cardY n a * ∫ x, LN n v x * (χ x * φ x) ∂μN n := by
  have hLχ : MemLp (fun x => LN n v x * χ x) 2 (μN n) := by
    simpa only [mul_comm] using memLp_mul_cont (continuous_LN v) hχ.1
  have h2 := integral_mul_altY_of_antiY hLχ ((antiY_of_mem hχ).mul_sym (LN_pm v)) hφ
  have e1 : ∫ x, LN n v x * (χ x * altY a φ x) ∂μN n = ∫ x, LN n v x * χ x * altY a φ x ∂μN n :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  have e2 : ∫ x, LN n v x * (χ x * φ x) ∂μN n = ∫ x, LN n v x * χ x * φ x ∂μN n :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e1, h2, e2]

/-- **The weak equation against all `H¹` test functions.** A ground state of mixed symmetry `c`
(relabelling-invariant `w`) satisfies `h₀(g, φ) + ⟨g, V φ⟩ = E ⟨g, φ⟩` for every `H¹` function
`φ`, of any symmetry. -/
theorem el_all {c : ℕ} {v : Pot} {g : Cfg n → ℝ} (hg : IsGS (settingWS (ymix c) w hw) v g)
    {φ : Cfg n → ℝ} (hφ : H1W φ) :
    h0W n w g φ + ∫ x, LN n v x * (g x * φ x) ∂μN n =
      Q (settingWS (ymix c) w hw) v g / ip (μ := μN n) g g * ∫ x, g x * φ x ∂μN n := by
  have hel := euler_lagrange hg (altY_memWS (a := c) hφ)
  change h0W n w g (altY c φ) + ∫ x, LN n v x * (g x * altY c φ x) ∂μN n =
    _ * ∫ x, g x * altY c φ x ∂μN n at hel
  rw [h0W_altY hw hws hg.1 hφ, LN_altY v hg.1 hφ.1,
    integral_mul_altY_of_antiY hg.1.1 (antiY_of_mem hg.1) hφ.1] at hel
  have hc := (cardY_pos (n := n) (a := c)).ne'
  have : cardY n c * (h0W n w g φ + ∫ x, LN n v x * (g x * φ x) ∂μN n) =
      cardY n c * (Q (settingWS (ymix c) w hw) v g / ip (μ := μN n) g g *
        ∫ x, g x * φ x ∂μN n) := by linear_combination hel
  exact mul_left_cancel₀ hc this

omit hw hws in
lemma h0W_symm' (ψ φ : Cfg n → ℝ) : h0W n w ψ φ = h0W n w φ ψ := by
  simp only [h0W]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by congr 1; funext x; ring
  · congr 1; funext x; ring

/-- **The lowered state is an eigenstate with the same energy.** For a ground state `g` of type
`c`, `f = altY a g` (of type `a`) has `Q(f) = E ⟨f, f⟩`. -/
theorem Q_altY_W {c : ℕ} {v : Pot} {g : Cfg n → ℝ} (hg : IsGS (settingWS (ymix c) w hw) v g) :
    Q (settingWS (ymix a) w hw) v (altY a g) =
      Q (settingWS (ymix c) w hw) v g / ip (μ := μN n) g g *
        ip (μ := μN n) (altY a g) (altY a g) := by
  set E := Q (settingWS (ymix c) w hw) v g / ip (μ := μN n) g g
  have hg1 : H1W g := h1W_of_mem hg.1
  have hf : altY a g ∈ DomWS (ymix (n := n) a) := altY_memWS hg1
  have hel := el_all hw hws hg (h1W_of_mem hf)
  change h0W n w (altY a g) (altY a g) + ∫ x, LN n v x * (altY a g x * altY a g x) ∂μN n =
    E * ∫ x, altY a g x * altY a g x ∂μN n
  rw [h0W_altY hw hws hf hg1, LN_altY v hf hg1.1,
    integral_mul_altY_of_antiY hf.1 (antiY_of_mem hf) hg1.1, h0W_symm']
  have e1 : ∫ x, LN n v x * (altY a g x * g x) ∂μN n = ∫ x, LN n v x * (g x * altY a g x) ∂μN n :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  have e2 : ∫ x, altY a g x * g x ∂μN n = ∫ x, g x * altY a g x ∂μN n :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e1, e2]
  linear_combination cardY n a * hel

end form

end DFT.Continuum.Line
