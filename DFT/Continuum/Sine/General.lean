/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Decay
import DFT.Continuum.Line.HardCore

/-!
# Interacting ground states on a line for smooth potentials

Removes the cosine-series hypothesis of `Sine/Exists`: it suffices that `Σ_k v(x_k) + w(x)`
agrees on the closed cube with a smooth function. In each coordinate
`2 sin(πk'x) sin(πkx) = cos(π|k' - k|x) - cos(π(k' + k)x)`, so the kernel `⟨s_{m'}, V s_m⟩` is a
signed sum of `2^{n+1}` cosine coefficients of `V`, at distinct admissible indices. These decay
like `Π_j (1 + l_j)^{-2}` (`Sine/Decay`), which is the kernel bound of `Sine/Mixed` with
`r = 3/4`.

* `sn_mul_sn`, `smd_mul_smd`: products of sines as sums of cosines.
* `Ker_bound_of_coef`: the kernel bound from bounds on cosine coefficients.
* `kernel_of_smooth`: **the kernel bound for smooth potentials**.
* `exists_isGS_smooth`, `exists_unique_gs_smooth`, `hk_line_smooth`, `lieb_line_smooth`:
  **existence, uniqueness, Hohenberg–Kohn and Lieb** for `N` bosons or fermions on `[0, 1]`
  whenever `Σ_k v(x_k) + w(x)` is smooth on the closed cube.
* `pairU`, `hk_line_pair`, `lieb_line_pair`, `exists_unique_gs_pair`: the same for a smooth
  one-body potential and a smooth pair interaction `½ Σ_{i ≠ j} u(x_i - x_j)`.
* `exists_unique_gs_hardcore_smooth`: hard-core bosons with a smooth potential.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real
open scoped ENNReal ContDiff

variable {n : ℕ}

/-! ### Products of sines as sums of cosines -/

/-- The two cosine indices of `s_{k'} s_k`: `|k' - k|` (`false`) and `k' + k` (`true`). -/
def cix (k' k : ℕ) : Bool → ℕ
  | false => if k ≤ k' then k' - k else k - k'
  | true => k' + k

/-- Their signs. -/
def csg : Bool → ℝ
  | false => 1
  | true => -1

lemma abs_csg (b : Bool) : |csg b| = 1 := by cases b <;> simp [csg]

lemma sn_mul_sn (k' k : ℕ) (t : ℝ) :
    sn k' t * sn k t = ∑ b : Bool, csg b * Real.cos (π * cix k' k b * t) := by
  rw [Fintype.sum_bool]
  simp only [csg, cix]
  have h2 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have key : Real.cos (π * k' * t - π * k * t) - Real.cos (π * k' * t + π * k * t) =
      2 * Real.sin (π * k' * t) * Real.sin (π * k * t) := by
    rw [Real.cos_sub, Real.cos_add]; ring
  have hL : Real.cos (π * ((if k ≤ k' then k' - k else k - k' : ℕ) : ℝ) * t) =
      Real.cos (π * k' * t - π * k * t) := by
    split_ifs with h
    · rw [Nat.cast_sub h]; congr 1; ring
    · rw [Nat.cast_sub (by omega), ← Real.cos_neg]; congr 1; ring
  have hS : Real.cos (π * ((k' + k : ℕ) : ℝ) * t) = Real.cos (π * k' * t + π * k * t) := by
    push_cast; congr 1; ring
  rw [hL, hS]
  unfold sn
  linear_combination (Real.sin (π * k' * t) * Real.sin (π * k * t)) * h2 - key

/-- The cosine index of a choice `ε` of one of the two terms in each coordinate. -/
def cixM (m' m : Fin (n + 1) → ℕ) (ε : Fin (n + 1) → Bool) : Fin (n + 1) → ℕ :=
  fun j => cix (m' j + 1) (m j + 1) (ε j)

/-- The sign of a choice `ε`. -/
noncomputable def csgM (ε : Fin (n + 1) → Bool) : ℝ := ∏ j, csg (ε j)

lemma abs_csgM (ε : Fin (n + 1) → Bool) : |csgM ε| = 1 := by
  rw [csgM, Finset.abs_prod]; simp [abs_csg]

lemma smd_mul_smd (m' m : Fin (n + 1) → ℕ) (x : Cfg n) :
    smd m' x * smd m x = ∑ ε : Fin (n + 1) → Bool, csgM ε * cosM (cixM m' m ε) x := by
  rw [smd, smd, ← Finset.prod_mul_distrib]
  simp only [sn_mul_sn]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, csgM, cosM, cixM, ← Finset.prod_mul_distrib]

lemma adm_cixM (m' m : Fin (n + 1) → ℕ) (ε : Fin (n + 1) → Bool) : adm m' (cixM m' m ε) m :=
  fun j => by
    simp only [cixM]
    cases ε j <;> simp only [cix, adm1] <;> (try split_ifs) <;> first | omega | simp

lemma cixM_injective (m' m : Fin (n + 1) → ℕ) : Function.Injective (cixM m' m) := by
  intro ε ε' h
  funext j
  have := congrFun h j
  simp only [cixM] at this
  cases hε : ε j <;> cases hε' : ε' j <;> simp only [hε, hε', cix] at this ⊢ <;>
    split_ifs at this <;> omega

/-! ### The kernel bound -/

/-- The cosine coefficient `∫ V Π_j cos(π l_j x_j)` on the cube. -/
noncomputable def ccV (V : Cfg n → ℝ) (l : Fin (n + 1) → ℕ) : ℝ := ∫ x, V x * cosM l x ∂μN n

lemma Ker_eq_sum {V : Cfg n → ℝ} (hV : Continuous V) (m' m : Fin (n + 1) → ℕ) :
    Ker V m' m = ∑ ε, csgM ε * ccV V (cixM m' m ε) := by
  rw [Ker]
  have e : (fun x => smd m' x * (V x * smd m x)) =
      fun x => ∑ ε, csgM ε * (V x * cosM (cixM m' m ε) x) := by
    funext x
    rw [show smd m' x * (V x * smd m x) = V x * (smd m' x * smd m x) by ring, smd_mul_smd,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => by ring
  rw [e, integral_finsetSum Finset.univ
    (f := fun ε x => csgM ε * (V x * cosM (cixM m' m ε) x)) fun ε _ =>
    (integrableN (hV.mul (continuous_cosM _))).const_mul _]
  simp only [ccV, integral_const_mul]

/-- **The kernel bound from bounds on cosine coefficients.** -/
theorem Ker_bound_of_coef {V : Cfg n → ℝ} (hV : Continuous V) {b : (Fin (n + 1) → ℕ) → ℝ}
    (hb0 : ∀ l, 0 ≤ b l) (hbS : Summable b) (hcc : ∀ l, |ccV V l| ≤ b l)
    (m' m : Fin (n + 1) → ℕ) :
    |Ker V m' m| ≤ ∑' l, b l * (if adm m' l m then 1 else 0) := by
  rw [Ker_eq_sum hV]
  have hs : Summable fun l => b l * (if adm m' l m then 1 else 0) :=
    Summable.of_nonneg_of_le (fun l => mul_nonneg (hb0 l) (by split_ifs <;> norm_num))
      (fun l => by split_ifs <;> simp [hb0 l]) hbS
  calc |∑ ε, csgM ε * ccV V (cixM m' m ε)| ≤ ∑ ε, |csgM ε * ccV V (cixM m' m ε)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ε, b (cixM m' m ε) := Finset.sum_le_sum fun ε _ => by
        rw [abs_mul, abs_csgM, one_mul]; exact hcc _
    _ = ∑ l ∈ Finset.univ.image (cixM m' m), b l :=
        (Finset.sum_image fun ε _ ε' _ h => cixM_injective m' m h).symm
    _ = ∑ l ∈ Finset.univ.image (cixM m' m), b l * (if adm m' l m then 1 else 0) :=
        Finset.sum_congr rfl fun l hl => by
          obtain ⟨ε, -, rfl⟩ := Finset.mem_image.1 hl
          simp only [adm_cixM m' m ε, ↓reduceIte, mul_one]
    _ ≤ ∑' l, b l * (if adm m' l m then 1 else 0) :=
        Summable.sum_le_tsum _ (fun l _ => mul_nonneg (hb0 l) (by split_ifs <;> norm_num)) hs

/-- Cosine coefficients of a potential that is smooth on the closed cube decay like
`Π_j (1 + l_j)^{-2}`. -/
lemma ccV_decay {V F : Cfg n → ℝ} (hF : ContDiff ℝ ∞ F) (hVF : ∀ x ∈ CubeC n, V x = F x) :
    ∃ C, 0 ≤ C ∧ ∀ l, |ccV V l| ≤ C * ∏ j, rho (l j) := by
  obtain ⟨C, hC0, hC⟩ := coef_decay (n + 1) (E := ℝ) (S := {0}) isCompact_singleton
    (F := fun _ y => F y) (hF.comp contDiff_snd)
  refine ⟨C, hC0, fun l => ?_⟩
  have e : ccV V l = ∫ y, F y * cosP l y ∂piM (n + 1) := by
    rw [ccV, ← muN_eq]
    refine integral_congr_ae ((ae_restrict_mem measurableSet_cube).mono fun x hx => ?_)
    simp only [hVF x (cube_subset hx), cosM, cosP]
  rw [e]
  exact hC 0 rfl l

lemma summable_prod_pi {g : ℕ → ℝ} (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g) :
    Summable fun l : Fin (n + 1) → ℕ => ∏ j, g (l j) := by
  refine summable_of_ofReal_abs ?_
  have e : ∀ l : Fin (n + 1) → ℕ,
      ENNReal.ofReal |∏ j, g (l j)| = ∏ j, ENNReal.ofReal (g (l j)) := fun l => by
    rw [abs_of_nonneg (Finset.prod_nonneg fun j _ => hg0 _),
      ENNReal.ofReal_prod_of_nonneg fun j _ => hg0 _]
  simp only [e]
  rw [tsum_pi_prod (n + 1) (fun _ k => ENNReal.ofReal (g k)),
    ← ENNReal.ofReal_tsum_of_nonneg hg0 hg]
  simp

lemma summable_rho : Summable rho := by
  have := (Real.summable_one_div_nat_pow (p := 2)).2 one_lt_two
  refine ((summable_nat_add_iff 1).2 this).congr fun k => ?_
  simp [rho]

lemma summable_rho_rpow : Summable fun k : ℕ => rho k * ((k : ℝ) + 1) ^ (3 / 4 : ℝ) := by
  have h1 := (Real.summable_nat_rpow_inv (p := 5 / 4)).2 (by norm_num)
  refine ((summable_nat_add_iff 1).2 h1).congr fun k => ?_
  push_cast
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [rho, ← Real.rpow_natCast ((k : ℝ) + 1) 2, ← Real.rpow_neg hk.le, ← Real.rpow_neg hk.le,
    ← Real.rpow_add hk]
  norm_num

/-- **The kernel bound for smooth potentials**: if `V` agrees on the closed cube with a smooth
function, the hypotheses of `exists_isGS_kernel` hold with `r = 3/4`. -/
theorem kernel_of_smooth {V F : Cfg n → ℝ} (hV : Continuous V) (hF : ContDiff ℝ ∞ F)
    (hVF : ∀ x ∈ CubeC n, V x = F x) :
    ∃ b : (Fin (n + 1) → ℕ) → ℝ, (∀ l, 0 ≤ b l) ∧ Summable b ∧
      (∀ m' m, |Ker V m' m| ≤ ∑' l, b l * (if adm m' l m then 1 else 0)) ∧
      Summable fun l => b l * om (3 / 4) l := by
  obtain ⟨C, hC0, hC⟩ := ccV_decay hF hVF
  set b : (Fin (n + 1) → ℕ) → ℝ := fun l => C * ∏ j, rho (l j) with hbdef
  have hb0 : ∀ l, 0 ≤ b l := fun l =>
    mul_nonneg hC0 (Finset.prod_nonneg fun j _ => (rho_pos _).le)
  have hbS : Summable b := (summable_prod_pi (fun k => (rho_pos k).le) summable_rho).mul_left C
  refine ⟨b, hb0, hbS, fun m' m => Ker_bound_of_coef hV hb0 hbS hC m' m, ?_⟩
  have h := (summable_prod_pi (n := n) (g := fun k => rho k * ((k : ℝ) + 1) ^ (3 / 4 : ℝ))
    (fun k => by have := rho_pos k; positivity) summable_rho_rpow).mul_left C
  refine h.congr fun l => ?_
  simp only [hbdef, om, Finset.prod_mul_distrib, mul_assoc]

/-! ### Ground states for smooth potentials -/

section existence

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot}

/-- **Interacting ground states on a line exist** whenever `Σ_k v(x_k) + w(x)` agrees on the
closed cube with a smooth function. -/
theorem exists_isGS_smooth {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x) {F : Cfg n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x) :
    ∃ Φ, IsGS (setting τ n w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 := by
  obtain ⟨b, hb0, hbS, hK, hG⟩ := kernel_of_smooth ((continuous_LN v).add hw) hF hVF
  exact exists_isGS_kernel hws hb0 hbS hK (by norm_num) (by norm_num) hG

theorem exists_isNGS_smooth {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x) {F : Cfg n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x) :
    ∃ ψ, IsNGS (setting τ n w hw) v ψ := by
  obtain ⟨Φ, hΦ, hip⟩ := exists_isGS_smooth (τ := τ) (hw := hw) hws hF hVF
  refine ⟨Φ, ⟨hΦ.1, hip⟩, fun φ hφ => ?_⟩
  have := hΦ.2.2 φ hφ.1
  rwa [hφ.2, hip, mul_one, mul_one] at this

/-- Existence and uniqueness of the ground state for smooth potentials. -/
theorem exists_unique_gs_smooth {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x) {F : Cfg n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x) :
    ∃ Φ, IsGS (setting τ n w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 ∧
      ∀ Ψ, IsGS (setting τ n w hw) v Ψ → ∃ c : ℝ, ∀ x ∈ CubeC n, Ψ x = c * Φ x := by
  obtain ⟨Φ, hΦ, hip⟩ := exists_isGS_smooth (τ := τ) (hw := hw) hws hF hVF
  exact ⟨Φ, hΦ, hip, fun Ψ hΨ => gs_unique_line hws hΨ hΦ⟩

/-- **Hohenberg–Kohn for `N` interacting bosons or fermions on a line** whenever
`Σ_k v(x_k) + w(x)` is smooth on the closed cube: the ground state of `v` exists, and ground
states of `v` and of any continuous `v'` with the same one-body density force `v - v'` to be
constant. -/
theorem hk_line_smooth {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x) {F : Cfg n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x) (v' : Pot) :
    (∃ Φ, IsGS (setting τ n w hw) v Φ) ∧ ∀ Φ Φ', IsGS (setting τ n w hw) v Φ →
      IsGS (setting τ n w hw) v' Φ' →
      (∀ t ∈ Ioo (0 : ℝ) 1, ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 =
        ∫ y in Cube' n, Φ' (Fin.cons t y) ^ 2) → ∃ k : ℝ, v - v' = k • one :=
  ⟨(exists_isGS_smooth hws hF hVF).imp fun _ h => h.1, fun _ _ h h' hρ =>
    hk_line_of_ucp h h' hρ (ucp_line_stat hws h)⟩

/-- **The Lieb functional for `N` interacting bosons or fermions on a line** whenever
`Σ_k v(x_k) + w(x)` is smooth on the closed cube: a normalised ground state `ψ` exists; at its
density the Lieb functional equals `⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient, and every other
subgradient `-v'` has `v - v'` constant. -/
theorem lieb_line_smooth {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x) {F : Cfg n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x) :
    ∃ ψ, IsNGS (setting τ n w hw) v ψ ∧
      liebF (setting τ n w hw) (dens (setting τ n w hw) ψ) =
        (((setting τ n w hw).h0 ψ ψ : ℝ) : EReal) ∧
      (∀ ρ : Pot → ℝ, (((setting τ n w hw).h0 ψ ψ + dens (setting τ n w hw) ψ v - ρ v : ℝ) :
        EReal) ≤ liebF (setting τ n w hw) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ,
        (((setting τ n w hw).h0 ψ ψ + dens (setting τ n w hw) ψ v' - ρ v' : ℝ) : EReal) ≤
          liebF (setting τ n w hw) ρ) → ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨ψ, hψ⟩ := exists_isNGS_smooth (τ := τ) (hw := hw) hws hF hVF
  exact ⟨ψ, hψ, lieb_line hws hψ⟩

/-- **Hard-core bosons** with a smooth potential: the ground state exists and is unique up to a
constant factor. -/
theorem exists_unique_gs_hardcore_smooth (hws : ∀ σ x, w (pm σ x) = w x) {F : Cfg n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x) :
    ∃ Φ, IsGS (settingHC n w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 ∧
      ∀ Ψ, IsGS (settingHC n w hw) v Ψ → ∃ c : ℝ, ∀ x ∈ CubeC n, Ψ x = c * Φ x := by
  obtain ⟨Φ, hΦ, hip⟩ := exists_isGS_smooth (τ := .fer) (hw := hw) hws hF hVF
  have hG := (isGS_mulA_iff hΦ.1 v).2 hΦ
  exact ⟨mulA Φ, hG, by rw [ip_mulA hΦ.1]; exact hip,
    fun Ψ hΨ => gs_unique_hardcore hws hΨ hG⟩

end existence

/-! ### A smooth one-body potential and a smooth pair interaction -/

/-- The pair interaction `½ Σ_{i ≠ j} u(x_i - x_j)`. -/
noncomputable def pairU (u : ℝ → ℝ) (x : Cfg n) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else 1 / 2 * u (x i - x j)

lemma contDiff_pairU {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (pairU (n := n) u) := by
  unfold pairU
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  split_ifs
  · exact contDiff_const
  · exact contDiff_const.mul (hu.comp ((contDiff_apply ℝ (fun _ => ℝ) i).sub
      (contDiff_apply ℝ (fun _ => ℝ) j)))

lemma pairU_pm (u : ℝ → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    pairU u (pm σ x) = pairU u x := by
  set H : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j => if i = j then 0 else 1 / 2 * u (x i - x j)
  calc pairU u (pm σ x) = ∑ i, ∑ j, H (σ i) (σ j) := by
        simp only [pairU, pm, H, σ.injective.eq_iff]
    _ = ∑ i, ∑ j, H (σ i) j := Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (H (σ i))
    _ = pairU u x := Equiv.sum_comp σ fun i => ∑ j, H i j

section pair

variable {u f : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) {v : Pot}
  (hv : ∀ t : Icc (0 : ℝ) 1, v t = f t)

include hv in
lemma LN_eq_of_smooth (x : Cfg n) (hx : x ∈ CubeC n) : LN n v x = ∑ k, f (x k) := by
  change ∑ k, Box.ext v (x k) = _
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Box.ext, projIcc_of_mem _ (hx k (mem_univ k)), hv]

include hu hf hv in
lemma smooth_pair :
    ∃ F : Cfg n → ℝ, ContDiff ℝ ∞ F ∧ ∀ x ∈ CubeC n, LN n v x + pairU u x = F x :=
  ⟨fun x => ∑ k, f (x k) + pairU u x,
    (ContDiff.sum fun k _ => hf.comp (contDiff_apply ℝ (fun _ => ℝ) k)).add (contDiff_pairU hu),
    fun x hx => by rw [LN_eq_of_smooth hv x hx]⟩

include hu hf hv

/-- **Hohenberg–Kohn for `N` bosons or fermions on `[0, 1]` with a smooth one-body potential and
a smooth pair interaction** `½ Σ_{i ≠ j} u(x_i - x_j)`: the ground state of `v` exists, and
ground states of `v` and of any continuous `v'` with the same density force `v - v'` to be
constant. -/
theorem hk_line_pair {τ : Stat} (v' : Pot) :
    (∃ Φ, IsGS (setting τ n (pairU u) (contDiff_pairU hu).continuous) v Φ) ∧
      ∀ Φ Φ', IsGS (setting τ n (pairU u) (contDiff_pairU hu).continuous) v Φ →
        IsGS (setting τ n (pairU u) (contDiff_pairU hu).continuous) v' Φ' →
        (∀ t ∈ Ioo (0 : ℝ) 1, ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 =
          ∫ y in Cube' n, Φ' (Fin.cons t y) ^ 2) → ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨F, hF, hVF⟩ := smooth_pair (n := n) hu hf hv
  exact hk_line_smooth (pairU_pm u) hF hVF v'

/-- **The Lieb functional for `N` bosons or fermions on `[0, 1]` with a smooth one-body potential
and a smooth pair interaction**: a normalised ground state `ψ` of `v` exists; at its density the
Lieb functional equals `⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient, and every other subgradient `-v'`
has `v - v'` constant. -/
theorem lieb_line_pair {τ : Stat} :
    ∃ ψ, IsNGS (setting τ n (pairU u) (contDiff_pairU hu).continuous) v ψ ∧
      liebF (setting τ n (pairU u) (contDiff_pairU hu).continuous)
          (dens (setting τ n (pairU u) (contDiff_pairU hu).continuous) ψ) =
        (((setting τ n (pairU u) (contDiff_pairU hu).continuous).h0 ψ ψ : ℝ) : EReal) ∧
      (∀ ρ : Pot → ℝ,
        (((setting τ n (pairU u) (contDiff_pairU hu).continuous).h0 ψ ψ +
          dens (setting τ n (pairU u) (contDiff_pairU hu).continuous) ψ v - ρ v : ℝ) : EReal) ≤
          liebF (setting τ n (pairU u) (contDiff_pairU hu).continuous) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ,
        (((setting τ n (pairU u) (contDiff_pairU hu).continuous).h0 ψ ψ +
          dens (setting τ n (pairU u) (contDiff_pairU hu).continuous) ψ v' - ρ v' : ℝ) :
            EReal) ≤ liebF (setting τ n (pairU u) (contDiff_pairU hu).continuous) ρ) →
        ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨F, hF, hVF⟩ := smooth_pair (n := n) hu hf hv
  exact lieb_line_smooth (pairU_pm u) hF hVF

/-- Existence and uniqueness of the ground state with a smooth pair interaction. -/
theorem exists_unique_gs_pair {τ : Stat} :
    ∃ Φ, IsGS (setting τ n (pairU u) (contDiff_pairU hu).continuous) v Φ ∧
      ip (μ := μN n) Φ Φ = 1 ∧
      ∀ Ψ, IsGS (setting τ n (pairU u) (contDiff_pairU hu).continuous) v Ψ →
        ∃ c : ℝ, ∀ x ∈ CubeC n, Ψ x = c * Φ x := by
  obtain ⟨F, hF, hVF⟩ := smooth_pair (n := n) hu hf hv
  exact exists_unique_gs_smooth (pairU_pm u) hF hVF

end pair

end DFT.Continuum.Sine
