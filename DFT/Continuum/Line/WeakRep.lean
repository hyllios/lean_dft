/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Weak
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Every density with `√ρ ∈ H¹₀` is `N`-representable

The sufficiency half of Lieb's characterisation, on the state space `DomW` of finite kinetic
energy (`Line/Weak`). On `[0, 1]`, `H¹₀` is the class `H10` of functions that are absolutely
continuous on `[0, 1]` (Mathlib's `AbsolutelyContinuousOnInterval`), vanish at `0` and `1`, and
have square-integrable derivative.

If `g ∈ H10` and `∫ g² = 1`, the density `N g²` is the density of
* a normalised bosonic `H¹₀` state, the product `Π g(x_k)` (`nrepW_bos`), and
* a normalised fermionic `H¹₀` state, the Slater determinant of the Harriman orbitals
  `g · e_j(F)`, `F(x) = ∫₀ˣ g²` (`nrepW_fer`).

So the Lieb functional on `H¹₀` is finite at every such density (`liebF_W_ne_top`), and in terms
of the density itself (`nrepW_of_sqrt`): every `ρ ≥ 0` on `[0, 1]` with `√ρ ∈ H10` and
`∫ ρ = N` is `N`-representable. Together with `sqrt_dens_H1` (`Line/Density`) this is Lieb's
characterisation of `N`-representable densities on a line, except that necessity is proved for
`C²` states only.

The key step is `isWD_tens`: a product `Π_j f_j(x_j)` of `H10` functions has weak derivatives
`f_k'(x_k) Π_{j ≠ k} f_j(x_j)` with zero boundary values. Its proof is Fubini and Mathlib's
integration by parts for absolutely continuous functions.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ}

/-! ### `H¹₀` on the unit interval -/

/-- `g ∈ H¹₀(0, 1)`: absolutely continuous on `[0, 1]`, zero at both ends, `g' ∈ L²`. -/
def H10 (g : ℝ → ℝ) : Prop :=
  AbsolutelyContinuousOnInterval g 0 1 ∧ g 0 = 0 ∧ g 1 = 0 ∧
    IntegrableOn (fun t => deriv g t ^ 2) (Ioo (0 : ℝ) 1)

instance : IsProbabilityMeasure μ1 := ⟨by simp⟩

lemma uIcc01 : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one

namespace H10

variable {g : ℝ → ℝ}

lemma continuousOn (hg : H10 g) : ContinuousOn g (Icc 0 1) := by
  simpa [uIcc01] using hg.1.continuousOn

lemma aesm_of_contOn {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) : AEStronglyMeasurable f μ1 :=
  (hf.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo

lemma int_sq_of_contOn {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    Integrable (fun t => f t ^ 2) μ1 :=
  ((hf.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- The clamped function `g ∘ proj_{[0,1]}`: continuous on `ℝ`, equal to `g` on `[0, 1]`. -/
noncomputable def clamp (g : ℝ → ℝ) (t : ℝ) : ℝ := g (projIcc (0 : ℝ) 1 zero_le_one t)

lemma clamp_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp g t = g t := by
  rw [clamp, projIcc_of_mem _ ht]

lemma continuous_clamp (hg : H10 g) : Continuous (clamp g) :=
  hg.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    fun t => (projIcc _ _ _ t).2

lemma clamp_H10 (hg : H10 g) : H10 (clamp g) := by
  have hEq : EqOn g (clamp g) (Icc 0 1) := fun t ht => (clamp_eq ht).symm
  have hd : EqOn (fun t => deriv g t ^ 2) (fun t => deriv (clamp g) t ^ 2) (Ioo 0 1) :=
    fun t ht => by
      have : clamp g =ᶠ[𝓝 t] g := Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
        fun s hs => clamp_eq (Ioo_subset_Icc_self hs)
      simp only [this.deriv_eq]
  refine ⟨hg.1.congr (by rw [uIcc01]; exact hEq), ?_, ?_, hg.2.2.2.congr_fun hd measurableSet_Ioo⟩
  · rw [clamp_eq ⟨le_rfl, zero_le_one⟩, hg.2.1]
  · rw [clamp_eq ⟨zero_le_one, le_rfl⟩, hg.2.2.1]

/-- The product of an `H10` function and a `C¹` function is `H10`. -/
lemma mul_C1 (hg : H10 g) (hgc : Continuous g) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) :
    H10 (fun t => g t * u t) := by
  have huAC : AbsolutelyContinuousOnInterval u 0 1 :=
    ContDiffOn.absolutelyContinuousOnInterval hu.contDiffOn
  have hdu : Continuous (deriv u) := hu.continuous_deriv le_rfl
  obtain ⟨Cu, hCu⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hu.continuous.continuousOn
  obtain ⟨Cd, hCd⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hdu.continuousOn
  obtain ⟨Cg, hCg⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hgc.continuousOn
  refine ⟨hg.1.fun_mul huAC, by simp [hg.2.1], by simp [hg.2.2.1], ?_⟩
  have hbound : Integrable (fun t => 2 * Cu ^ 2 * deriv g t ^ 2 + 2 * (Cg * Cd) ^ 2) μ1 :=
    (hg.2.2.2.const_mul _).add (integrable_const _)
  refine hbound.mono' ((measurable_deriv _).pow_const 2).aestronglyMeasurable ?_
  have hdiff := hg.1.ae_differentiableAt
  rw [uIcc01] at hdiff
  filter_upwards [ae_restrict_of_ae hdiff, ae_restrict_mem measurableSet_Ioo] with t h1 ht
  have hti : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  have hD : deriv (fun t => g t * u t) t = deriv g t * u t + g t * deriv u t :=
    ((h1 hti).hasDerivAt.mul (hu.differentiable one_ne_zero t).hasDerivAt).deriv
  rw [hD, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have a1 : |u t| ≤ Cu := by simpa using hCu t hti
  have a2 : |deriv u t| ≤ Cd := by simpa using hCd t hti
  have a3 : |g t| ≤ Cg := by simpa using hCg t hti
  have b1 : (deriv g t * u t) ^ 2 ≤ Cu ^ 2 * deriv g t ^ 2 := by
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.1 a1).1 (abs_le.1 a1).2) (sq_nonneg _)
  have b2 : (g t * deriv u t) ^ 2 ≤ (Cg * Cd) ^ 2 := by
    rw [← sq_abs, abs_mul]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul a3 a2 (abs_nonneg _) ((abs_nonneg _).trans a3)) 2
  nlinarith [sq_nonneg (deriv g t * u t - g t * deriv u t)]

end H10

/-! ### Products of `H¹₀` functions -/

/-- The tensor product `Π_j f_j(x_j)`. -/
noncomputable def tens (f : Fin (n + 1) → ℝ → ℝ) (x : Cfg n) : ℝ := ∏ j, f j (x j)

/-- A tensor product of continuous orbitals is continuous. -/
lemma continuous_tens {f : Fin (n + 1) → ℝ → ℝ} (hf : ∀ j, Continuous (f j)) : Continuous (tens f) :=
  continuous_finsetProd _ fun j _ => (hf j).comp (continuous_apply j)

lemma memLp_tens {f : Fin (n + 1) → ℝ → ℝ} (hm : ∀ j, AEStronglyMeasurable (f j) μ1)
    (hs : ∀ j, Integrable (fun t => f j t ^ 2) μ1) : MemLp (tens f) 2 (μN n) := by
  rw [Sine.muN_eq]
  have hmeas : AEStronglyMeasurable (tens f) (Sine.piM (n + 1)) :=
    Finset.aestronglyMeasurable_fun_prod _ fun j _ =>
      (hm j).comp_measurePreserving (measurePreserving_eval (μ := fun _ => μ1) j)
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  refine (Integrable.fintype_prod (μ := fun _ : Fin (n + 1) => μ1)
    (f := fun j t => f j t ^ 2) hs).congr (ae_of_all _ fun x => ?_)
  simp [tens, Finset.prod_pow]

lemma contDiff_ins (k : Fin (n + 1)) (y : Fin n → ℝ) :
    ContDiff ℝ 1 fun s : ℝ => (Fin.insertNth k s y : Cfg n) :=
  contDiff_pi.2 fun i => by
    rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact contDiff_id
    · simp only [Fin.insertNth_apply_succAbove]; exact contDiff_const

lemma tens_ins (f : Fin (n + 1) → ℝ → ℝ) (k : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    tens f (Fin.insertNth k t y) = f k t * ∏ i, f (k.succAbove i) (y i) := by
  simp only [tens]
  rw [Fin.prod_univ_succAbove _ k]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- **Weak derivatives of products**: `∂_k Π_j f_j(x_j) = f_k'(x_k) Π_{j ≠ k} f_j(x_j)`, with
zero boundary values. -/
theorem isWD_tens {f : Fin (n + 1) → ℝ → ℝ} (hf : ∀ j, H10 (f j)) (k : Fin (n + 1)) :
    IsWD k (tens f) (tens (Function.update f k (deriv (f k)))) := by
  have hT : MemLp (tens f) 2 (μN n) :=
    memLp_tens (fun j => H10.aesm_of_contOn (hf j).continuousOn)
      (fun j => H10.int_sq_of_contOn (hf j).continuousOn)
  have hG : MemLp (tens (Function.update f k (deriv (f k)))) 2 (μN n) := by
    refine memLp_tens (fun j => ?_) (fun j => ?_)
    · rcases eq_or_ne j k with rfl | hj
      · simpa using (measurable_deriv (f j)).aestronglyMeasurable
      · simpa [Function.update_of_ne hj] using H10.aesm_of_contOn (hf j).continuousOn
    · rcases eq_or_ne j k with rfl | hj
      · simp only [Function.update_self]; exact (hf j).2.2.2
      · simpa [Function.update_of_ne hj] using H10.int_sq_of_contOn (hf j).continuousOn
  refine ⟨hG, fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ k
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  rw [integral_cube_ins (F := fun x => tens f x * dk k φ x) k (int_mul_cont hT hd),
    integral_cube_ins (F := fun x => tens (Function.update f k (deriv (f k))) x * φ x) k
      (int_mul_cont hG hφ.continuous), ← integral_neg]
  refine setIntegral_congr_fun measurableSet_cube' fun y _ => ?_
  set P := ∏ i, f (k.succAbove i) (y i)
  have hG' : ∀ t, tens (Function.update f k (deriv (f k))) (Fin.insertNth k t y) =
      deriv (f k) t * P := fun t => by
    rw [tens_ins]
    simp only [Function.update_self, P]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [Function.update_of_ne (Fin.succAbove_ne k i)]
  simp only [tens_ins, hG', integral_Ioo_eq_interval]
  set u : ℝ → ℝ := fun t => φ (Fin.insertNth k t y)
  have hu : ∀ t, HasDerivAt u (dk k φ (Fin.insertNth k t y)) t := hasDerivAt_ins hφd k y
  have huAC : AbsolutelyContinuousOnInterval u 0 1 :=
    ContDiffOn.absolutelyContinuousOnInterval (hφ.comp (contDiff_ins k y)).contDiffOn
  have ibp := (hf k).1.integral_mul_deriv_eq_deriv_mul huAC
  rw [(hf k).2.1, (hf k).2.2.1, zero_mul, zero_mul, sub_zero, zero_sub] at ibp
  have e1 : ∫ t in (0 : ℝ)..1, f k t * P * dk k φ (Fin.insertNth k t y) =
      P * ∫ t in (0 : ℝ)..1, f k t * deriv u t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; rw [(hu t).deriv]; ring
  have e2 : ∫ t in (0 : ℝ)..1, deriv (f k) t * P * φ (Fin.insertNth k t y) =
      P * ∫ t in (0 : ℝ)..1, deriv (f k) t * u t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  rw [e1, e2, ibp]; ring

/-! ### Bosons -/

section bos

variable {w : Cfg n → ℝ} {hw : Continuous w} {g : ℝ → ℝ}

lemma prodS_eq_tens (g : ℝ → ℝ) : prodS (n := n) g = tens fun _ => g := rfl

lemma prodS_memW (hg : H10 g) (hgc : Continuous g) : prodS (n := n) g ∈ DomW .bos n := by
  refine ⟨memLp_cont (continuous_finsetProd _ fun k _ => hgc.comp (continuous_apply k)),
    fun k => ⟨_, isWD_tens (fun _ => hg) k⟩, fun σ _ => ae_of_all _ fun x => ?_⟩
  simp only [prodS, pm, ch_bos, one_mul]
  exact Equiv.prod_comp σ fun i => g (x i)

lemma dens_prodS (hgc : Continuous g) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) (v : Pot) :
    ∫ x, LN n v x * (prodS g x * prodS g x) ∂μN n = ∫ t, ext v t * ((n + 1) * g t ^ 2) ∂μ1 := by
  have hsq : ∀ x : Cfg n, prodS g x * prodS g x = ∏ i, g (x i) ^ 2 := fun x => by
    simp only [prodS, ← Finset.prod_mul_distrib, sq]
  have hPc : Continuous fun x : Cfg n => prodS g x * prodS g x := by
    have : Continuous (prodS (n := n) g) :=
      continuous_finsetProd _ fun k _ => hgc.comp (continuous_apply k)
    exact this.mul this
  rw [integral_LN_mul v hPc]
  have hk : ∀ k : Fin (n + 1), ∫ x, ext v (x k) * (prodS g x * prodS g x) ∂μN n =
      ∫ t, ext v t * g t ^ 2 ∂μ1 := fun k => by
    have e : (fun x : Cfg n => ext v (x k) * (prodS g x * prodS g x)) = fun x =>
        ∏ i, (if i = k then fun t => ext v t * g t ^ 2 else fun t => g t ^ 2) (x i) := by
      funext x
      rw [hsq, ← prod_ite_mul k (fun i => ext v (x i)) (fun i => g (x i) ^ 2)]
      exact Finset.prod_congr rfl fun i _ => by split_ifs with h <;> simp [h]
    rw [e, integral_prod_cube]
    simp only [apply_ite (fun f : ℝ → ℝ => ∫ t, f t ∂μ1), hnorm]
    rw [Finset.prod_eq_single k (fun i _ hi => ite_eq_right hi)
      (fun h => absurd (Finset.mem_univ k) h), ite_eq_left rfl]
  simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← integral_const_mul]
  push_cast
  exact integral_congr_ae (ae_of_all _ fun t => by ring)

lemma ip_prodS (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) : ip (μ := μN n) (prodS g) (prodS g) = 1 := by
  have hsq : ∀ x : Cfg n, prodS g x * prodS g x = ∏ i, g (x i) ^ 2 := fun x => by
    simp only [prodS, ← Finset.prod_mul_distrib, sq]
  simp only [ip, hsq, integral_prod_cube (fun _ t => g t ^ 2), hnorm, Finset.prod_const_one]

end bos

/-! ### Fermions: Harriman orbitals of an `H¹₀` function -/

section fer

variable {g : ℝ → ℝ}

lemma hasDerivAt_cumF' (hgc : Continuous g) (x : ℝ) : HasDerivAt (cumF g) (g x ^ 2) x :=
  ((hgc.pow 2).integral_hasStrictDerivAt 0 x).hasDerivAt

lemma contDiff_cumF' (hgc : Continuous g) : ContDiff ℝ 1 (cumF g) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hasDerivAt_cumF' hgc x).differentiableAt, ?_⟩
  rw [show deriv (cumF g) = fun x => g x ^ 2 from funext fun x => (hasDerivAt_cumF' hgc x).deriv]
  exact hgc.pow 2

lemma integral_cumF' (hgc : Continuous g) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) {h : ℝ → ℝ}
    (hh : Continuous h) : ∫ t, g t ^ 2 * h (cumF g t) ∂μ1 = ∫ u in (0 : ℝ)..1, h u := by
  have h0 : cumF g 0 = 0 := intervalIntegral.integral_same
  have h1 : cumF g 1 = 1 := by rw [cumF, ← Box.integral_mu1, hnorm]
  rw [Box.integral_mu1]
  have := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := 1) (f := cumF g)
    (f' := fun x => g x ^ 2) (g := h) (fun x _ => hasDerivAt_cumF' hgc x)
    (hgc.pow 2).continuousOn hh
  rw [h0, h1] at this
  rw [← this]
  exact intervalIntegral.integral_congr fun x _ => by simp only [Function.comp]; ring

lemma continuous_slater {φ : Fin (n + 1) → ℝ → ℝ} (hφ : ∀ j, Continuous (φ j)) :
    Continuous (slater φ) := by
  rw [show slater φ = fun x => _ from funext (slater_eq_sum φ)]
  exact continuous_finsetSum _ fun σ _ => by fun_prop

/-- A Slater determinant of continuous `H10` orbitals is an `H¹₀` fermionic state. -/
lemma slater_memW {φ : Fin (n + 1) → ℝ → ℝ} (hφ : ∀ j, H10 (φ j))
    (hφc : ∀ j, Continuous (φ j)) : slater φ ∈ DomW .fer n := by
  refine ⟨memLp_cont (continuous_slater hφc), fun k => ?_, fun σ _ => ae_of_all _ fun x => ?_⟩
  · have e : slater φ = fun x => ∑ σ : Equiv.Perm (Fin (n + 1)),
        sgn σ * tens (fun i => φ (σ i)) x := funext (slater_eq_sum φ)
    have h := IsWD.sum (k := k) (Finset.univ : Finset (Equiv.Perm (Fin (n + 1))))
      (Φs := fun σ x => sgn σ * tens (fun i => φ (σ i)) x)
      (Gs := fun σ x => sgn σ *
        tens (Function.update (fun i => φ (σ i)) k (deriv (φ (σ k)))) x)
      (fun σ _ => memLp_cont (continuous_const.mul (continuous_tens fun i => hφc (σ i))))
      (fun σ _ => IsWD.const_mul (sgn σ) (isWD_tens (fun i => hφ (σ i)) k))
    rw [e]
    exact ⟨_, h.2⟩
  · rw [slater_eq_alt, alt_pm]

/-- The Harriman orbitals `g · e_j(F)` and their orthonormality. -/
lemma harriman (hg : H10 g) (hgc : Continuous g) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) :
    ∃ φ : Fin (n + 1) → ℝ → ℝ, (∀ j, H10 (φ j)) ∧ (∀ j, Continuous (φ j)) ∧
      (∀ a b, ∫ t, φ a t * φ b t ∂μ1 = if a = b then 1 else 0) ∧
      ∀ t, ∑ j, φ j t ^ 2 = (n + 1) * g t ^ 2 := by
  set N := n + 1
  let e : Fin N ≃ Hix N := (Fintype.equivFinOfCardEq (card_Hix N)).symm
  have hu : ∀ j, ContDiff ℝ 1 (fun x => eH (e j) (cumF g x)) := fun j =>
    ((contDiff_eH (e j)).of_le le_top).comp (contDiff_cumF' hgc)
  refine ⟨fun j x => g x * eH (e j) (cumF g x), fun j => hg.mul_C1 hgc (hu j),
    fun j => hgc.mul (hu j).continuous, fun a b => ?_, fun t => ?_⟩
  · have := integral_cumF' hgc hnorm (h := fun u => eH (e a) u * eH (e b) u)
      (((contDiff_eH _).continuous).mul (contDiff_eH _).continuous)
    simp only [integral_eH, e.injective.eq_iff] at this
    rw [← this]
    exact integral_congr_ae (ae_of_all _ fun t => by ring)
  · simp only [mul_pow, ← Finset.mul_sum]
    rw [e.sum_comp (fun a => eH a (cumF g t) ^ 2), sum_eH_sq]
    simp only [N]; push_cast; ring

end fer

/-! ### `N`-representability on `H¹₀` -/

section rep

variable {w : Cfg n → ℝ} {hw : Continuous w} {g : ℝ → ℝ}

/-- The integral over `(0, 1)` only sees `g` on `[0, 1]`. -/
lemma integral_mu1_clamp {F : ℝ → ℝ → ℝ} :
    ∫ t, F t (H10.clamp g t) ∂μ1 = ∫ t, F t (g t) ∂μ1 :=
  setIntegral_congr_fun measurableSet_Ioo fun t ht => by
    simp only [H10.clamp_eq (Ioo_subset_Icc_self ht)]

lemma nrepW_cont {τ : Stat} (hg : H10 g) (hgc : Continuous g) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) :
    ∃ ψ ∈ Nst (settingW τ n w hw),
      ∀ v, dens (settingW τ n w hw) ψ v = ∫ t, ext v t * ((n + 1) * g t ^ 2) ∂μ1 := by
  cases τ
  · refine ⟨prodS g, ⟨prodS_memW hg hgc, ip_prodS hnorm⟩, fun v => ?_⟩
    exact dens_prodS hgc hnorm v
  · obtain ⟨φ, hφH, hφc, hon, hsum⟩ := harriman (n := n) hg hgc hnorm
    have hfac : (0 : ℝ) < (Nat.factorial (n + 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + 1)
    set c := (√(Nat.factorial (n + 1) : ℝ))⁻¹
    have hc2 : c * c * (Nat.factorial (n + 1) : ℝ) = 1 := by
      simp only [c]; rw [← mul_inv, Real.mul_self_sqrt hfac.le, inv_mul_cancel₀ hfac.ne']
    have hD : c • slater φ ∈ DomW .fer n := (DomW .fer n).smul_mem c (slater_memW hφH hφc)
    refine ⟨c • slater φ, ⟨hD, ?_⟩, fun v => ?_⟩
    · change ∫ x, (c • slater φ) x * (c • slater φ) x ∂μN n = 1
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (fun x => c * slater φ x * (c * slater φ x)) =
        fun x => (c * c) * (slater φ x * slater φ x) from funext fun x => by ring,
        integral_const_mul, integral_slater_sq hφc hon, hc2]
    · change ∫ x, LN n v x * ((c • slater φ) x * (c • slater φ) x) ∂μN n = _
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (fun x => LN n v x * (c * slater φ x * (c * slater φ x))) =
        fun x => (c * c) * (LN n v x * (slater φ x * slater φ x)) from funext fun x => by ring,
        integral_const_mul, integral_LN_slater hφc hon, ← mul_assoc, hc2, one_mul]
      exact integral_congr_ae (ae_of_all _ fun t => by simp only [hsum t])

/-- **`N`-representability on `H¹₀`**: for `g ∈ H¹₀(0, 1)` with `∫ g² = 1`, the density `N g²`
is the density of a normalised `H¹₀` state, bosonic or fermionic. -/
theorem nrepW {τ : Stat} (hg : H10 g) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) :
    ∃ ψ ∈ Nst (settingW τ n w hw),
      ∀ v, dens (settingW τ n w hw) ψ v = ∫ t, ext v t * ((n + 1) * g t ^ 2) ∂μ1 := by
  have hn' : ∫ t, H10.clamp g t ^ 2 ∂μ1 = 1 := by
    rw [integral_mu1_clamp (F := fun _ s => s ^ 2)]; exact hnorm
  obtain ⟨ψ, hψ, hd⟩ := nrepW_cont (τ := τ) (w := w) (hw := hw) hg.clamp_H10
    (H10.continuous_clamp hg) hn'
  refine ⟨ψ, hψ, fun v => ?_⟩
  rw [hd v, integral_mu1_clamp (F := fun t s => ext v t * ((n + 1) * s ^ 2))]

/-- **The Lieb functional on `H¹₀` is finite** at every density `N g²` with `g ∈ H¹₀(0, 1)`. -/
theorem liebF_W_ne_top {τ : Stat} (hg : H10 g) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) :
    liebF (settingW τ n w hw) (rhoG n g) ≠ ⊤ := by
  obtain ⟨ψ, hψ, hd⟩ := nrepW (τ := τ) (w := w) (hw := hw) hg hnorm
  have h := liebF_le_h0 hψ
  rw [show dens (settingW τ n w hw) ψ = rhoG n g from funext hd] at h
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) h

/-- **`√ρ ∈ H¹₀` suffices for `N`-representability**: every `ρ ≥ 0` on `[0, 1]` with
`∫₀¹ ρ = N` and `√ρ` absolutely continuous on `[0, 1]`, zero at the ends, with
`(√ρ)' ∈ L²`, is the density of a normalised `H¹₀` state of `N` bosons or fermions. -/
theorem nrepW_of_sqrt {τ : Stat} {ρ : ℝ → ℝ} (hρ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ρ t)
    (hH : H10 fun t => √(ρ t)) (hN : ∫ t, ρ t ∂μ1 = n + 1) :
    ∃ ψ ∈ Nst (settingW τ n w hw),
      ∀ v, dens (settingW τ n w hw) ψ v = ∫ t, ext v t * ρ t ∂μ1 := by
  have hNp : (0 : ℝ) < n + 1 := by positivity
  set c := (√((n : ℝ) + 1))⁻¹
  have hc2 : c ^ 2 * ((n : ℝ) + 1) = 1 := by
    simp only [c, inv_pow, Real.sq_sqrt hNp.le, inv_mul_cancel₀ hNp.ne']
  set g : ℝ → ℝ := fun t => c * √(ρ t)
  have hg : H10 g := by
    refine ⟨hH.1.const_mul c, by simp [g, hH.2.1], by simp [g, hH.2.2.1], ?_⟩
    have e : (fun t => deriv g t ^ 2) = fun t => c ^ 2 * deriv (fun t => √(ρ t)) t ^ 2 := by
      funext t; simp only [g, deriv_const_mul_field', mul_pow]
    rw [e]; exact hH.2.2.2.const_mul _
  have hsq : ∀ t ∈ Ioo (0 : ℝ) 1, ((n : ℝ) + 1) * g t ^ 2 = ρ t := fun t ht => by
    simp only [g, mul_pow, Real.sq_sqrt (hρ0 t (Ioo_subset_Icc_self ht))]
    linear_combination ρ t * hc2
  have hnorm : ∫ t, g t ^ 2 ∂μ1 = 1 := by
    have : ∫ t, g t ^ 2 ∂μ1 = c ^ 2 * ∫ t, ρ t ∂μ1 := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
      simp only [g, mul_pow, Real.sq_sqrt (hρ0 t (Ioo_subset_Icc_self ht))]
    rw [this, hN, hc2]
  obtain ⟨ψ, hψ, hd⟩ := nrepW (τ := τ) (w := w) (hw := hw) hg hnorm
  refine ⟨ψ, hψ, fun v => ?_⟩
  rw [hd v]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by simp only [hsq t ht]

end rep

end DFT.Continuum.Line
