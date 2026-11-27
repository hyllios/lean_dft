/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Algebra.Order.Chebyshev
import DFT.Continuum.Line.Neumann.NeuSuff

/-!
# Local `N`-representability with Neumann walls

Every density close to a positive `ρ₀ ∈ H¹(0, 1)` of mass `N` is the density of a normalised
Neumann state with uniformly bounded kinetic energy: the product `Π g(x_k)` for bosons, the
Slater determinant of the Harriman orbitals `g · e_j(∫₀ˣ g²)` for fermions, with `g = √(ρ/N)`.

* `isWDN_tens`: weak derivatives of products of `H¹(0, 1)` functions, Neumann walls;
  `kinN_tens_sq`: `∫ (Π f_j)² = Π ∫ f_j²`.
* `sqrtProf`: the profile `g = √(ρ/N)` of a density bounded below, `h1N_sqrtProf`,
  `kinM_sqrtProf_le`.
* `prodS_memN`, `kinN_prodS`, `rhoE_prodS`: bosons.
* **`locRepNH_of_pos`**: local `N`-representability around a positive density;
  `vrepNH_suff`, `vrepNH_iff` (Corso's Theorem 2.3).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ}

/-! ### Products of `H¹(0, 1)` functions -/

/-- **Weak derivatives of products** with Neumann walls. -/
theorem isWDN_tens {f : Fin (n + 1) → ℝ → ℝ} (hf : ∀ j, H1N (f j))
    (hfc : ∀ j, Continuous (f j)) (k : Fin (n + 1)) :
    IsWDN k (tens f) (tens (Function.update f k (deriv (f k)))) := by
  have hT : MemLp (tens f) 2 (μN n) :=
    memLp_tens (fun j => (hfc j).aestronglyMeasurable) (fun j => (hf j).int_sq)
  have hG : MemLp (tens (Function.update f k (deriv (f k)))) 2 (μN n) := by
    refine memLp_tens (fun j => ?_) (fun j => ?_)
    · rcases eq_or_ne j k with rfl | hj
      · simpa using (measurable_deriv (f j)).aestronglyMeasurable
      · simpa [Function.update_of_ne hj] using (hfc j).aestronglyMeasurable
    · rcases eq_or_ne j k with rfl | hj
      · simp only [Function.update_self]; exact (hf j).int_dsq
      · simpa [Function.update_of_ne hj] using (hf j).int_sq
  refine ⟨hG, fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ.1 k
  have hφd : Differentiable ℝ φ := hφ.1.differentiable one_ne_zero
  rw [integral_cube_ins (F := fun x => tens f x * dk k φ x) k (int_mul_cont hT hd),
    integral_cube_ins (F := fun x => tens (Function.update f k (deriv (f k))) x * φ x) k
      (int_mul_cont hG hφ.1.continuous), ← integral_neg]
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
    ContDiffOn.absolutelyContinuousOnInterval (hφ.1.comp (contDiff_ins k y)).contDiffOn
  have hu0 : u 0 = 0 := hφ.2 _ (Or.inl (by simp))
  have hu1 : u 1 = 0 := hφ.2 _ (Or.inr (by simp))
  have ibp := (hf k).1.integral_mul_deriv_eq_deriv_mul huAC
  rw [hu0, hu1, mul_zero, mul_zero, sub_zero, zero_sub] at ibp
  have e1 : ∫ t in (0 : ℝ)..1, f k t * P * dk k φ (Fin.insertNth k t y) =
      P * ∫ t in (0 : ℝ)..1, f k t * deriv u t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; rw [(hu t).deriv]; ring
  have e2 : ∫ t in (0 : ℝ)..1, deriv (f k) t * P * φ (Fin.insertNth k t y) =
      P * ∫ t in (0 : ℝ)..1, deriv (f k) t * u t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  rw [e1, e2, ibp]; ring

lemma integral_tens_sq (f : Fin (n + 1) → ℝ → ℝ) :
    ∫ x, tens f x ^ 2 ∂μN n = ∏ i, ∫ t, f i t ^ 2 ∂vol01 := by
  rw [← integral_prod_cube (fun i t => f i t ^ 2)]
  congr 1; funext x; simp only [tens, Finset.prod_pow]

/-! ### Bosons -/

section bos

variable {g : ℝ → ℝ}

lemma prodS_memN (hg : H1N g) (hgc : Continuous g) : prodS (n := n) g ∈ DomN .bos n := by
  refine ⟨memLp_cont (continuous_finsetProd _ fun k _ => hgc.comp (continuous_apply k)),
    fun k => ⟨_, isWDN_tens (fun _ => hg) (fun _ => hgc) k⟩, fun σ _ => ae_of_all _ fun x => ?_⟩
  simp only [prodS, pm]
  change ∏ i, g (x (σ i)) = 1 * ∏ i, g (x i)
  rw [one_mul]
  exact Equiv.prod_comp σ fun i => g (x i)

lemma integral_prodS_sq (hnorm : ∫ t, g t ^ 2 ∂vol01 = 1) :
    ∫ x, prodS (n := n) g x ^ 2 ∂μN n = 1 := by
  rw [prodS_eq_tens, integral_tens_sq]; simp [hnorm]

lemma kinN_prodS (hg : H1N g) (hgc : Continuous g) (hnorm : ∫ t, g t ^ 2 ∂vol01 = 1) :
    kinN (prodS (n := n) g) = (n + 1) * kinM g := by
  have hk : ∀ k : Fin (n + 1), ∫ x, dWN k (prodS (n := n) g) x * dWN k (prodS g) x ∂μN n =
      kinM g := fun k => by
    have hd := dWN_ae_eq (isWDN_tens (n := n) (fun _ => hg) (fun _ => hgc) k)
    rw [prodS_eq_tens, integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx, ← sq]),
      integral_tens_sq]
    rw [Finset.prod_eq_single k (fun i _ hi => by simp [Function.update_of_ne hi, hnorm])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp only [Function.update_self, kinM]
  simp only [kinN, hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

end bos

/-! ### The square-root profile of a density bounded below -/

/-- `√(ρ/N)` of the clamped `ρ`. -/
noncomputable def sqrtProf (n : ℕ) (ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  √(ρ (projIcc (0 : ℝ) 1 zero_le_one t) / (n + 1))

section prof

variable {ρ : ℝ → ℝ} (hρ : H1N ρ) {c : ℝ} (hc : 0 < c) (hρc : ∀ t ∈ Icc (0 : ℝ) 1, c ≤ ρ t)
include hρ hc hρc

omit hρ hc hρc in
lemma sqrtProf_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : sqrtProf n ρ t = √(ρ t / (n + 1)) := by
  simp [sqrtProf, projIcc_of_mem _ ht]

omit hc hρc in
lemma continuous_sqrtProf : Continuous (sqrtProf n ρ) :=
  continuous_sqrt.comp ((hρ.continuousOn.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc)
    fun t => (projIcc 0 1 zero_le_one t).2).div_const _)

omit hρ in
lemma sqrtProf_sq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (n + 1) * sqrtProf n ρ t ^ 2 = ρ t := by
  rw [sqrtProf_eq ht, Real.sq_sqrt (div_nonneg (hc.le.trans (hρc t ht)) (by positivity))]
  field_simp

omit hρ in
/-- The profile has derivative `ρ' / (2 N g)` where `ρ` is differentiable inside. -/
lemma hasDerivAt_sqrtProf {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hd : DifferentiableAt ℝ ρ t) :
    HasDerivAt (sqrtProf n ρ) (deriv ρ t / (n + 1) / (2 * √(ρ t / (n + 1)))) t := by
  have hpos : 0 < ρ t / (n + 1) := div_pos (hc.trans_le (hρc t (Ioo_subset_Icc_self ht)))
    (by positivity)
  have h1 : HasDerivAt (fun s => √(ρ s / (n + 1))) (deriv ρ t / (n + 1) / (2 * √(ρ t / (n + 1))))
      t := (hd.hasDerivAt.div_const _).sqrt hpos.ne'
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact sqrtProf_eq (Ioo_subset_Icc_self hs)

lemma deriv_sqrtProf_sq_le :
    ∀ᵐ t ∂vol01, deriv (sqrtProf n ρ) t ^ 2 ≤ deriv ρ t ^ 2 / (4 * (n + 1) * c) := by
  filter_upwards [ae_restrict_of_ae hρ.1.ae_differentiableAt, ae_restrict_mem measurableSet_Ioo]
    with t hdt ht
  have hd := hdt (by rw [uIcc01]; exact Ioo_subset_Icc_self ht)
  rw [(hasDerivAt_sqrtProf hc hρc ht hd).deriv]
  have hρt := hρc t (Ioo_subset_Icc_self ht)
  have hpos : 0 < ρ t / (n + 1) := div_pos (hc.trans_le hρt) (by positivity)
  have hN : (0 : ℝ) < n + 1 := by positivity
  have e : (deriv ρ t / (n + 1) / (2 * √(ρ t / (n + 1)))) ^ 2 =
      deriv ρ t ^ 2 / (4 * (n + 1) * ρ t) := by
    rw [div_pow, div_pow, mul_pow, Real.sq_sqrt hpos.le]
    field_simp
    ring
  rw [e]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_left hρt (by positivity))

lemma h1N_sqrtProf : H1N (sqrtProf n ρ) := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  set m := c / (n + 1)
  have hm : 0 < m := by positivity
  -- `√` is Lipschitz on `[m, ∞)`
  have hlip : LipschitzOnWith (Real.toNNReal (1 / (2 * √m))) Real.sqrt (Ici m) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have ha' : m ≤ a := ha
    have hb' : m ≤ b := hb
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq]
    have hsa := Real.sqrt_le_sqrt ha'
    have hsb := Real.sqrt_le_sqrt hb'
    have hsm : 0 < √m := Real.sqrt_pos.2 hm
    have hsum : 0 < √a + √b := by linarith
    have e : √a - √b = (a - b) / (√a + √b) := by
      rw [eq_div_iff hsum.ne']
      have := Real.sq_sqrt (hm.le.trans ha'); have := Real.sq_sqrt (hm.le.trans hb')
      nlinarith
    rw [e, abs_div, abs_of_pos hsum, div_le_iff₀ hsum]
    have : 2 * √m ≤ √a + √b := by linarith
    calc |a - b| = 1 / (2 * √m) * |a - b| * (2 * √m) := by field_simp
      _ ≤ 1 / (2 * √m) * |a - b| * (√a + √b) :=
          mul_le_mul_of_nonneg_left this (by positivity)
  have hAC : AbsolutelyContinuousOnInterval (fun t => ρ t / (n + 1)) 0 1 := by
    simpa [div_eq_mul_inv, mul_comm] using hρ.1.const_mul ((n : ℝ) + 1)⁻¹
  have hmaps : MapsTo (fun t => ρ t / (n + 1)) (uIcc 0 1) (Ici m) := fun t ht => by
    rw [uIcc01] at ht
    exact div_le_div_of_nonneg_right (hρc t ht) hN.le
  have hAC' := hlip.comp_absolutelyContinuousOnInterval hmaps hAC
  refine ⟨hAC'.congr ?_, ?_⟩
  · intro t ht; rw [uIcc01] at ht
    simp only [Function.comp, sqrtProf_eq ht]
  · have hm : AEStronglyMeasurable (fun t => deriv (sqrtProf n ρ) t ^ 2) vol01 :=
      ((measurable_deriv _).pow_const 2).aestronglyMeasurable
    refine Integrable.mono' (hρ.int_dsq.div_const (4 * (n + 1) * c)) hm ?_
    filter_upwards [deriv_sqrtProf_sq_le hρ hc hρc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact ht

lemma kinM_sqrtProf_le : kinM (sqrtProf n ρ) ≤ kinM ρ / (4 * (n + 1) * c) := by
  rw [kinM, kinM, ← integral_div]
  exact integral_mono_ae (h1N_sqrtProf hρ hc hρc).int_dsq (hρ.int_dsq.div_const _)
    (deriv_sqrtProf_sq_le hρ hc hρc)

end prof

/-! ### Fermions: Slater determinants of `H¹(0, 1)` orbitals -/

section slater

variable {φ : Fin (n + 1) → ℝ → ℝ}

lemma slater_tens_sum (φ : Fin (n + 1) → ℝ → ℝ) :
    slater φ = fun x => ∑ σ : Equiv.Perm (Fin (n + 1)), sgn σ * tens (fun i => φ (σ i)) x :=
  funext (slater_eq_sum φ)

lemma isWDN_slater (hφ : ∀ j, H1N (φ j)) (hφc : ∀ j, Continuous (φ j)) (k : Fin (n + 1)) :
    IsWDN k (slater φ) (fun x => ∑ σ : Equiv.Perm (Fin (n + 1)), sgn σ *
      tens (Function.update (fun i => φ (σ i)) k (deriv (φ (σ k)))) x) := by
  have h := IsWDN.sum (k := k) (Finset.univ : Finset (Equiv.Perm (Fin (n + 1))))
    (Φs := fun σ x => sgn σ * tens (fun i => φ (σ i)) x)
    (Gs := fun σ x => sgn σ *
      tens (Function.update (fun i => φ (σ i)) k (deriv (φ (σ k)))) x)
    (fun σ _ => memLp_cont (continuous_const.mul (continuous_tens fun i => hφc (σ i))))
    (fun σ _ => IsWDN.const_mul (sgn σ)
      (isWDN_tens (fun i => hφ (σ i)) (fun i => hφc (σ i)) k))
  rw [slater_tens_sum]
  exact h.2

/-- A Slater determinant of continuous `H¹(0, 1)` orbitals is a fermionic Neumann state. -/
lemma slater_memN (hφ : ∀ j, H1N (φ j)) (hφc : ∀ j, Continuous (φ j)) :
    slater φ ∈ DomN .fer n :=
  ⟨memLp_cont (continuous_slater hφc), fun k => ⟨_, isWDN_slater hφ hφc k⟩,
    fun σ _ => ae_of_all _ fun x => by rw [slater_eq_alt, alt_pm]⟩

/-- **The kinetic energy of a Slater determinant** of orthonormal orbitals is at most
`N · N!² · max_j ∫ φ_j'²`. -/
lemma kinN_slater_le (hφ : ∀ j, H1N (φ j)) (hφc : ∀ j, Continuous (φ j))
    (hon : ∀ a b, ∫ t, φ a t * φ b t ∂vol01 = if a = b then 1 else 0) {K : ℝ}
    (hK : ∀ j, kinM (φ j) ≤ K) :
    kinN (slater φ) ≤ (n + 1) * ((Nat.factorial (n + 1) : ℝ) ^ 2 * K) := by
  have h1 : ∀ j, ∫ t, φ j t ^ 2 ∂vol01 = 1 := fun j => by
    have := hon j j; simp only [↓reduceIte] at this; rw [← this]; simp only [sq]
  have hk : ∀ k : Fin (n + 1), ∫ x, dWN k (slater φ) x * dWN k (slater φ) x ∂μN n ≤
      (Nat.factorial (n + 1) : ℝ) ^ 2 * K := fun k => by
    set T : Equiv.Perm (Fin (n + 1)) → Cfg n → ℝ := fun σ =>
      tens (Function.update (fun i => φ (σ i)) k (deriv (φ (σ k))))
    have hW := isWDN_slater hφ hφc k
    have hd := dWN_ae_eq hW
    have hTm : ∀ σ, MemLp (T σ) 2 (μN n) := fun σ => by
      refine memLp_tens (fun j => ?_) (fun j => ?_)
      · rcases eq_or_ne j k with rfl | hj
        · simpa using (measurable_deriv (φ (σ j))).aestronglyMeasurable
        · simpa [Function.update_of_ne hj] using (hφc (σ j)).aestronglyMeasurable
      · rcases eq_or_ne j k with rfl | hj
        · simp only [Function.update_self]; exact (hφ (σ j)).int_dsq
        · simpa [Function.update_of_ne hj] using (hφ (σ j)).int_sq
    have hTi : ∀ σ, ∫ x, T σ x ^ 2 ∂μN n ≤ K := fun σ => by
      rw [integral_tens_sq, Finset.prod_eq_single k (fun i _ hi => by
        simp [Function.update_of_ne hi, h1]) (fun h => absurd (Finset.mem_univ k) h)]
      simp only [Function.update_self]
      exact hK (σ k)
    have hsumi : Integrable (fun x => ∑ σ : Equiv.Perm (Fin (n + 1)), T σ x ^ 2) (μN n) :=
      integrable_finsetSum _ fun σ _ => int_sq (hTm σ)
    calc ∫ x, dWN k (slater φ) x * dWN k (slater φ) x ∂μN n
        = ∫ x, (∑ σ : Equiv.Perm (Fin (n + 1)), sgn σ * T σ x) ^ 2 ∂μN n :=
          integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx, sq])
      _ ≤ ∫ x, (Nat.factorial (n + 1) : ℝ) * ∑ σ : Equiv.Perm (Fin (n + 1)), T σ x ^ 2 ∂μN n := by
          refine integral_mono_ae (int_sq hW.1) (hsumi.const_mul _) (ae_of_all _ fun x => ?_)
          have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))))
            (f := fun σ => sgn σ * T σ x)
          simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin, mul_pow] at this
          have hs : ∀ σ : Equiv.Perm (Fin (n + 1)), sgn σ ^ 2 = 1 := fun σ => by
            rw [sq, sgn_mul_self]
          simp only [hs, one_mul] at this
          exact_mod_cast this
      _ = (Nat.factorial (n + 1) : ℝ) * ∑ σ : Equiv.Perm (Fin (n + 1)), ∫ x, T σ x ^ 2 ∂μN n := by
          rw [integral_const_mul, integral_finsetSum _ fun σ _ => int_sq (hTm σ)]
      _ ≤ (Nat.factorial (n + 1) : ℝ) * ∑ _σ : Equiv.Perm (Fin (n + 1)), K := by
          gcongr with σ; exact hTi σ
      _ = (Nat.factorial (n + 1) : ℝ) ^ 2 * K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]; ring
  calc kinN (slater φ) ≤ ∑ _k : Fin (n + 1), (Nat.factorial (n + 1) : ℝ) ^ 2 * K :=
        Finset.sum_le_sum fun k _ => hk k
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring

end slater

/-! ### Harriman orbitals with bounds -/

lemma exists_eH_bound (N : ℕ) : ∃ C, 0 ≤ C ∧ ∀ a : Hix N, ∀ u ∈ Icc (0 : ℝ) 1,
    |eH a u| ≤ C ∧ |deriv (eH a) u| ≤ C := by
  have h : ∀ a : Hix N, ∃ C, ∀ u ∈ Icc (0 : ℝ) 1, ‖|eH a u| + |deriv (eH a) u|‖ ≤ C := fun a =>
    isCompact_Icc.exists_bound_of_continuousOn
      ((continuous_abs.comp (contDiff_eH a).continuous).add (continuous_abs.comp
        (((contDiff_eH a).of_le le_top : ContDiff ℝ 1 (eH a)).continuous_deriv le_rfl))).continuousOn
  choose C hC using h
  refine ⟨∑ a, |C a|, by positivity, fun a u hu => ?_⟩
  have h1 := hC a u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
  have h2 : |C a| ≤ ∑ a, |C a| :=
    Finset.single_le_sum (f := fun b => |C b|) (fun b _ => abs_nonneg (C b)) (Finset.mem_univ a)
  constructor <;> linarith [abs_nonneg (eH a u), abs_nonneg (deriv (eH a) u), le_abs_self (C a)]

section harr

variable {g : ℝ → ℝ} (hg : H1N g) (hgc : Continuous g) (hnorm : ∫ t, g t ^ 2 ∂vol01 = 1)
include hg hgc hnorm

/-- **Harriman orbitals** of a continuous `g ∈ H¹(0, 1)`, with a kinetic bound. -/
lemma harrimanN {Gm Kg : ℝ} (hGm : ∀ t ∈ Icc (0 : ℝ) 1, |g t| ≤ Gm) (hKg : kinM g ≤ Kg)
    {C : ℝ} (hC : 0 ≤ C) (hCb : ∀ a : Hix (n + 1), ∀ u ∈ Icc (0 : ℝ) 1,
      |eH a u| ≤ C ∧ |deriv (eH a) u| ≤ C) :
    ∃ φ : Fin (n + 1) → ℝ → ℝ, (∀ j, H1N (φ j)) ∧ (∀ j, Continuous (φ j)) ∧
      (∀ a b, ∫ t, φ a t * φ b t ∂vol01 = if a = b then 1 else 0) ∧
      (∀ t, ∑ j, φ j t ^ 2 = (n + 1) * g t ^ 2) ∧
      ∀ j, kinM (φ j) ≤ 2 * C ^ 2 * (Kg + Gm ^ 6) := by
  set N := n + 1
  let e : Fin N ≃ Hix N := (Fintype.equivFinOfCardEq (card_Hix N)).symm
  have hu : ∀ j, ContDiff ℝ 1 (fun x => eH (e j) (cumF g x)) := fun j =>
    ((contDiff_eH (e j)).of_le le_top).comp (contDiff_cumF' hgc)
  have huN : ∀ j, H1N (fun x => eH (e j) (cumF g x)) := fun j =>
    ⟨(hu j).contDiffOn.absolutelyContinuousOnInterval,
      integrable_cont_mu1 (((hu j).continuous_deriv le_rfl).pow 2)⟩
  have hF : ∀ t ∈ Icc (0 : ℝ) 1, cumF g t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    int_mem01 (hgc.pow 2) (fun s => sq_nonneg _) hnorm ht
  have hGm0 : 0 ≤ Gm := (abs_nonneg _).trans (hGm 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨fun j x => g x * eH (e j) (cumF g x), fun j => hg.mul (huN j),
    fun j => hgc.mul (hu j).continuous, fun a b => ?_, fun t => ?_, fun j => ?_⟩
  · have := integral_cumF' hgc hnorm (h := fun u => eH (e a) u * eH (e b) u)
      (((contDiff_eH _).continuous).mul (contDiff_eH _).continuous)
    simp only [integral_eH, e.injective.eq_iff] at this
    rw [← this]
    exact integral_congr_ae (ae_of_all _ fun t => by ring)
  · simp only [mul_pow, ← Finset.mul_sum]
    rw [e.sum_comp (fun a => eH a (cumF g t) ^ 2), sum_eH_sq]
    simp only [N]; push_cast; ring
  · -- the kinetic bound
    have hpt : ∀ᵐ t ∂vol01, deriv (fun x => g x * eH (e j) (cumF g x)) t ^ 2 ≤
        2 * C ^ 2 * (deriv g t ^ 2 + Gm ^ 6) := by
      filter_upwards [ae_restrict_of_ae hg.1.ae_differentiableAt,
        ae_restrict_mem measurableSet_Ioo] with t hdt ht
      have htI := Ioo_subset_Icc_self ht
      have hd := hdt (by rw [uIcc01]; exact htI)
      have hE : HasDerivAt (fun x => eH (e j) (cumF g x))
          (deriv (eH (e j)) (cumF g t) * g t ^ 2) t :=
        (((contDiff_eH (e j)).differentiable (by simp)).differentiableAt.hasDerivAt).comp t
          (hasDerivAt_cumF' hgc t)
      have hφd : HasDerivAt (fun x => g x * eH (e j) (cumF g x))
          (deriv g t * eH (e j) (cumF g t) + g t * (deriv (eH (e j)) (cumF g t) * g t ^ 2)) t :=
        hd.hasDerivAt.mul hE
      rw [hφd.deriv]
      obtain ⟨hb1, hb2⟩ := hCb (e j) _ (hF t htI)
      have hgt := hGm t htI
      set a := deriv g t * eH (e j) (cumF g t)
      set b := g t * (deriv (eH (e j)) (cumF g t) * g t ^ 2)
      have ha : a ^ 2 ≤ C ^ 2 * deriv g t ^ 2 := by
        have hE2 : eH (e j) (cumF g t) ^ 2 ≤ C ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb1 2
        simp only [a, mul_pow]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hE2 (sq_nonneg _)
      have hb : b ^ 2 ≤ C ^ 2 * Gm ^ 6 := by
        have : |b| ≤ C * Gm ^ 3 := by
          simp only [b, abs_mul, abs_pow]
          calc |g t| * (|deriv (eH (e j)) (cumF g t)| * |g t| ^ 2)
              ≤ Gm * (C * Gm ^ 2) := by gcongr
            _ = C * Gm ^ 3 := by ring
        calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
          _ ≤ (C * Gm ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
          _ = C ^ 2 * Gm ^ 6 := by ring
      nlinarith [sq_nonneg (a - b)]
    calc kinM (fun x => g x * eH (e j) (cumF g x))
        ≤ ∫ t, 2 * C ^ 2 * (deriv g t ^ 2 + Gm ^ 6) ∂vol01 :=
          integral_mono_ae (hg.mul (huN j)).int_dsq
            ((hg.int_dsq.add (integrable_const _)).const_mul _) hpt
      _ = 2 * C ^ 2 * (kinM g + Gm ^ 6) := by
          rw [integral_const_mul, integral_add hg.int_dsq (integrable_const _), integral_const,
            mu1_real_univ, one_smul, kinM]
      _ ≤ 2 * C ^ 2 * (Kg + Gm ^ 6) := by gcongr

end harr

/-! ### States with a given profile -/

/-- **A normalised Neumann state with density `N g²`** and kinetic energy bounded in terms of
`sup g` and `∫ g'²`, for bosons or fermions. -/
theorem rep_of_prof (τ : Stat) {g : ℝ → ℝ} (hg : H1N g) (hgc : Continuous g)
    (hnorm : ∫ t, g t ^ 2 ∂vol01 = 1) {Gm Kg : ℝ} (hGm : ∀ t ∈ Icc (0 : ℝ) 1, |g t| ≤ Gm)
    (hKg : kinM g ≤ Kg) {C : ℝ} (hC : 0 ≤ C) (hCb : ∀ a : Hix (n + 1), ∀ u ∈ Icc (0 : ℝ) 1,
      |eH a u| ≤ C ∧ |deriv (eH a) u| ≤ C) :
    ∃ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 ∧
      (∀ u : C01, pfN u Φ Φ = ∫ t, iccExt u t * ((n + 1) * g t ^ 2) ∂vol01) ∧
      kinN Φ ≤ (n + 1) * ((Nat.factorial (n + 1) : ℝ) * (2 * C ^ 2 * (Kg + Gm ^ 6)) + Kg) := by
  have hKg0 : 0 ≤ Kg := (integral_nonneg fun _ => sq_nonneg _).trans hKg
  have hGm0 : 0 ≤ Gm := (abs_nonneg _).trans (hGm 0 ⟨le_rfl, zero_le_one⟩)
  have hfac : (0 : ℝ) < (Nat.factorial (n + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hX : 0 ≤ (Nat.factorial (n + 1) : ℝ) * (2 * C ^ 2 * (Kg + Gm ^ 6)) := by positivity
  cases τ with
  | bos =>
    refine ⟨prodS g, prodS_memN hg hgc, integral_prodS_sq hnorm,
      fun u => dens_prodS hgc hnorm u, ?_⟩
    rw [kinN_prodS hg hgc hnorm]
    have : (n + 1 : ℝ) * kinM g ≤ (n + 1) * Kg := mul_le_mul_of_nonneg_left hKg (by positivity)
    nlinarith
  | fer =>
    obtain ⟨φ, hφH, hφc, hon, hsum, hφK⟩ := harrimanN (n := n) hg hgc hnorm hGm hKg hC hCb
    set c := (√(Nat.factorial (n + 1) : ℝ))⁻¹
    have hc2 : c * c * (Nat.factorial (n + 1) : ℝ) = 1 := by
      simp only [c]; rw [← mul_inv, Real.mul_self_sqrt hfac.le, inv_mul_cancel₀ hfac.ne']
    have hS := slater_memN hφH hφc
    have hD : c • slater φ ∈ DomN .fer n := (DomN .fer n).smul_mem c hS
    refine ⟨c • slater φ, hD, ?_, fun u => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (fun x => (c * slater φ x) ^ 2) = fun x => (c * c) * (slater φ x * slater φ x)
        from funext fun x => by ring, integral_const_mul, integral_slater_sq hφc hon, hc2]
    · change ∫ x, LN n u x * ((c • slater φ) x * (c • slater φ) x) ∂μN n = _
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (fun x => LN n u x * (c * slater φ x * (c * slater φ x))) =
        fun x => (c * c) * (LN n u x * (slater φ x * slater φ x)) from funext fun x => by ring,
        integral_const_mul, integral_LN_slater hφc hon, ← mul_assoc, hc2, one_mul]
      exact integral_congr_ae (ae_of_all _ fun t => by simp only [hsum t])
    · rw [kinN_smul (h1NW_of_mem hS)]
      have hk := kinN_slater_le hφH hφc hon hφK
      have hc2' : c ^ 2 = 1 / (Nat.factorial (n + 1) : ℝ) := by
        rw [sq, eq_div_iff hfac.ne', hc2]
      rw [hc2']
      calc 1 / (Nat.factorial (n + 1) : ℝ) * kinN (slater φ)
          ≤ 1 / (Nat.factorial (n + 1) : ℝ) * ((n + 1) * ((Nat.factorial (n + 1) : ℝ) ^ 2 *
              (2 * C ^ 2 * (Kg + Gm ^ 6)))) :=
            mul_le_mul_of_nonneg_left hk (by positivity)
        _ = (n + 1) * ((Nat.factorial (n + 1) : ℝ) * (2 * C ^ 2 * (Kg + Gm ^ 6))) := by
            field_simp
        _ ≤ _ := by
            have : (0 : ℝ) ≤ (n + 1) * Kg := by positivity
            nlinarith

/-! ### Sufficiency and the characterisation -/

lemma abs_fnE_le (e : H1E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |fnE e t| ≤ ‖evE‖ * ‖e‖ := by
  have h := (evE e).norm_coe_le_norm ⟨t, ht⟩
  rw [evE_apply, Real.norm_eq_abs] at h
  exact h.trans (evE.le_opNorm e)

lemma fnE_add (e e' : H1E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fnE (e + e') t = fnE e t + fnE e' t := by
  have := congrArg (fun P : C01 => P ⟨t, ht⟩) (map_add evE e e')
  simpa only [ContinuousMap.add_apply, evE_apply] using this

/-- **Local `N`-representability**: around every `ρ₀ ∈ H¹(0, 1)`, positive on `[0, 1]`, with
`∫ ρ₀ = N`, the densities of the same mass are densities of normalised Neumann states of bounded
energy (product states for bosons, Slater determinants of Harriman orbitals for fermions). -/
theorem locRepNH_of_pos {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) {ρ0 : H1E}
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < fnE ρ0 t) (hN : ∫ t, fnE ρ0 t ∂vol01 = n + 1) :
    LocRepNH τ n w ρ0 := by
  obtain ⟨tm, htm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
    (continuousOn_fnE ρ0)
  set c0 := fnE ρ0 tm
  have hc0 : 0 < c0 := hpos tm htm
  have hNp : (0 : ℝ) < n + 1 := by positivity
  set r := c0 / (2 * (‖evE‖ + 1))
  have hr : 0 < r := by positivity
  have hEr : ‖evE‖ * r ≤ c0 / 2 := by
    simp only [r]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg evE]
  obtain ⟨B, hB⟩ := ae_bound_cont (n := n) hw
  obtain ⟨C, hC, hCb⟩ := exists_eH_bound (n + 1)
  set U := ‖evE‖ * (‖ρ0‖ + r)
  set Gm := √(U / (n + 1))
  set Kg := (‖ρ0‖ + r) ^ 2 / (4 * (n + 1) * (c0 / 2))
  refine ⟨r, hr, (n + 1) * ((Nat.factorial (n + 1) : ℝ) * (2 * C ^ 2 * (Kg + Gm ^ 6)) + Kg) + B,
    fun h hh hhr => ?_⟩
  set ρ := fnE (ρ0 + h)
  have hρ : H1N ρ := h1N_fnE _
  have hρc : ∀ t ∈ Icc (0 : ℝ) 1, c0 / 2 ≤ ρ t := fun t ht => by
    have h1 := abs_fnE_le h ht
    have h2 : ‖evE‖ * ‖h‖ ≤ ‖evE‖ * r := mul_le_mul_of_nonneg_left hhr (ContinuousLinearMap.opNorm_nonneg _)
    have h3 := hmin ht
    simp only [ρ, fnE_add ρ0 h ht]
    rw [abs_le] at h1
    have : c0 ≤ fnE ρ0 t := h3
    linarith [h1.1]
  have hρU : ∀ t ∈ Icc (0 : ℝ) 1, ρ t ≤ U := fun t ht => by
    have h1 := abs_fnE_le (ρ0 + h) ht
    have h2 : ‖ρ0 + h‖ ≤ ‖ρ0‖ + r := (norm_add_le _ _).trans (by linarith)
    exact (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_left h2 (ContinuousLinearMap.opNorm_nonneg _)))
  have hc2 : 0 < c0 / 2 := by positivity
  set g := sqrtProf n ρ
  have hg := h1N_sqrtProf (n := n) hρ hc2 hρc
  have hgc := continuous_sqrtProf (n := n) hρ
  have hmass : ∫ t, ρ t ∂vol01 = n + 1 := by
    rw [← ellE_apply, map_add, hh, add_zero, ellE_apply, hN]
  have hnorm : ∫ t, g t ^ 2 ∂vol01 = 1 := by
    have e : ∫ t, g t ^ 2 ∂vol01 = ∫ t, ρ t / (n + 1) ∂vol01 :=
      setIntegral_congr_fun measurableSet_Ioo fun t ht => by
        have := sqrtProf_sq (n := n) hc2 hρc (Ioo_subset_Icc_self ht)
        simp only [g]; field_simp; linarith
    rw [e, integral_div, hmass, div_self hNp.ne']
  have hGm : ∀ t ∈ Icc (0 : ℝ) 1, |g t| ≤ Gm := fun t ht => by
    simp only [g]
    rw [sqrtProf_eq ht, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (hρU t ht) hNp.le)
  have hKg : kinM g ≤ Kg := by
    refine (kinM_sqrtProf_le hρ hc2 hρc).trans (div_le_div_of_nonneg_right ?_ (by positivity))
    rw [kinM_fnE]
    have h2 : ‖ρ0 + h‖ ≤ ‖ρ0‖ + r := (norm_add_le _ _).trans (by linarith)
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_snd_le _).trans h2) 2
  obtain ⟨Φ, hΦ, hn, hpf, hkin⟩ := rep_of_prof τ hg hgc hnorm hGm hKg hC hCb
  refine ⟨Φ, hΦ, hn, eq_of_int fun u => ?_, ?_⟩
  · rw [int_rhoE hΦ, hpf u]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have htI := Ioo_subset_Icc_self ht
    rw [ext_evE htI, sqrtProf_sq hc2 hρc htI]
  · have := abs_int_w_le hB hΦ.1 hn
    linarith [le_abs_self (∫ x, w x * (Φ x * Φ x) ∂μN n)]

/-- **Sufficiency in Corso's Theorem 2.3**: every `ρ ∈ H¹(0, 1)`, positive on `[0, 1]`, with
`∫ ρ = N`, is the density of a Neumann ground state of some `v ∈ H⁻¹`, for bosons or fermions
and any continuous interaction. -/
theorem vrepNH_suff {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) {ρ0 : H1E}
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < fnE ρ0 t) (hN : ∫ t, fnE ρ0 t ∂vol01 = n + 1) :
    VRepNH τ n w ρ0 :=
  vrepNH_of_rep hw hN (locRepNH_of_pos hw hpos hN)

/-- **Corso's Theorem 2.3** (pure-state `v`-representability with Neumann walls): for bosons or
fermions and any continuous interaction, `ρ ∈ H¹(0, 1)` is the density of a Neumann ground state
of some `H⁻¹` potential if and only if `ρ > 0` on `[0, 1]` and `∫ ρ = N`. -/
theorem vrepNH_iff {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) (ρ : H1E) :
    VRepNH τ n w ρ ↔ (∀ t ∈ Icc (0 : ℝ) 1, 0 < fnE ρ t) ∧ ∫ t, fnE ρ t ∂vol01 = n + 1 :=
  ⟨vrepNH_nec hw, fun h => vrepNH_suff hw h.1 h.2⟩

end DFT.Continuum.Line
