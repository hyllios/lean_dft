/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.NeuUcp
import DFT.Continuum.Line.YoungGS

/-!
# Fermionic Neumann states restricted to the chamber

The restriction lemmas of `Line/HalfSpace` and `Line/YoungChamber` with Neumann walls. The proofs
are unchanged: the cutoffs near the planes multiply Neumann test functions into Neumann test
functions, and the cosine truncations of a fermionic state vanish on the planes `xᵢ = xⱼ`.

* **`isWDN_half_of_bound`**, `IsWDN.congr_right`, **`isWDN_pairs_of_bound`**;
* `truncC_plane`, **`isWDN_RY`**: `1_R Ψ` has Neumann weak derivatives `1_R ∂ₖΨ`;
* `IsWDN.comp_pm`: weak derivatives after relabelling the particles.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ}

theorem isWDN_half_of_bound {F G : Cfg n → ℝ} {k : Fin (n + 1)} (hF : MemLp F 2 (μN n))
    (hG : IsWDN k F G) {i j : Fin (n + 1)} (hij : i ≠ j) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ᵐ x ∂μN n, |F x| ≤ L * |x j - x i|) :
    IsWDN k ((Hij i j).indicator F) ((Hij i j).indicator G) := by
  set H := Hij (n := n) i j
  refine ⟨hG.1.indicator (measurableSet_Hij i j).nullMeasurableSet, fun φ hφ => ?_⟩
  have hdφ := continuous_dk_of_C1 hφ.1 k
  set δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hδ : ∀ m, 0 < δ m := fun m => by positivity
  set θ : ℕ → Cfg n → ℝ := fun m => cutH i j (δ m)
  have hθc : ∀ m, ContDiff ℝ 1 (θ m) := fun m => contDiff_cutH i j _
  have hdθc : ∀ m, Continuous (dk k (θ m)) := fun m => continuous_dk_of_C1 (hθc m) k
  have hθ01 : ∀ m x, 0 ≤ θ m x ∧ θ m x ≤ 1 := fun m x =>
    ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  have hm : ∀ m, ∫ x, F x * (θ m x * dk k φ x) ∂μN n + ∫ x, F x * (dk k (θ m) x * φ x) ∂μN n =
      -∫ x, G x * (θ m x * φ x) ∂μN n := fun m => by
    have h := hG.2 (fun x => θ m x * φ x) ⟨(hθc m).mul hφ.1, fun x hx => by simp [hφ.2 x hx]⟩
    simp only [dk_mul ((hθc m).differentiable one_ne_zero) (hφ.1.differentiable one_ne_zero)] at h
    rw [← integral_add (f := fun x => F x * (θ m x * dk k φ x))
      (g := fun x => F x * (dk k (θ m) x * φ x))
      (int_mul_cont hF ((hθc m).continuous.mul hdφ))
      (int_mul_cont hF ((hdθc m).mul hφ.1.continuous))]
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) h
    ring
  have L1 : Tendsto (fun m => ∫ x, F x * (θ m x * dk k φ x) ∂μN n) atTop
      (𝓝 (∫ x, H.indicator F x * dk k φ x ∂μN n)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |F x * dk k φ x|)
      (fun m => hF.aestronglyMeasurable.mul ((hθc m).continuous.mul hdφ).aestronglyMeasurable)
      (int_mul_cont hF hdφ).abs (fun m => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, show F x * (θ m x * dk k φ x) = θ m x * (F x * dk k φ x) by ring,
        abs_mul, abs_of_nonneg (hθ01 m x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hθ01 m x).2
    · have h := ((tendsto_cutH i j x).mul_const (dk k φ x)).const_mul (F x)
      convert h using 2
      by_cases hx : x ∈ H <;> simp [H, hx]
  have L3 : Tendsto (fun m => ∫ x, G x * (θ m x * φ x) ∂μN n) atTop
      (𝓝 (∫ x, H.indicator G x * φ x ∂μN n)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |G x * φ x|)
      (fun m => hG.1.aestronglyMeasurable.mul
        ((hθc m).continuous.mul hφ.1.continuous).aestronglyMeasurable)
      (int_mul_cont hG.1 hφ.1.continuous).abs (fun m => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, show G x * (θ m x * φ x) = θ m x * (G x * φ x) by ring,
        abs_mul, abs_of_nonneg (hθ01 m x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hθ01 m x).2
    · have h := ((tendsto_cutH i j x).mul_const (φ x)).const_mul (G x)
      convert h using 2
      by_cases hx : x ∈ H <;> simp [H, hx]
  obtain ⟨Mθ, hMθ⟩ := deriv_smoothTransition_bound
  obtain ⟨Bφ, hBφ⟩ := ae_bound_cont hφ.1.continuous
  have L2 : Tendsto (fun m => ∫ x, F x * (dk k (θ m) x * φ x) ∂μN n) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ x, (0 : ℝ) ∂μN n := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun _ => L * Mθ * Bφ)
      (fun m => hF.aestronglyMeasurable.mul ((hdθc m).mul hφ.1.continuous).aestronglyMeasurable)
      (integrable_const _) (fun m => ?_) (ae_of_all _ fun x => ?_)
    · filter_upwards [hBφ, hL] with x hx hLx
      rw [Real.norm_eq_abs] at hx ⊢
      have hMθ0 : 0 ≤ Mθ := (abs_nonneg _).trans (hMθ 0)
      have hB0 : 0 ≤ Bφ := (abs_nonneg _).trans hx
      simp only [θ, dk_cutH]
      set d := x j - x i
      by_cases hd : 0 < d / δ m ∧ d / δ m < 1
      · have hdpos : 0 < d := by
          have := hd.1; rwa [div_pos_iff_of_pos_right (hδ m)] at this
        have hdlt : d < δ m := by
          have := hd.2; rwa [div_lt_one (hδ m)] at this
        rw [abs_of_pos hdpos] at hLx
        rw [abs_mul, abs_mul, abs_mul, abs_div, abs_of_pos (hδ m)]
        have h1 : |(Pi.single k (1 : ℝ) : Cfg n) j - (Pi.single k (1 : ℝ) : Cfg n) i| / δ m ≤
            1 / δ m := div_le_div_of_nonneg_right (abs_single_sub_le k i j hij) (hδ m).le
        calc |F x| * (|deriv smoothTransition (d / δ m)| *
              (|(Pi.single k (1 : ℝ) : Cfg n) j - (Pi.single k (1 : ℝ) : Cfg n) i| / δ m) * |φ x|)
            ≤ (L * δ m) * (Mθ * (1 / δ m) * Bφ) := by
              gcongr
              · exact hLx.trans (mul_le_mul_of_nonneg_left hdlt.le hL0)
              · exact hMθ _
          _ = L * Mθ * Bφ := by have := (hδ m).ne'; field_simp
      · have hz : deriv smoothTransition (d / δ m) = 0 := by
          rw [not_and_or, not_lt, not_lt] at hd
          rcases hd with h | h
          · exact deriv_smoothTransition_of_nonpos h
          · exact deriv_smoothTransition_of_one_le h
        rw [hz]; simp only [zero_mul, mul_zero, abs_zero]
        positivity
    · refine tendsto_const_nhds.congr' ?_
      simp only [θ, dk_cutH]
      by_cases hx : 0 < x j - x i
      · obtain ⟨m0, hm0⟩ := exists_nat_gt (1 / (x j - x i))
        filter_upwards [eventually_ge_atTop m0] with m hmm
        have h1 : (1 : ℝ) / (x j - x i) < m + 1 := by
          have := (Nat.cast_le (α := ℝ)).2 hmm; linarith
        rw [div_lt_iff₀ hx] at h1
        rw [deriv_smoothTransition_of_one_le (by
          simp only [δ]; rw [div_div_eq_mul_div, div_one]; linarith)]
        ring
      · refine Eventually.of_forall fun m => ?_
        beta_reduce
        rw [deriv_smoothTransition_of_nonpos (div_nonpos_of_nonpos_of_nonneg
          (show x j - x i ≤ 0 by linarith) (hδ m).le)]
        ring
  have hlim := L1.add L2
  rw [add_zero] at hlim
  have heq : (fun m => ∫ x, F x * (θ m x * dk k φ x) ∂μN n +
      ∫ x, F x * (dk k (θ m) x * φ x) ∂μN n) =
      fun m => -∫ x, G x * (θ m x * φ x) ∂μN n := funext hm
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim L3.neg


lemma IsWDN.congr_right {k : Fin (n + 1)} {F G G' : Cfg n → ℝ} (h : IsWDN k F G)
    (hG : G =ᵐ[μN n] G') : IsWDN k F G' := by
  refine ⟨h.1.ae_eq hG, fun φ hφ => ?_⟩
  rw [h.2 φ hφ]
  congr 1
  exact integral_congr_ae (by filter_upwards [hG] with x hx; rw [hx])

/-- **Restriction to a pair-inequality set**, for functions vanishing linearly on each plane. -/
theorem isWDN_pairs_of_bound {F G : Cfg n → ℝ} {k : Fin (n + 1)} (hF : MemLp F 2 (μN n))
    (hG : IsWDN k F G) (s : Finset (Fin (n + 1) × Fin (n + 1))) (hs : ∀ p ∈ s, p.1 ≠ p.2)
    (hL : ∀ p ∈ s, ∃ L, 0 ≤ L ∧ ∀ᵐ x ∂μN n, |F x| ≤ L * |x p.2 - x p.1|) :
    IsWDN k ((PairS s).indicator F) ((PairS s).indicator G) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : PairS (n := n) ∅ = univ := by ext x; simp [PairS]
    rw [e, indicator_univ, indicator_univ]; exact hG
  | insert p s hp ih =>
    have ih' := ih (fun q hq => hs q (Finset.mem_insert_of_mem hq))
      (fun q hq => hL q (Finset.mem_insert_of_mem hq))
    have hset : Hij p.1 p.2 ∩ PairS s = PairS (n := n) (insert p s) := by
      ext x; simp [PairS, Hij]
    have e : ∀ f : Cfg n → ℝ, (PairS (insert p s)).indicator f =
        (Hij p.1 p.2).indicator ((PairS s).indicator f) := fun f => by
      rw [indicator_indicator, hset]
    rw [e, e]
    obtain ⟨L, hL0, hLb⟩ := hL p (Finset.mem_insert_self p s)
    refine isWDN_half_of_bound (hF.indicator (measurableSet_PairS s).nullMeasurableSet) ih'
      (hs p (Finset.mem_insert_self p s)) hL0 ?_
    filter_upwards [hLb] with x hx
    by_cases h : x ∈ PairS s
    · rw [indicator_of_mem h]; exact hx
    · rw [indicator_of_notMem h, abs_zero]; positivity

/-! ### The chamber -/

/-- The cosine truncations of a fermionic state vanish on the planes `xᵢ = xⱼ`. -/
lemma truncC_plane {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomN .fer n) (M : ℕ) {i j : Fin (n + 1)}
    (hij : i ≠ j) {x : Cfg n} (hx : x i = x j) : truncC M Ψ x = 0 := by
  have hpm : pm (Equiv.swap i j) x = x := by
    funext l
    simp only [pm_apply]
    by_cases hli : l = i
    · subst hli; simp [hx]
    · by_cases hlj : l = j
      · subst hlj; simp [hx]
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
  have h := (truncC_mem hΨ M).2 (Equiv.swap i j) x
  rw [hpm, ch_fer, sgn, Equiv.Perm.sign_swap hij] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  linarith

/-- **Fermionic Neumann states restricted to the chamber.** -/
theorem isWDN_RY {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomN .fer n) (k : Fin (n + 1)) :
    IsWDN k ((RY (n + 1) n).indicator Ψ) ((RY (n + 1) n).indicator (dWN k Ψ)) := by
  set C := PairS (n := n) (pY (n + 1) n)
  have hCm : MeasurableSet C := measurableSet_PairS _
  suffices H : IsWDN k (C.indicator Ψ) (C.indicator (dWN k Ψ)) from
    (H.congr_ae (indicator_RY_ae Ψ)).congr_right (indicator_RY_ae _)
  refine ⟨(memLp_dWN (h1NW_of_mem hΨ) k).indicator hCm.nullMeasurableSet, fun φ hφ => ?_⟩
  have hdφ := continuous_dk_of_C1 hφ.1 k
  have hM : ∀ M, ∫ x, C.indicator (truncC M Ψ) x * dk k φ x ∂μN n =
      -∫ x, C.indicator (dk k (truncC M Ψ)) x * φ x ∂μN n := fun M => by
    have hP1 : ContDiff ℝ 1 (truncC M Ψ) := (contDiff_truncC M Ψ).of_le (by norm_num)
    refine (isWDN_pairs_of_bound (memLp_cont (continuous_truncC M Ψ))
      (isWDN_of_C1 hP1 k) (pY (n + 1) n) (fun p hp => ?_) (fun p hp => ?_)).2 φ hφ
    · exact (Finset.mem_filter.1 hp).2.1.ne
    · have hp' := (Finset.mem_filter.1 hp).2
      exact abs_le_of_plane' hP1 hp'.1.ne fun x hx => truncC_plane hΨ M hp'.1.ne hx
  have hg1 : MemLp (C.indicator (dk k φ)) 2 (μN n) :=
    (memLp_cont hdφ).indicator hCm.nullMeasurableSet
  have hg2 : MemLp (C.indicator φ) 2 (μN n) :=
    (memLp_cont hφ.1.continuous).indicator hCm.nullMeasurableSet
  have e1 : ∀ f : Cfg n → ℝ, ∫ x, C.indicator f x * dk k φ x ∂μN n =
      ∫ x, f x * C.indicator (dk k φ) x ∂μN n := fun f =>
    integral_congr_ae (ae_of_all _ fun x => by by_cases hx : x ∈ C <;> simp [hx])
  have e2 : ∀ f : Cfg n → ℝ, ∫ x, C.indicator f x * φ x ∂μN n =
      ∫ x, C.indicator φ x * f x ∂μN n := fun f =>
    integral_congr_ae (ae_of_all _ fun x => by by_cases hx : x ∈ C <;> simp [hx, mul_comm])
  have L1 := tendsto_integral_mul_of_L2 (fun M => memLp_cont (continuous_truncC M Ψ)) hΨ.1 hg1
    (tendsto_truncC hΨ.1)
  have L2 := tendsto_truncC_dk hΨ k hg2
  simp only [← e1] at L1
  simp only [← e2] at L2
  have heq : (fun M => ∫ x, C.indicator (truncC M Ψ) x * dk k φ x ∂μN n) =
      fun M => -∫ x, C.indicator (dk k (truncC M Ψ)) x * φ x ∂μN n := funext hM
  rw [heq] at L1
  exact tendsto_nhds_unique L1 L2.neg

/-- **Weak derivatives after relabelling the particles.** -/
lemma IsWDN.comp_pm {k : Fin (n + 1)} {f G : Cfg n → ℝ} (σ : Equiv.Perm (Fin (n + 1)))
    (h : IsWDN (σ⁻¹ k) f G) : IsWDN k (fun x => f (pm σ x)) (fun x => G (pm σ x)) := by
  refine ⟨h.1.comp_measurePreserving (mpN σ), fun φ hφ => ?_⟩
  set ψ : Cfg n → ℝ := fun y => φ (pm σ⁻¹ y)
  have hψ : TestN (σ⁻¹ k) ψ := ⟨hφ.1.comp (contDiff_pm σ⁻¹), fun y hy => hφ.2 _ (by
    simpa only [pm_apply] using hy)⟩
  have hφψ : (fun x => ψ (pm σ x)) = φ := funext fun x => by simp only [ψ, pm_inv_pm]
  have hd : ∀ x, dk k φ x = dk (σ⁻¹ k) ψ (pm σ x) := fun x => by
    have := dk_comp_pm (hψ.1.differentiable one_ne_zero) σ k x
    rwa [hφψ] at this
  calc ∫ x, f (pm σ x) * dk k φ x ∂μN n
      = ∫ x, (fun y => f y * dk (σ⁻¹ k) ψ y) (pm σ x) ∂μN n := by simp only [hd]
    _ = ∫ y, f y * dk (σ⁻¹ k) ψ y ∂μN n := integral_pm σ (fun y => f y * dk (σ⁻¹ k) ψ y)
    _ = -∫ y, G y * ψ y ∂μN n := h.2 ψ hψ
    _ = -∫ x, G (pm σ x) * φ x ∂μN n := by
        rw [← integral_pm σ (fun y => G y * ψ y)]
        simp only [ψ, pm_inv_pm]

end DFT.Continuum.Line
