/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.HalfSpace
import DFT.Continuum.Line.Chamber

/-!
# Restriction to the ordered chamber

* `isWD_half_of_bound`: the half-space restriction `1_{xᵢ < xⱼ} F` of a weakly differentiable `F`
  with `|F| ≤ L |xⱼ - xᵢ|` has weak derivatives `1_{xᵢ < xⱼ} ∂ₖF` (as `isWD_half_C1`).
* `isWD_chamber_of_bound`: the same for the ordered chamber `C = {x₀ < x₁ < ⋯ < x_N}`, given the
  bound for every adjacent pair.
* **`isWD_chamber`**: for a fermionic `H¹₀` state `Ψ`, `1_C Ψ` has weak derivatives `1_C ∂ₖΨ`
  (through the truncations, which are small near collisions by `abs_le_pair`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ}

/-- **Half-space restriction for functions vanishing linearly on the plane.** -/
theorem isWD_half_of_bound {F G : Cfg n → ℝ} {k : Fin (n + 1)} (hF : MemLp F 2 (μN n))
    (hG : IsWD k F G) {i j : Fin (n + 1)} (hij : i ≠ j) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ᵐ x ∂μN n, |F x| ≤ L * |x j - x i|) :
    IsWD k ((Hij i j).indicator F) ((Hij i j).indicator G) := by
  set H := Hij (n := n) i j
  refine ⟨hG.1.indicator (measurableSet_Hij i j).nullMeasurableSet, fun φ hφ => ?_⟩
  have hdφ := continuous_dk_of_C1 hφ k
  set δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hδ : ∀ m, 0 < δ m := fun m => by positivity
  set θ : ℕ → Cfg n → ℝ := fun m => cutH i j (δ m)
  have hθc : ∀ m, ContDiff ℝ 1 (θ m) := fun m => contDiff_cutH i j _
  have hdθc : ∀ m, Continuous (dk k (θ m)) := fun m => continuous_dk_of_C1 (hθc m) k
  have hθ01 : ∀ m x, 0 ≤ θ m x ∧ θ m x ≤ 1 := fun m x =>
    ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  have hm : ∀ m, ∫ x, F x * (θ m x * dk k φ x) ∂μN n + ∫ x, F x * (dk k (θ m) x * φ x) ∂μN n =
      -∫ x, G x * (θ m x * φ x) ∂μN n := fun m => by
    have h := hG.2 (fun x => θ m x * φ x) ((hθc m).mul hφ)
    simp only [dk_mul ((hθc m).differentiable one_ne_zero) (hφ.differentiable one_ne_zero)] at h
    rw [← integral_add (f := fun x => F x * (θ m x * dk k φ x))
      (g := fun x => F x * (dk k (θ m) x * φ x))
      (int_mul_cont hF ((hθc m).continuous.mul hdφ))
      (int_mul_cont hF ((hdθc m).mul hφ.continuous))]
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
        ((hθc m).continuous.mul hφ.continuous).aestronglyMeasurable)
      (int_mul_cont hG.1 hφ.continuous).abs (fun m => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, show G x * (θ m x * φ x) = θ m x * (G x * φ x) by ring,
        abs_mul, abs_of_nonneg (hθ01 m x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hθ01 m x).2
    · have h := ((tendsto_cutH i j x).mul_const (φ x)).const_mul (G x)
      convert h using 2
      by_cases hx : x ∈ H <;> simp [H, hx]
  obtain ⟨Mθ, hMθ⟩ := deriv_smoothTransition_bound
  obtain ⟨Bφ, hBφ⟩ := ae_bound_cont hφ.continuous
  have L2 : Tendsto (fun m => ∫ x, F x * (dk k (θ m) x * φ x) ∂μN n) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ x, (0 : ℝ) ∂μN n := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun _ => L * Mθ * Bφ)
      (fun m => hF.aestronglyMeasurable.mul ((hdθc m).mul hφ.continuous).aestronglyMeasurable)
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

/-! ### The ordered chamber -/

/-- The points ordered on the coordinates in `s`: `x_j < x_{j+1}` for `j ∈ s`. -/
def OrdS (s : Finset (Fin n)) : Set (Cfg n) := {x | ∀ j ∈ s, x j.castSucc < x j.succ}

/-- The ordered chamber `x₀ < x₁ < ⋯ < x_N`. -/
def Ord (n : ℕ) : Set (Cfg n) := OrdS (n := n) Finset.univ

lemma measurableSet_OrdS (s : Finset (Fin n)) : MeasurableSet (OrdS (n := n) s) := by
  have : OrdS (n := n) s = ⋂ j ∈ s, Hij j.castSucc j.succ := by
    ext x; simp [OrdS, Hij]
  rw [this]
  exact Finset.measurableSet_biInter s fun j _ => measurableSet_Hij _ _

lemma mem_Ord_iff {x : Cfg n} : x ∈ Ord n ↔ StrictMono x := by
  simp [Ord, OrdS, Fin.strictMono_iff_lt_succ]

/-- **Chamber restriction for functions vanishing linearly at adjacent collisions.** -/
theorem isWD_chamber_of_bound {F G : Cfg n → ℝ} {k : Fin (n + 1)} (hF : MemLp F 2 (μN n))
    (hG : IsWD k F G) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ j : Fin n, ∀ᵐ x ∂μN n, |F x| ≤ L * |x j.succ - x j.castSucc|) :
    IsWD k ((Ord n).indicator F) ((Ord n).indicator G) := by
  classical
  suffices H : ∀ s : Finset (Fin n),
      IsWD k ((OrdS s).indicator F) ((OrdS s).indicator G) by exact H Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    have e : OrdS (n := n) ∅ = univ := by ext x; simp [OrdS]
    rw [e, indicator_univ, indicator_univ]; exact hG
  | insert j s hj ih =>
    have hset : Hij j.castSucc j.succ ∩ OrdS s = OrdS (n := n) (insert j s) := by
      ext x; simp [OrdS, Hij]
    have e : ∀ f : Cfg n → ℝ, (OrdS (insert j s)).indicator f =
        (Hij j.castSucc j.succ).indicator ((OrdS s).indicator f) := fun f => by
      rw [indicator_indicator, hset]
    rw [e, e]
    have hne : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ (i := j)).ne
    refine isWD_half_of_bound (hF.indicator (measurableSet_OrdS s).nullMeasurableSet) ih hne hL0 ?_
    filter_upwards [hL j] with x hx
    by_cases h : x ∈ OrdS s
    · rw [indicator_of_mem h]; exact hx
    · rw [indicator_of_notMem h, abs_zero]; positivity

/-- A `C¹` function has partial derivatives bounded on the closed cube. -/
lemma exists_dk_bound_cubeC {P : Cfg n → ℝ} (hP : ContDiff ℝ 1 P) :
    ∃ C, 0 ≤ C ∧ ∀ y ∈ CubeC n, ∀ i, |dk i P y| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_cubeC.exists_bound_of_continuousOn
    (hP.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y hy i => ?_⟩
  have := (fderiv ℝ P y).le_opNorm (Pi.single i 1)
  rw [Pi.norm_single, norm_one, mul_one] at this
  exact (Real.norm_eq_abs _ ▸ this).trans ((hC y hy).trans (le_max_left _ _))

/-- **Fermionic `H¹₀` states restricted to the ordered chamber.** -/
theorem isWD_chamber {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW .fer n) (k : Fin (n + 1)) :
    IsWD k ((Ord n).indicator Ψ) ((Ord n).indicator (dW k Ψ)) := by
  set C := Ord n
  have hCm : MeasurableSet C := measurableSet_OrdS _
  refine ⟨(memLp_dW hΨ k).indicator hCm.nullMeasurableSet, fun φ hφ => ?_⟩
  have hdφ := continuous_dk_of_C1 hφ k
  have hM : ∀ M, ∫ x, C.indicator (trunc M Ψ) x * dk k φ x ∂μN n =
      -∫ x, C.indicator (dk k (trunc M Ψ)) x * φ x ∂μN n := fun M => by
    have hP := trunc_mem hΨ M
    obtain ⟨L, hL0, hL⟩ :=
      exists_dk_bound_cubeC (hP.1.of_le (by norm_num) : ContDiff ℝ 1 (trunc M Ψ))
    have hb : ∀ j : Fin n, ∀ᵐ x ∂μN n,
        |trunc M Ψ x| ≤ L * |x j.succ - x j.castSucc| := fun j => by
      filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
      exact abs_le_pair hP (Fin.castSucc_lt_succ (i := j)).ne' (fun y hy => hL y hy _)
        (cube_subset hx)
    exact (isWD_chamber_of_bound (memLp_cont (continuous_trunc M Ψ)) (isWD_dk hP k) hL0 hb).2 φ hφ
  have hg1 : MemLp (C.indicator (dk k φ)) 2 (μN n) :=
    (memLp_cont hdφ).indicator hCm.nullMeasurableSet
  have hg2 : MemLp (C.indicator φ) 2 (μN n) :=
    (memLp_cont hφ.continuous).indicator hCm.nullMeasurableSet
  have e1 : ∀ f : Cfg n → ℝ, ∫ x, C.indicator f x * dk k φ x ∂μN n =
      ∫ x, f x * C.indicator (dk k φ) x ∂μN n := fun f =>
    integral_congr_ae (ae_of_all _ fun x => by by_cases hx : x ∈ C <;> simp [hx])
  have e2 : ∀ f : Cfg n → ℝ, ∫ x, C.indicator f x * φ x ∂μN n =
      ∫ x, C.indicator φ x * f x ∂μN n := fun f =>
    integral_congr_ae (ae_of_all _ fun x => by by_cases hx : x ∈ C <;> simp [hx, mul_comm])
  have L1 := tendsto_integral_mul_of_L2 (fun M => memLp_cont (continuous_trunc M Ψ)) hΨ.1 hg1
    (tendsto_trunc hΨ.1)
  have L2 := tendsto_trunc_dk (h1W_of_mem hΨ) k hg2
  simp only [← e1] at L1
  simp only [← e2] at L2
  have heq : (fun M => ∫ x, C.indicator (trunc M Ψ) x * dk k φ x ∂μN n) =
      fun M => -∫ x, C.indicator (dk k (trunc M Ψ)) x * φ x ∂μN n := funext hM
  rw [heq] at L1
  exact tendsto_nhds_unique L1 L2.neg

end DFT.Continuum.Line
