/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Strong
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Fin.Tuple.Sort

/-!
# A smooth sign of the ordering, and the collision strips

For `η > 0`, `Sgn η = alt χ_η` is the antisymmetrisation of the smooth indicator
`χ_η(x) = Πⱼ τ((x_{j+1} - x_j)/η)` of the ordered chamber (`τ` is Mathlib's smooth transition). It is
smooth and antisymmetric. Away from collisions (`|xᵢ - xⱼ| > η` for all `i ≠ j`) it equals the sign of
the permutation that sorts `x` and is locally constant; everywhere its partial derivatives are
`O(1/η)`.

* `Sgn_eq_of_strictMono`, `Sgn_eventually_const`: `Sgn η` away from collisions.
* `exists_dk_Sgn_bound`: `|∂ₖ Sgn η| ≤ C / η`.
* `abs_le_pair`: an antisymmetric `C¹` function satisfies `|Φ(x)| ≤ M |xᵢ - xⱼ|` on the closed cube.
* `mu_near_le`: the set of near-collisions `{∃ i ≠ j, |xᵢ - xⱼ| ≤ η}` has measure at most
  `(n + 1)² · 2η` in the cube.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box

variable {n : ℕ}

/-! ### The smooth transition -/

lemma deriv_smoothTransition_of_lt {t : ℝ} (ht : t < 0 ∨ 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  rcases ht with h | h
  · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 :=
      (gt_mem_nhds h).mono fun s hs => Real.smoothTransition.zero_of_nonpos hs.le
    rw [this.deriv_eq, deriv_const]
  · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 :=
      (lt_mem_nhds h).mono fun s hs => Real.smoothTransition.one_of_one_le hs.le
    rw [this.deriv_eq, deriv_const]

lemma contDiff_smoothTransition2 : ContDiff ℝ 2 Real.smoothTransition :=
  Real.smoothTransition.contDiff (n := 2)

lemma exists_deriv_smoothTransition_bound :
    ∃ C, 0 ≤ C ∧ ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    contDiff_smoothTransition2.continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hC t ht).trans (le_max_left _ _)
  · rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rw [deriv_smoothTransition_of_lt ht, abs_zero]; exact le_max_right _ _

/-! ### The smooth indicator of the ordered chamber -/

/-- The gap factor `τ((x_{j+1} - x_j)/η)`. -/
noncomputable def gapF (η : ℝ) (j : Fin n) (x : Cfg n) : ℝ :=
  Real.smoothTransition ((x j.succ - x j.castSucc) / η)

/-- The smooth indicator `χ_η` of the ordered chamber. -/
noncomputable def chi (η : ℝ) (x : Cfg n) : ℝ := ∏ j : Fin n, gapF η j x

/-- The smooth sign of the ordering, `Sgn η = alt χ_η`. -/
noncomputable def Sgn (η : ℝ) : Cfg n → ℝ := alt (chi η)

lemma contDiff_gapF (η : ℝ) (j : Fin n) : ContDiff ℝ 2 (gapF η j) :=
  contDiff_smoothTransition2.comp
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j.succ).contDiff.sub
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ)
        j.castSucc).contDiff).div_const η)

lemma contDiff_chi (η : ℝ) : ContDiff ℝ 2 (chi (n := n) η) :=
  contDiff_prod fun j _ => contDiff_gapF η j

lemma contDiff_Sgn (η : ℝ) : ContDiff ℝ 2 (Sgn (n := n) η) := contDiff_alt (contDiff_chi η)

lemma Sgn_pm (η : ℝ) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    Sgn η (pm σ x) = sgn σ * Sgn η x := alt_pm _ σ x

lemma chi_nonneg (η : ℝ) (x : Cfg n) : 0 ≤ chi η x :=
  Finset.prod_nonneg fun j _ => Real.smoothTransition.nonneg _

lemma chi_le_one (η : ℝ) (x : Cfg n) : chi η x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => Real.smoothTransition.nonneg _)
    fun _ _ => Real.smoothTransition.le_one _

lemma abs_sgn (σ : Equiv.Perm (Fin (n + 1))) : |sgn σ| = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [sgn, h]

lemma abs_Sgn_le (η : ℝ) (x : Cfg n) : |Sgn η x| ≤ Fintype.card (Equiv.Perm (Fin (n + 1))) := by
  simp only [Sgn, alt]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_univ.symm, ← nsmul_one, ← Finset.sum_const]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [abs_mul, abs_sgn, one_mul, abs_of_nonneg (chi_nonneg η _)]
  exact chi_le_one η _

/-- In the ordered chamber with gaps `> η`, `χ_η = 1`. -/
lemma chi_eq_one {η : ℝ} (hη : 0 < η) {x : Cfg n} (h : ∀ j : Fin n, η ≤ x j.succ - x j.castSucc) :
    chi η x = 1 :=
  Finset.prod_eq_one fun j _ => Real.smoothTransition.one_of_one_le (by
    rw [le_div_iff₀ hη]; linarith [h j])

/-- Outside the ordered chamber, `χ_η = 0`. -/
lemma chi_eq_zero {η : ℝ} (hη : 0 < η) {x : Cfg n} (h : ∃ j : Fin n, x j.succ ≤ x j.castSucc) :
    chi η x = 0 := by
  obtain ⟨j, hj⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ j) (Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le))

/-- Points without near-collisions. -/
def Far (η : ℝ) (x : Cfg n) : Prop := ∀ i j, i ≠ j → η < |x i - x j|

lemma Far.injective {η : ℝ} (hη : 0 ≤ η) {x : Cfg n} (h : Far η x) : Function.Injective x := by
  intro i j hij
  by_contra hne
  have := h i j hne
  rw [hij, sub_self, abs_zero] at this
  linarith

lemma Far.pm {η : ℝ} {x : Cfg n} (h : Far η x) (σ : Equiv.Perm (Fin (n + 1))) : Far η (pm σ x) :=
  fun i j hij => h (σ i) (σ j) (σ.injective.ne hij)

/-- Two strictly monotone rearrangements of an injective configuration coincide. -/
lemma perm_eq_of_strictMono {x : Cfg n} (hx : Function.Injective x)
    {σ ρ : Equiv.Perm (Fin (n + 1))} (hσ : StrictMono (pm σ x)) (hρ : StrictMono (pm ρ x)) :
    σ = ρ := by
  have hr : Set.range (pm σ x) = Set.range (pm ρ x) := by
    have e : ∀ τ : Equiv.Perm (Fin (n + 1)), Set.range (pm τ x) = Set.range x := fun τ =>
      (τ.surjective.range_comp x)
    rw [e, e]
  have hf := (StrictMono.range_inj_of_wellFoundedLT hσ hρ).1 hr
  ext i
  exact congrArg Fin.val (hx (congrFun hf i))

/-- Away from collisions, `Sgn η` is the sign of the sorting permutation. -/
lemma Sgn_eq_of_strictMono {η : ℝ} (hη : 0 < η) {x : Cfg n} (hx : Far η x)
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : StrictMono (pm σ x)) : Sgn η x = sgn σ := by
  simp only [Sgn, alt]
  rw [Finset.sum_eq_single σ]
  · rw [chi_eq_one hη, mul_one]
    intro j
    have hlt := Fin.strictMono_iff_lt_succ.1 hσ j
    have := hx.pm σ j.succ j.castSucc (Fin.castSucc_lt_succ (i := j)).ne'
    rw [abs_of_pos (by linarith)] at this
    exact this.le
  · intro ρ _ hρ
    rw [chi_eq_zero hη, mul_zero]
    by_contra hall
    push Not at hall
    have hmono : StrictMono (pm ρ x) := Fin.strictMono_iff_lt_succ.2 fun j => hall j
    exact hρ (perm_eq_of_strictMono (hx.injective hη.le) hmono hσ)
  · intro h; exact absurd (Finset.mem_univ σ) h

/-- A configuration without collisions has a sorting permutation. -/
lemma exists_strictMono {x : Cfg n} (hx : Function.Injective x) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), StrictMono (pm σ x) :=
  ⟨Tuple.sort x, (Tuple.monotone_sort x).strictMono_of_injective
    (hx.comp (Tuple.sort x).injective)⟩

lemma isOpen_far (η : ℝ) : IsOpen {x : Cfg n | Far η x} := by
  have : {x : Cfg n | Far η x} = ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {x | η < |x i - x j|} := by
    ext x; simp [Far]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ =>
      isOpen_lt continuous_const ((continuous_apply i).sub (continuous_apply j)).abs

/-- **Away from collisions `Sgn η` is locally constant**, equal to `±1`. -/
lemma Sgn_eventually_const {η : ℝ} (hη : 0 < η) {x : Cfg n} (hx : Far η x) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), Sgn η x = sgn σ ∧ Sgn η =ᶠ[𝓝 x] fun _ => sgn σ := by
  obtain ⟨σ, hσ⟩ := exists_strictMono (hx.injective hη.le)
  refine ⟨σ, Sgn_eq_of_strictMono hη hx hσ, ?_⟩
  have hO : IsOpen ({y : Cfg n | Far η y} ∩ {y | StrictMono (pm σ y)}) := by
    refine (isOpen_far η).inter ?_
    have : {y : Cfg n | StrictMono (pm σ y)} =
        ⋂ j : Fin n, {y | y (σ j.castSucc) < y (σ j.succ)} := by
      ext y; simp [Fin.strictMono_iff_lt_succ]
    rw [this]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt (continuous_apply _) (continuous_apply _)
  filter_upwards [hO.mem_nhds ⟨hx, hσ⟩] with y hy
  exact Sgn_eq_of_strictMono hη hy.1 hy.2

lemma dk_Sgn_far {η : ℝ} (hη : 0 < η) {x : Cfg n} (hx : Far η x) (k : Fin (n + 1)) :
    dk k (Sgn η) x = 0 := by
  obtain ⟨σ, -, hev⟩ := Sgn_eventually_const hη hx
  simp [dk, hev.fderiv_eq]

lemma Sgn_mul_Sgn_far {η η' : ℝ} (hη : 0 < η) (hη' : 0 < η') {x : Cfg n} (hx : Far η x)
    (hx' : Far η' x) : Sgn η x * Sgn η' x = 1 := by
  obtain ⟨σ, hσ⟩ := exists_strictMono (hx.injective hη.le)
  rw [Sgn_eq_of_strictMono hη hx hσ, Sgn_eq_of_strictMono hη' hx' hσ, sgn_mul_self]

/-! ### The derivative bound -/

/-- The gap as a continuous linear functional, `x ↦ (x_{j+1} - x_j)/η`. -/
noncomputable def gapL (η : ℝ) (j : Fin n) : Cfg n →L[ℝ] ℝ :=
  η⁻¹ • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j.succ -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j.castSucc)

lemma gapF_eq (η : ℝ) (j : Fin n) : gapF η j = Real.smoothTransition ∘ gapL η j := by
  funext x
  simp [gapF, gapL, div_eq_inv_mul]

lemma hasFDerivAt_gapF (η : ℝ) (j : Fin n) (x : Cfg n) :
    HasFDerivAt (gapF η j) (deriv Real.smoothTransition (gapL η j x) • gapL η j) x := by
  rw [gapF_eq]
  exact ((contDiff_smoothTransition2.differentiable (by norm_num)) _).hasDerivAt.comp_hasFDerivAt
    x (gapL η j).hasFDerivAt

lemma abs_gapL_single {η : ℝ} (hη : 0 < η) (j : Fin n) (k : Fin (n + 1)) :
    |gapL η j (Pi.single k 1)| ≤ η⁻¹ := by
  simp only [gapL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hη]
  have h01 : ∀ i : Fin (n + 1), (Pi.single k (1 : ℝ) : Cfg n) i ∈ Icc (0 : ℝ) 1 := by
    intro i; by_cases h : i = k
    · subst h; simp
    · simp [Pi.single_apply, h]
  have ha := h01 j.succ
  have hb := h01 j.castSucc
  have : |(Pi.single k (1 : ℝ) : Cfg n) j.succ - (Pi.single k (1 : ℝ) : Cfg n) j.castSucc| ≤ 1 :=
    abs_sub_le_iff.2 ⟨by linarith [ha.2, hb.1], by linarith [ha.1, hb.2]⟩
  calc η⁻¹ * |_| ≤ η⁻¹ * 1 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = η⁻¹ := mul_one _

lemma abs_dk_chi_le {η C : ℝ} (hη : 0 < η)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) (k : Fin (n + 1)) (x : Cfg n) :
    |dk k (chi η) x| ≤ n * (C * η⁻¹) := by
  have hd := HasFDerivAt.finsetProd (u := Finset.univ) (x := x)
    (fun j _ => hasFDerivAt_gapF η j x)
  have e : chi η = fun y => ∏ j ∈ (Finset.univ : Finset (Fin n)), gapF η j y := rfl
  simp only [dk, e, hd.fderiv, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      |(∏ i ∈ Finset.univ.erase j, gapF η i x) *
        (deriv Real.smoothTransition (gapL η j x) * gapL η j (Pi.single k 1))| ≤ C * η⁻¹ := by
    intro j _
    rw [abs_mul, abs_mul]
    have hnn : 0 ≤ ∏ i ∈ Finset.univ.erase j, gapF η i x :=
      Finset.prod_nonneg fun i _ => Real.smoothTransition.nonneg _
    have hle : ∏ i ∈ Finset.univ.erase j, gapF η i x ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => Real.smoothTransition.nonneg _)
        fun _ _ => Real.smoothTransition.le_one _
    have hp : |∏ i ∈ Finset.univ.erase j, gapF η i x| ≤ 1 :=
      abs_le.2 ⟨by linarith, hle⟩
    have h0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    calc _ ≤ 1 * (C * η⁻¹) := mul_le_mul hp (mul_le_mul (hC _) (abs_gapL_single hη j k)
          (abs_nonneg _) h0) (by positivity) zero_le_one
      _ = C * η⁻¹ := one_mul _
  refine (Finset.sum_le_sum hb).trans ?_
  simp

/-- **The derivative bound** `|∂ₖ Sgn η| ≤ C / η`. -/
lemma exists_dk_Sgn_bound :
    ∃ C, 0 ≤ C ∧ ∀ η > 0, ∀ (k : Fin (n + 1)) (x : Cfg n), |dk k (Sgn η) x| ≤ C / η := by
  obtain ⟨C, hC0, hC⟩ := exists_deriv_smoothTransition_bound
  set N := (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ)
  refine ⟨N * (n * C), by positivity, fun η hη k x => ?_⟩
  have hdiff : ∀ σ : Equiv.Perm (Fin (n + 1)),
      Differentiable ℝ fun y => sgn σ * chi η (pm σ y) := fun σ =>
    (differentiable_const _).mul
      (((contDiff_chi η).differentiable (by norm_num)).comp
        ((contDiff_pm σ (m := 1)).differentiable one_ne_zero))
  have e : Sgn (n := n) η = fun y => ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))),
      sgn σ * chi η (pm σ y) := rfl
  have hsum : dk k (Sgn η) x = ∑ σ, sgn σ * dk (σ⁻¹ k) (chi η) (pm σ x) := by
    simp only [dk, e]
    rw [fderiv_fun_sum (fun σ _ => (hdiff σ x))]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show (fun y => sgn σ * chi η (pm σ y)) = fun y => sgn σ * (chi η ∘ pm σ) y from rfl,
      fderiv_const_mul (((contDiff_chi η).differentiable (by norm_num)).comp
        ((contDiff_pm σ (m := 1)).differentiable one_ne_zero) x)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr 1
    exact dk_comp_pm ((contDiff_chi η).differentiable (by norm_num)) σ k x
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ σ, |sgn σ * dk (σ⁻¹ k) (chi η) (pm σ x)| ≤ ∑ _σ : Equiv.Perm (Fin (n + 1)),
        n * (C * η⁻¹) := Finset.sum_le_sum fun σ _ => by
          rw [abs_mul, abs_sgn, one_mul]; exact abs_dk_chi_le hη hC _ _
    _ = N * (n * C) / η := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp; simp only [N]; ring

/-! ### Antisymmetric functions near collisions -/

/-- An antisymmetric function vanishes at a collision. -/
lemma eq_zero_of_collision {Φ : Cfg n → ℝ} (hD : Φ ∈ DomF n) {x : Cfg n} {i j : Fin (n + 1)}
    (hij : i ≠ j) (h : x i = x j) : Φ x = 0 := by
  have hpm : pm (Equiv.swap i j) x = x := by
    funext l
    simp only [pm_apply]
    by_cases hl : l = i
    · subst hl; simp [h]
    by_cases hl' : l = j
    · subst hl'; simp [h]
    · rw [Equiv.swap_apply_of_ne_of_ne hl hl']
  have := hD.2.1 (Equiv.swap i j) x
  rw [hpm, sgn_swap hij] at this
  linarith

/-- **An antisymmetric function is small near collisions**: `|Φ(x)| ≤ M |xᵢ - xⱼ|` on the closed
cube, where `M` bounds `∂ᵢΦ` there. -/
lemma abs_le_pair {Φ : Cfg n → ℝ} (hD : Φ ∈ DomF n) {M : ℝ} {i j : Fin (n + 1)} (hij : i ≠ j)
    (hM : ∀ y ∈ CubeC n, |dk i Φ y| ≤ M) {x : Cfg n} (hx : x ∈ CubeC n) :
    |Φ x| ≤ M * |x i - x j| := by
  have hz : Φ (Function.update x i (x j)) = 0 :=
    eq_zero_of_collision hD hij (by simp [Function.update_of_ne hij.symm])
  have hin : ∀ s ∈ Icc (0 : ℝ) 1, Function.update x i s ∈ CubeC n := by
    intro s hs l _
    by_cases hl : l = i
    · subst hl; simpa using hs
    · simpa [Function.update_of_ne hl] using hx l (mem_univ _)
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => Φ (Function.update x i s)) (f' := fun s => dk i Φ (Function.update x i s))
    (C := M) (fun s _ => (hasDerivAt_slice (diffF hD) x i s).hasDerivWithinAt)
    (fun s hs => by rw [Real.norm_eq_abs]; exact hM _ (hin s hs))
    (hx j (mem_univ _)) (hx i (mem_univ _))
  simp only [Function.update_eq_self, hz, sub_zero, Real.norm_eq_abs] at h
  exact h

/-! ### The measure of the near-collision set -/

lemma volume_cube' : volume (Cube' n) = 1 := by
  rw [Real.volume_pi_Ioo]; simp

/-- A single collision strip has measure at most `2η` in the cube. -/
lemma mu_strip_le {η : ℝ} (hη : 0 ≤ η) {i j : Fin (n + 1)} (hij : i ≠ j) :
    μN n {x | |x i - x j| ≤ η} ≤ ENNReal.ofReal (2 * η) := by
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hij.symm
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e.symm (volume.prod volume) (volume : Measure (Cfg n)) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hm : MeasurableSet {x : Cfg n | |x i - x (i.succAbove j')| ≤ η} :=
    measurableSet_le (show Continuous fun x : Cfg n => |x i - x (i.succAbove j')| by
      fun_prop).measurable measurable_const
  rw [Measure.restrict_apply hm, ← he.measure_preimage (hm.inter measurableSet_cube).nullMeasurableSet]
  set T : Set (ℝ × (Fin n → ℝ)) := {p | |p.1 - p.2 j'| ≤ η ∧ p.2 ∈ Cube' n}
  have hsub : e.symm ⁻¹' ({x : Cfg n | |x i - x (i.succAbove j')| ≤ η} ∩ Cube n) ⊆ T := by
    rintro ⟨t, y⟩ ⟨h1, h2⟩
    have hc : e.symm (t, y) = Fin.insertNth i t y := rfl
    simp only [mem_preimage, mem_setOf_eq, hc, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove] at h1 h2
    refine ⟨h1, fun l _ => ?_⟩
    have := h2 (i.succAbove l) (mem_univ _)
    simpa [hc, Fin.insertNth_apply_succAbove] using this
  have hTm : MeasurableSet T :=
    (measurableSet_le (show Continuous fun p : ℝ × (Fin n → ℝ) => |p.1 - p.2 j'| by
      fun_prop).measurable measurable_const).inter (measurable_snd (MeasurableSet.univ_pi fun _ => measurableSet_Ioo))
  refine (measure_mono hsub).trans ?_
  rw [Measure.prod_apply_symm hTm]
  calc ∫⁻ y, volume ((fun t => (t, y)) ⁻¹' T)
      ≤ ∫⁻ y, (Cube' n).indicator (fun _ => ENNReal.ofReal (2 * η)) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ Cube' n
        · rw [indicator_of_mem hy]
          refine (measure_mono (t := Icc (y j' - η) (y j' + η)) fun t ht => ?_).trans ?_
          · have := (abs_le.mp ht.1); exact ⟨by linarith [this.1], by linarith [this.2]⟩
          · rw [Real.volume_Icc]; ring_nf; exact le_rfl
        · rw [indicator_of_notMem hy]
          have : (fun t => (t, y)) ⁻¹' T = ∅ := by
            ext t; simp only [mem_preimage, mem_empty_iff_false, iff_false]
            exact fun h => hy h.2
          rw [this, measure_empty]
    _ = ENNReal.ofReal (2 * η) := by
        rw [lintegral_indicator_const (MeasurableSet.univ_pi fun _ => measurableSet_Ioo),
          volume_cube', mul_one]

/-- The near-collision set. -/
def NearS (η : ℝ) : Set (Cfg n) := {x | ¬ Far η x}

lemma NearS_eq (η : ℝ) :
    NearS (n := n) η = ⋃ i, ⋃ j, {x : Cfg n | i ≠ j ∧ |x i - x j| ≤ η} := by
  ext x; simp [NearS, Far]

lemma measurableSet_pair (η : ℝ) (i j : Fin (n + 1)) :
    MeasurableSet {x : Cfg n | i ≠ j ∧ |x i - x j| ≤ η} := by
  by_cases h : i = j
  · simp [h]
  · simp only [ne_eq, h, not_false_eq_true, true_and]
    exact measurableSet_le (show Continuous fun x : Cfg n => |x i - x j| by fun_prop).measurable
      measurable_const

lemma measurableSet_NearS (η : ℝ) : MeasurableSet (NearS (n := n) η) := by
  rw [NearS_eq]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => measurableSet_pair η i j

/-- **The near-collision set is small**: measure at most `(n + 1)² · 2η` in the cube. -/
lemma mu_near_le {η : ℝ} (hη : 0 ≤ η) :
    (μN n).real (NearS η) ≤ (n + 1) ^ 2 * (2 * η) := by
  have h : μN n (NearS η) ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ENNReal.ofReal (2 * η) := by
    rw [NearS_eq]
    refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    by_cases hij : i = j
    · subst hij; simp
    · exact (measure_mono (s := {x : Cfg n | i ≠ j ∧ |x i - x j| ≤ η})
        (t := {x : Cfg n | |x i - x j| ≤ η}) fun x hx => hx.2).trans (mu_strip_le hη hij)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [Measure.real]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h.trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1; push_cast; ring

end DFT.Continuum.Line
