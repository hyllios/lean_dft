/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Core.Chamber
import DFT.Continuum.Line.Symmetry.Young

/-!
# Mixed symmetry: the ordered region and collisions

For states antisymmetric within the first `a` particles and within the last `N - a`:

* `altY`, `altY_mem`, `eq_zero_of_integral_altY`: the Young antisymmetrisation and the
  fundamental lemma with test functions of mixed symmetry.
* `SameB`, `RY`: same-group pairs, and the region where each group is strictly ordered (open and
  convex).
* `eq_zero_of_collisionY`: a state vanishes where two particles of the same group meet.
* `exists_YG_mem_RY`: a configuration without same-group collisions is relabelled into `RY` by
  the Young subgroup.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Sine

variable {n : ℕ} {a : ℕ}

/-! ### The Young antisymmetrisation -/

/-- `Σ_{σ ∈ YG a} sgn σ · f ∘ σ`. -/
noncomputable def altY (a : ℕ) (f : Cfg n → ℝ) (x : Cfg n) : ℝ :=
  open Classical in ∑ σ, if YG a σ then sgn σ * f (pm σ x) else 0

lemma altY_pm (f : Cfg n → ℝ) {ρ : Equiv.Perm (Fin (n + 1))} (hρ : YG a ρ) (x : Cfg n) :
    altY a f (pm ρ x) = sgn ρ * altY a f x := by
  classical
  simp only [altY, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ρ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulLeft, ← pm_mul]
  have hiff : YG a (ρ * σ) ↔ YG a σ :=
    ⟨fun h => by simpa using YG_mul (YG_inv hρ) h, fun h => YG_mul hρ h⟩
  simp only [hiff]
  split_ifs
  · rw [sgn_mul]; linear_combination (-(sgn σ * f (pm (ρ * σ) x))) * sgn_mul_self ρ
  · ring

lemma contDiff_altY {f : Cfg n → ℝ} {m : WithTop ℕ∞} (hf : ContDiff ℝ m f) :
    ContDiff ℝ m (altY a f) := by
  classical
  exact ContDiff.sum fun σ _ => by
    split_ifs
    · exact contDiff_const.mul (hf.comp (contDiff_pm σ))
    · exact contDiff_const

lemma altY_mem {f : Cfg n → ℝ} (hf : ContDiff ℝ 2 f) (hout : ∀ x, x ∉ Cube n → f x = 0) :
    altY a f ∈ DomY a n := by
  classical
  refine ⟨contDiff_altY hf, fun σ hσ x => altY_pm f hσ x, fun x k hk => ?_⟩
  simp only [altY]
  exact Finset.sum_eq_zero fun σ _ => by
    split_ifs
    · rw [hout _ (pm_not_mem_cube hk σ), mul_zero]
    · rfl

/-- **Fundamental lemma with test functions of mixed symmetry.** -/
lemma eq_zero_of_integral_altY {g : Cfg n → ℝ} (hg : Continuous g)
    (hgs : ∀ σ, YG a σ → ∀ x, g (pm σ x) = sgn σ * g x)
    (h : ∀ φ ∈ DomY a n, ∫ x, g x * φ x ∂μN n = 0) : ∀ x ∈ Cube n, g x = 0 := by
  classical
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (U := Cube n) (μ := volume)
    (f := g) isOpen_cube (hg.locallyIntegrable.locallyIntegrableOn _)
    (fun φ hφ _ (hsub : tsupport φ ⊆ Cube n) => ?_)
  · have h' : g =ᵐ[μN n] 0 := (ae_restrict_iff' measurableSet_cube).2 hae
    exact Measure.eqOn_open_of_ae_eq h' isOpen_cube hg.continuousOn continuousOn_const
  have hout : ∀ x, x ∉ Cube n → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hsub h')
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have h1 := h (altY a φ) (altY_mem hφ2 hout)
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)),
      ∫ x, g x * (if YG a σ then sgn σ * φ (pm σ x) else 0) ∂μN n =
        if YG a σ then ∫ x, g x * φ x ∂μN n else 0 := by
    intro σ
    split_ifs with hσ
    · have := integral_pm σ (fun y => g (pm σ⁻¹ y) * (sgn σ * φ y))
      simp only [pm_inv_pm] at this
      rw [this]
      congr 1; funext y
      rw [hgs σ⁻¹ (YG_inv hσ), sgn_inv]
      linear_combination (g y * φ y) * sgn_mul_self σ
    · simp
  have hsum : ∫ x, g x * altY a φ x ∂μN n =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        ∫ x, g x * (if YG a σ then sgn σ * φ (pm σ x) else 0) ∂μN n := by
    simp only [altY, Finset.mul_sum]
    refine integral_finsetSum (f := fun σ x => g x * (if YG a σ then sgn σ * φ (pm σ x) else 0))
      _ fun σ _ => ?_
    split_ifs
    · exact integrableN (hg.mul (continuous_const.mul (hφ.continuous.comp (continuous_pm σ))))
    · simp
  rw [hsum] at h1
  simp only [hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul] at h1
  have hc : ((Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => YG a σ).card : ℝ) ≠ 0 := by
    have : (1 : Equiv.Perm (Fin (n + 1))) ∈ Finset.univ.filter fun σ => YG a σ := by
      simp [YG_one]
    exact_mod_cast (Finset.card_pos.2 ⟨_, this⟩).ne'
  have hμ : ∫ x, g x * φ x ∂μN n = 0 := (mul_eq_zero.mp h1).resolve_left hc
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Cube n)]
  · simpa [smul_eq_mul, mul_comm] using hμ
  · intro x hx; rw [hout x hx, zero_smul]

/-! ### The strong equation -/

lemma lapN_pmY {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomY a n) {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ)
    (x : Cfg n) : lapN Φ (pm σ x) = sgn σ * lapN Φ x := by
  rw [← lapN_comp_pm hΦ.1 σ x]
  have e : (fun y => Φ (pm σ y)) = sgn σ • Φ := by
    funext y; rw [hΦ.2.1 σ hσ y]; rfl
  rw [e]
  simp only [lapN, dkk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dk_smul (hΦ.1.differentiable (by norm_num)),
    dk_smul ((contDiff_dk hΦ.1 k).differentiable one_ne_zero)]
  rfl

/-! ### The ordered region and collisions -/

/-- `i` and `j` belong to the same group. -/
def SameB (a : ℕ) (i j : Fin (n + 1)) : Prop := ((i : ℕ) < a ↔ (j : ℕ) < a)

instance (a : ℕ) (i j : Fin (n + 1)) : Decidable (SameB a i j) := by
  unfold SameB; infer_instance

lemma YG_sameB {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) (i j : Fin (n + 1)) :
    SameB a (σ i) (σ j) ↔ SameB a i j := by
  simp only [SameB, hσ i, hσ j]

/-- The region where each group is strictly ordered. -/
def RY (a n : ℕ) : Set (Cfg n) :=
  {x | x ∈ Cube n ∧ ∀ i j, i < j → SameB a i j → x i < x j}

lemma isOpen_RY : IsOpen (RY a n) := by
  have : RY a n = Cube n ∩ ⋂ i, ⋂ j, ⋂ (_ : i < j ∧ SameB a i j), {x : Cfg n | x i < x j} := by
    ext x; simp only [RY, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    exact ⟨fun h => ⟨h.1, fun i j hij => h.2 i j hij.1 hij.2⟩,
      fun h => ⟨h.1, fun i j h1 h2 => h.2 i j ⟨h1, h2⟩⟩⟩
  rw [this]
  exact isOpen_cube.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i) (continuous_apply j))

lemma convex_RY : Convex ℝ (RY a n) := by
  intro x hx y hy s t hs ht hst
  refine ⟨?_, fun i j hij hsame => ?_⟩
  · intro k _
    have h1 := hx.1 k (mem_univ k)
    have h2 := hy.1 k (mem_univ k)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · rcases hs.lt_or_eq with hs' | hs'
      · nlinarith [h1.1, h2.1]
      · subst hs'; simp only [zero_add] at hst; subst hst; simpa using h2.1
    · rcases hs.lt_or_eq with hs' | hs'
      · nlinarith [h1.2, h2.2]
      · subst hs'; simp only [zero_add] at hst; subst hst; simpa using h2.2
  · have h1 := hx.2 i j hij hsame
    have h2 := hy.2 i j hij hsame
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hs.lt_or_eq with hs' | hs'
    · nlinarith [mul_lt_mul_of_pos_left h1 hs', mul_le_mul_of_nonneg_left h2.le ht]
    · subst hs'; simp only [zero_add] at hst; subst hst; simpa using h2

lemma YG_swap {i j : Fin (n + 1)} (h : SameB a i j) : YG a (Equiv.swap i j) := by
  intro l
  by_cases hl : l = i
  · subst hl; simp only [Equiv.swap_apply_left]; exact h.symm
  by_cases hl' : l = j
  · subst hl'; simp only [Equiv.swap_apply_right]; exact h
  · rw [Equiv.swap_apply_of_ne_of_ne hl hl']

/-- **A state vanishes where two particles of the same group meet.** -/
lemma eq_zero_of_collisionY {Φ : Cfg n → ℝ} (hD : Φ ∈ DomY a n) {x : Cfg n} {i j : Fin (n + 1)}
    (hij : i ≠ j) (hs : SameB a i j) (h : x i = x j) : Φ x = 0 := by
  have hpm : pm (Equiv.swap i j) x = x := by
    funext l
    simp only [pm_apply]
    by_cases hl : l = i
    · subst hl; simp [h]
    by_cases hl' : l = j
    · subst hl'; simp [h]
    · rw [Equiv.swap_apply_of_ne_of_ne hl hl']
  have := hD.2.1 (Equiv.swap i j) (YG_swap hs) x
  rw [hpm] at this
  change Φ x = sgn (Equiv.swap i j) * Φ x at this
  rw [sgn_swap hij] at this
  linarith

/-! ### Sorting within the groups -/

/-- **Sorting within groups**: a configuration in the cube without same-group collisions is
relabelled into `RY` by an element of the Young subgroup. -/
lemma exists_YG_mem_RY {x : Cfg n} (hx : x ∈ Cube n)
    (hinj : ∀ i j, i ≠ j → SameB a i j → x i ≠ x j) :
    ∃ σ, YG a σ ∧ pm σ x ∈ RY a n := by
  classical
  -- shift the second group by `2` and sort everything
  set x' : Cfg n := fun i => x i + if (i : ℕ) < a then 0 else 2
  have hlt : ∀ i : Fin (n + 1), (i : ℕ) < a → x' i < 1 := fun i hi => by
    simp only [x', ite_eq_left hi, add_zero]; exact (hx i (mem_univ i)).2
  have hge : ∀ i : Fin (n + 1), ¬ (i : ℕ) < a → 2 < x' i := fun i hi => by
    simp only [x', ite_eq_right hi]; linarith [(hx i (mem_univ i)).1]
  have hinj' : Function.Injective x' := by
    intro i j hij
    by_contra hne
    by_cases hs : SameB a i j
    · refine hinj i j hne hs ?_
      simp only [x'] at hij
      by_cases hi : (i : ℕ) < a
      · rw [ite_eq_left hi, ite_eq_left (hs.1 hi)] at hij; linarith
      · rw [ite_eq_right hi, ite_eq_right (fun h => hi (hs.2 h))] at hij; linarith
    · simp only [SameB] at hs
      by_cases hi : (i : ℕ) < a
      · have hj : ¬ (j : ℕ) < a := fun hj => hs ⟨fun _ => hj, fun _ => hi⟩
        have := hlt i hi; have := hge j hj; linarith
      · have hj : (j : ℕ) < a := by
          by_contra hj; exact hs ⟨fun h => absurd h hi, fun h => absurd h hj⟩
        have := hlt j hj; have := hge i hi; linarith
  obtain ⟨σ, hσ⟩ := exists_strictMono hinj'
  -- the positions of the first group form an initial segment
  have hdown : ∀ i j : Fin (n + 1), i < j → ((σ j : ℕ) < a) → ((σ i : ℕ) < a) := by
    intro i j hij hj
    by_contra hi
    have h1 := hσ hij
    simp only [pm_apply] at h1
    have := hlt (σ j) hj; have := hge (σ i) hi; linarith
  -- a down-set of `Fin (n + 1)` is an initial segment
  have hseg : ∀ T : Finset (Fin (n + 1)), (∀ i j, i < j → j ∈ T → i ∈ T) →
      ∀ j, j ∈ T ↔ (j : ℕ) < T.card := by
    intro T hT j
    constructor
    · intro hj
      have hsub : Finset.Iic j ⊆ T := fun i hi => by
        rcases (Finset.mem_Iic.1 hi).lt_or_eq with h | h
        · exact hT i j h hj
        · rw [h]; exact hj
      have := Finset.card_le_card hsub
      rw [Fin.card_Iic] at this; omega
    · intro hj
      by_contra hjT
      have hsub : T ⊆ Finset.Iio j := fun i hi => by
        rw [Finset.mem_Iio]
        by_contra h
        rcases (not_lt.1 h).lt_or_eq with h | h
        · exact hjT (hT j i h hi)
        · exact hjT (h ▸ hi)
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio] at this; omega
  set S := Finset.univ.filter fun i : Fin (n + 1) => ((σ i : ℕ) < a)
  set A := Finset.univ.filter fun i : Fin (n + 1) => ((i : ℕ) < a)
  have hcard : S.card = A.card :=
    Finset.card_bij (fun i _ => σ i) (fun i hi => by simpa [S, A] using hi)
      (fun i _ j _ h => σ.injective h) (fun j hj => ⟨σ⁻¹ j, by simpa [S, A] using hj, by simp⟩)
  have hS := hseg S fun i j hij hj => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hdown i j hij hj
  have hA := hseg A fun i j hij hj => by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact lt_trans (Fin.lt_def.1 hij) hj
  have hYG : YG a σ := by
    intro i
    have h1 := hS i
    have h2 := hA i
    simp only [S, A, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1, h2, hcard]
  refine ⟨σ, hYG, pm_mem_cube.2 hx, fun i j hij hsame => ?_⟩
  have h1 := hσ hij
  simp only [pm_apply, x'] at h1 ⊢
  have hs' := (YG_sameB hYG i j).2 hsame
  by_cases hi : ((σ i : ℕ) < a)
  · rw [ite_eq_left hi, ite_eq_left (hs'.1 hi)] at h1; linarith
  · rw [ite_eq_right hi, ite_eq_right (fun h => hi (hs'.2 h))] at h1; linarith

end DFT.Continuum.Line
