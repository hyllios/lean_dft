/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.WeakS
import DFT.Continuum.Line.YoungStrong
import DFT.Continuum.Line.HalfSpace
import DFT.Continuum.Line.Chamber
import DFT.Continuum.Line.LogEst
import DFT.Continuum.Line.HardCore
import DFT.Continuum.Line.SpinWeak
import DFT.Continuum.Line.AbsW

/-!
# `H¹₀` states of mixed symmetry restricted to the Young chamber

For the Young symmetry `ymix a` (antisymmetric within particles `0, …, a-1` and within
`a, …, N-1`), the chamber is `RY a n`, the points of the cube where each group is strictly
ordered.

* `PairS s`, **`isWD_pairs_of_bound`**: restriction to `{x | xᵢ < xⱼ for (i, j) ∈ s}` commutes
  with weak derivatives for functions vanishing linearly on each plane `xᵢ = xⱼ`;
* `trunc_pmY`, `trunc_planeY`: the sine truncations of a state of `DomWS (ymix a)` have the same
  symmetry and vanish on the planes of same-group pairs;
* **`isWD_RY`**: `1_{RY} Ψ` has weak derivatives `1_{RY} ∂ₖΨ`;
* `shiftY` (shift the second group by `2`), **`YG_eq_of_mem_RY`**: at an injective point of the
  cube, the relabelling of `YG a` that sorts each group is unique.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ} {a : ℕ}

/-! ### Restriction to a set cut out by pair inequalities -/

/-- `{x | xᵢ < xⱼ for every (i, j) ∈ s}`. -/
def PairS (s : Finset (Fin (n + 1) × Fin (n + 1))) : Set (Cfg n) := {x | ∀ p ∈ s, x p.1 < x p.2}

lemma measurableSet_PairS (s : Finset (Fin (n + 1) × Fin (n + 1))) :
    MeasurableSet (PairS (n := n) s) := by
  have : PairS (n := n) s = ⋂ p ∈ s, Hij p.1 p.2 := by ext x; simp [PairS, Hij]
  rw [this]
  exact Finset.measurableSet_biInter s fun p _ => measurableSet_Hij _ _

lemma IsWD.congr_right {k : Fin (n + 1)} {F G G' : Cfg n → ℝ} (h : IsWD k F G)
    (hG : G =ᵐ[μN n] G') : IsWD k F G' := by
  refine ⟨h.1.ae_eq hG, fun φ hφ => ?_⟩
  rw [h.2 φ hφ]
  congr 1
  exact integral_congr_ae (by filter_upwards [hG] with x hx; rw [hx])

/-- **Restriction to a pair-inequality set**, for functions vanishing linearly on each plane. -/
theorem isWD_pairs_of_bound {F G : Cfg n → ℝ} {k : Fin (n + 1)} (hF : MemLp F 2 (μN n))
    (hG : IsWD k F G) (s : Finset (Fin (n + 1) × Fin (n + 1))) (hs : ∀ p ∈ s, p.1 ≠ p.2)
    (hL : ∀ p ∈ s, ∃ L, 0 ≤ L ∧ ∀ᵐ x ∂μN n, |F x| ≤ L * |x p.2 - x p.1|) :
    IsWD k ((PairS s).indicator F) ((PairS s).indicator G) := by
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
    refine isWD_half_of_bound (hF.indicator (measurableSet_PairS s).nullMeasurableSet) ih'
      (hs p (Finset.mem_insert_self p s)) hL0 ?_
    filter_upwards [hLb] with x hx
    by_cases h : x ∈ PairS s
    · rw [indicator_of_mem h]; exact hx
    · rw [indicator_of_notMem h, abs_zero]; positivity

/-! ### The Young chamber -/

/-- The same-group pairs `i < j`. -/
noncomputable def pY (a n : ℕ) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ SameB a p.1 p.2

lemma RY_eq : RY a n = Cube n ∩ PairS (pY a n) := by
  ext x
  simp only [RY, PairS, pY, mem_inter_iff, mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.forall]
  exact ⟨fun h => ⟨h.1, fun i j hij => h.2 i j hij.1 hij.2⟩,
    fun h => ⟨h.1, fun i j h1 h2 => h.2 i j ⟨h1, h2⟩⟩⟩

lemma measurableSet_RY : MeasurableSet (RY a n) := isOpen_RY.measurableSet

lemma indicator_RY_ae (f : Cfg n → ℝ) :
    (PairS (pY a n)).indicator f =ᵐ[μN n] (RY a n).indicator f := by
  filter_upwards [ae_cube] with x hx
  have hiff : x ∈ PairS (pY a n) ↔ x ∈ RY a n := by rw [RY_eq]; exact ⟨fun h => ⟨hx, h⟩, And.right⟩
  by_cases h : x ∈ RY a n
  · rw [indicator_of_mem h, indicator_of_mem (hiff.2 h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (mt hiff.1 h)]

/-! ### Truncations of states of mixed symmetry -/

section trunc

variable {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomWS (ymix a))
include hΨ

/-- The truncations keep the Young symmetry. -/
lemma trunc_pmY (M : ℕ) {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) (x : Cfg n) :
    trunc M Ψ (pm σ x) = sgn σ * trunc M Ψ x := by
  simp only [trunc, smd_pm', Finset.mul_sum]
  refine Finset.sum_nbij' (pmI σ⁻¹) (pmI σ) (fun m hm => (pmI_mem_boxI σ⁻¹).2 hm)
    (fun m hm => (pmI_mem_boxI σ).2 hm) (fun m _ => ?_) (fun m _ => ?_) (fun m _ => ?_)
  · rw [pmI_pmI, inv_mul_cancel, pmI_one]
  · rw [pmI_pmI, mul_inv_cancel, pmI_one]
  · have h := cN_pmWS hΨ (s := ymix a) hσ (pmI σ⁻¹ m)
    rw [pmI_pmI, inv_mul_cancel, pmI_one] at h
    change cN m Ψ = sgn σ * cN (pmI σ⁻¹ m) Ψ at h
    rw [h]; ring

/-- The truncations vanish on the planes of same-group pairs. -/
lemma trunc_planeY (M : ℕ) {i j : Fin (n + 1)} (hij : i ≠ j) (hs : SameB a i j) {x : Cfg n}
    (hx : x i = x j) : trunc M Ψ x = 0 := by
  have hpm : pm (Equiv.swap i j) x = x := by
    funext l
    simp only [pm_apply]
    by_cases hli : l = i
    · subst hli; simp [hx]
    · by_cases hlj : l = j
      · subst hlj; simp [hx]
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
  have h := trunc_pmY hΨ M (YG_swap hs) x
  rw [hpm, sgn, Equiv.Perm.sign_swap hij] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  linarith

/-- **States of mixed symmetry restricted to the Young chamber.** -/
theorem isWD_RY (k : Fin (n + 1)) :
    IsWD k ((RY a n).indicator Ψ) ((RY a n).indicator (dW k Ψ)) := by
  set C := PairS (n := n) (pY a n)
  have hCm : MeasurableSet C := measurableSet_PairS _
  suffices H : IsWD k (C.indicator Ψ) (C.indicator (dW k Ψ)) from
    (H.congr (indicator_RY_ae Ψ)).congr_right (indicator_RY_ae _)
  refine ⟨(memLp_dW_H (h1W_of_memS hΨ) k).indicator hCm.nullMeasurableSet, fun φ hφ => ?_⟩
  have hdφ := continuous_dk_of_C1 hφ k
  have hM : ∀ M, ∫ x, C.indicator (trunc M Ψ) x * dk k φ x ∂μN n =
      -∫ x, C.indicator (dk k (trunc M Ψ)) x * φ x ∂μN n := fun M => by
    have hP1 : ContDiff ℝ 1 (trunc M Ψ) := (contDiff_trunc M Ψ).of_le (by norm_num)
    refine (isWD_pairs_of_bound (memLp_cont (continuous_trunc M Ψ))
      (isWD_of_C1 hP1 (trunc_wall M Ψ) k) (pY a n) (fun p hp => ?_) (fun p hp => ?_)).2 φ hφ
    · exact (Finset.mem_filter.1 hp).2.1.ne
    · have hp' := (Finset.mem_filter.1 hp).2
      exact abs_le_of_plane' hP1 hp'.1.ne fun x hx => trunc_planeY hΨ M hp'.1.ne hp'.2 hx
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
  have L2 := tendsto_trunc_dk (h1W_of_memS hΨ) k hg2
  simp only [← e1] at L1
  simp only [← e2] at L2
  have heq : (fun M => ∫ x, C.indicator (trunc M Ψ) x * dk k φ x ∂μN n) =
      fun M => -∫ x, C.indicator (dk k (trunc M Ψ)) x * φ x ∂μN n := funext hM
  rw [heq] at L1
  exact tendsto_nhds_unique L1 L2.neg

end trunc

/-! ### Uniqueness of the sorting relabelling -/

/-- Shift the second group by `2`. -/
noncomputable def shiftY (a : ℕ) (x : Cfg n) : Cfg n := fun i => x i + if (i : ℕ) < a then 0 else 2

lemma shiftY_pm {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) (x : Cfg n) :
    shiftY a (pm σ x) = pm σ (shiftY a x) := by
  funext i
  simp only [shiftY, pm_apply]
  by_cases h : (i : ℕ) < a
  · simp only [h, (hσ i).2 h, ↓reduceIte]
  · simp only [h, mt (hσ i).1 h, ↓reduceIte]

lemma strictMono_shiftY {y : Cfg n} (hy : y ∈ RY a n) : StrictMono (shiftY a y) := by
  intro i j hij
  have hi := Set.mem_univ_pi.1 hy.1 i
  have hj := Set.mem_univ_pi.1 hy.1 j
  simp only [shiftY]
  by_cases hs : SameB a i j
  · have h := hy.2 i j hij hs
    by_cases hia : (i : ℕ) < a
    · simp only [hia, hs.1 hia, ↓reduceIte]; linarith
    · simp only [hia, mt hs.2 hia, ↓reduceIte]; linarith
  · have hia : (i : ℕ) < a := by
      by_contra hia
      exact hs ⟨fun h => absurd h hia, fun h => absurd (lt_trans (Fin.lt_def.1 hij) h) hia⟩
    have hja : ¬ (j : ℕ) < a := fun hja => hs ⟨fun _ => hja, fun _ => hia⟩
    simp only [hia, hja, ↓reduceIte]
    linarith [hi.2, hj.1]

lemma injective_shiftY {x : Cfg n} (hx : x ∈ Cube n) (hinj : Function.Injective x) :
    Function.Injective (shiftY a x) := by
  intro i j h
  have hi := Set.mem_univ_pi.1 hx i
  have hj := Set.mem_univ_pi.1 hx j
  simp only [shiftY] at h
  by_cases hia : (i : ℕ) < a <;> by_cases hja : (j : ℕ) < a <;>
    simp only [hia, hja, ↓reduceIte, add_zero] at h
  · exact hinj h
  · linarith [hi.2, hj.1]
  · linarith [hi.1, hj.2]
  · exact hinj (by linarith)

/-- **At an injective point of the cube, the sorting relabelling in `YG a` is unique.** -/
theorem YG_eq_of_mem_RY {x : Cfg n} (hx : x ∈ Cube n) (hinj : Function.Injective x)
    {σ ρ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) (hρ : YG a ρ) (h1 : pm σ x ∈ RY a n)
    (h2 : pm ρ x ∈ RY a n) : σ = ρ := by
  have m1 := strictMono_shiftY h1
  have m2 := strictMono_shiftY h2
  rw [shiftY_pm hσ] at m1
  rw [shiftY_pm hρ] at m2
  exact perm_eq_of_strictMono (injective_shiftY hx hinj) m1 m2

/-- At an injective point of the cube, some relabelling of `YG a` sorts each group. -/
lemma exists_YG_sort {x : Cfg n} (hx : x ∈ Cube n) (hinj : Function.Injective x) :
    ∃ σ, YG a σ ∧ pm σ x ∈ RY a n :=
  exists_YG_mem_RY hx fun _ _ hij _ h => hij (hinj h)

end DFT.Continuum.Line
