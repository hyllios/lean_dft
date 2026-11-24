/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.YoungInj

/-!
# A highest-weight reference state of mixed symmetry

For `a + b = N` with `b ≤ a`, a state `φ₀` of type `(a, b)` that satisfies Fock's condition
`altY (a + 1) φ₀ = 0` (it has total spin `S = S_z`) and is nonnegative on the Young chamber `RY a`,
strictly positive on a box of positive measure there.

Orbitals are tent functions `h_k` with disjoint supports `I_0 < I_1 < ⋯` inside `(0, 1)`. Particle
`i` carries orbital `orb i` (`i` in the first group, `i - a` in the second),
`P = Π_i h_{orb i}(x_i)` and `φ₀ = altY a P`.

* `phi0_pm`: `φ₀` has type `(a, b)`;
* **`altY_phi0`**: Fock's condition. For `σ ∈ YG a`, `P ∘ σ` carries the same orbital on a particle
  `j < a` and on particle `a`, so the transposition `(j a) ∈ YG (a + 1)` fixes it and kills its
  antisymmetrisation (`altY_eq_zero_of_inv`);
* `phi0_eq_P`: on `RY a` (off collisions) every `σ ≠ 1` has an inversion within a group, and the
  ordered supports make its term vanish, so `φ₀ = P ≥ 0`;
* `boxB`, `boxB_sub_RY`, `P_pos_boxB`, `measure_boxB_pos`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ}

/-! ### Antisymmetrisations of invariant functions vanish -/

lemma altY_eq_zero_of_inv {c : ℕ} {F : Cfg n → ℝ} {τ : Equiv.Perm (Fin (n + 1))}
    (hτ : YG c τ) (hsgn : sgn τ = -1) (hF : ∀ x, F (pm τ x) = F x) (x : Cfg n) :
    altY c F x = 0 := by
  classical
  have h : altY c F x = -altY c F x := by
    calc altY c F x = ∑ ρ, if YG c ρ then sgn ρ * F (pm τ (pm ρ x)) else 0 := by
          simp only [altY, hF]
      _ = ∑ ρ, if YG c ρ then sgn ρ * F (pm (ρ * τ) x) else 0 := by simp only [pm_mul]
      _ = ∑ ρ, if YG c (ρ * τ⁻¹) then sgn (ρ * τ⁻¹) * F (pm ρ x) else 0 := by
          refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun ρ => ?_
          simp only [Equiv.coe_mulRight, mul_inv_cancel_right]
      _ = -altY c F x := by
          simp only [altY, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          have hiff : YG c (ρ * τ⁻¹) ↔ YG c ρ :=
            ⟨fun h => by simpa using YG_mul h hτ, fun h => YG_mul h (YG_inv hτ)⟩
          simp only [hiff, sgn_mul, sgn_inv, hsgn]
          split_ifs <;> ring
  linarith

/-! ### Orbitals -/

/-- The half-width of the supports. -/
noncomputable def epsB (a : ℕ) : ℝ := 1 / (4 * ((a : ℝ) + 1))

/-- The centre of orbital `k`. -/
noncomputable def cenB (a k : ℕ) : ℝ := ((k : ℝ) + 1) / ((a : ℝ) + 1)

/-- The tent orbital `k`, supported in `(cenB a k - epsB a, cenB a k + epsB a)`. -/
noncomputable def bump (a k : ℕ) (t : ℝ) : ℝ := max 0 (epsB a - |t - cenB a k|)

lemma bump_nonneg (a k : ℕ) (t : ℝ) : 0 ≤ bump a k t := le_max_left _ _

lemma continuous_bump (a k : ℕ) : Continuous (bump a k) :=
  continuous_const.max (continuous_const.sub (continuous_abs.comp
    (continuous_id.sub continuous_const)))

lemma lt_of_bump_ne {a k : ℕ} {t : ℝ} (h : bump a k t ≠ 0) : |t - cenB a k| < epsB a := by
  by_contra hc; push Not at hc
  exact h (max_eq_left (by linarith))

lemma epsB_pos (a : ℕ) : 0 < epsB a := by unfold epsB; positivity

lemma cen_sub_cen {a k l : ℕ} (hkl : k < l) : 2 * epsB a < cenB a l - cenB a k := by
  unfold epsB cenB
  have hkl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
  have ha : (0 : ℝ) < a + 1 := by positivity
  rw [← sub_div]
  have e : 2 * (1 / (4 * ((a : ℝ) + 1))) = (1 / 2) / ((a : ℝ) + 1) := by field_simp; ring
  rw [e]
  exact div_lt_div_of_pos_right (by linarith) ha

/-- **Ordered supports.** -/
lemma lt_of_bump {a k l : ℕ} (hkl : k < l) {s t : ℝ} (hs : |s - cenB a k| < epsB a)
    (ht : |t - cenB a l| < epsB a) : s < t := by
  have := cen_sub_cen (a := a) hkl
  have h1 := (abs_lt.1 hs).2
  have h2 := (abs_lt.1 ht).1
  linarith

lemma interval_sub_unit {a k : ℕ} (hk : k < a) {t : ℝ} (ht : |t - cenB a k| < epsB a) :
    0 < t ∧ t < 1 := by
  have ha : (0 : ℝ) < a + 1 := by positivity
  have hk' : (k : ℝ) + 1 ≤ a := by exact_mod_cast hk
  have h1 := abs_lt.1 ht
  unfold epsB cenB at h1
  constructor
  · have : (0 : ℝ) < ((k : ℝ) + 1) / (a + 1) - 1 / (4 * (a + 1)) := by
      rw [div_sub_div _ _ ha.ne' (by positivity), lt_div_iff₀ (by positivity)]; nlinarith
    linarith
  · have : ((k : ℝ) + 1) / (a + 1) + 1 / (4 * (a + 1)) < 1 := by
      rw [div_add_div _ _ ha.ne' (by positivity), div_lt_one (by positivity)]; nlinarith
    linarith

/-! ### The product state and the reference state -/

/-- The orbital carried by particle `i`. -/
def orb (a : ℕ) (i : Fin (n + 1)) : ℕ := if (i : ℕ) < a then i else i - a

lemma orb_lt {a b : ℕ} (hab : a + b = n + 1) (hba : b ≤ a) (i : Fin (n + 1)) : orb a i < a := by
  unfold orb; split_ifs <;> omega

lemma orb_strictMono {a : ℕ} {i j : Fin (n + 1)} (hij : i < j) (hs : SameB a i j) :
    orb a i < orb a j := by
  have hij' : (i : ℕ) < j := hij
  unfold orb SameB at *
  by_cases hi : (i : ℕ) < a
  · simp only [hi, hs.1 hi, ↓reduceIte]; exact hij'
  · have hj : ¬ (j : ℕ) < a := fun h => hi (hs.2 h)
    simp only [hi, hj, ↓reduceIte]; omega

/-- The product state `Π_i h_{orb i}(x_i)`. -/
noncomputable def Pst (a : ℕ) (x : Cfg n) : ℝ := ∏ i, bump a (orb a i) (x i)

/-- **The reference state** `φ₀ = altY a P`. -/
noncomputable def phi0 (a : ℕ) : Cfg n → ℝ := altY a (Pst a)

lemma continuous_Pst (a : ℕ) : Continuous (Pst (n := n) a) :=
  continuous_finsetProd _ fun i _ => (continuous_bump _ _).comp (continuous_apply i)

lemma Pst_nonneg (a : ℕ) (x : Cfg n) : 0 ≤ Pst a x :=
  Finset.prod_nonneg fun _ _ => bump_nonneg _ _ _

lemma continuous_phi0 (a : ℕ) : Continuous (phi0 (n := n) a) :=
  contDiff_zero.1 (contDiff_altY (contDiff_zero.2 (continuous_Pst a)))

lemma phi0_pm (a : ℕ) {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) (x : Cfg n) :
    phi0 a (pm σ x) = sgn σ * phi0 a x := altY_pm _ hσ x

lemma antiY_phi0 (a : ℕ) : AntiY a (phi0 (n := n) a) := fun _ hσ =>
  ae_of_all _ fun x => phi0_pm a hσ x

/-- **Fock's condition** `altY (a + 1) φ₀ = 0`. -/
theorem altY_phi0 {a b : ℕ} (hab : a + b = n + 1) (hb : 1 ≤ b) (hba : b ≤ a) (x : Cfg n) :
    altY (a + 1) (phi0 a) x = 0 := by
  classical
  -- expand `φ₀` and swap the sums
  have hc : ∀ (c : ℕ) (f : Cfg n → ℝ) (y : Cfg n), altY c f y =
      ∑ σ, (if YG c σ then sgn σ else 0) * f (pm σ y) := fun c f y => by
    simp only [altY]; exact Finset.sum_congr rfl fun σ _ => by split_ifs <;> simp
  have e : altY (a + 1) (phi0 a) x =
      ∑ σ, if YG a σ then sgn σ * altY (a + 1) (fun y => Pst a (pm σ y)) x else 0 := by
    rw [hc]
    simp only [phi0, hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases h : YG a σ
    · simp only [h, ↓reduceIte]
      exact Finset.sum_congr rfl fun τ _ => by ring
    · simp [h]
  rw [e]
  refine Finset.sum_eq_zero fun σ _ => ?_
  split_ifs with hσ
  swap; · rfl
  -- the repeated orbital
  set A : Fin (n + 1) := ⟨a, by omega⟩
  set s := σ⁻¹ A
  have hs : a ≤ (s : ℕ) := by
    have := YG_inv hσ A
    by_contra h; push Not at h
    exact absurd (this.1 h) (by simp [A])
  set m : Fin (n + 1) := ⟨(s : ℕ) - a, by omega⟩
  have hm : (m : ℕ) < a := by
    simp only [m]; have := s.isLt; omega
  have hms : m ≠ s := fun h => by
    have := congrArg Fin.val h; simp only [m] at this; omega
  have horb : orb a m = orb a s := by
    have hs' : ¬ (s : ℕ) < a := by omega
    unfold orb; simp only [hm, hs', ↓reduceIte]; rfl
  set j := σ m
  have hj : (j : ℕ) < a := (hσ m).2 hm
  have hjA : j ≠ A := fun h => by have := congrArg Fin.val h; simp [A] at this; omega
  set τ := Equiv.swap j A
  have hτ : YG (a + 1) τ := YG_swap (by simp only [SameB, A]; omega)
  have hτsgn : sgn τ = -1 := by simp [τ, sgn, Equiv.Perm.sign_swap hjA]
  have hσA : σ s = A := by simp [s]
  have hτσ : ∀ i, τ (σ i) = σ (Equiv.swap m s i) := fun i => by
    have h2 : τ = σ * Equiv.swap m s * σ⁻¹ := by
      have := Equiv.swap_apply_apply σ m s
      rw [hσA] at this
      exact this
    rw [h2]
    simp [Equiv.Perm.mul_apply]
  have horb' : ∀ i, orb a (Equiv.swap m s i) = orb a i := fun i => by
    rcases eq_or_ne i m with h | h
    · subst h; simp [horb]
    · rcases eq_or_ne i s with h' | h'
      · subst h'; simp [horb]
      · rw [Equiv.swap_apply_of_ne_of_ne h h']
  rw [altY_eq_zero_of_inv hτ hτsgn (fun y => ?_) x, mul_zero]
  simp only [Pst, pm_apply, hτσ]
  calc ∏ i, bump a (orb a i) (y (σ (Equiv.swap m s i)))
      = ∏ i, (fun k => bump a (orb a k) (y (σ k))) (Equiv.swap m s i) :=
        Finset.prod_congr rfl fun i _ => by simp only [horb']
    _ = ∏ k, bump a (orb a k) (y (σ k)) :=
        Equiv.prod_comp (Equiv.swap m s) (fun k => bump a (orb a k) (y (σ k)))

/-! ### On the Young chamber -/

/-- On the Young chamber, off collisions, `φ₀ = P`. -/
theorem phi0_eq_Pst {a : ℕ} {x : Cfg n} (hx : x ∈ RY a n) (hinj : Function.Injective x) :
    phi0 a x = Pst a x := by
  classical
  unfold phi0 altY
  rw [Finset.sum_eq_single 1 (fun σ _ hσ1 => ?_) (fun h => absurd (Finset.mem_univ _) h)]
  · simp [YG_one, sgn_one, pm_one]
  · split_ifs with hσ
    swap; · rfl
    have hnot : pm σ x ∉ RY a n := fun h =>
      hσ1 (YG_eq_of_mem_RY hx.1 hinj hσ (YG_one a) h (by rw [pm_one]; exact hx))
    have hcube : pm σ x ∈ Cube n := pm_mem_cube.2 hx.1
    obtain ⟨i, j, hij, hs, hle⟩ : ∃ i j, i < j ∧ SameB a i j ∧ x (σ j) ≤ x (σ i) := by
      by_contra h; push Not at h
      exact hnot ⟨hcube, fun i j hij hs => h i j hij hs⟩
    have hz : Pst a (pm σ x) = 0 := by
      by_contra h0
      have hall := Finset.prod_ne_zero_iff.1 h0
      have h1 := lt_of_bump (orb_strictMono hij hs) (lt_of_bump_ne (hall i (Finset.mem_univ _)))
        (lt_of_bump_ne (hall j (Finset.mem_univ _)))
      simp only [pm_apply] at h1
      linarith
    rw [hz, mul_zero]

/-- A box of positive measure inside the Young chamber. -/
def boxB (a : ℕ) : Set (Cfg n) := {x | ∀ i, |x i - cenB a (orb a i)| < epsB a}

lemma isOpen_boxB (a : ℕ) : IsOpen (boxB (n := n) a) := by
  have : boxB (n := n) a = ⋂ i, {x : Cfg n | |x i - cenB a (orb a i)| < epsB a} := by
    ext x; simp [boxB]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt
    (continuous_abs.comp ((continuous_apply i).sub continuous_const)) continuous_const

lemma boxB_sub_RY {a b : ℕ} (hab : a + b = n + 1) (hba : b ≤ a) :
    boxB (n := n) a ⊆ RY a n := fun _ hx =>
  ⟨fun i _ => interval_sub_unit (orb_lt hab hba i) (hx i),
    fun i j hij hs => lt_of_bump (orb_strictMono hij hs) (hx i) (hx j)⟩

lemma Pst_pos_boxB {a : ℕ} {x : Cfg n} (hx : x ∈ boxB a) : 0 < Pst a x :=
  Finset.prod_pos fun i _ => lt_max_of_lt_right (by have := hx i; linarith)

lemma measure_boxB_pos (a : ℕ) : 0 < volume (boxB (n := n) a) :=
  (isOpen_boxB a).measure_pos volume ⟨fun i => cenB a (orb a i), fun i => by
    simp [epsB_pos]⟩

end DFT.Continuum.Line
