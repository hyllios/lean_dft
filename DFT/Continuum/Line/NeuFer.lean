/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.NeuYoung

/-!
# Unique continuation for fermionic Neumann ground states of `H⁻¹` potentials

For `N` fermions on `[0, 1]` with Neumann walls, an `H⁻¹` potential and a continuous interaction,
every ground state is nonzero almost everywhere (**`gsNH_ne_zero_fer`**).

The companion `B = |Ψ|` of the chamber ground state satisfies the weak equation against symmetric
test functions vanishing linearly on the diagonals (`eq_PhiBY_H`). Moser's estimate for `H⁻¹`
potentials (`log_estimate_gen`) applies with the cutoff `η = η_a · Π_{i≠j}(xᵢ - xⱼ)`
(`log_estimate_fer`), and the cutoff `ζ_a` moves `B` into `H¹₀` on balls of the chamber inside
`[a, 1 - a]ᴺ` (`logData_fer`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Metric

variable {n : ℕ}

/-! ### The diagonal cutoff -/

lemma DgY_diag (x : Cfg n) {i j : Fin (n + 1)} (hij : i ≠ j) (h : x i = x j) :
    DgY (n + 1) x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j)
    (by simp [hij, h, SameB, Fin.is_le]))

lemma abs_DgY_le {x : Cfg n} (hx : x ∈ Cube n) : |DgY (n + 1) x| ≤ 1 := by
  rw [DgY, Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
  rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => ?_
  split_ifs
  · simp
  · have hi := hx i trivial
    have hj := hx j trivial
    rw [abs_le]; constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]

lemma DgY_ne_zero {x : Cfg n} (hx : x ∈ RY (n + 1) n) : DgY (n + 1) x ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  by_cases h : i = j ∨ ¬ SameB (n + 1) i j
  · simp [h]
  · simp only [h, ↓reduceIte]
    push Not at h
    rcases lt_or_gt_of_ne h.1 with hij | hij
    · exact (sub_neg.2 (hx.2 i j hij h.2)).ne
    · exact (sub_pos.2 (hx.2 j i hij h.2.symm)).ne'

section cut

variable {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)

/-- The cutoff `η_a · Π_{i ≠ j}(xᵢ - xⱼ)`. -/
noncomputable def etaF (x : Cfg n) : ℝ := etaA ha ha2 x * DgY (n + 1) x

include ha ha2

lemma contDiff_etaF : ContDiff ℝ 1 (etaF (n := n) ha ha2) :=
  (contDiff_etaA ha ha2).mul contDiff_DgY

lemma etaF_pm (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    etaF ha ha2 (pm σ x) = etaF ha ha2 x := by
  simp only [etaF, etaA_pm, DgY_pm (YG_all σ)]

lemma abs_etaF_le : ∀ᵐ x ∂μN n, |etaF ha ha2 x| ≤ 1 := by
  filter_upwards [ae_cube] with x hx
  rw [etaF, abs_mul]
  calc |etaA ha ha2 x| * |DgY (n + 1) x| ≤ 1 * 1 :=
        mul_le_mul (abs_etaA_le ha ha2 x) (abs_DgY_le hx) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma etaF_plane (x : Cfg n) {i j : Fin (n + 1)} (hij : i ≠ j) (h : x i = x j) :
    etaF ha ha2 x = 0 := by
  simp [etaF, DgY_diag x hij h]

lemma etaF_ne_zero {x : Cfg n} (hR : x ∈ RY (n + 1) n) (hQ : x ∈ Qa n a) :
    etaF ha ha2 x ≠ 0 := by
  rw [etaF, etaA_eq_one ha ha2 hQ, one_mul]; exact DgY_ne_zero hR

lemma mem_Va_of_etaF {x : Cfg n} (h : etaF ha ha2 x ≠ 0) : x ∈ Va n a :=
  mem_Va_of_etaA ha ha2 (left_ne_zero_of_mul h)

end cut

/-! ### Moser's estimate for the companion -/

/-- **The logarithmic estimate for the companion of a fermionic Neumann ground state.** -/
theorem log_estimate_fer {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH .fer w v Ψ) {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    ∃ K, 0 ≤ K ∧ ∀ ε > 0, ∑ k, ∫ x, (etaF ha ha2 x *
      (dWN k (PhiBY (n + 1) Ψ) x / (PhiBY (n + 1) Ψ x + ε))) ^ 2 ∂μN n ≤ K := by
  set u := PhiBY (n + 1) Ψ
  set η := etaF (n := n) ha ha2
  have hu : u ∈ DomN .bos n := PhiBY_memN hΨ.1
  have hη : ContDiff ℝ 1 η := contDiff_etaF ha ha2
  have hηs : ∀ σ x, η (pm σ x) = η x := etaF_pm ha ha2
  refine log_estimate_gen (v := v) hw hu (ae_of_all _ (PhiBY_nonneg Ψ)) hη hηs (abs_etaF_le ha ha2)
    (QNH .fer w v (PhiY (n + 1) Ψ)) fun ε hε => ?_
  set φ := logTest η u ε
  have hφ : H1NW φ := h1NW_of_mem (logTest_memN hu hη hηs hε)
  have hφs : ∀ σ x, φ (pm σ x) = φ x := fun σ x => by
    simp only [φ, logTest, hηs, u, PhiBY_pm Ψ (YG_all σ)]
  obtain ⟨Bη, hBη⟩ := ae_bound_cont hη.continuous
  have hφη : ∀ᵐ x ∂μN n, |φ x| ≤ max Bη 0 / ε * |η x| := by
    filter_upwards [hBη] with x hx
    rw [Real.norm_eq_abs] at hx
    have hu0 : 0 ≤ u x := PhiBY_nonneg Ψ x
    have hp : 0 < u x + ε := by linarith
    have e : φ x = η x * η x / (u x + ε) := by
      simp only [φ, logTest, Gr_of_nonneg hu0]; field_simp; ring
    rw [e, abs_div, abs_of_pos hp, abs_mul, div_le_iff₀ hp]
    have h1 : |η x| ≤ max Bη 0 := hx.trans (le_max_left _ _)
    have h2 : max Bη 0 / ε * |η x| * ε ≤ max Bη 0 / ε * |η x| * (u x + ε) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (div_nonneg (le_max_right _ _) hε.le) (abs_nonneg _))
    have h3 : max Bη 0 / ε * |η x| * ε = max Bη 0 * |η x| := by field_simp
    nlinarith [abs_nonneg (η x)]
  have hL : ∀ p ∈ pY (n + 1) n, ∃ L, 0 ≤ L ∧ ∀ᵐ x ∂μN n, |φ x| ≤ L * |x p.2 - x p.1| := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    obtain ⟨Lp, hLp0, hLp⟩ := abs_le_of_plane' hη hp'.1.ne
      fun x hx => etaF_plane ha ha2 x hp'.1.ne hx
    refine ⟨max Bη 0 / ε * Lp, mul_nonneg (div_nonneg (le_max_right _ _) hε.le) hLp0, ?_⟩
    filter_upwards [hφη, hLp] with x h1 h2
    calc |φ x| ≤ max Bη 0 / ε * |η x| := h1
      _ ≤ max Bη 0 / ε * (Lp * |x p.2 - x p.1|) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg (le_max_right _ _) hε.le)
      _ = _ := by ring
  exact eq_PhiBY_H hw hΨ hφ hφs hL

/-- A fermionic Neumann ground state gives the logarithmic data for `ζ_a B` on closed balls in
the chamber inside `[a, 1 - a]ᴺ`. -/
theorem logData_fer {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH .fer w v Ψ) {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) {x0 : Cfg n} {R : ℝ}
    (hR : 0 ≤ R) (hsub : closedBall x0 R ⊆ RY (n + 1) n) (hsubQ : closedBall x0 R ⊆ Qa n a) :
    LogData (fun x => zetaA ha ha2 x * PhiBY (n + 1) Ψ x) (closedBall x0 R) := by
  set u := PhiBY (n + 1) Ψ
  have hu : u ∈ DomN .bos n := PhiBY_memN hΨ.1
  have hζ := contDiff_zetaA (n := n) ha ha2
  have hζw : ∀ (x : Cfg n) (j : Fin (n + 1)), (x j = 0 ∨ x j = 1) → zetaA ha ha2 x = 0 :=
    fun x j h => zetaA_wall ha ha2 x j h
  have hWD : ∀ k, IsWD k (fun x => zetaA ha ha2 x * u x)
      (fun x => zetaA ha ha2 x * dWN k u x + dk k (zetaA ha ha2) x * u x) := fun k =>
    (dWN_spec (hu.2.1 k)).mul_cutoff hu.1 hζ hζw
  obtain ⟨K, hK0, hK⟩ := log_estimate_fer hw hΨ ha ha2
  have hηc := (contDiff_etaF (n := n) ha ha2).continuous
  obtain ⟨xm, hxm, hmin⟩ := (isCompact_closedBall x0 R).exists_isMinOn
    ⟨x0, mem_closedBall_self hR⟩ (continuous_abs.comp hηc).continuousOn
  refine ⟨⟨memLp_mul_cont hζ.continuous hu.1, fun k => ⟨_, hWD k⟩⟩, ?_,
    isClosed_closedBall.measurableSet, fun x hx => (hsub hx).1, convex_closedBall x0 R,
    etaF ha ha2, hηc, |etaF ha ha2 xm|, abs_pos.2 (etaF_ne_zero ha ha2 (hsub hxm) (hsubQ hxm)),
    fun x hx => hmin hx, K, hK0, fun ε hε => ?_⟩
  · exact ae_of_all _ fun x => mul_nonneg (zetaA_nonneg ha ha2 x) (PhiBY_nonneg Ψ x)
  refine le_trans (le_of_eq ?_) (hK ε hε)
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  filter_upwards [dW_ae_eq (hWD k)] with x hx
  rw [hx]
  by_cases h0 : etaF ha ha2 x = 0
  · simp [h0]
  · have hV := mem_Va_of_etaF ha ha2 h0
    rw [zetaA_eq_one ha ha2 hV, dk_zetaA ha ha2 hV, one_mul, one_mul, zero_mul, add_zero]

/-- Every point of the open cube has a sub-cube `[a, 1 - a]ᴺ` containing a ball around it. -/
lemma exists_Qa_ball {x0 : Cfg n} (hx0 : x0 ∈ Cube n) :
    ∃ a, 0 < a ∧ a ≤ 1 / 2 ∧ closedBall x0 a ⊆ Qa n a := by
  set m := Finset.univ.inf' Finset.univ_nonempty fun j : Fin (n + 1) => min (x0 j) (1 - x0 j)
  have hm : 0 < m := (Finset.lt_inf'_iff _).2 fun j _ => by
    have := hx0 j trivial
    exact lt_min this.1 (by linarith [this.2])
  have hmj : ∀ j, m ≤ min (x0 j) (1 - x0 j) := fun j =>
    Finset.inf'_le _ (Finset.mem_univ j)
  have hm2 : m ≤ 1 / 2 := by
    have := hmj 0
    have h1 := min_le_left (x0 0) (1 - x0 0)
    have h2 := min_le_right (x0 0) (1 - x0 0)
    linarith
  refine ⟨m / 2, by positivity, by linarith, fun y hy => Set.mem_univ_pi.2 fun j => ?_⟩
  have hyj : dist (y j) (x0 j) ≤ m / 2 := (dist_le_pi_dist y x0 j).trans hy
  rw [Real.dist_eq, abs_le] at hyj
  have := hmj j
  have h1 := min_le_left (x0 j) (1 - x0 j)
  have h2 := min_le_right (x0 j) (1 - x0 j)
  constructor <;> linarith [hyj.1, hyj.2]

/-- **Fermionic Neumann ground states of `H⁻¹` potentials are nonzero almost everywhere.** -/
theorem gsNH_ne_zero_fer {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH .fer w v Ψ) : ∀ᵐ x ∂μN n, Ψ x ≠ 0 := by
  set u := PhiBY (n + 1) Ψ
  have hum := (PhiBY_memN hΨ.1).1.aestronglyMeasurable
  set u' := hum.mk u
  have hue : u =ᵐ[μN n] u' := hum.ae_eq_mk
  have hu'm : Measurable u' := hum.stronglyMeasurable_mk.measurable
  set Z : Set (Cfg n) := {x | u' x = 0}
  have hZ : MeasurableSet Z := hu'm (measurableSet_singleton 0)
  have hv : ∀ᵐ x ∂volume, x ∈ Cube n → u x = u' x := (ae_restrict_iff' measurableSet_cube).1 hue
  have hloc : ∀ x0 ∈ RY (n + 1) n, ∃ B, IsOpen B ∧ x0 ∈ B ∧ B ⊆ RY (n + 1) n ∧
      ((∀ᵐ y ∂volume.restrict B, y ∈ Z) ∨ (∀ᵐ y ∂volume.restrict B, y ∉ Z)) := by
    intro x0 hx0
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_RY x0 hx0
    obtain ⟨a, ha, ha2, hQ⟩ := exists_Qa_ball hx0.1
    set R := min (δ / 4) (a / 2)
    have hR : 0 < R := by positivity
    have hR2 : 2 * R < δ := by
      have := min_le_left (δ / 4) (a / 2); linarith
    have hRa : 2 * R ≤ a := by
      have := min_le_right (δ / 4) (a / 2); linarith
    have hP : closedBall x0 (2 * R) ⊆ RY (n + 1) n := (closedBall_subset_ball hR2).trans hball
    have hPQ : closedBall x0 (2 * R) ⊆ Qa n a := (closedBall_subset_closedBall hRa).trans hQ
    have hL := logData_fer hw hΨ ha ha2 (by positivity) hP hPQ
    set P := closedBall x0 (2 * R)
    have hPc : P ⊆ Cube n := fun x hx => (hP hx).1
    have hinv : ∀ k (h : ℝ), 0 ≤ h →
        ∀ᵐ x ∂volume, x ∈ SP P h k → (x ∈ Z ↔ x + h • ek k ∈ Z) := by
      intro k h hh
      have hv' := (measurePreserving_add_right volume (h • ek k)).quasiMeasurePreserving.ae hv
      filter_upwards [hL.zero_set_translate k hh, hv, hv'] with x hx h1 h2 hxS
      simp only [Z, mem_ofPred_eq]
      rw [← h1 (hPc hxS.1), ← h2 (hPc hxS.2)]
      have hx' := hx hxS
      rwa [zetaA_eq_one ha ha2 (Qa_sub_Va ha (hPQ hxS.1)),
        zetaA_eq_one ha ha2 (Qa_sub_Va ha (hPQ hxS.2)), one_mul, one_mul] at hx'
    have hPpi : P = univ.pi fun j => closedBall (x0 j) (2 * R) := closedBall_pi x0 (by positivity)
    have hV : ∀ t : Cfg n, ∀ᵐ x ∂volume, x ∈ P → x + t ∈ P → (x ∈ Z ↔ x + t ∈ Z) := by
      intro t
      have hA := invariant_all_gen hinv
      rw [hPpi] at hA ⊢
      exact invariant_vec_gen hA t
    refine ⟨ball x0 R, isOpen_ball, mem_ball_self hR,
      (ball_subset_ball (by linarith)).trans hball, ?_⟩
    refine const_on_set hZ hPc isOpen_ball (convex_ball x0 R).isPreconnected hR ?_ hV
    intro x hx t ht
    rw [hPpi]
    rw [ball_pi x0 hR] at hx
    refine Set.mem_univ_pi.2 fun j => ?_
    have h1 := Set.mem_univ_pi.1 hx j
    have h2 := Set.mem_univ_pi.1 ht j
    rw [mem_ball, Real.dist_eq] at h1
    rw [mem_closedBall, Real.dist_eq, Pi.sub_apply]
    have h3 : |t j| ≤ R := abs_le.2 h2
    calc |x j - t j - x0 j| ≤ |x j - x0 j| + |t j| := by
          rw [show x j - t j - x0 j = (x j - x0 j) + -t j by ring]
          exact (abs_add_le _ _).trans (by rw [abs_neg])
      _ ≤ 2 * R := by linarith
  have hUc : ∀ᵐ x ∂volume.restrict (RY (n + 1) n), u x = u' x :=
    (ae_restrict_iff' measurableSet_RY).2 (by filter_upwards [hv] with x hx hxU using hx hxU.1)
  have hsym : ∀ (q : ℝ → Prop) σ, YG (n + 1) σ → ∀ x, q (u (pm σ x)) ↔ q (u x) :=
    fun q σ hσ x => by simp only [u, PhiBY_pm Ψ hσ]
  rcases null_or_conull_of_local convex_RY.isPreconnected hloc with h | h
  · exfalso
    have h0 : ∀ᵐ x ∂μN n, u x = 0 := ae_of_ae_RY (hsym (· = 0)) (by
      filter_upwards [h, hUc] with x hx he
      simp only [Z, mem_ofPred_eq] at hx
      rw [he, hx])
    have hz : ∀ᵐ x ∂μN n, Ψ x ^ 2 = 0 := by
      filter_upwards [h0, PhiBY_ae_eq_absN hΨ.1] with x h1 h2
      have : |Ψ x| = 0 := h2 ▸ h1
      rw [abs_eq_zero.1 this]; ring
    have := integral_eq_zero_of_ae hz
    rw [hΨ.2.1] at this; exact one_ne_zero this
  · have h0 : ∀ᵐ x ∂μN n, u x ≠ 0 := ae_of_ae_RY (hsym (· ≠ 0)) (by
      filter_upwards [h, hUc] with x hx he
      simp only [Z, mem_ofPred_eq] at hx
      rwa [he])
    filter_upwards [h0, PhiBY_ae_eq_absN hΨ.1] with x h1 h2
    have : |Ψ x| ≠ 0 := h2 ▸ h1
    exact abs_ne_zero.1 this

/-- **Unique continuation for Neumann ground states of `H⁻¹` potentials**, bosons or fermions,
any continuous interaction. -/
theorem gsNH_ne_zero {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH}
    {Ψ : Cfg n → ℝ} (hΨ : IsGSNH τ w v Ψ) : ∀ᵐ x ∂μN n, Ψ x ≠ 0 := by
  cases τ with
  | bos => exact gsNH_ne_zero_bos hw hΨ
  | fer => exact gsNH_ne_zero_fer hw hΨ

end DFT.Continuum.Line
