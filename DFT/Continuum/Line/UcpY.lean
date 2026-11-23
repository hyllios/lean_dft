/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.YoungGS
import DFT.Continuum.Line.UcpBos

/-!
# Unique continuation for `H¹₀` ground states of mixed symmetry

For the Young symmetry `ymix a` (the spatial part of a spin-½ state with `a` spins up), any
continuous `v` and continuous `w`, every `H¹₀` ground state is nonzero almost everywhere
(**`gs_ne_zero_WY`**). The proof follows `Line/UcpBos` on the Young chamber `RY` (open and
convex), with the companion `B = |Ψ|` of `Line/YoungGS` and the cutoff
`η = Π_j sin(πxⱼ) · Π_{i ≠ j same group}(xᵢ - xⱼ)` (`etaY`), which vanishes on the walls and on the
same-group diagonals and is bounded below on closed balls in `RY` (`logData_ballY`); local
constancy of the zero set spreads through the convex chamber (`null_or_conull_of_local`).

* **`gs_ne_zero_W_fer`**, **`ucpW_fer`**: fermions are the case `a = N` (`DomW_fer_eq`,
  `isGS_fer_Y`).
* `ae_of_ae_RY`: a `YG a`-invariant statement that holds a.e. in `RY` holds a.e. in the cube;
* `logData_ballY`: the logarithmic data for the companion `B = |Ψ|` on closed balls in `RY`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Metric

variable {n : ℕ} {a : ℕ}

/-! ### Transfer from the Young chamber -/

/-- A `YG a`-invariant statement that holds a.e. in `RY` holds a.e. in the cube. -/
theorem ae_of_ae_RY {p : Cfg n → Prop} (hp : ∀ σ, YG a σ → ∀ x, p (pm σ x) ↔ p x)
    (h : ∀ᵐ x ∂volume.restrict (RY a n), p x) : ∀ᵐ x ∂μN n, p x := by
  have h1 : ∀ᵐ x ∂μN n, x ∈ RY a n → p x :=
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_RY).1 h)
  have h2 : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), pm σ x ∈ RY a n → p (pm σ x) :=
    ae_all_iff.2 fun σ => ae_pm h1 σ
  filter_upwards [h2, ae_cube, ae_injective] with x hx hxc hinj
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := a) hxc hinj
  exact (hp σ hσ x).1 (hx σ hσR)

/-! ### A cutoff vanishing on the walls and the same-group diagonals -/

/-- `Π_{i ≠ j, same group} (xᵢ - xⱼ)`. -/
noncomputable def DgY (a : ℕ) (x : Cfg n) : ℝ :=
  ∏ i, ∏ j, if i = j ∨ ¬ SameB a i j then 1 else x i - x j

/-- `η = Π_j sin(πxⱼ) · Π_{i ≠ j, same group}(xᵢ - xⱼ)`. -/
noncomputable def etaY (a : ℕ) (x : Cfg n) : ℝ := etaS x * DgY a x

lemma contDiff_DgY : ContDiff ℝ 1 (DgY (n := n) a) := by
  unfold DgY
  refine contDiff_prod fun i _ => contDiff_prod fun j _ => ?_
  by_cases h : i = j ∨ ¬ SameB a i j
  · simp only [h, ↓reduceIte]; exact contDiff_const
  · simp only [h, ↓reduceIte]; fun_prop

lemma contDiff_etaY : ContDiff ℝ 1 (etaY (n := n) a) := contDiff_etaS.mul contDiff_DgY

lemma DgY_pm {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) (x : Cfg n) :
    DgY a (pm σ x) = DgY a x := by
  simp only [DgY, pm_apply]
  rw [← Equiv.prod_comp σ (fun i => ∏ j, if i = j ∨ ¬ SameB a i j then (1 : ℝ) else x i - x j)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Equiv.prod_comp σ
    (fun j => if σ i = j ∨ ¬ SameB a (σ i) j then (1 : ℝ) else x (σ i) - x j)]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [σ.injective.eq_iff, YG_sameB hσ]

lemma etaY_pm {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) (x : Cfg n) :
    etaY a (pm σ x) = etaY a x := by
  simp only [etaY, etaS_pm, DgY_pm hσ]

lemma etaY_wall (x : Cfg n) (k : Fin (n + 1)) (h : x k = 0 ∨ x k = 1) : etaY a x = 0 := by
  simp [etaY, etaS_wall x k h]

lemma etaY_diag (x : Cfg n) (i j : Fin (n + 1)) (hij : i ≠ j) (hs : SameB a i j)
    (h : x i = x j) : etaY a x = 0 := by
  have : DgY a x = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j)
      (by simp [hij, hs, h]))
  simp [etaY, this]

lemma etaY_ne_zero {x : Cfg n} (hx : x ∈ RY a n) : etaY a x ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.2 fun j _ => (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).ne'
    · have := (Set.mem_univ_pi.1 hx.1 j).1; positivity
    · have := (Set.mem_univ_pi.1 hx.1 j).2; nlinarith [Real.pi_pos]
  · refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    by_cases h : i = j ∨ ¬ SameB a i j
    · simp [h]
    · simp only [h, ↓reduceIte]
      push Not at h
      rcases lt_or_gt_of_ne h.1 with hij | hij
      · exact (sub_neg.2 (hx.2 i j hij h.2)).ne
      · exact (sub_pos.2 (hx.2 j i hij h.2.symm)).ne'

/-! ### Unique continuation -/

section ucp

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {Ψ : Cfg n → ℝ}

/-- The logarithmic data for the companion on a closed ball inside the Young chamber. -/
theorem logData_ballY (hΨ : IsGS (settingWS (ymix a) w hw) v Ψ) {x0 : Cfg n} {R : ℝ}
    (hR : 0 ≤ R) (hsub : closedBall x0 R ⊆ RY a n) : LogData (PhiBY a Ψ) (closedBall x0 R) := by
  set E := Q (settingWS (ymix a) w hw) v (PhiY a Ψ) / ip (μ := μN n) (PhiY a Ψ) (PhiY a Ψ)
  obtain ⟨C, hC⟩ := ae_bound_cont (n := n)
    (continuous_const.sub ((continuous_LN v).add hw) : Continuous fun x => E - (LN n v x + w x))
  set C' := max C 0
  have hC' : ∀ᵐ x ∂μN n, |E - (LN n v x + w x)| ≤ C' := by
    filter_upwards [hC] with x hx
    rw [Real.norm_eq_abs] at hx; exact hx.trans (le_max_left _ _)
  set K := 4 * ∑ k, ∫ x, dk k (etaY a) x ^ 2 ∂μN n + 2 * C' * ∫ x, etaY a x ^ 2 ∂μN n
  have hK : 0 ≤ K := by
    have h1 : 0 ≤ ∑ k, ∫ x, dk k (etaY (n := n) a) x ^ 2 ∂μN n :=
      Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
    have h2 : 0 ≤ ∫ x, etaY (n := n) a x ^ 2 ∂μN n := integral_nonneg fun x => sq_nonneg _
    have h3 : 0 ≤ C' := le_max_right _ _
    positivity
  obtain ⟨xm, hxm, hmin⟩ := (isCompact_closedBall x0 R).exists_isMinOn
    ⟨x0, mem_closedBall_self hR⟩ (continuous_abs.comp contDiff_etaY.continuous).continuousOn
  refine ⟨h1W_PhiBY hΨ.1, ae_of_all _ (PhiBY_nonneg Ψ), isClosed_closedBall.measurableSet,
    fun x hx => (hsub hx).1, convex_closedBall x0 R, etaY a, contDiff_etaY.continuous,
    |etaY a xm|, abs_pos.2 (etaY_ne_zero (hsub hxm)), fun x hx => hmin hx, K, hK,
    fun ε hε => ?_⟩
  exact log_estimate_Y hΨ contDiff_etaY (fun σ hσ x => etaY_pm hσ x) etaY_wall etaY_diag hε
    (le_max_right C 0) hC'

/-- **Ground states of mixed symmetry are nonzero almost everywhere.** For any continuous `v` and
continuous `w`, every `H¹₀` ground state of the Young symmetry `ymix a` is nonzero a.e. -/
theorem gs_ne_zero_WY (hΨ : IsGS (settingWS (ymix a) w hw) v Ψ) : ∀ᵐ x ∂μN n, Ψ x ≠ 0 := by
  set u := PhiBY a Ψ
  have hum := (h1W_PhiBY hΨ.1).1.aestronglyMeasurable
  set u' := hum.mk u
  have hue : u =ᵐ[μN n] u' := hum.ae_eq_mk
  have hu'm : Measurable u' := hum.stronglyMeasurable_mk.measurable
  set Z : Set (Cfg n) := {x | u' x = 0}
  have hZ : MeasurableSet Z := hu'm (measurableSet_singleton 0)
  have hv : ∀ᵐ x ∂volume, x ∈ Cube n → u x = u' x := (ae_restrict_iff' measurableSet_cube).1 hue
  have hloc : ∀ x0 ∈ RY a n, ∃ B, IsOpen B ∧ x0 ∈ B ∧ B ⊆ RY a n ∧
      ((∀ᵐ y ∂volume.restrict B, y ∈ Z) ∨ (∀ᵐ y ∂volume.restrict B, y ∉ Z)) := by
    intro x0 hx0
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_RY x0 hx0
    set R := δ / 4
    have hR : 0 < R := by positivity
    have hR2 : 2 * R < δ := by simp only [R]; linarith
    have hP : closedBall x0 (2 * R) ⊆ RY a n := (closedBall_subset_ball hR2).trans hball
    have hL := logData_ballY hΨ (by positivity) hP
    set P := closedBall x0 (2 * R)
    have hPc : P ⊆ Cube n := fun x hx => (hP hx).1
    have hinv : ∀ k (h : ℝ), 0 ≤ h →
        ∀ᵐ x ∂volume, x ∈ SP P h k → (x ∈ Z ↔ x + h • ek k ∈ Z) := by
      intro k h hh
      have hv' := (measurePreserving_add_right volume (h • ek k)).quasiMeasurePreserving.ae hv
      filter_upwards [hL.zero_set_translate k hh, hv, hv'] with x hx h1 h2 hxS
      simp only [Z, mem_ofPred_eq]
      rw [← h1 (hPc hxS.1), ← h2 (hPc hxS.2)]
      exact hx hxS
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
  have hUc : ∀ᵐ x ∂volume.restrict (RY a n), u x = u' x :=
    (ae_restrict_iff' measurableSet_RY).2 (by filter_upwards [hv] with x hx hxU using hx hxU.1)
  have hsym : ∀ (q : ℝ → Prop) σ, YG a σ → ∀ x, q (u (pm σ x)) ↔ q (u x) := fun q σ hσ x => by
    simp only [u, PhiBY_pm Ψ hσ]
  rcases null_or_conull_of_local convex_RY.isPreconnected hloc with h | h
  · exfalso
    have h0 : ∀ᵐ x ∂μN n, u x = 0 := ae_of_ae_RY (hsym (· = 0)) (by
      filter_upwards [h, hUc] with x hx he
      simp only [Z, mem_ofPred_eq] at hx
      rw [he, hx])
    have hz : ∀ᵐ x ∂μN n, Ψ x * Ψ x = 0 := by
      filter_upwards [h0, PhiBY_ae_eq_abs hΨ.1] with x h1 h2
      have : |Ψ x| = 0 := h2 ▸ h1
      rw [abs_eq_zero.1 this, mul_zero]
    exact hΨ.2.1.ne' (integral_eq_zero_of_ae hz)
  · have h0 : ∀ᵐ x ∂μN n, u x ≠ 0 := ae_of_ae_RY (hsym (· ≠ 0)) (by
      filter_upwards [h, hUc] with x hx he
      simp only [Z, mem_ofPred_eq] at hx
      rwa [he])
    filter_upwards [h0, PhiBY_ae_eq_abs hΨ.1] with x h1 h2
    have : |Ψ x| ≠ 0 := h2 ▸ h1
    exact abs_ne_zero.1 this

end ucp

/-! ### Fermions: the case `a = N` -/

/-- Fermionic states are the Young states with all particles in one group. -/
lemma DomW_fer_eq : DomW .fer n = DomWS (ymix (n := n) (n + 1)) := by
  ext Φ
  refine ⟨fun h => ⟨h.1, h.2.1, fun σ _ => h.2.2 σ⟩, fun h => ⟨h.1, h.2.1, fun σ => h.2.2 σ ?_⟩⟩
  intro i
  exact ⟨fun _ => i.isLt, fun _ => (σ i).isLt⟩

lemma isGS_fer_Y {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW .fer n w hw) v Ψ) : IsGS (settingWS (ymix (n + 1)) w hw) v Ψ := by
  have hD : ∀ φ, φ ∈ DomWS (ymix (n := n) (n + 1)) ↔ φ ∈ DomW .fer n := fun φ => by
    rw [DomW_fer_eq]
  exact ⟨(hD Ψ).2 hΨ.1, hΨ.2.1, fun φ hφ => hΨ.2.2 φ ((hD φ).1 hφ)⟩

/-- **Fermionic `H¹₀` ground states of continuous potentials are nonzero almost everywhere.** -/
theorem gs_ne_zero_W_fer {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW .fer n w hw) v Ψ) : ∀ᵐ x ∂μN n, Ψ x ≠ 0 :=
  gs_ne_zero_WY (isGS_fer_Y hΨ)

/-- **Unique continuation for fermionic `H¹₀` ground states.** -/
theorem ucpW_fer (w : Cfg n → ℝ) (hw : Continuous w) : UcpW .fer n w hw :=
  fun _ _ hΨ => gs_ne_zero_W_fer hΨ


end DFT.Continuum.Line
