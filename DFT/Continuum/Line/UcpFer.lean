/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.FerLog
import DFT.Continuum.Line.UcpBos

/-!
# Unique continuation for fermionic `H¹₀` ground states, and Hohenberg–Kohn

For fermions on the line with any continuous one-body potential `v` and continuous interaction
`w`, every `H¹₀` ground state `Ψ` is nonzero almost everywhere (`gs_ne_zero_W_fer`):

* the bosonic companion `B = |Ψ|` satisfies the logarithmic estimate for cutoffs vanishing on the
  diagonals (`log_estimate_fer`), here `η = Π_j sin(πxⱼ) · Π_{i ≠ j}(xᵢ - xⱼ)` (`etaD`);
* on every closed ball inside the open chamber `U = (0,1)ᴺ ∩ {x₀ < … < x_N}`, `|η|` is bounded
  below, so the zero set of `B` is translation invariant there (`LogData.zero_set_translate`) and
  null or conull on the concentric ball of half the radius (`const_on_set`);
* the chamber is convex, so the zero set is null or conull in it (`null_or_conull_of_local`);
* `B` is symmetric, so the same holds in the cube (`ae_of_ae_chamber`).

Hence `UcpW .fer` holds (`ucpW_fer`), and **Hohenberg–Kohn holds on `H¹₀` for fermions with
continuous potentials** (`hk_line_W_cont_fer`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Metric

variable {n : ℕ}

/-! ### Locally null or conull sets -/

/-- **Local constancy propagates through a connected set.** If every point of the preconnected
set `U` has an open neighbourhood in `U` on which `Z` is null or conull, then `Z` is
null or conull in `U`. -/
theorem null_or_conull_of_local {Z U : Set (Cfg n)} (hUc : IsPreconnected U)
    (hloc : ∀ x ∈ U, ∃ B, IsOpen B ∧ x ∈ B ∧ B ⊆ U ∧
      ((∀ᵐ y ∂volume.restrict B, y ∈ Z) ∨ (∀ᵐ y ∂volume.restrict B, y ∉ Z))) :
    (∀ᵐ y ∂volume.restrict U, y ∈ Z) ∨ (∀ᵐ y ∂volume.restrict U, y ∉ Z) := by
  -- the union of the open subsets of `U` on which `p` holds a.e.
  let A : (Cfg n → Prop) → Set (Cfg n) := fun p =>
    ⋃ i : {B : Set (Cfg n) // IsOpen B ∧ B ⊆ U ∧ ∀ᵐ y ∂volume.restrict B, p y}, i.1
  have hAo : ∀ p, IsOpen (A p) := fun p => isOpen_iUnion fun i => i.2.1
  have hAU : ∀ p, A p ⊆ U := fun p => iUnion_subset fun i => i.2.2.1
  have hAae : ∀ p, ∀ᵐ y ∂volume.restrict (A p), p y := fun p => by
    obtain ⟨T, hT, hTe⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : {B : Set (Cfg n) // IsOpen B ∧ B ⊆ U ∧ ∀ᵐ y ∂volume.restrict B, p y} => i.1)
      fun i => i.2.1
    change ∀ᵐ y ∂volume.restrict (⋃ i, _), p y
    rw [← hTe]
    exact (ae_restrict_biUnion_iff _ hT p).2 fun i _ => i.2.2.2
  have hmem : ∀ (p : Cfg n → Prop) (x : Cfg n) (B : Set (Cfg n)), IsOpen B → x ∈ B → B ⊆ U →
      (∀ᵐ y ∂volume.restrict B, p y) → x ∈ A p := fun p x B hB hx hBU h =>
    mem_iUnion.2 ⟨⟨B, hB, hBU, h⟩, hx⟩
  set A1 := A fun y => y ∈ Z
  set A0 := A fun y => y ∉ Z
  have hdisj : Disjoint A1 A0 := by
    rw [Set.disjoint_iff]
    intro x ⟨h1, h0⟩
    have hO : IsOpen (A1 ∩ A0) := (hAo _).inter (hAo _)
    have hpos : 0 < volume (A1 ∩ A0) := hO.measure_pos volume ⟨x, h1, h0⟩
    have hae : ∀ᵐ y ∂volume.restrict (A1 ∩ A0), False := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left (hAae _),
        ae_restrict_of_ae_restrict_of_subset inter_subset_right (hAae _)] with y a b using b a
    rw [ae_iff, Measure.restrict_apply' hO.measurableSet] at hae
    simp only [not_false_eq_true, ofPred_true, univ_inter] at hae
    exact hpos.ne' hae
  have hcov : U ⊆ A1 ∪ A0 := fun x hx => by
    obtain ⟨B, hB, hxB, hBU, h | h⟩ := hloc x hx
    · exact Or.inl (hmem _ x B hB hxB hBU h)
    · exact Or.inr (hmem _ x B hB hxB hBU h)
  by_cases h1 : (U ∩ A1).Nonempty
  · left
    exact ae_restrict_of_ae_restrict_of_subset
      (hUc.subset_left_of_subset_union (hAo _) (hAo _) hdisj hcov h1) (hAae _)
  · right
    have hsub : U ⊆ A0 := fun x hx => by
      rcases hcov hx with h | h
      · exact absurd ⟨x, hx, h⟩ h1
      · exact h
    exact ae_restrict_of_ae_restrict_of_subset hsub (hAae _)

/-! ### The open chamber -/

/-- The open chamber `(0,1)ᴺ ∩ {x₀ < … < x_N}`. -/
def UC (n : ℕ) : Set (Cfg n) := Cube n ∩ Ord n

lemma isOpen_Ord : IsOpen (Ord n) := by
  have e : Ord n = ⋂ j : Fin n, {x : Cfg n | x j.castSucc < x j.succ} := by
    ext x; simp [Ord, OrdS]
  rw [e]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (continuous_apply _) (continuous_apply _)

lemma convex_Ord : Convex ℝ (Ord n) := by
  intro x hx y hy a b ha hb hab
  simp only [Ord, OrdS, Finset.mem_univ, true_implies, mem_ofPred_eq, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  intro j
  have h1 := hx j
  have h2 := hy j
  rcases ha.lt_or_eq with ha | ha
  · nlinarith
  · subst ha
    have : b = 1 := by linarith
    subst this; linarith

lemma isOpen_UC : IsOpen (UC n) := isOpen_cube.inter isOpen_Ord

lemma isPreconnected_UC : IsPreconnected (UC n) :=
  ((convex_pi fun _ _ => convex_Ioo (0 : ℝ) 1).inter convex_Ord).isPreconnected

lemma measurableSet_UC : MeasurableSet (UC n) := isOpen_UC.measurableSet

/-- A statement about a symmetric quantity that holds a.e. in the chamber holds a.e. in the
cube. -/
theorem ae_of_ae_chamber {p : Cfg n → Prop} (hp : ∀ σ x, p (pm σ x) ↔ p x)
    (h : ∀ᵐ x ∂volume.restrict (UC n), p x) : ∀ᵐ x ∂μN n, p x := by
  have h1 : ∀ᵐ x ∂μN n, x ∈ Ord n → p x := by
    refine (ae_restrict_iff' measurableSet_cube).2 ?_
    filter_upwards [(ae_restrict_iff' measurableSet_UC).1 h] with x hx hxc hxo
    exact hx ⟨hxc, hxo⟩
  have h2 : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), pm σ x ∈ Ord n → p (pm σ x) :=
    ae_all_iff.2 fun σ => ae_pm h1 σ
  filter_upwards [h2, ae_injective] with x hx hinj
  obtain ⟨σ, hσ⟩ := exists_strictMono hinj
  exact (hp σ x).1 (hx σ (mem_Ord_iff.2 hσ))

/-! ### A cutoff vanishing on the walls and the diagonals -/

/-- `Π_{i ≠ j} (xᵢ - xⱼ)`. -/
noncomputable def Dg (x : Cfg n) : ℝ := ∏ i, ∏ j, if i = j then 1 else x i - x j

/-- `η = Π_j sin(πxⱼ) · Π_{i ≠ j}(xᵢ - xⱼ)`. -/
noncomputable def etaD (x : Cfg n) : ℝ := etaS x * Dg x

lemma contDiff_Dg : ContDiff ℝ 1 (Dg (n := n)) := by
  unfold Dg
  refine contDiff_prod fun i _ => contDiff_prod fun j _ => ?_
  by_cases h : i = j
  · simp only [h, ↓reduceIte]; exact contDiff_const
  · simp only [h, ↓reduceIte]; fun_prop

lemma contDiff_etaD : ContDiff ℝ 1 (etaD (n := n)) := contDiff_etaS.mul contDiff_Dg

lemma Dg_pm (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : Dg (pm σ x) = Dg x := by
  simp only [Dg, pm_apply]
  rw [← Equiv.prod_comp σ (fun i => ∏ j, if i = j then (1 : ℝ) else x i - x j)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Equiv.prod_comp σ (fun j => if σ i = j then (1 : ℝ) else x (σ i) - x j)]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [σ.injective.eq_iff]

lemma etaD_pm (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : etaD (pm σ x) = etaD x := by
  simp only [etaD, etaS_pm, Dg_pm]

lemma etaD_wall (x : Cfg n) (k : Fin (n + 1)) (h : x k = 0 ∨ x k = 1) : etaD x = 0 := by
  simp [etaD, etaS_wall x k h]

lemma etaD_diag (x : Cfg n) (i j : Fin (n + 1)) (hij : i ≠ j) (h : x i = x j) : etaD x = 0 := by
  have : Dg x = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j)
      (by simp [hij, h]))
  simp [etaD, this]

lemma etaD_ne_zero {x : Cfg n} (hx : x ∈ UC n) : etaD x ≠ 0 := by
  have hinj := (mem_Ord_iff.1 hx.2).injective
  refine mul_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.2 fun j _ => (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).ne'
    · have := (Set.mem_univ_pi.1 hx.1 j).1; positivity
    · have := (Set.mem_univ_pi.1 hx.1 j).2; nlinarith [Real.pi_pos]
  · refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    by_cases h : i = j
    · simp [h]
    · simp only [h, ↓reduceIte]
      exact sub_ne_zero.2 fun he => h (hinj he)

/-! ### Unique continuation -/

section ucp

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {Ψ : Cfg n → ℝ}

/-- The logarithmic data for the bosonic companion on a closed ball inside the chamber. -/
theorem logData_ball (hΨ : IsGS (settingW .fer n w hw) v Ψ) {x0 : Cfg n} {R : ℝ} (hR : 0 ≤ R)
    (hsub : closedBall x0 R ⊆ UC n) : LogData (PhiB Ψ) (closedBall x0 R) := by
  set E := Q (settingW .fer n w hw) v (PhiF Ψ) / ip (μ := μN n) (PhiF Ψ) (PhiF Ψ)
  obtain ⟨C, hC⟩ := ae_bound_cont (n := n)
    (continuous_const.sub ((continuous_LN v).add hw) : Continuous fun x => E - (LN n v x + w x))
  set C' := max C 0
  have hC' : ∀ᵐ x ∂μN n, |E - (LN n v x + w x)| ≤ C' := by
    filter_upwards [hC] with x hx
    rw [Real.norm_eq_abs] at hx; exact hx.trans (le_max_left _ _)
  set K := 4 * ∑ k, ∫ x, dk k etaD x ^ 2 ∂μN n + 2 * C' * ∫ x, etaD x ^ 2 ∂μN n
  have hK : 0 ≤ K := by
    have h1 : 0 ≤ ∑ k, ∫ x, dk k (etaD (n := n)) x ^ 2 ∂μN n :=
      Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
    have h2 : 0 ≤ ∫ x, etaD (n := n) x ^ 2 ∂μN n := integral_nonneg fun x => sq_nonneg _
    have h3 : 0 ≤ C' := le_max_right _ _
    positivity
  -- `|η|` attains a positive minimum on the compact ball
  obtain ⟨xm, hxm, hmin⟩ := (isCompact_closedBall x0 R).exists_isMinOn
    ⟨x0, mem_closedBall_self hR⟩ (continuous_abs.comp contDiff_etaD.continuous).continuousOn
  refine ⟨h1W_of_mem (PhiB_mem hΨ.1), ae_of_all _ (PhiB_nonneg Ψ),
    isClosed_closedBall.measurableSet, fun x hx => (hsub hx).1, convex_closedBall x0 R, etaD,
    contDiff_etaD.continuous, |etaD xm|, abs_pos.2 (etaD_ne_zero (hsub hxm)),
    fun x hx => hmin hx, K, hK, fun ε hε => ?_⟩
  exact log_estimate_fer hΨ contDiff_etaD etaD_pm etaD_wall etaD_diag hε (le_max_right C 0) hC'

/-- **Fermionic `H¹₀` ground states of continuous potentials are nonzero almost everywhere.** -/
theorem gs_ne_zero_W_fer (hΨ : IsGS (settingW .fer n w hw) v Ψ) : ∀ᵐ x ∂μN n, Ψ x ≠ 0 := by
  set u := PhiB Ψ
  have hum := (PhiB_mem hΨ.1).1.aestronglyMeasurable
  set u' := hum.mk u
  have hue : u =ᵐ[μN n] u' := hum.ae_eq_mk
  have hu'm : Measurable u' := hum.stronglyMeasurable_mk.measurable
  set Z : Set (Cfg n) := {x | u' x = 0}
  have hZ : MeasurableSet Z := hu'm (measurableSet_singleton 0)
  have hv : ∀ᵐ x ∂volume, x ∈ Cube n → u x = u' x := (ae_restrict_iff' measurableSet_cube).1 hue
  -- local constancy of `Z` in the chamber
  have hloc : ∀ x0 ∈ UC n, ∃ B, IsOpen B ∧ x0 ∈ B ∧ B ⊆ UC n ∧
      ((∀ᵐ y ∂volume.restrict B, y ∈ Z) ∨ (∀ᵐ y ∂volume.restrict B, y ∉ Z)) := by
    intro x0 hx0
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_UC x0 hx0
    set R := δ / 4
    have hR : 0 < R := by positivity
    have hR2 : 2 * R < δ := by simp only [R]; linarith
    have hP : closedBall x0 (2 * R) ⊆ UC n :=
      (closedBall_subset_ball hR2).trans hball
    have hL := logData_ball hΨ (by positivity) hP
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
  -- transfer from `u'` to `u` in the chamber
  have hUc : ∀ᵐ x ∂volume.restrict (UC n), u x = u' x :=
    (ae_restrict_iff' measurableSet_UC).2 (by filter_upwards [hv] with x hx hxU using hx hxU.1)
  have hsym : ∀ (q : ℝ → Prop) σ x, q (u (pm σ x)) ↔ q (u x) := fun q σ x => by
    simp only [u, PhiB_pm]
  rcases null_or_conull_of_local isPreconnected_UC hloc with h | h
  · exfalso
    have h0 : ∀ᵐ x ∂μN n, u x = 0 := ae_of_ae_chamber (hsym (· = 0)) (by
      filter_upwards [h, hUc] with x hx he
      simp only [Z, mem_ofPred_eq] at hx
      rw [he, hx])
    have hz : ∀ᵐ x ∂μN n, Ψ x * Ψ x = 0 := by
      filter_upwards [h0, PhiB_ae_eq_abs hΨ.1] with x h1 h2
      have : |Ψ x| = 0 := h2 ▸ h1
      rw [abs_eq_zero.1 this, mul_zero]
    exact hΨ.2.1.ne' (integral_eq_zero_of_ae hz)
  · have h0 : ∀ᵐ x ∂μN n, u x ≠ 0 := ae_of_ae_chamber (hsym (· ≠ 0)) (by
      filter_upwards [h, hUc] with x hx he
      simp only [Z, mem_ofPred_eq] at hx
      rwa [he])
    filter_upwards [h0, PhiB_ae_eq_abs hΨ.1] with x h1 h2
    have : |Ψ x| ≠ 0 := h2 ▸ h1
    exact abs_ne_zero.1 this

end ucp

variable {w : Cfg n → ℝ} {hw : Continuous w}

/-- **Unique continuation for fermionic `H¹₀` ground states.** -/
theorem ucpW_fer (w : Cfg n → ℝ) (hw : Continuous w) : UcpW .fer n w hw :=
  fun _ _ hΨ => gs_ne_zero_W_fer hΨ

/-- **Hohenberg–Kohn on `H¹₀` for fermions with continuous potentials.** For every continuous
one-body potential `v` and continuous interaction `w`, ground states exist, and ground states of
`v` and `v'` with the same norm and density force `v - v'` to be constant. -/
theorem hk_line_W_cont_fer (v v' : Pot) :
    (∃ Φ, IsGS (settingW .fer n w hw) v Φ) ∧ ∀ Ψ Ψ', IsGS (settingW .fer n w hw) v Ψ →
      IsGS (settingW .fer n w hw) v' Ψ' → ip (μ := μN n) Ψ Ψ = ip (μ := μN n) Ψ' Ψ' →
      dens (settingW .fer n w hw) Ψ = dens (settingW .fer n w hw) Ψ' →
        ∃ k : ℝ, v - v' = k • one :=
  hk_line_W_cont (ucpW_fer w hw) v v'

end DFT.Continuum.Line
