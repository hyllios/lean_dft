/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.General.Lieb
import DFT.Continuum.Line.H1.Density

/-!
# The finite-kinetic-energy state space `H¹₀` on a line

The form domain `Dom τ n` of `Line/Basic` consists of `C²` functions. Lieb's characterisation of
`N`-representable densities needs all states of finite kinetic energy, i.e. the Sobolev space
`H¹₀` of the cube. Mathlib has no Sobolev spaces, so we define it directly by weak derivatives
with zero boundary values:

`G` is the weak `k`-th derivative of `Φ` (`IsWD k Φ G`) if `G ∈ L²` and
`∫ Φ ∂ₖφ = -∫ G φ` for **every** `C¹` function `φ` (not only those vanishing on the walls).

Testing against functions that do not vanish on the walls encodes `Φ = 0` there: for `C²` `Φ`
the boundary term of the integration by parts is `∫_{walls} Φ φ`. Equivalently, the extension of
`Φ` by zero has weak derivative `G` (extended by zero) on all of `ℝᴺ`.

* `IsWD`, `IsWD.add`, `IsWD.smul`, `IsWD.sum`, `IsWD.unique`: weak derivatives, their linearity
  and their uniqueness a.e. (fundamental lemma of the calculus of variations).
* `DomWS s`: `L²` functions with all `N` weak derivatives and symmetry type `s` (a.e.);
  `DomW τ n = DomWS τ.toSym` for bosons and fermions.
* `dW k Φ`: the weak derivative (a chosen representative).
* `settingWS s w hw`, `settingW τ n w hw = settingWS τ.toSym w hw`: the Hohenberg–Kohn setting,
  with kinetic energy
  `Σ_k ∫ |∂_k Φ|²` in the weak sense.
* `integral_cube_ins`: Fubini on the cube for integrable functions, splitting off particle `k`.
* `Dom_le_DomW`, `dW_ae_eq_dk`, `h0W_eq`: the `C²` states are `H¹₀` states, with the same
  derivatives and energies; `liebF_W_le`: so the Lieb functional on `H¹₀` is at most the one on
  `C²` states.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ} {τ : Stat}

instance : IsFiniteMeasure (μN n) :=
  isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top isCompact_cubeC.measure_lt_top.ne
    (measure_mono cube_subset))

/-- Continuous functions are bounded on the cube. -/
lemma ae_bound_cont {f : Cfg n → ℝ} (hf : Continuous f) : ∃ C, ∀ᵐ x ∂μN n, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_cubeC.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, (ae_restrict_mem measurableSet_cube).mono fun x hx => hC x (cube_subset hx)⟩

lemma memLp_cont {f : Cfg n → ℝ} (hf : Continuous f) : MemLp f 2 (μN n) := by
  obtain ⟨C, hC⟩ := ae_bound_cont hf
  exact MemLp.of_bound hf.aestronglyMeasurable C hC

/-- An `L²` function times a continuous function is integrable on the cube. -/
lemma int_mul_cont {Φ f : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) (hf : Continuous f) :
    Integrable (fun x => Φ x * f x) (μN n) := by
  obtain ⟨C, hC⟩ := ae_bound_cont hf
  exact (hΦ.integrable one_le_two).mul_bdd hf.aestronglyMeasurable hC

lemma int_mul_L2 {Φ Ψ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) (hΨ : MemLp Ψ 2 (μN n)) :
    Integrable (fun x => Φ x * Ψ x) (μN n) :=
  hΦ.integrable_mul hΨ

/-! ### Weak derivatives -/

/-- `G` is the weak `k`-th partial derivative of `Φ`, with zero boundary values. -/
def IsWD (k : Fin (n + 1)) (Φ G : Cfg n → ℝ) : Prop :=
  MemLp G 2 (μN n) ∧ ∀ φ : Cfg n → ℝ, ContDiff ℝ 1 φ →
    ∫ x, Φ x * dk k φ x ∂μN n = -∫ x, G x * φ x ∂μN n

lemma continuous_dk_of_C1 {φ : Cfg n → ℝ} (hφ : ContDiff ℝ 1 φ) (k : Fin (n + 1)) :
    Continuous (dk k φ) :=
  (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

namespace IsWD

variable {k : Fin (n + 1)} {Φ Ψ G H : Cfg n → ℝ}

lemma zero (k : Fin (n + 1)) : IsWD k (0 : Cfg n → ℝ) 0 :=
  ⟨MemLp.zero, fun φ _ => by simp⟩

lemma add (hΦ : MemLp Φ 2 (μN n)) (hΨ : MemLp Ψ 2 (μN n)) (hG : IsWD k Φ G) (hH : IsWD k Ψ H) :
    IsWD k (fun x => Φ x + Ψ x) (fun x => G x + H x) := by
  refine ⟨hG.1.add hH.1, fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ k
  have e1 : ∫ x, (Φ x + Ψ x) * dk k φ x ∂μN n =
      ∫ x, Φ x * dk k φ x ∂μN n + ∫ x, Ψ x * dk k φ x ∂μN n := by
    rw [← integral_add (int_mul_cont hΦ hd) (int_mul_cont hΨ hd)]
    congr 1; funext x; ring
  have e2 : ∫ x, (G x + H x) * φ x ∂μN n = ∫ x, G x * φ x ∂μN n + ∫ x, H x * φ x ∂μN n := by
    rw [← integral_add (int_mul_cont hG.1 hφ.continuous) (int_mul_cont hH.1 hφ.continuous)]
    congr 1; funext x; ring
  rw [e1, e2, hG.2 φ hφ, hH.2 φ hφ]; ring

lemma const_mul (c : ℝ) (hG : IsWD k Φ G) : IsWD k (fun x => c * Φ x) (fun x => c * G x) := by
  refine ⟨hG.1.const_mul c, fun φ hφ => ?_⟩
  have e1 : ∫ x, c * Φ x * dk k φ x ∂μN n = c * ∫ x, Φ x * dk k φ x ∂μN n := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have e2 : ∫ x, c * G x * φ x ∂μN n = c * ∫ x, G x * φ x ∂μN n := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [e1, e2, hG.2 φ hφ]; ring

lemma sum {ι : Type*} (s : Finset ι) {Φs Gs : ι → Cfg n → ℝ} (hΦ : ∀ i ∈ s, MemLp (Φs i) 2 (μN n))
    (hG : ∀ i ∈ s, IsWD k (Φs i) (Gs i)) :
    MemLp (fun x => ∑ i ∈ s, Φs i x) 2 (μN n) ∧
      IsWD k (fun x => ∑ i ∈ s, Φs i x) (fun x => ∑ i ∈ s, Gs i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨by exact MemLp.zero, by exact MemLp.zero, fun φ _ => by simp⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have ih' := ih (fun i hi => hΦ i (Finset.mem_insert_of_mem hi))
      (fun i hi => hG i (Finset.mem_insert_of_mem hi))
    have h1 := hΦ a (Finset.mem_insert_self a s)
    exact ⟨by exact h1.add ih'.1, add h1 ih'.1 (hG a (Finset.mem_insert_self a s)) ih'.2⟩

/-- **Uniqueness of weak derivatives** (a.e. on the cube). -/
lemma unique (hG : IsWD k Φ G) (hH : IsWD k Φ H) : G =ᵐ[μN n] H := by
  have hint : Integrable (fun x => G x - H x) (μN n) :=
    (hG.1.integrable one_le_two).sub (hH.1.integrable one_le_two)
  have h0 : ∀ φ : Cfg n → ℝ, ContDiff ℝ 1 φ → ∫ x, φ x * (G x - H x) ∂μN n = 0 := by
    intro φ hφ
    have a := hG.2 φ hφ
    have b := hH.2 φ hφ
    have e : ∫ x, φ x * (G x - H x) ∂μN n = ∫ x, G x * φ x ∂μN n - ∫ x, H x * φ x ∂μN n := by
      rw [← integral_sub (int_mul_cont hG.1 hφ.continuous) (int_mul_cont hH.1 hφ.continuous)]
      congr 1; funext x; ring
    rw [e]; linarith
  have h := isOpen_cube.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (f := fun x => G x - H x)
    ((show IntegrableOn (fun x => G x - H x) (Cube n) volume from hint).locallyIntegrableOn)
    (fun g hg _ hsupp => by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Cube n) fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h), zero_smul]]
      exact h0 g (hg.of_le (by exact_mod_cast le_top)))
  filter_upwards [(ae_restrict_iff' measurableSet_cube).2 h] with x hx
  exact sub_eq_zero.1 hx

end IsWD

/-- The weak derivative (a chosen representative; `0` if there is none). -/
noncomputable def dW (k : Fin (n + 1)) (Φ : Cfg n → ℝ) : Cfg n → ℝ :=
  open Classical in if h : ∃ G, IsWD k Φ G then h.choose else 0

lemma dW_spec {k : Fin (n + 1)} {Φ : Cfg n → ℝ} (h : ∃ G, IsWD k Φ G) : IsWD k Φ (dW k Φ) := by
  unfold dW
  split_ifs
  exact h.choose_spec

lemma dW_ae_eq {k : Fin (n + 1)} {Φ G : Cfg n → ℝ} (h : IsWD k Φ G) : dW k Φ =ᵐ[μN n] G :=
  (dW_spec ⟨G, h⟩).unique h

/-! ### The state space -/

/-- `H¹₀` states of symmetry type `s`: `L²` functions with all weak derivatives, with
`Φ(σx) = χ(σ) Φ(x)` a.e. for `σ ∈ G`. -/
def DomWS (s : Sine.SymT n) : Submodule ℝ (Cfg n → ℝ) where
  carrier := {Φ | MemLp Φ 2 (μN n) ∧ (∀ k, ∃ G, IsWD k Φ G) ∧
    ∀ σ, s.G σ → ∀ᵐ x ∂μN n, Φ (pm σ x) = s.χ σ * Φ x}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun k => by
      obtain ⟨G, hG⟩ := ha.2.1 k
      obtain ⟨H, hH⟩ := hb.2.1 k
      exact ⟨_, IsWD.add ha.1 hb.1 hG hH⟩,
    fun σ hσ => by
      filter_upwards [ha.2.2 σ hσ, hb.2.2 σ hσ] with x h1 h2
      simp only [Pi.add_apply, h1, h2]; ring⟩
  zero_mem' := ⟨MemLp.zero, fun k => ⟨0, IsWD.zero k⟩, fun σ _ => ae_of_all _ fun x => by simp⟩
  smul_mem' c a ha := ⟨ha.1.const_smul c, fun k => by
      obtain ⟨G, hG⟩ := ha.2.1 k
      exact ⟨_, IsWD.const_mul c hG⟩,
    fun σ hσ => by
      filter_upwards [ha.2.2 σ hσ] with x h1
      simp only [Pi.smul_apply, smul_eq_mul, h1]; ring⟩

/-- `H¹₀` states of exchange symmetry `τ`. -/
noncomputable abbrev DomW (τ : Stat) (n : ℕ) : Submodule ℝ (Cfg n → ℝ) := DomWS (n := n) τ.toSym

/-- `L²` functions with all weak first derivatives (zero boundary values), no symmetry. -/
def H1W (Φ : Cfg n → ℝ) : Prop := MemLp Φ 2 (μN n) ∧ ∀ k, ∃ G, IsWD k Φ G

lemma h1W_of_mem {s : Sine.SymT n} {Φ : Cfg n → ℝ} (h : Φ ∈ DomWS s) : H1W Φ := ⟨h.1, h.2.1⟩

section dom

variable {Φ Ψ : Cfg n → ℝ}

lemma memLp_dW_H (hΦ : H1W Φ) (k : Fin (n + 1)) : MemLp (dW k Φ) 2 (μN n) := (dW_spec (hΦ.2 k)).1

lemma dW_add_H (hΦ : H1W Φ) (hΨ : H1W Ψ) (k : Fin (n + 1)) :
    dW k (Φ + Ψ) =ᵐ[μN n] dW k Φ + dW k Ψ :=
  dW_ae_eq (IsWD.add hΦ.1 hΨ.1 (dW_spec (hΦ.2 k)) (dW_spec (hΨ.2 k)))

lemma dW_smul_H (hΦ : H1W Φ) (c : ℝ) (k : Fin (n + 1)) : dW k (c • Φ) =ᵐ[μN n] c • dW k Φ :=
  dW_ae_eq (IsWD.const_mul c (dW_spec (hΦ.2 k)))

variable {s : Sine.SymT n}

lemma memLp_dW (hΦ : Φ ∈ DomWS s) (k : Fin (n + 1)) : MemLp (dW k Φ) 2 (μN n) :=
  memLp_dW_H (h1W_of_mem hΦ) k

lemma dW_add (hΦ : Φ ∈ DomWS s) (hΨ : Ψ ∈ DomWS s) (k : Fin (n + 1)) :
    dW k (Φ + Ψ) =ᵐ[μN n] dW k Φ + dW k Ψ :=
  dW_add_H (h1W_of_mem hΦ) (h1W_of_mem hΨ) k

lemma dW_smul (hΦ : Φ ∈ DomWS s) (c : ℝ) (k : Fin (n + 1)) :
    dW k (c • Φ) =ᵐ[μN n] c • dW k Φ :=
  dW_smul_H (h1W_of_mem hΦ) c k

end dom

/-- The energy form on `H¹₀`: weak kinetic energy plus interaction `w`. -/
noncomputable def h0W (n : ℕ) (w : Cfg n → ℝ) (ψ φ : Cfg n → ℝ) : ℝ :=
  ∑ k, ∫ x, dW k ψ x * dW k φ x ∂μN n + ∫ x, w x * (ψ x * φ x) ∂μN n

/-- `N` particles with exchange symmetry `s` on a line, with all finite-kinetic-energy states. -/
noncomputable def settingWS (s : Sine.SymT n) (w : Cfg n → ℝ) (hw : Continuous w) :
    Setting (μN n) Pot where
  D := DomWS s
  h0 := h0W n w
  h0_add a ha b hb c hc := by
    have hk : ∀ k, ∫ x, dW k (a + b) x * dW k c x ∂μN n =
        ∫ x, dW k a x * dW k c x ∂μN n + ∫ x, dW k b x * dW k c x ∂μN n := fun k => by
      rw [← integral_add (int_mul_L2 (memLp_dW ha k) (memLp_dW hc k))
        (int_mul_L2 (memLp_dW hb k) (memLp_dW hc k))]
      refine integral_congr_ae ?_
      filter_upwards [dW_add ha hb k] with x hx
      simp only [hx, Pi.add_apply]; ring
    have hw' : ∫ x, w x * ((a + b) x * c x) ∂μN n =
        ∫ x, w x * (a x * c x) ∂μN n + ∫ x, w x * (b x * c x) ∂μN n := by
      obtain ⟨C, hC⟩ := ae_bound_cont hw
      rw [← integral_add ((int_mul_L2 ha.1 hc.1).bdd_mul hw.aestronglyMeasurable hC)
        ((int_mul_L2 hb.1 hc.1).bdd_mul hw.aestronglyMeasurable hC)]
      congr 1; funext x; simp only [Pi.add_apply]; ring
    simp only [h0W, hk, Finset.sum_add_distrib, hw']; ring
  h0_smul r a ha c hc := by
    have hk : ∀ k, ∫ x, dW k (r • a) x * dW k c x ∂μN n =
        r * ∫ x, dW k a x * dW k c x ∂μN n := fun k => by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [dW_smul ha r k] with x hx
      simp only [hx, Pi.smul_apply, smul_eq_mul]; ring
    have hw' : ∫ x, w x * ((r • a) x * c x) ∂μN n = r * ∫ x, w x * (a x * c x) ∂μN n := by
      rw [← integral_const_mul]; congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
    simp only [h0W, hk, ← Finset.mul_sum, hw']; ring
  h0_symm ψ _ φ _ := by
    simp only [h0W]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      congr 1; funext x; ring
    · congr 1; funext x; ring
  L := LN n
  int_L v ψ φ hψ hφ := by
    obtain ⟨C, hC⟩ := ae_bound_cont (continuous_LN (n := n) v)
    exact (int_mul_L2 hψ.1 hφ.1).bdd_mul (continuous_LN v).aestronglyMeasurable hC
  int_sq ψ φ hψ hφ := int_mul_L2 hψ.1 hφ.1

/-- `N` particles of statistics `τ` on a line, with all finite-kinetic-energy states. -/
noncomputable abbrev settingW (τ : Stat) (n : ℕ) (w : Cfg n → ℝ) (hw : Continuous w) :
    Setting (μN n) Pot :=
  settingWS (n := n) τ.toSym w hw

/-! ### Fubini, splitting off particle `k` -/

lemma insertNth_mem_cube (k : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    (Fin.insertNth k t y : Cfg n) ∈ Cube n ↔ t ∈ Ioo (0 : ℝ) 1 ∧ y ∈ Cube' n := by
  simp only [Set.mem_pi, mem_univ, true_implies]
  rw [Fin.forall_iff_succAbove k]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- **Fubini on the cube**, with particle `k` innermost. -/
lemma integral_cube_ins (k : Fin (n + 1)) {F : Cfg n → ℝ} (hF : Integrable F (μN n)) :
    ∫ x, F x ∂μN n = ∫ y in Cube' n, ∫ t in Ioo (0 : ℝ) 1, F (Fin.insertNth k t y) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k
  have he : MeasurePreserving e.symm (volume.prod volume) (volume : Measure (Cfg n)) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm
  have hcomp : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.insertNth k p.1 p.2 := by
    rintro ⟨t, y⟩; rfl
  have hpre : e.symm ⁻¹' Cube n = Ioo (0 : ℝ) 1 ×ˢ Cube' n := by
    ext ⟨t, y⟩
    simp only [mem_preimage, hcomp, mem_prod]
    exact insertNth_mem_cube k t y
  have h := he.setIntegral_preimage_emb e.symm.measurableEmbedding F (Cube n)
  rw [hpre] at h
  rw [← h, ← Measure.prod_restrict]
  simp only [hcomp]
  refine integral_prod_symm (fun p : ℝ × (Fin n → ℝ) => F (Fin.insertNth k p.1 p.2)) ?_
  have hr := he.restrict_preimage_emb e.symm.measurableEmbedding (Cube n)
  rw [hpre, ← Measure.prod_restrict] at hr
  have := (hr.integrable_comp_emb e.symm.measurableEmbedding).2 hF
  simpa [Function.comp_def, hcomp] using this

/-! ### `C²` states are `H¹₀` states -/

lemma hasDerivAt_ins {f : Cfg n → ℝ} (hf : Differentiable ℝ f) (k : Fin (n + 1))
    (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s => f (Fin.insertNth k s y)) (dk k f (Fin.insertNth k t y)) t := by
  simpa [Fin.update_insertNth] using hasDerivAt_slice hf (Fin.insertNth k t y) k t

lemma continuous_ins (k : Fin (n + 1)) (y : Fin n → ℝ) :
    Continuous fun s : ℝ => (Fin.insertNth k s y : Cfg n) :=
  continuous_pi fun i => by
    rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact continuous_id
    · simp only [Fin.insertNth_apply_succAbove]; exact continuous_const

lemma integral_Ioo_eq_interval {f : ℝ → ℝ} :
    ∫ t in Ioo (0 : ℝ) 1, f t = ∫ t in (0 : ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- Integration by parts in particle `k` for a `C²` state vanishing on the walls. -/
lemma isWD_dk {Φ : Cfg n → ℝ} (hΦ : Φ ∈ Dom τ n) (k : Fin (n + 1)) : IsWD k Φ (dk k Φ) := by
  refine ⟨memLp_cont (cont_dk hΦ k), fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ k
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  rw [integral_cube_ins (F := fun x => Φ x * dk k φ x) k (integrableN (hΦ.1.continuous.mul hd)),
    integral_cube_ins (F := fun x => dk k Φ x * φ x) k
      (integrableN ((cont_dk hΦ k).mul hφ.continuous)),
    ← integral_neg]
  refine setIntegral_congr_fun measurableSet_cube' fun y _ => ?_
  simp only [integral_Ioo_eq_interval]
  have hc : ∀ {g : Cfg n → ℝ}, Continuous g →
      IntervalIntegrable (fun t => g (Fin.insertNth k t y)) volume 0 1 := fun hg =>
    (hg.comp (continuous_ins k y)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t => Φ (Fin.insertNth k t y)) (v := fun t => φ (Fin.insertNth k t y))
    (fun t _ => hasDerivAt_ins (diffF hΦ) k y t) (fun t _ => hasDerivAt_ins hφd k y t)
    (hc (cont_dk hΦ k)) (hc hd)]
  have w0 : Φ (Fin.insertNth k 0 y) = 0 := hΦ.2.2 _ k (Or.inl (by simp))
  have w1 : Φ (Fin.insertNth k 1 y) = 0 := hΦ.2.2 _ k (Or.inr (by simp))
  rw [w0, w1]; ring

theorem Dom_le_DomW : Dom τ n ≤ DomW τ n := fun _ hΦ =>
  ⟨memLp_cont hΦ.1.continuous, fun k => ⟨_, isWD_dk hΦ k⟩,
    fun σ _ => ae_of_all _ fun x => hΦ.2.1 σ x⟩

lemma dW_ae_eq_dk {Φ : Cfg n → ℝ} (hΦ : Φ ∈ Dom τ n) (k : Fin (n + 1)) :
    dW k Φ =ᵐ[μN n] dk k Φ :=
  dW_ae_eq (isWD_dk hΦ k)

/-- On `C²` states the weak energy form is the classical one. -/
theorem h0W_eq {w : Cfg n → ℝ} {Φ Ψ : Cfg n → ℝ} (hΦ : Φ ∈ Dom τ n) (hΨ : Ψ ∈ Dom τ n) :
    h0W n w Φ Ψ = h0N n w Φ Ψ := by
  simp only [h0W, h0N]
  congr 1
  rw [integral_finsetSum (f := fun k x => dk k Φ x * dk k Ψ x) _
    fun k _ => integrableN ((cont_dk hΦ k).mul (cont_dk hΨ k))]
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  filter_upwards [dW_ae_eq_dk hΦ k, dW_ae_eq_dk hΨ k] with x h1 h2
  rw [h1, h2]

/-- The Lieb functional over all `H¹₀` states is at most the one over `C²` states. -/
theorem liebF_W_le {w : Cfg n → ℝ} {hw : Continuous w} (ρ : Pot → ℝ) :
    liebF (settingW τ n w hw) ρ ≤ liebF (setting τ n w hw) ρ := by
  refine iSup_mono fun v => EReal.sub_le_sub ?_ le_rfl
  refine le_iInf₂ fun ψ hψ => ?_
  have hψW : ψ ∈ Nst (settingW τ n w hw) := ⟨Dom_le_DomW hψ.1, hψ.2⟩
  refine (iInf₂_le ψ hψW).trans (le_of_eq ?_)
  congr 1
  change h0W n w ψ ψ + pf (settingW τ n w hw) v ψ ψ = h0N n w ψ ψ + pf (setting τ n w hw) v ψ ψ
  rw [h0W_eq hψ.1 hψ.1]
  rfl

end DFT.Continuum.Line
