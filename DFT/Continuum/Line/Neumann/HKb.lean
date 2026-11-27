/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Neumann.HKa
import DFT.Continuum.Line.Neumann.Pos

/-!
# The pair-density term for smooth states

For a `C²` symmetric state `X` of `N = m + 2 ≥ 2` particles and a `C¹` function `g`, the mixed
density of `X` and `X Σ_k g(x_k)` is `g ρ_X` plus a pair-density term. Against an `H⁻¹` potential
`D`, written as `D(e) = α e(0) + ∫ β e'` (Riesz), the pair term is `∫ g R_X` with an explicit
`R_X` (**`D_smooth`**).

* `hQ F j t u = ∫ F(t, (u in slot j, z)) dz`; `continuous_hQ`, `abs_hQ_le`.
* `mF_mulG`: `∫ F(t, y) Σ_j g(y_j) dy = Σ_j ∫ g(u) hQ F j t u du`.
* `D_apply`: the Riesz form of `D`; `LgD`: the functional `e ↦ D(g e)`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n m : ℕ}

/-! ### Compactness bounds -/

lemma exists_bound_cubeC {F : Cfg n → ℝ} (hF : Continuous F) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ CubeC n, |F x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ => isCompact_Icc :
    IsCompact (CubeC n)).exists_bound_of_continuousOn hF.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

lemma mem_cubeC_cons_ins {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    {z : Fin m → ℝ} (hz : z ∈ Cube' m) (j : Fin (m + 1)) :
    (Fin.cons t (Fin.insertNth j u z) : Cfg (m + 1)) ∈ CubeC (m + 1) := by
  intro i _
  refine Fin.cases ?_ (fun i' => ?_) i
  · simpa using ht
  · simp only [Fin.cons_succ]
    rcases Fin.eq_self_or_eq_succAbove j i' with rfl | ⟨l, rfl⟩
    · simpa using hu
    · simp only [Fin.insertNth_apply_succAbove]
      exact Ioo_subset_Icc_self (hz l trivial)

lemma mem_cubeC_cons {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {y : Fin (n + 1) → ℝ}
    (hy : y ∈ Cube' (n + 1)) : (Fin.cons t y : Cfg (n + 1)) ∈ CubeC (n + 1) := by
  intro i _
  refine Fin.cases ?_ (fun i' => ?_) i
  · simpa using ht
  · simpa using Ioo_subset_Icc_self (hy i' trivial)

/-! ### Continuity of marginals -/

lemma continuous_mF {F : Cfg n → ℝ} (hF : Continuous F) : Continuous (mF F) := by
  have hae : Cube' n =ᵐ[volume] Icc (0 : Fin n → ℝ) 1 :=
    Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin n => (volume : Measure ℝ)) (f := 0) (g := 1)
  have e : ∀ t, mF F t = ∫ y in Icc (0 : Fin n → ℝ) 1, F (Fin.cons t y) :=
    fun t => setIntegral_congr_set hae
  rw [show mF F = fun t => ∫ y in Icc (0 : Fin n → ℝ) 1, F (Fin.cons t y) from funext e]
  exact continuous_parametric_integral_of_continuous
    (f := fun (t : ℝ) (y : Fin n → ℝ) => F (Fin.cons t y)) (by fun_prop) isCompact_Icc

/-! ### The pair functions -/

/-- `hQ F j t u = ∫ F(t, (u in slot j, z)) dz`. -/
noncomputable def hQ (F : Cfg (m + 1) → ℝ) (j : Fin (m + 1)) (t u : ℝ) : ℝ :=
  ∫ z in Cube' m, F (Fin.cons t (Fin.insertNth j u z))

lemma continuous_hQ {F : Cfg (m + 1) → ℝ} (hF : Continuous F) (j : Fin (m + 1)) :
    Continuous fun p : ℝ × ℝ => hQ F j p.1 p.2 := by
  have hae : Cube' m =ᵐ[volume] Icc (0 : Fin m → ℝ) 1 :=
    Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ)) (f := 0) (g := 1)
  have e : ∀ p : ℝ × ℝ, hQ F j p.1 p.2 =
      ∫ z in Icc (0 : Fin m → ℝ) 1, F (Fin.cons p.1 (Fin.insertNth j p.2 z)) :=
    fun p => setIntegral_congr_set hae
  simp only [e]
  exact continuous_parametric_integral_of_continuous
    (f := fun (p : ℝ × ℝ) (z : Fin m → ℝ) => F (Fin.cons p.1 (Fin.insertNth j p.2 z)))
    (by fun_prop) isCompact_Icc

lemma abs_hQ_le {F : Cfg (m + 1) → ℝ} {C : ℝ} (hC : ∀ x ∈ CubeC (m + 1), |F x| ≤ C)
    (j : Fin (m + 1)) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    |hQ F j t u| ≤ C := by
  rw [hQ, ← Real.norm_eq_abs]
  calc ‖∫ z in Cube' m, F (Fin.cons t (Fin.insertNth j u z))‖
      ≤ C * (volume.restrict (Cube' m)).real univ :=
        norm_integral_le_of_norm_le_const ((ae_restrict_mem (MeasurableSet.univ_pi
          fun _ => measurableSet_Ioo)).mono fun z hz => by
            rw [Real.norm_eq_abs]; exact hC _ (mem_cubeC_cons_ins ht hu hz j))
    _ = C := by simp [measureReal_def, volume_cube']

/-- Continuous functions are integrable on `Cube' m × (0, 1)`. -/
lemma integrable_cube'_Ioo {F : (Fin m → ℝ) × ℝ → ℝ} (hF : Continuous F) :
    Integrable F ((volume.restrict (Cube' m)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  exact (hF.continuousOn.integrableOn_compact ((isCompact_univ_pi fun _ => isCompact_Icc).prod
    isCompact_Icc)).mono_set (prod_mono (pi_mono fun _ _ => Ioo_subset_Icc_self)
      Ioo_subset_Icc_self)

/-- **The pair term in coordinates**: `∫ F(t, y) Σ_j g(y_j) dy = Σ_j ∫ g(u) hQ F j t u du`. -/
lemma mF_mulG {F : Cfg (m + 1) → ℝ} (hF : Continuous F) {g : ℝ → ℝ} (hg : Continuous g)
    (t : ℝ) : mF (fun x => F x * ∑ j : Fin (m + 1), g (x j.succ)) t =
      ∑ j : Fin (m + 1), ∫ u, g u * hQ F j t u ∂vol01 := by
  rw [mF]
  simp only [Fin.cons_succ]
  have hint : ∀ j : Fin (m + 1), IntegrableOn (fun y : Fin (m + 1) → ℝ =>
      F (Fin.cons t y) * g (y j)) (Cube' (m + 1)) := fun j =>
    integrableOn_cube' (by fun_prop)
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : Continuous fun y : Cfg m => F (Fin.cons t y) * g (y j) := by fun_prop
  change ∫ y, F (Fin.cons t y) * g (y j) ∂μN m = _
  rw [integral_cube_insertNth hc j]
  simp only [Fin.insertNth_apply_same]
  have hFi := integrable_cube'_Ioo (m := m) (F := Function.uncurry fun (z : Fin m → ℝ) (u : ℝ) =>
    F (Fin.cons t (Fin.insertNth j u z)) * g u) (by fun_prop)
  rw [integral_integral_swap hFi]
  refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  rw [hQ, ← integral_const_mul]
  congr 1; funext z; ring

/-! ### The Riesz form of an `H⁻¹` potential -/

lemma D_apply (D : PotH) (e : H1E) :
    D e = ((InnerProductSpace.toDual ℝ H1E).symm D).fst * fnE e 0 +
      ∫ t, ((InnerProductSpace.toDual ℝ H1E).symm D).snd t * e.snd t ∂vol01 := by
  rw [← InnerProductSpace.toDual_symm_apply, WithLp.prod_inner_apply, L2.inner_def]
  simp only [fnE, prim_zero, add_zero, Real.inner_apply]
  ring_nf
  rfl

/-- The functional `e ↦ D(g · e)`. -/
noncomputable def LgD (D : PotH) (g : ℝ → ℝ) (e : H1E) : ℝ :=
  ((InnerProductSpace.toDual ℝ H1E).symm D).fst * (g 0 * fnE e 0) +
    ∫ t, ((InnerProductSpace.toDual ℝ H1E).symm D).snd t *
      (deriv g t * fnE e t + g t * e.snd t) ∂vol01

/-- A continuous function a.e. equal to `fnE e` agrees with it on `[0, 1]`. -/
lemma fnE_eq_of_ae {e : H1E} {f : ℝ → ℝ} (hf : Continuous f) (h : fnE e =ᵐ[vol01] f) :
    ∀ t ∈ Icc (0 : ℝ) 1, fnE e t = f t := by
  have hIoo : EqOn (fnE e) f (Ioo 0 1) :=
    Measure.eqOn_of_ae_eq h ((continuousOn_fnE e).mono Ioo_subset_Icc_self) hf.continuousOn
      (by rw [interior_Ioo]; exact subset_closure)
  exact fun t ht => hIoo.of_subset_closure (continuousOn_fnE e) hf.continuousOn
    Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one]) ht

/-! ### The identity for smooth states -/

section smooth

variable {τ : Stat}

/-- **The pair density of `D` against a smooth state `X`.** -/
noncomputable def RfD (D : PotH) (X : Cfg (m + 1) → ℝ) (u : ℝ) : ℝ :=
  ((↑(m + 1) : ℝ) + 1) * ∑ j : Fin (m + 1),
    (((InnerProductSpace.toDual ℝ H1E).symm D).fst * hQ (fun x => X x * X x) j 0 u +
      ∫ t, ((InnerProductSpace.toDual ℝ H1E).symm D).snd t *
        hQ (dk 0 (fun x => X x * X x)) j t u ∂vol01)

/-- The mixed density of a smooth state with its product by `FF g`, as an element with the
integrals of `N mF (X² FF g)`. -/
lemma int_rhoE2_FF {X : Cfg (m + 1) → ℝ} (hX : X ∈ DomN τ (m + 1)) (hX1 : ContDiff ℝ 1 X)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (u : C01) :
    ∫ t, iccExt u t * iccExt (evE (rhoE2 τ X (fun x => FF g x * X x))) t ∂vol01 =
      ∫ t, iccExt u t * (((↑(m + 1) : ℝ) + 1) * mF (fun x => X x * X x * FF g x) t) ∂vol01 := by
  have hχ : (fun x => FF g x * X x) ∈ DomN τ (m + 1) :=
    ⟨memLp_mul_cont (contDiff_FF hg).continuous hX.1,
      fun k => ⟨_, (dWN_spec (hX.2.1 k)).mul_C1 hX.1 (contDiff_FF hg)⟩,
      fun σ _ => by
        filter_upwards [hX.2.2 σ trivial] with x hx
        simp only [FF_pm, hx]; ring⟩
  have hp : Continuous fun x => X x * X x * FF g x :=
    (hX1.continuous.mul hX1.continuous).mul (contDiff_FF hg).continuous
  have hsym : ∀ σ : Equiv.Perm (Fin (m + 1 + 1)), ∀ᵐ x ∂μN (m + 1),
      X (pm σ x) * X (pm σ x) * FF g (pm σ x) = X x * X x * FF g x := fun σ => by
    filter_upwards [hX.2.2 σ trivial] with x hx
    have hc := ch_mul_self τ σ
    simp only [hx, FF_pm]
    change ch τ σ * X x * (ch τ σ * X x) * FF g x = _
    linear_combination (X x * X x * FF g x) * hc
  rw [int_rhoE2 hX hχ, int_mF (integrableN hp) hsym, pfN]
  congr 1; funext x; ring

end smooth

/-! ### Splitting off the one-body part -/

lemma integrable_mF_cont {F : Cfg n → ℝ} (hF : Continuous F) (t : ℝ) :
    IntegrableOn (fun y : Fin n → ℝ => F (Fin.cons t y)) (Cube' n) :=
  integrableOn_cube' (by fun_prop)

lemma mF_add {F G : Cfg n → ℝ} (hF : Continuous F) (hG : Continuous G) (t : ℝ) :
    mF (fun x => F x + G x) t = mF F t + mF G t :=
  integral_add (integrable_mF_cont hF t) (integrable_mF_cont hG t)

lemma mF_mul_coord0 (F : Cfg n → ℝ) (a : ℝ → ℝ) (t : ℝ) :
    mF (fun x => F x * a (x 0)) t = a t * mF F t := by
  simp only [mF, Fin.cons_zero]
  rw [integral_mul_const, mul_comm]

lemma mF_FF_split {F : Cfg (m + 1) → ℝ} (hF : Continuous F) {g : ℝ → ℝ} (hg : Continuous g)
    (t : ℝ) : mF (fun x => F x * FF g x) t =
      g t * mF F t + mF (fun x => F x * ∑ j : Fin (m + 1), g (x j.succ)) t := by
  have e : (fun x : Cfg (m + 1) => F x * FF g x) =
      fun x => F x * g (x 0) + F x * ∑ j : Fin (m + 1), g (x j.succ) := funext fun x => by
    rw [show x = Fin.cons (x 0) (Fin.tail x) from (Fin.cons_self_tail x).symm, FF_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]; ring
  rw [e, mF_add (F := fun x => F x * g (x 0)) (G := fun x => F x * ∑ j : Fin (m + 1), g (x j.succ))
    (hF.mul (hg.comp (continuous_apply 0)))
    (hF.mul (continuous_finsetSum _ fun j _ => hg.comp (continuous_apply _))), mF_mul_coord0]

lemma continuous_int_hQ {F : Cfg (m + 1) → ℝ} (hF : Continuous F) {g : ℝ → ℝ}
    (hg : Continuous g) (j : Fin (m + 1)) :
    Continuous fun t => ∫ u, g u * hQ F j t u ∂vol01 := by
  have e : ∀ t, ∫ u, g u * hQ F j t u ∂vol01 = ∫ u in Icc (0 : ℝ) 1, g u * hQ F j t u :=
    fun t => setIntegral_congr_set Ioo_ae_eq_Icc
  rw [show (fun t => ∫ u, g u * hQ F j t u ∂vol01) = fun t => ∫ u in Icc (0 : ℝ) 1,
    g u * hQ F j t u from funext e]
  exact continuous_parametric_integral_of_continuous
    (f := fun (t u : ℝ) => g u * hQ F j t u)
    ((hg.comp continuous_snd).mul (continuous_hQ hF j)) isCompact_Icc

/-- Fubini for `∫ β(t) ∫ g(u) hQ(t, u)`. -/
lemma swap_beta {β : ℝ → ℝ} (hβ : Integrable β vol01) {F : Cfg (m + 1) → ℝ} (hF : Continuous F)
    {g : ℝ → ℝ} (hg : Continuous g) (j : Fin (m + 1)) :
    ∫ t, β t * ∫ u, g u * hQ F j t u ∂vol01 ∂vol01 = ∫ u, g u * ∫ t, β t * hQ F j t u ∂vol01 ∂vol01 := by
  obtain ⟨CF, -, hCF⟩ := exists_bound_cubeC hF
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.continuousOn (s := Icc (0 : ℝ) 1))
  have hb : ∀ᵐ z ∂(vol01.prod vol01), ‖g z.2 * hQ F j z.1 z.2‖ ≤ Cg * CF := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    rw [norm_mul, Real.norm_eq_abs (hQ F j z.1 z.2)]
    exact mul_le_mul (hCg _ (Ioo_subset_Icc_self hz.2))
      (abs_hQ_le hCF j (Ioo_subset_Icc_self hz.1) (Ioo_subset_Icc_self hz.2))
      (abs_nonneg _) ((norm_nonneg _).trans (hCg _ (Ioo_subset_Icc_self hz.2)))
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => g z.2 * hQ F j z.1 z.2) (vol01.prod vol01) :=
    ((hg.comp continuous_snd).mul (continuous_hQ hF j)).aestronglyMeasurable
  have hint : Integrable (fun z : ℝ × ℝ => β z.1 * (g z.2 * hQ F j z.1 z.2)) (vol01.prod vol01) := by
    have h1 := (hβ.mul_prod (integrable_const (1 : ℝ) (μ := vol01))).bdd_mul hm hb
    refine h1.congr (ae_of_all _ fun z => ?_)
    simp only [mul_one]; ring
  have e1 : ∫ t, β t * ∫ u, g u * hQ F j t u ∂vol01 ∂vol01 =
      ∫ t, ∫ u, β t * (g u * hQ F j t u) ∂vol01 ∂vol01 :=
    integral_congr_ae (ae_of_all _ fun t => (integral_const_mul _ _).symm)
  have e2 : ∫ u, g u * ∫ t, β t * hQ F j t u ∂vol01 ∂vol01 =
      ∫ u, ∫ t, β t * (g u * hQ F j t u) ∂vol01 ∂vol01 :=
    integral_congr_ae (ae_of_all _ fun u => by
      show g u * ∫ t, β t * hQ F j t u ∂vol01 = ∫ t, β t * (g u * hQ F j t u) ∂vol01
      rw [← integral_const_mul]; congr 1; funext t; ring)
  rw [e1, e2]
  exact integral_integral_swap (f := fun t u => β t * (g u * hQ F j t u)) hint

/-- **The identity for smooth states**: `D(ρ(X, X FF g)) = D(g ρ_X) + ∫ g R_X`. -/
theorem D_smooth (D : PotH) {τ : Stat} {X : Cfg (m + 1) → ℝ} (hX : X ∈ DomN τ (m + 1))
    (hX2 : ContDiff ℝ 2 X) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    D (rhoE2 τ X (fun x => FF g x * X x)) = LgD D g (rhoE τ X) + ∫ u, g u * RfD D X u ∂vol01 := by
  set α := ((InnerProductSpace.toDual ℝ H1E).symm D).fst
  set β := ((InnerProductSpace.toDual ℝ H1E).symm D).snd
  have hβi : Integrable (β : ℝ → ℝ) vol01 := integrable_L2I β
  set N : ℝ := (↑(m + 1) : ℝ) + 1
  have hX1 : ContDiff ℝ 1 X := hX2.of_le (by norm_num)
  set p0 : Cfg (m + 1) → ℝ := fun x => X x * X x
  have hp0 : ContDiff ℝ 1 p0 := hX1.mul hX1
  set p : Cfg (m + 1) → ℝ := fun x => X x * X x * FF g x
  have hp : ContDiff ℝ 1 p := hp0.mul (contDiff_FF hg)
  have hgc := hg.continuous
  have hgd : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hdp0 : Continuous (dk 0 p0) := continuous_dk_of_C1 hp0 0
  -- marginal formulas
  set e := rhoE2 τ X (fun x => FF g x * X x)
  obtain ⟨hf, hs⟩ := snd_marg (memLp_cont hp.continuous) (isWDN_of_C1 hp 0)
    (int_rhoE2_FF hX hX1 hg)
  have hsym0 : ∀ σ : Equiv.Perm (Fin (m + 1 + 1)), ∀ᵐ x ∂μN (m + 1), p0 (pm σ x) = p0 x :=
    fun σ => by
      filter_upwards [hX.2.2 σ trivial] with x hx
      have hc := ch_mul_self τ σ
      simp only [p0, hx]
      linear_combination (X x * X x) * hc
  have he0 : ∀ u : C01, ∫ t, iccExt u t * iccExt (evE (rhoE τ X)) t ∂vol01 =
      ∫ t, iccExt u t * (N * mF p0 t) ∂vol01 := fun u => by
    rw [int_rhoE hX, int_mF (integrableN hp0.continuous) hsym0]; rfl
  obtain ⟨hf0, hs0⟩ := snd_marg (memLp_cont hp0.continuous) (isWDN_of_C1 hp0 0) he0
  have hv0 : fnE e 0 = N * mF p 0 :=
    fnE_eq_of_ae (continuous_const.mul (continuous_mF hp.continuous)) hf 0 ⟨le_rfl, zero_le_one⟩
  have hvρ : ∀ t ∈ Icc (0 : ℝ) 1, fnE (rhoE τ X) t = N * mF p0 t :=
    fnE_eq_of_ae (continuous_const.mul (continuous_mF hp0.continuous)) hf0
  -- the splits
  set G : ℝ → ℝ := fun t => mF (fun x => p0 x * ∑ j : Fin (m + 1), g (x j.succ)) t
  set GD : ℝ → ℝ := fun t => mF (fun x => dk 0 p0 x * ∑ j : Fin (m + 1), g (x j.succ)) t
  have hsp : ∀ t, mF p t = g t * mF p0 t + G t := mF_FF_split hp0.continuous hgc
  have hsd : ∀ t, mF (dk 0 p) t = g t * mF (dk 0 p0) t + GD t + deriv g t * mF p0 t := by
    intro t
    have e1 : dk 0 p = fun x => dk 0 p0 x * FF g x + p0 x * deriv g (x 0) := funext fun x => by
      have := dk_mul (hp0.differentiable one_ne_zero)
        ((contDiff_FF hg).differentiable one_ne_zero) 0 x
      rw [show p = fun x => p0 x * FF g x from rfl, this, dk_FF (hg.differentiable one_ne_zero)]
      ring
    rw [e1, mF_add (F := fun x => dk 0 p0 x * FF g x) (G := fun x => p0 x * deriv g (x 0))
      (hdp0.mul (contDiff_FF hg).continuous)
      (hp0.continuous.mul (hgd.comp (continuous_apply 0))), mF_FF_split hdp0 hgc, mF_mul_coord0]
  have hG : ∀ t, G t = ∑ j : Fin (m + 1), ∫ u, g u * hQ p0 j t u ∂vol01 :=
    mF_mulG hp0.continuous hgc
  have hGD : ∀ t, GD t = ∑ j : Fin (m + 1), ∫ u, g u * hQ (dk 0 p0) j t u ∂vol01 :=
    mF_mulG hdp0 hgc
  -- the two sides
  have hcd : Continuous (mF (dk 0 p)) := continuous_mF (continuous_dk_of_C1 hp 0)
  have hD : D e = α * (N * mF p 0) + ∫ t, β t * (N * mF (dk 0 p) t) ∂vol01 := by
    rw [D_apply, hv0]
    congr 1
    exact integral_congr_ae (by filter_upwards [hs] with t ht; rw [ht])
  have hL : LgD D g (rhoE τ X) = α * (g 0 * (N * mF p0 0)) +
      ∫ t, β t * (deriv g t * (N * mF p0 t) + g t * (N * mF (dk 0 p0) t)) ∂vol01 := by
    rw [LgD, hvρ 0 ⟨le_rfl, zero_le_one⟩]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hs0, ae_restrict_mem measurableSet_Ioo] with t ht hti
    rw [ht, hvρ t (Ioo_subset_Icc_self hti)]
  -- integrability
  have hc1 : Continuous fun t => deriv g t * (N * mF p0 t) + g t * (N * mF (dk 0 p0) t) :=
    (hgd.mul (continuous_const.mul (continuous_mF hp0.continuous))).add
      (hgc.mul (continuous_const.mul (continuous_mF hdp0)))
  have hcGD : Continuous GD := continuous_mF (hdp0.mul
    (continuous_finsetSum _ fun j _ => hgc.comp (continuous_apply _)))
  have iA : Integrable (fun t => β t * (N * mF (dk 0 p) t)) vol01 :=
    integrable_mul_cont1 hβi (continuous_const.mul hcd)
  have iB : Integrable (fun t => β t * (deriv g t * (N * mF p0 t) +
      g t * (N * mF (dk 0 p0) t))) vol01 := integrable_mul_cont1 hβi hc1
  have hdiff : D e - LgD D g (rhoE τ X) = α * (N * G 0) + ∫ t, β t * (N * GD t) ∂vol01 := by
    rw [hD, hL]
    have h1 : ∫ t, β t * (N * mF (dk 0 p) t) ∂vol01 -
        ∫ t, β t * (deriv g t * (N * mF p0 t) + g t * (N * mF (dk 0 p0) t)) ∂vol01 =
        ∫ t, β t * (N * GD t) ∂vol01 := by
      rw [← integral_sub iA iB]
      congr 1; funext t; rw [hsd t]; ring
    rw [hsp 0]
    linarith

  -- the pair term as `∫ g R`
  have hR : α * (N * G 0) + ∫ t, β t * (N * GD t) ∂vol01 = ∫ u, g u * RfD D X u ∂vol01 := by
    have hQ0i : ∀ j : Fin (m + 1), Integrable (fun u => g u * hQ p0 j 0 u) vol01 := fun j =>
      integrable_cont_mu1 (hgc.mul ((continuous_hQ hp0.continuous j).comp
        (Continuous.prodMk continuous_const continuous_id)))
    have hQDi : ∀ j : Fin (m + 1), Integrable (fun u => g u * ∫ t, β t * hQ (dk 0 p0) j t u ∂vol01)
        vol01 := fun j => by
      obtain ⟨CF, -, hCF⟩ := exists_bound_cubeC hdp0
      obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (hgc.continuousOn (s := Icc (0 : ℝ) 1))
      have hmeas : AEStronglyMeasurable (fun u => ∫ t, β t * hQ (dk 0 p0) j t u ∂vol01) vol01 := by
        have hint : Integrable (fun z : ℝ × ℝ => β z.1 * hQ (dk 0 p0) j z.1 z.2) (vol01.prod vol01) := by
          have hb : ∀ᵐ z ∂(vol01.prod vol01), ‖hQ (dk 0 p0) j z.1 z.2‖ ≤ CF := by
            rw [Measure.prod_restrict]
            filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
            rw [Real.norm_eq_abs]
            exact abs_hQ_le hCF j (Ioo_subset_Icc_self hz.1) (Ioo_subset_Icc_self hz.2)
          have h1 := (hβi.mul_prod (integrable_const (1 : ℝ) (μ := vol01))).bdd_mul
            (continuous_hQ hdp0 j).aestronglyMeasurable hb
          refine h1.congr (ae_of_all _ fun z => ?_)
          simp only [mul_one]; ring
        exact hint.integral_prod_right.aestronglyMeasurable
      refine Integrable.of_bound (hgc.aestronglyMeasurable.mul hmeas) (Cg * (CF * ∫ t, |β t| ∂vol01))
        ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      rw [norm_mul]
      refine mul_le_mul (hCg u (Ioo_subset_Icc_self hu)) ?_ (norm_nonneg _)
        ((norm_nonneg _).trans (hCg u (Ioo_subset_Icc_self hu)))
      rw [Real.norm_eq_abs]
      calc |∫ t, β t * hQ (dk 0 p0) j t u ∂vol01| ≤ ∫ t, |β t| * CF ∂vol01 := by
            rw [← Real.norm_eq_abs]
            refine norm_integral_le_of_norm_le (hβi.abs.mul_const _) ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left
              (abs_hQ_le hCF j (Ioo_subset_Icc_self ht) (Ioo_subset_Icc_self hu)) (abs_nonneg _)
        _ = CF * ∫ t, |β t| ∂vol01 := by rw [integral_mul_const, mul_comm]
    have hIc : ∀ j : Fin (m + 1), Continuous fun t => ∫ u, g u * hQ (dk 0 p0) j t u ∂vol01 :=
      fun j => continuous_int_hQ hdp0 hgc j
    have e1 : ∫ t, β t * (N * GD t) ∂vol01 =
        ∑ j : Fin (m + 1), N * ∫ u, g u * ∫ t, β t * hQ (dk 0 p0) j t u ∂vol01 ∂vol01 := by
      simp only [hGD, Finset.mul_sum]
      rw [integral_finsetSum (f := fun j t => β t * (N * ∫ u, g u * hQ (dk 0 p0) j t u ∂vol01))
        _ fun j _ => integrable_mul_cont1 hβi (continuous_const.mul (hIc j))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← swap_beta hβi hdp0 hgc j, ← integral_const_mul]
      congr 1; funext t; ring
    have hpt : ∀ u, g u * RfD D X u = ∑ j : Fin (m + 1), (N * α * (g u * hQ p0 j 0 u) +
        N * (g u * ∫ t, β t * hQ (dk 0 p0) j t u ∂vol01)) := fun u => by
      simp only [RfD, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [p0, α, β, N]; ring
    have e2 : ∫ u, g u * RfD D X u ∂vol01 = ∑ j : Fin (m + 1), (N * α * ∫ u, g u * hQ p0 j 0 u ∂vol01 +
        N * ∫ u, g u * ∫ t, β t * hQ (dk 0 p0) j t u ∂vol01 ∂vol01) := by
      simp only [hpt]
      rw [integral_finsetSum (f := fun j u => N * α * (g u * hQ p0 j 0 u) +
        N * (g u * ∫ t, β t * hQ (dk 0 p0) j t u ∂vol01))
        _ fun j _ => ((hQ0i j).const_mul _).add ((hQDi j).const_mul _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_add ((hQ0i j).const_mul _) ((hQDi j).const_mul _), integral_const_mul,
        integral_const_mul]
    rw [e1, e2, hG 0, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have := hdiff.trans hR
  linarith

/-! ### The `L¹` estimate for the pair densities -/

/-- `∫ |hQ F j t · - hQ F' j t ·| ≤ ∫ |F - F'|(t, y) dy`. -/
lemma integral_abs_hQ_sub_le {F F' : Cfg (m + 1) → ℝ} (hF : Continuous F) (hF' : Continuous F')
    (j : Fin (m + 1)) (t : ℝ) :
    ∫ u, |hQ F j t u - hQ F' j t u| ∂vol01 ≤ ∫ y in Cube' (m + 1), |F (Fin.cons t y) - F' (Fin.cons t y)| := by
  have hpt : ∀ u, |hQ F j t u - hQ F' j t u| ≤
      ∫ z in Cube' m, |F (Fin.cons t (Fin.insertNth j u z)) -
        F' (Fin.cons t (Fin.insertNth j u z))| := fun u => by
    rw [hQ, hQ, ← integral_sub (integrableOn_cube' (by fun_prop))
      (integrableOn_cube' (by fun_prop))]
    exact abs_integral_le_integral_abs
  have hc : Continuous fun y : Cfg m => |F (Fin.cons t y) - F' (Fin.cons t y)| := by fun_prop
  have hFi := integrable_cube'_Ioo (m := m) (F := Function.uncurry fun (z : Fin m → ℝ) (u : ℝ) =>
    |F (Fin.cons t (Fin.insertNth j u z)) - F' (Fin.cons t (Fin.insertNth j u z))|) (by fun_prop)
  have hR : ∫ y in Cube' (m + 1), |F (Fin.cons t y) - F' (Fin.cons t y)| =
      ∫ u in Ioo (0 : ℝ) 1, ∫ z in Cube' m, |F (Fin.cons t (Fin.insertNth j u z)) -
        F' (Fin.cons t (Fin.insertNth j u z))| := by
    change ∫ y, |F (Fin.cons t y) - F' (Fin.cons t y)| ∂μN m = _
    rw [integral_cube_insertNth hc j, integral_integral_swap hFi]
  rw [hR]
  have hi1 : Integrable (fun u => |hQ F j t u - hQ F' j t u|) vol01 :=
    integrable_cont_mu1 (((continuous_hQ hF j).comp (Continuous.prodMk continuous_const
      continuous_id)).sub ((continuous_hQ hF' j).comp (Continuous.prodMk continuous_const
        continuous_id))).abs
  exact integral_mono hi1 hFi.integral_prod_right hpt

/-- Cauchy–Schwarz on `(0, 1)`. -/
lemma integral_abs_mul_le_mu1 {a b : ℝ → ℝ} (ha : MemLp a 2 vol01) (hb : MemLp b 2 vol01) :
    ∫ t, |a t * b t| ∂vol01 ≤ √(∫ t, a t ^ 2 ∂vol01) * √(∫ t, b t ^ 2 ∂vol01) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := vol01) Real.HolderConjugate.two_two
    (f := fun t => |a t|) (g := fun t => |b t|)
    (ae_of_all _ fun t => abs_nonneg _) (ae_of_all _ fun t => abs_nonneg _)
    (by rw [ENNReal.ofReal_ofNat]; exact ha.abs) (by rw [ENNReal.ofReal_ofNat]; exact hb.abs)
  have e1 : (∫ t, |a t| ^ (2 : ℝ) ∂vol01) = ∫ t, a t ^ 2 ∂vol01 := by
    congr 1; funext t; rw [Real.rpow_two, sq_abs]
  have e2 : (∫ t, |b t| ^ (2 : ℝ) ∂vol01) = ∫ t, b t ^ 2 ∂vol01 := by
    congr 1; funext t; rw [Real.rpow_two, sq_abs]
  rw [e1, e2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  calc ∫ t, |a t * b t| ∂vol01 = ∫ t, |a t| * |b t| ∂vol01 := by congr 1; funext t; rw [abs_mul]
    _ ≤ _ := h

section est

variable {τ : Stat}

/-- For a `C¹` state, `N ∫ X(t, y)² dy` is the continuous density. -/
lemma mF_sq_eq {X : Cfg (m + 1) → ℝ} (hX : X ∈ DomN τ (m + 1)) (hX1 : ContDiff ℝ 1 X) :
    ∀ t ∈ Icc (0 : ℝ) 1, fnE (rhoE τ X) t = ((↑(m + 1) : ℝ) + 1) * mF (fun x => X x * X x) t := by
  have hp0 : ContDiff ℝ 1 fun x => X x * X x := hX1.mul hX1
  have hsym0 : ∀ σ : Equiv.Perm (Fin (m + 1 + 1)), ∀ᵐ x ∂μN (m + 1),
      X (pm σ x) * X (pm σ x) = X x * X x := fun σ => by
    filter_upwards [hX.2.2 σ trivial] with x hx
    have hc := ch_mul_self τ σ
    rw [hx]; linear_combination (X x * X x) * hc
  have he0 : ∀ u : C01, ∫ t, iccExt u t * iccExt (evE (rhoE τ X)) t ∂vol01 =
      ∫ t, iccExt u t * (((↑(m + 1) : ℝ) + 1) * mF (fun x => X x * X x) t) ∂vol01 := fun u => by
    rw [int_rhoE hX, int_mF (integrableN hp0.continuous) hsym0]; rfl
  obtain ⟨hf0, -⟩ := snd_marg (memLp_cont hp0.continuous) (isWDN_of_C1 hp0 0) he0
  exact fnE_eq_of_ae (continuous_const.mul (continuous_mF hp0.continuous)) hf0

lemma fnE_rhoE_le (X : Cfg (m + 1) → ℝ) (hX : X ∈ DomN τ (m + 1)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : fnE (rhoE τ X) t ≤ 2 * SHN X := by
  rw [rhoE, sqE, fnE_toE _ ht]
  have h1 := sq_le_H1N (h1N_gNH (τ := τ) X) one_pos ht
  rw [integral_gNH_sq hX] at h1
  have h2 := kinM_gNH_le hX
  have : 0 ≤ ∫ x, X x ^ 2 ∂μN (m + 1) := integral_nonneg fun _ => sq_nonneg _
  rw [div_one] at h1
  have e : gNH τ X t * gNH τ X t = gNH τ X t ^ 2 := (sq _).symm
  simp only [SHN]
  linarith [kinN_nonneg X]

lemma mF_sq_le {X : Cfg (m + 1) → ℝ} (hX : X ∈ DomN τ (m + 1)) (hX1 : ContDiff ℝ 1 X) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : mF (fun x => X x * X x) t ≤ 2 * SHN X := by
  have h1 := mF_sq_eq hX hX1 t ht
  have h2 := fnE_rhoE_le X hX ht
  have h0 : 0 ≤ mF (fun x => X x * X x) t := integral_nonneg fun _ => mul_self_nonneg _
  have hN : (1 : ℝ) ≤ (↑(m + 1) : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (m + 1); linarith
  nlinarith

lemma integral_mF_dk_sq_le {X : Cfg (m + 1) → ℝ} (hX1 : ContDiff ℝ 1 X) :
    ∫ t, mF (fun x => dk 0 X x * dk 0 X x) t ∂vol01 ≤ kinN X := by
  have hd := continuous_dk_of_C1 hX1 0
  have hc : ∫ t, mF (fun x => dk 0 X x * dk 0 X x) t ∂vol01 =
      ∫ x, dk 0 X x * dk 0 X x ∂μN (m + 1) :=
    (integral_cube_cons' (F := fun x => dk 0 X x * dk 0 X x) (integrableN (hd.mul hd))).symm
  rw [hc]
  have hk : ∀ k, ∫ x, dWN k X x * dWN k X x ∂μN (m + 1) = ∫ x, dk k X x * dk k X x ∂μN (m + 1) :=
    fun k => integral_congr_ae (by
      filter_upwards [dWN_ae_eq (isWDN_of_C1 hX1 k)] with x hx; rw [hx])
  calc ∫ x, dk 0 X x * dk 0 X x ∂μN (m + 1) = ∫ x, dWN 0 X x * dWN 0 X x ∂μN (m + 1) :=
        (hk 0).symm
    _ ≤ kinN X := Finset.single_le_sum (f := fun k => ∫ x, dWN k X x * dWN k X x ∂μN (m + 1))
        (fun k _ => integral_nonneg fun _ => mul_self_nonneg _) (Finset.mem_univ 0)

end est

/-- Fubini with absolute values for the `β` part. -/
lemma int_beta_abs_le {β : ℝ → ℝ} (hβ : Integrable β vol01) {F F' : Cfg (m + 1) → ℝ}
    (hF : Continuous F) (hF' : Continuous F') (j : Fin (m + 1)) :
    Integrable (fun u => ∫ t, |β t| * |hQ F j t u - hQ F' j t u| ∂vol01) vol01 ∧
    ∫ u, ∫ t, |β t| * |hQ F j t u - hQ F' j t u| ∂vol01 ∂vol01 ≤
      ∫ t, |β t| * mF (fun x => |F x - F' x|) t ∂vol01 := by
  obtain ⟨CF, -, hCF⟩ := exists_bound_cubeC hF
  obtain ⟨CF', -, hCF'⟩ := exists_bound_cubeC hF'
  have hc : Continuous fun z : ℝ × ℝ => |hQ F j z.1 z.2 - hQ F' j z.1 z.2| :=
    ((continuous_hQ hF j).sub (continuous_hQ hF' j)).abs
  have hb : ∀ᵐ z ∂(vol01.prod vol01), ‖|hQ F j z.1 z.2 - hQ F' j z.1 z.2|‖ ≤ CF + CF' := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_hQ_le hCF j (Ioo_subset_Icc_self hz.1) (Ioo_subset_Icc_self hz.2)
    have h2 := abs_hQ_le hCF' j (Ioo_subset_Icc_self hz.1) (Ioo_subset_Icc_self hz.2)
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hint : Integrable (fun z : ℝ × ℝ => |β z.1| * |hQ F j z.1 z.2 - hQ F' j z.1 z.2|)
      (vol01.prod vol01) := by
    have h1 := (hβ.abs.mul_prod (integrable_const (1 : ℝ) (μ := vol01))).bdd_mul
      hc.aestronglyMeasurable hb
    refine h1.congr (ae_of_all _ fun z => ?_)
    simp only [mul_one]; ring
  refine ⟨hint.integral_prod_right, ?_⟩
  rw [← integral_integral_swap (f := fun t u => |β t| * |hQ F j t u - hQ F' j t u|) hint]
  have hmc : Continuous (mF fun x => |F x - F' x|) := continuous_mF (hF.sub hF').abs
  refine integral_mono_of_nonneg (ae_of_all _ fun t => integral_nonneg fun _ => by positivity)
    (integrable_mul_cont1 hβ.abs hmc) ?_
  filter_upwards with t
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_abs_hQ_sub_le hF hF' j t) (abs_nonneg _)

section cauchy

variable {τ : Stat}

lemma sqrt_mF_memLp {F : Cfg n → ℝ} (hF : Continuous F) :
    MemLp (fun t => √(mF F t)) 2 vol01 :=
  (memLp_two_iff_integrable_sq ((continuous_mF hF).sqrt).aestronglyMeasurable).2
    (integrable_cont_mu1 (((continuous_mF hF).sqrt).pow 2))

/-- `∫ |X² - Y²|(t, y) dy ≤ √(mF (X - Y)² · mF (X + Y)²)`. -/
lemma mF_abs_sq_sub_le {X Y : Cfg (m + 1) → ℝ} (hX : Continuous X) (hY : Continuous Y) (t : ℝ) :
    mF (fun x => |X x * X x - Y x * Y x|) t ≤
      √(mF (fun x => (X x - Y x) * (X x - Y x)) t * mF (fun x => (X x + Y x) * (X x + Y x)) t) := by
  have h := integral_abs_mul_le (n := m + 1) (a := fun y => X (Fin.cons t y) - Y (Fin.cons t y))
    (b := fun y => X (Fin.cons t y) + Y (Fin.cons t y)) (by fun_prop) (by fun_prop)
  calc mF (fun x => |X x * X x - Y x * Y x|) t
      = ∫ y in Cube' (m + 1), |(X (Fin.cons t y) - Y (Fin.cons t y)) *
          (X (Fin.cons t y) + Y (Fin.cons t y))| := by
        simp only [mF]; congr 1; funext y; ring_nf
    _ ≤ _ := h
    _ = _ := by
        simp only [mF]
        congr 2
        · congr 1; funext y; ring
        · congr 1; funext y; ring

/-- `∫ |∂(X²) - ∂(Y²)|(t, y) dy` by the two Cauchy–Schwarz terms. -/
lemma mF_abs_dsq_sub_le {X Y : Cfg (m + 1) → ℝ} (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y)
    (t : ℝ) : mF (fun x => |dk 0 (fun x => X x * X x) x - dk 0 (fun x => Y x * Y x) x|) t ≤
      2 * √(mF (fun x => (X x - Y x) * (X x - Y x)) t * mF (fun x => dk 0 X x * dk 0 X x) t) +
      2 * √(mF (fun x => Y x * Y x) t *
        mF (fun x => dk 0 (fun x => X x - Y x) x * dk 0 (fun x => X x - Y x) x) t) := by
  have hdX := continuous_dk_of_C1 hX 0
  have hdY := continuous_dk_of_C1 hY 0
  have hdXY : ∀ x, dk 0 (fun x => X x - Y x) x = dk 0 X x - dk 0 Y x := fun x => by
    simp only [dk]
    rw [show (fun x => X x - Y x) = X - Y from rfl,
      fderiv_sub ((hX.differentiable one_ne_zero) x) ((hY.differentiable one_ne_zero) x)]
    rfl
  have hdsq : ∀ (Z : Cfg (m + 1) → ℝ), ContDiff ℝ 1 Z → ∀ x,
      dk 0 (fun x => Z x * Z x) x = 2 * (Z x * dk 0 Z x) := fun Z hZ x => by
    rw [dk_mul (hZ.differentiable one_ne_zero) (hZ.differentiable one_ne_zero)]; ring
  have hpt : ∀ x, |dk 0 (fun x => X x * X x) x - dk 0 (fun x => Y x * Y x) x| ≤
      2 * |(X x - Y x) * dk 0 X x| + 2 * |Y x * dk 0 (fun x => X x - Y x) x| := fun x => by
    rw [hdsq X hX, hdsq Y hY, hdXY]
    calc |2 * (X x * dk 0 X x) - 2 * (Y x * dk 0 Y x)|
        = |2 * ((X x - Y x) * dk 0 X x) + 2 * (Y x * (dk 0 X x - dk 0 Y x))| := by ring_nf
      _ ≤ |2 * ((X x - Y x) * dk 0 X x)| + |2 * (Y x * (dk 0 X x - dk 0 Y x))| := abs_add_le _ _
      _ = _ := by
          rw [abs_mul (2 : ℝ) ((X x - Y x) * dk 0 X x), abs_mul (2 : ℝ), abs_two]
  have hc1 : Continuous fun x => (X x - Y x) * dk 0 X x := (hX.continuous.sub hY.continuous).mul hdX
  have hdXYc : Continuous (dk 0 (fun x => X x - Y x)) := continuous_dk_of_C1 (hX.sub hY) 0
  have hc2 : Continuous fun x => Y x * dk 0 (fun x => X x - Y x) x :=
    hY.continuous.mul hdXYc
  have hcons : Continuous fun y : Fin (m + 1) → ℝ => (Fin.cons t y : Cfg (m + 1)) := by fun_prop
  have h1 := integral_abs_mul_le (n := m + 1) (a := fun y => X (Fin.cons t y) - Y (Fin.cons t y))
    (b := fun y => dk 0 X (Fin.cons t y)) (by fun_prop) (hdX.comp hcons)
  have h2 := integral_abs_mul_le (n := m + 1) (a := fun y => Y (Fin.cons t y))
    (b := fun y => dk 0 (fun x => X x - Y x) (Fin.cons t y)) (by fun_prop) (hdXYc.comp hcons)
  calc mF (fun x => |dk 0 (fun x => X x * X x) x - dk 0 (fun x => Y x * Y x) x|) t
      ≤ mF (fun x => 2 * |(X x - Y x) * dk 0 X x| + 2 * |Y x * dk 0 (fun x => X x - Y x) x|) t :=
        setIntegral_mono_on (integrable_mF_cont (by
          exact ((continuous_dk_of_C1 (hX.mul hX) 0).sub (continuous_dk_of_C1 (hY.mul hY) 0)).abs) t)
          (integrable_mF_cont ((continuous_const.mul hc1.abs).add (continuous_const.mul hc2.abs)) t)
          (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) fun y _ => hpt _
    _ = 2 * mF (fun x => |(X x - Y x) * dk 0 X x|) t +
        2 * mF (fun x => |Y x * dk 0 (fun x => X x - Y x) x|) t := by
        rw [mF_add (F := fun x => 2 * |(X x - Y x) * dk 0 X x|)
          (G := fun x => 2 * |Y x * dk 0 (fun x => X x - Y x) x|)
          (continuous_const.mul hc1.abs) (continuous_const.mul hc2.abs)]
        simp only [mF, integral_const_mul]
    _ ≤ _ := by
        gcongr
        · simp only [mF]; convert h1 using 3 <;> (try funext y) <;> ring_nf
        · simp only [mF]; convert h2 using 3 <;> (try funext y) <;> ring_nf

end cauchy

section cauchy2

variable {τ : Stat}

lemma continuous_hQ_left {F : Cfg (m + 1) → ℝ} (hF : Continuous F) (j : Fin (m + 1)) (u : ℝ) :
    Continuous fun t => hQ F j t u :=
  (continuous_hQ hF j).comp (Continuous.prodMk continuous_id continuous_const)

/-- `∫ |β| √b ≤ ‖β‖ √(∫ b)`. -/
lemma int_abs_mul_sqrt_le {β : ℝ → ℝ} (hβ : MemLp β 2 vol01) {b : ℝ → ℝ} (hb : Continuous b)
    (hb0 : ∀ t, 0 ≤ b t) :
    ∫ t, |β t| * √(b t) ∂vol01 ≤ √(∫ t, β t ^ 2 ∂vol01) * √(∫ t, b t ∂vol01) := by
  have hm : MemLp (fun t => √(b t)) 2 vol01 :=
    (memLp_two_iff_integrable_sq hb.sqrt.aestronglyMeasurable).2 (integrable_cont_mu1 (hb.sqrt.pow 2))
  have h := integral_abs_mul_le_mu1 hβ hm
  have e1 : ∫ t, |β t * √(b t)| ∂vol01 = ∫ t, |β t| * √(b t) ∂vol01 := by
    congr 1; funext t; rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have e2 : ∫ t, √(b t) ^ 2 ∂vol01 = ∫ t, b t ∂vol01 := by
    congr 1; funext t; rw [Real.sq_sqrt (hb0 t)]
  rw [e1, e2] at h; exact h

/-- **The pair densities of nearby smooth states are `L¹`-close.** -/
theorem integral_abs_RfD_sub_le (D : PotH) {X Y : Cfg (m + 1) → ℝ} (hX : X ∈ DomN τ (m + 1))
    (hY : Y ∈ DomN τ (m + 1)) (hX1 : ContDiff ℝ 1 X) (hY1 : ContDiff ℝ 1 Y) :
    ∫ u, |RfD D X u - RfD D Y u| ∂vol01 ≤
      ((↑(m + 1) : ℝ) + 1) * (m + 1) *
        ((2 * |((InnerProductSpace.toDual ℝ H1E).symm D).fst| +
          3 * √(∫ t, ((InnerProductSpace.toDual ℝ H1E).symm D).snd t ^ 2 ∂vol01)) *
        (√(SHN (X - Y)) * (√(SHN (X + Y)) + √(SHN X) + √(SHN Y)))) := by
  set α := ((InnerProductSpace.toDual ℝ H1E).symm D).fst
  set β := ((InnerProductSpace.toDual ℝ H1E).symm D).snd
  have hβi : Integrable (β : ℝ → ℝ) vol01 := integrable_L2I β
  set N : ℝ := (↑(m + 1) : ℝ) + 1
  have hN : 0 ≤ N := by positivity
  set nb := √(∫ t, β t ^ 2 ∂vol01)
  set Sm := SHN (X - Y)
  set Sp := SHN (X + Y)
  have hSm := SHN_nonneg (X - Y)
  -- the two families of functions
  set FX : Cfg (m + 1) → ℝ := fun x => X x * X x
  set FY : Cfg (m + 1) → ℝ := fun x => Y x * Y x
  set GX : Cfg (m + 1) → ℝ := dk 0 FX
  set GY : Cfg (m + 1) → ℝ := dk 0 FY
  have hFX : Continuous FX := hX1.continuous.mul hX1.continuous
  have hFY : Continuous FY := hY1.continuous.mul hY1.continuous
  have hGX : Continuous GX := continuous_dk_of_C1 (hX1.mul hX1) 0
  have hGY : Continuous GY := continuous_dk_of_C1 (hY1.mul hY1) 0
  -- pointwise bound
  have hβQ : ∀ (F : Cfg (m + 1) → ℝ), Continuous F → ∀ j u,
      Integrable (fun t => β t * hQ F j t u) vol01 := fun F hF j u =>
    integrable_mul_cont1 hβi (continuous_hQ_left hF j u)
  set U : ℝ → ℝ := fun u => N * ∑ j : Fin (m + 1), (|α| * |hQ FX j 0 u - hQ FY j 0 u| +
    ∫ t, |β t| * |hQ GX j t u - hQ GY j t u| ∂vol01)
  have hpt : ∀ u, |RfD D X u - RfD D Y u| ≤ U u := fun u => by
    simp only [RfD, U, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (↑(m + 1) : ℝ) + 1)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)) hN
    have e : α * hQ FX j 0 u + ∫ t, β t * hQ GX j t u ∂vol01 -
        (α * hQ FY j 0 u + ∫ t, β t * hQ GY j t u ∂vol01) =
        α * (hQ FX j 0 u - hQ FY j 0 u) + ∫ t, β t * (hQ GX j t u - hQ GY j t u) ∂vol01 := by
      have hi : ∫ t, β t * (hQ GX j t u - hQ GY j t u) ∂vol01 =
          ∫ t, β t * hQ GX j t u ∂vol01 - ∫ t, β t * hQ GY j t u ∂vol01 := by
        rw [← integral_sub (hβQ GX hGX j u) (hβQ GY hGY j u)]; simp only [mul_sub]
      rw [hi]; ring
    change |α * hQ FX j 0 u + ∫ t, β t * hQ GX j t u ∂vol01 -
        (α * hQ FY j 0 u + ∫ t, β t * hQ GY j t u ∂vol01)| ≤ _
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) ?_)
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext t; rw [Real.norm_eq_abs, abs_mul]
  -- integrability of the upper function
  have hU0 : ∀ j : Fin (m + 1), Integrable (fun u => |hQ FX j 0 u - hQ FY j 0 u|) vol01 := fun j =>
    integrable_cont_mu1 (((continuous_hQ hFX j).comp (Continuous.prodMk continuous_const
      continuous_id)).sub ((continuous_hQ hFY j).comp (Continuous.prodMk continuous_const
        continuous_id))).abs
  have hU1 : ∀ j : Fin (m + 1), Integrable (fun u => ∫ t, |β t| * |hQ GX j t u - hQ GY j t u| ∂vol01)
      vol01 := fun j => (int_beta_abs_le hβi hGX hGY j).1
  have hUi : Integrable U vol01 :=
    (integrable_finsetSum _ fun j _ => ((hU0 j).const_mul _).add (hU1 j)).const_mul _
  have h1 : ∫ u, |RfD D X u - RfD D Y u| ∂vol01 ≤ ∫ u, U u ∂vol01 :=
    integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hUi (ae_of_all _ hpt)
  -- the bound on `∫ U`
  set A0 := mF (fun x => |FX x - FY x|) 0
  set B := ∫ t, |β t| * mF (fun x => |GX x - GY x|) t ∂vol01
  have h2 : ∫ u, U u ∂vol01 ≤ N * (m + 1) * (|α| * A0 + B) := by
    simp only [U]
    rw [integral_const_mul, integral_finsetSum (f := fun j u => |α| * |hQ FX j 0 u - hQ FY j 0 u| +
      ∫ t, |β t| * |hQ GX j t u - hQ GY j t u| ∂vol01) _ fun j _ => ((hU0 j).const_mul _).add (hU1 j)]
    have hj : ∀ j : Fin (m + 1), ∫ u, (|α| * |hQ FX j 0 u - hQ FY j 0 u| +
        ∫ t, |β t| * |hQ GX j t u - hQ GY j t u| ∂vol01) ∂vol01 ≤ |α| * A0 + B := fun j => by
      rw [integral_add ((hU0 j).const_mul _) (hU1 j), integral_const_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (integral_abs_hQ_sub_le hFX hFY j 0)
        (abs_nonneg _)) (int_beta_abs_le hβi hGX hGY j).2
    calc N * ∑ j : Fin (m + 1), ∫ u, (|α| * |hQ FX j 0 u - hQ FY j 0 u| +
          ∫ t, |β t| * |hQ GX j t u - hQ GY j t u| ∂vol01) ∂vol01
        ≤ N * ∑ _j : Fin (m + 1), (|α| * A0 + B) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hj j) hN
      _ = N * (m + 1) * (|α| * A0 + B) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  -- `A0`
  have hXmY : X - Y ∈ DomN τ (m + 1) := sub_mem hX hY
  have hXpY : X + Y ∈ DomN τ (m + 1) := add_mem hX hY
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hA0 : A0 ≤ 2 * √Sm * √Sp := by
    have h := mF_abs_sq_sub_le hX1.continuous hY1.continuous 0
    have ha := mF_sq_le hXmY (hX1.sub hY1) h01
    have hb := mF_sq_le hXpY (hX1.add hY1) h01
    calc A0 ≤ √(mF (fun x => (X x - Y x) * (X x - Y x)) 0 *
          mF (fun x => (X x + Y x) * (X x + Y x)) 0) := h
      _ ≤ √(2 * Sm * (2 * Sp)) := Real.sqrt_le_sqrt (mul_le_mul ha hb
          (integral_nonneg fun _ => mul_self_nonneg _) (by have := SHN_nonneg (X - Y); positivity))
      _ = 2 * √Sm * √Sp := by
          rw [show 2 * Sm * (2 * Sp) = 2 ^ 2 * (Sm * Sp) by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by norm_num), Real.sqrt_mul hSm]; ring
  -- `B`
  set a1 : ℝ → ℝ := mF (fun x => (X x - Y x) * (X x - Y x))
  set b1 : ℝ → ℝ := mF (fun x => dk 0 X x * dk 0 X x)
  set a2 : ℝ → ℝ := mF (fun x => Y x * Y x)
  set b2 : ℝ → ℝ := mF (fun x => dk 0 (fun x => X x - Y x) x * dk 0 (fun x => X x - Y x) x)
  have hdX := continuous_dk_of_C1 hX1 0
  have hdXY := continuous_dk_of_C1 (hX1.sub hY1) 0
  have hb1c : Continuous b1 := continuous_mF (hdX.mul hdX)
  have hb2c : Continuous b2 := continuous_mF (hdXY.mul hdXY)
  have hb10 : ∀ t, 0 ≤ b1 t := fun t => integral_nonneg fun _ => mul_self_nonneg _
  have hb20 : ∀ t, 0 ≤ b2 t := fun t => integral_nonneg fun _ => mul_self_nonneg _
  have hSY := SHN_nonneg Y
  have hB1 : B ≤ ∫ t, |β t| * (2 * √(2 * Sm) * √(b1 t) + 2 * √(2 * SHN Y) * √(b2 t)) ∂vol01 := by
    refine integral_mono_of_nonneg (ae_of_all _ fun t => by
      simp only [Pi.zero_apply]; exact mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _))
      (integrable_mul_cont1 hβi.abs (((continuous_const.mul hb1c.sqrt)).add
        (continuous_const.mul hb2c.sqrt))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htI := Ioo_subset_Icc_self ht
    refine mul_le_mul_of_nonneg_left ((mF_abs_dsq_sub_le hX1 hY1 t).trans ?_) (abs_nonneg _)
    have ha1 := mF_sq_le hXmY (hX1.sub hY1) htI
    have ha2 := mF_sq_le hY hY1 htI
    have ha10 : 0 ≤ a1 t := integral_nonneg fun _ => mul_self_nonneg _
    have ha20 : 0 ≤ a2 t := integral_nonneg fun _ => mul_self_nonneg _
    have k1 : √(a1 t * b1 t) ≤ √(2 * Sm) * √(b1 t) := by
      rw [Real.sqrt_mul ha10]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ha1) (Real.sqrt_nonneg _)
    have k2 : √(a2 t * b2 t) ≤ √(2 * SHN Y) * √(b2 t) := by
      rw [Real.sqrt_mul ha20]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ha2) (Real.sqrt_nonneg _)
    change 2 * √(a1 t * b1 t) + 2 * √(a2 t * b2 t) ≤ _
    linarith
  have hβL : MemLp (β : ℝ → ℝ) 2 vol01 := Lp.memLp β
  have hC1 := int_abs_mul_sqrt_le hβL hb1c hb10
  have hC2 := int_abs_mul_sqrt_le hβL hb2c hb20
  have hib1 : ∫ t, b1 t ∂vol01 ≤ SHN X := (integral_mF_dk_sq_le hX1).trans (by
    simp only [SHN]; have : (0 : ℝ) ≤ (↑(m + 1) + 1) * ∫ x, X x ^ 2 ∂μN (m + 1) := by
      have : 0 ≤ ∫ x, X x ^ 2 ∂μN (m + 1) := integral_nonneg fun x => sq_nonneg _
      positivity
    linarith)
  have hib2 : ∫ t, b2 t ∂vol01 ≤ Sm := (integral_mF_dk_sq_le (hX1.sub hY1)).trans (by
    simp only [Sm, SHN]
    have : (0 : ℝ) ≤ (↑(m + 1) + 1) * ∫ x, (X - Y) x ^ 2 ∂μN (m + 1) := by
      have : 0 ≤ ∫ x, (X - Y) x ^ 2 ∂μN (m + 1) := integral_nonneg fun x => sq_nonneg _
      positivity
    have e : kinN (fun x => X x - Y x) = kinN (X - Y) := rfl
    linarith)
  have hB : B ≤ 3 * nb * (√Sm * (√(SHN X) + √(SHN Y))) := by
    have i1 := integrable_mul_cont1 hβi.abs hb1c.sqrt
    have i2 := integrable_mul_cont1 hβi.abs hb2c.sqrt
    have e : ∫ t, |β t| * (2 * √(2 * Sm) * √(b1 t) + 2 * √(2 * SHN Y) * √(b2 t)) ∂vol01 =
        2 * √(2 * Sm) * ∫ t, |β t| * √(b1 t) ∂vol01 + 2 * √(2 * SHN Y) * ∫ t, |β t| * √(b2 t) ∂vol01 := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
        (i2.const_mul _)]
      congr 1; funext t; ring
    have hs2 : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hnb := Real.sqrt_nonneg (∫ t, β t ^ 2 ∂vol01)
    have k1 : 2 * √(2 * Sm) * ∫ t, |β t| * √(b1 t) ∂vol01 ≤ 3 * nb * (√Sm * √(SHN X)) := by
      calc 2 * √(2 * Sm) * ∫ t, |β t| * √(b1 t) ∂vol01
          ≤ 2 * √(2 * Sm) * (nb * √(SHN X)) :=
            mul_le_mul_of_nonneg_left (hC1.trans (mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt hib1) hnb)) (by positivity)
        _ = 2 * √2 * nb * (√Sm * √(SHN X)) := by rw [Real.sqrt_mul (by norm_num)]; ring
        _ ≤ 3 * nb * (√Sm * √(SHN X)) := by
            have : 0 ≤ nb * (√Sm * √(SHN X)) := by positivity
            nlinarith
    have k2 : 2 * √(2 * SHN Y) * ∫ t, |β t| * √(b2 t) ∂vol01 ≤ 3 * nb * (√Sm * √(SHN Y)) := by
      calc 2 * √(2 * SHN Y) * ∫ t, |β t| * √(b2 t) ∂vol01
          ≤ 2 * √(2 * SHN Y) * (nb * √Sm) :=
            mul_le_mul_of_nonneg_left (hC2.trans (mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt hib2) hnb)) (by positivity)
        _ = 2 * √2 * nb * (√Sm * √(SHN Y)) := by rw [Real.sqrt_mul (by norm_num)]; ring
        _ ≤ 3 * nb * (√Sm * √(SHN Y)) := by
            have : 0 ≤ nb * (√Sm * √(SHN Y)) := by positivity
            nlinarith
    linarith [hB1, e ▸ hB1]
  -- combine
  have hX0 := Real.sqrt_nonneg (SHN X)
  have hY0 := Real.sqrt_nonneg (SHN Y)
  have hp0 := Real.sqrt_nonneg Sp
  have hm0 := Real.sqrt_nonneg Sm
  have hnb := Real.sqrt_nonneg (∫ t, β t ^ 2 ∂vol01)
  calc ∫ u, |RfD D X u - RfD D Y u| ∂vol01 ≤ N * (m + 1) * (|α| * A0 + B) := h1.trans h2
    _ ≤ N * (m + 1) * (|α| * (2 * √Sm * √Sp) + 3 * nb * (√Sm * (√(SHN X) + √(SHN Y)))) := by
        gcongr
    _ ≤ _ := by
        have hNm : 0 ≤ N * (m + 1) := by positivity
        refine mul_le_mul_of_nonneg_left ?_ hNm
        have := abs_nonneg α
        nlinarith [mul_nonneg hm0 hp0, mul_nonneg hm0 hX0, mul_nonneg hm0 hY0,
          mul_nonneg hnb (mul_nonneg hm0 hp0), mul_nonneg this (mul_nonneg hm0 hX0),
          mul_nonneg this (mul_nonneg hm0 hY0)]

end cauchy2

end DFT.Continuum.Line
