/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.GroupTheory.Perm.Sign

/-!
# `N` fermions on a line

`N = n + 1` fermions on `[0, 1]` with hard walls, an interaction `w(x₀, …, xₙ)`, and a one-body
potential `v` acting as `Σₖ v(xₖ)`. The configuration space is the open cube `(0, 1)^N`; states
are `C²` functions that are antisymmetric under relabelling of the particles and vanish on the
walls. The kinetic energy is `∫ |∇ψ|²`.

* `pm σ x = x ∘ σ`: relabelling; it preserves Lebesgue measure and the cube (`integral_pm`).
* `DomF`: the fermionic form domain; `settingF`: the Hohenberg–Kohn setting.
* `sep_line`: separation, from the fundamental lemma with antisymmetrised test functions.
* `rigidL_line`: a continuous `v` with `Σₖ v(xₖ)` a.e. constant on the cube is constant.
* `dens_eq_of_marginal_line`: equal one-body densities `ρ(t) = ∫ ψ(t, y)² dy` give equal density
  functionals (Fubini, and symmetry of `ψ²`).
* `hk_line_of_ucp`: **Hohenberg–Kohn for `N` fermions on a line**, conditional on unique
  continuation of the ground state.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box

variable {n : ℕ}

/-- Configurations of `n + 1` particles on the line. -/
abbrev Cfg (n : ℕ) := Fin (n + 1) → ℝ

/-- The open cube `(0, 1)^(n+1)`. -/
abbrev Cube (n : ℕ) : Set (Cfg n) := Set.pi univ fun _ => Ioo (0 : ℝ) 1

/-- The closed cube. -/
abbrev CubeC (n : ℕ) : Set (Cfg n) := Set.pi univ fun _ => Icc (0 : ℝ) 1

/-- Lebesgue measure on the cube. -/
noncomputable abbrev μN (n : ℕ) : Measure (Cfg n) := volume.restrict (Cube n)

lemma isOpen_cube : IsOpen (Cube n) := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

lemma measurableSet_cube : MeasurableSet (Cube n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

lemma isCompact_cubeC : IsCompact (CubeC n) := isCompact_univ_pi fun _ => isCompact_Icc

lemma cube_subset : Cube n ⊆ CubeC n := pi_mono fun _ _ => Ioo_subset_Icc_self

lemma integrableN {F : Cfg n → ℝ} (hF : Continuous F) : Integrable F (μN n) :=
  (hF.continuousOn.integrableOn_compact isCompact_cubeC).mono_set cube_subset

/-! ### Relabelling of particles -/

/-- The sign of a permutation, as a real number. -/
noncomputable def sgn (σ : Equiv.Perm (Fin (n + 1))) : ℝ := ((Equiv.Perm.sign σ : ℤˣ) : ℤ)

lemma sgn_mul (σ τ : Equiv.Perm (Fin (n + 1))) : sgn (σ * τ) = sgn σ * sgn τ := by
  simp [sgn, Equiv.Perm.sign_mul]

lemma sgn_mul_self (σ : Equiv.Perm (Fin (n + 1))) : sgn σ * sgn σ = 1 := by
  rw [← sgn_mul]
  simp only [sgn, Equiv.Perm.sign_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

lemma sgn_inv (σ : Equiv.Perm (Fin (n + 1))) : sgn σ⁻¹ = sgn σ := by
  simp [sgn, Equiv.Perm.sign_inv]

lemma sgn_one : sgn (1 : Equiv.Perm (Fin (n + 1))) = 1 := by simp [sgn]

lemma sgn_swap {i j : Fin (n + 1)} (h : i ≠ j) : sgn (Equiv.swap i j) = -1 := by
  simp [sgn, Equiv.Perm.sign_swap h]

/-- Relabelling: `(pm σ x) i = x (σ i)`. -/
def pm (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : Cfg n := fun i => x (σ i)

@[simp] lemma pm_apply (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) (i : Fin (n + 1)) :
    pm σ x i = x (σ i) := rfl

lemma pm_mul (σ τ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : pm (σ * τ) x = pm τ (pm σ x) := rfl

lemma pm_one (x : Cfg n) : pm 1 x = x := rfl

lemma pm_inv_pm (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : pm σ⁻¹ (pm σ x) = x := by
  funext i; simp

lemma pm_pm_inv (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : pm σ (pm σ⁻¹ x) = x := by
  funext i; simp

lemma contDiff_pm (σ : Equiv.Perm (Fin (n + 1))) {m : WithTop ℕ∞} :
    ContDiff ℝ m (pm σ : Cfg n → Cfg n) :=
  contDiff_pi.2 fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (σ i)).contDiff

lemma continuous_pm (σ : Equiv.Perm (Fin (n + 1))) : Continuous (pm σ : Cfg n → Cfg n) :=
  continuous_pi fun i => continuous_apply (σ i)

lemma pm_mem_cube {σ : Equiv.Perm (Fin (n + 1))} {x : Cfg n} : pm σ x ∈ Cube n ↔ x ∈ Cube n := by
  simp only [Set.mem_pi, mem_univ, true_implies, pm_apply]
  exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩

/-- Relabelling as a measurable equivalence. -/
noncomputable def pmE (σ : Equiv.Perm (Fin (n + 1))) : Cfg n ≃ᵐ Cfg n :=
  MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℝ)

lemma coe_pmE (σ : Equiv.Perm (Fin (n + 1))) : ⇑(pmE σ) = pm σ := by
  funext x i
  simp [pmE, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr, pm]

lemma mp_pm (σ : Equiv.Perm (Fin (n + 1))) :
    MeasurePreserving (pm σ) (volume : Measure (Cfg n)) volume := by
  rw [← coe_pmE]
  exact volume_preserving_arrowCongr' σ.symm (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id volume)

/-- Relabelling preserves integrals over the cube. -/
lemma integral_pm (σ : Equiv.Perm (Fin (n + 1))) (F : Cfg n → ℝ) :
    ∫ x, F (pm σ x) ∂μN n = ∫ x, F x ∂μN n := by
  have h := (mp_pm σ).setIntegral_preimage_emb
    (by rw [← coe_pmE]; exact (pmE σ).measurableEmbedding) F (Cube n)
  have hpre : pm σ ⁻¹' Cube n = Cube n := by ext x; exact pm_mem_cube
  rw [hpre] at h
  exact h

/-! ### The form domain and the setting -/

/-- The fermionic form domain: `C²`, antisymmetric under relabelling, vanishing on the walls. -/
def DomF (n : ℕ) : Submodule ℝ (Cfg n → ℝ) where
  carrier := {ψ | ContDiff ℝ 2 ψ ∧ (∀ σ x, ψ (pm σ x) = sgn σ * ψ x) ∧
    ∀ x k, (x k = 0 ∨ x k = 1) → ψ x = 0}
  add_mem' ha hb := ⟨ha.1.add hb.1, fun σ x => by simp [ha.2.1 σ x, hb.2.1 σ x]; ring,
    fun x k hk => by simp [ha.2.2 x k hk, hb.2.2 x k hk]⟩
  zero_mem' := ⟨contDiff_const, fun _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' r _ ha := ⟨ha.1.const_smul r, fun σ x => by simp [ha.2.1 σ x]; ring,
    fun x k hk => by simp [ha.2.2 x k hk]⟩

/-- Partial derivatives. -/
noncomputable def dk (k : Fin (n + 1)) (ψ : Cfg n → ℝ) (x : Cfg n) : ℝ :=
  fderiv ℝ ψ x (Pi.single k 1)

section domain

variable {ψ : Cfg n → ℝ}

lemma diffF (h : ψ ∈ DomF n) : Differentiable ℝ ψ := h.1.differentiable (by norm_num)

lemma cont_dk (h : ψ ∈ DomF n) (k : Fin (n + 1)) : Continuous (dk k ψ) :=
  (h.1.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma contDiff_dk {ψ : Cfg n → ℝ} (h : ContDiff ℝ 2 ψ) (k : Fin (n + 1)) :
    ContDiff ℝ 1 (dk k ψ) :=
  (h.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

end domain

/-- Second partial derivatives `∂ₖₖψ`, and the Laplacian. -/
noncomputable def dkk (k : Fin (n + 1)) (ψ : Cfg n → ℝ) (x : Cfg n) : ℝ := dk k (dk k ψ) x

noncomputable def lapN (ψ : Cfg n → ℝ) (x : Cfg n) : ℝ := ∑ k, dkk k ψ x

lemma continuous_dkk {ψ : Cfg n → ℝ} (h : ContDiff ℝ 2 ψ) (k : Fin (n + 1)) :
    Continuous (dkk k ψ) :=
  ((contDiff_dk h k).continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma continuous_lapN {ψ : Cfg n → ℝ} (h : ContDiff ℝ 2 ψ) : Continuous (lapN ψ) :=
  continuous_finsetSum _ fun k _ => continuous_dkk h k

/-- The slice of `ψ` along coordinate `k` through `x`, and its derivative. -/
lemma hasDerivAt_slice {ψ : Cfg n → ℝ} (hψ : Differentiable ℝ ψ) (x : Cfg n) (k : Fin (n + 1))
    (t : ℝ) :
    HasDerivAt (fun s => ψ (Function.update x k s)) (dk k ψ (Function.update x k t)) t := by
  have hl : HasDerivAt (fun s : ℝ => Function.update x k s) (Pi.single k 1) t := by
    refine hasDerivAt_pi.2 fun i => ?_
    by_cases hi : i = k
    · subst hi; simpa using hasDerivAt_id' t
    · simpa [Function.update_of_ne hi, Pi.single_apply, hi] using hasDerivAt_const t (x i)
  exact (hψ _).hasFDerivAt.comp_hasDerivAt t hl

/-- Vanishing partial derivatives give a vanishing derivative. -/
lemma fderiv_eq_zero_of_dk {u : Cfg n → ℝ} {x : Cfg n} (h : ∀ k, dk k u x = 0) :
    fderiv ℝ u x = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = ∑ k, v k • (Pi.single k 1 : Cfg n) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  simp only [map_smul]
  simp [dk] at h
  simp [h]

/-- The coupling `Σₖ v(xₖ)`. -/
noncomputable def LN (n : ℕ) : Pot →ₗ[ℝ] (Cfg n → ℝ) where
  toFun v := fun x => ∑ k, Box.ext v (x k)
  map_add' a b := by
    funext x; simp only [Box.ext, ContinuousMap.add_apply, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r a := by
    funext x; simp only [Box.ext, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      Pi.smul_apply, Finset.mul_sum]

lemma continuous_LN (v : Pot) : Continuous (LN n v) :=
  show Continuous fun x : Cfg n => ∑ k, Box.ext v (x k) from
    continuous_finsetSum _ fun k _ => (continuous_ext v).comp (continuous_apply k)

lemma LN_pm (v : Pot) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : LN n v (pm σ x) = LN n v x := by
  simp only [LN, LinearMap.coe_mk, AddHom.coe_mk, pm_apply]
  exact Equiv.sum_comp σ (fun k => Box.ext v (x k))

/-- The energy form without potential: kinetic energy plus interaction `w`. -/
noncomputable def h0N (n : ℕ) (w : Cfg n → ℝ) (ψ φ : Cfg n → ℝ) : ℝ :=
  ∫ x, ∑ k, dk k ψ x * dk k φ x ∂μN n + ∫ x, w x * (ψ x * φ x) ∂μN n

lemma dk_add {a b : Cfg n → ℝ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (k : Fin (n + 1)) : dk k (a + b) = dk k a + dk k b := by
  funext x; simp [dk, fderiv_add (ha x) (hb x)]

lemma dk_smul {a : Cfg n → ℝ} (ha : Differentiable ℝ a) (r : ℝ) (k : Fin (n + 1)) :
    dk k (r • a) = r • dk k a := by
  funext x; simp [dk, fderiv_const_smul (ha x) r]

lemma cont_kin {ψ φ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) (hφ : φ ∈ DomF n) :
    Continuous fun x => ∑ k, dk k ψ x * dk k φ x :=
  continuous_finsetSum _ fun k _ => (cont_dk hψ k).mul (cont_dk hφ k)

/-- `n + 1` fermions on a line as a Hohenberg–Kohn setting. -/
noncomputable def settingF (n : ℕ) (w : Cfg n → ℝ) (hw : Continuous w) : Setting (μN n) Pot where
  D := DomF n
  h0 := h0N n w
  h0_add a ha b hb c hc := by
    have e : ∀ k, dk k (a + b) = dk k a + dk k b := dk_add (diffF ha) (diffF hb)
    simp only [h0N, e, Pi.add_apply]
    have ia := integrableN (cont_kin ha hc)
    have ib := integrableN (cont_kin hb hc)
    have ja := integrableN (hw.mul (ha.1.continuous.mul hc.1.continuous))
    have jb := integrableN (hw.mul (hb.1.continuous.mul hc.1.continuous))
    have h1 : ∫ x, ∑ k, (dk k a x + dk k b x) * dk k c x ∂μN n =
        ∫ x, ∑ k, dk k a x * dk k c x ∂μN n + ∫ x, ∑ k, dk k b x * dk k c x ∂μN n := by
      rw [← integral_add (f := fun x => ∑ k, dk k a x * dk k c x)
        (g := fun x => ∑ k, dk k b x * dk k c x) ia ib]
      congr 1; funext x; rw [← Finset.sum_add_distrib]; congr 1; funext k; ring
    have h2 : ∫ x, w x * ((a x + b x) * c x) ∂μN n =
        ∫ x, w x * (a x * c x) ∂μN n + ∫ x, w x * (b x * c x) ∂μN n := by
      rw [← integral_add (f := fun x => w x * (a x * c x)) (g := fun x => w x * (b x * c x)) ja jb]
      congr 1; funext x; ring
    rw [h1, h2]; ring
  h0_smul r a ha c hc := by
    have e : ∀ k, dk k (r • a) = r • dk k a := dk_smul (diffF ha) r
    simp only [h0N, e, Pi.smul_apply, smul_eq_mul]
    have h1 : ∫ x, ∑ k, r * dk k a x * dk k c x ∂μN n =
        r * ∫ x, ∑ k, dk k a x * dk k c x ∂μN n := by
      rw [← integral_const_mul]; congr 1; funext x; rw [Finset.mul_sum]; congr 1; funext k; ring
    have h2 : ∫ x, w x * (r * a x * c x) ∂μN n = r * ∫ x, w x * (a x * c x) ∂μN n := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [h1, h2]; ring
  h0_symm ψ _ φ _ := by
    simp only [h0N]
    congr 1
    · congr 1; funext x; congr 1; funext k; ring
    · congr 1; funext x; ring
  L := LN n
  int_L v ψ φ hψ hφ := integrableN ((continuous_LN v).mul (hψ.1.continuous.mul hφ.1.continuous))
  int_sq ψ φ hψ hφ := integrableN (hψ.1.continuous.mul hφ.1.continuous)

/-! ### Antisymmetrisation -/

/-- The antisymmetrisation `Σ_σ sgn σ · f ∘ σ` (without normalisation). -/
noncomputable def alt (f : Cfg n → ℝ) (x : Cfg n) : ℝ := ∑ σ, sgn σ * f (pm σ x)

/-- The symmetrisation `Σ_σ f ∘ σ`. -/
noncomputable def sym (f : Cfg n → ℝ) (x : Cfg n) : ℝ := ∑ σ, f (pm σ x)

lemma alt_pm (f : Cfg n → ℝ) (τ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    alt f (pm τ x) = sgn τ * alt f x := by
  simp only [alt, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulLeft, sgn_mul, ← pm_mul]
  linear_combination (-(sgn σ * f (pm (τ * σ) x))) * sgn_mul_self τ

lemma sym_pm (f : Cfg n → ℝ) (τ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    sym f (pm τ x) = sym f x := by
  simp only [sym]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulLeft, ← pm_mul]

lemma contDiff_alt {f : Cfg n → ℝ} {m : WithTop ℕ∞} (hf : ContDiff ℝ m f) : ContDiff ℝ m (alt f) :=
  ContDiff.sum fun σ _ => contDiff_const.mul (hf.comp (contDiff_pm σ))

lemma contDiff_sym {f : Cfg n → ℝ} {m : WithTop ℕ∞} (hf : ContDiff ℝ m f) : ContDiff ℝ m (sym f) :=
  ContDiff.sum fun σ _ => hf.comp (contDiff_pm σ)

/-- A point on a wall is relabelled to a point on a wall. -/
lemma pm_not_mem_cube {x : Cfg n} {k : Fin (n + 1)} (hk : x k = 0 ∨ x k = 1)
    (σ : Equiv.Perm (Fin (n + 1))) : pm σ x ∉ Cube n := by
  intro h
  have := h (σ.symm k) (mem_univ _)
  simp only [pm_apply, Equiv.apply_symm_apply] at this
  rcases hk with hk | hk <;> rw [hk] at this
  · exact lt_irrefl _ this.1
  · exact lt_irrefl _ this.2

/-- The antisymmetrisation of a `C²` function vanishing off the cube lies in the domain. -/
lemma alt_mem {f : Cfg n → ℝ} (hf : ContDiff ℝ 2 f) (hout : ∀ x, x ∉ Cube n → f x = 0) :
    alt f ∈ DomF n :=
  ⟨contDiff_alt hf, fun σ x => alt_pm f σ x, fun x k hk => by
    simp only [alt]
    exact Finset.sum_eq_zero fun σ _ => by rw [hout _ (pm_not_mem_cube hk σ), mul_zero]⟩

/-- `ψ · sym f` lies in the domain, for `ψ` in the domain and `f` smooth. -/
lemma mul_sym_mem {ψ f : Cfg n → ℝ} (hψ : ψ ∈ DomF n) (hf : ContDiff ℝ 2 f) :
    (fun x => ψ x * sym f x) ∈ DomF n :=
  ⟨hψ.1.mul (contDiff_sym hf), fun σ x => by
    change ψ (pm σ x) * sym f (pm σ x) = sgn σ * (ψ x * sym f x)
    rw [hψ.2.1 σ x, sym_pm]; ring,
    fun x k hk => by change ψ x * sym f x = 0; rw [hψ.2.2 x k hk, zero_mul]⟩

/-! ### Separation -/

/-- **Fundamental lemma with antisymmetric test functions.** -/
lemma eq_zero_of_integral_alt {g : Cfg n → ℝ} (hg : Continuous g)
    (hgs : ∀ σ x, g (pm σ x) = sgn σ * g x)
    (h : ∀ φ ∈ DomF n, ∫ x, g x * φ x ∂μN n = 0) : ∀ x ∈ Cube n, g x = 0 := by
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (U := Cube n) (μ := volume)
    (f := g) isOpen_cube (hg.locallyIntegrable.locallyIntegrableOn _)
    (fun φ hφ _ (hsub : tsupport φ ⊆ Cube n) => ?_)
  · have h' : g =ᵐ[μN n] 0 := (ae_restrict_iff' measurableSet_cube).2 hae
    exact Measure.eqOn_open_of_ae_eq h' isOpen_cube hg.continuousOn continuousOn_const
  have hout : ∀ x, x ∉ Cube n → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hsub h')
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have h1 := h (alt φ) (alt_mem hφ2 hout)
  -- each relabelled term contributes `∫ g φ`
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)),
      ∫ x, g x * (sgn σ * φ (pm σ x)) ∂μN n = ∫ x, g x * φ x ∂μN n := by
    intro σ
    have := integral_pm σ (fun y => g (pm σ⁻¹ y) * (sgn σ * φ y))
    simp only [pm_inv_pm] at this
    rw [this]
    congr 1; funext y
    rw [hgs, sgn_inv]
    linear_combination (g y * φ y) * sgn_mul_self σ
  have hsum : ∫ x, g x * alt φ x ∂μN n =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∫ x, g x * (sgn σ * φ (pm σ x)) ∂μN n := by
    simp only [alt, Finset.mul_sum]
    exact integral_finsetSum (f := fun σ x => g x * (sgn σ * φ (pm σ x))) _ fun σ _ =>
      integrableN (hg.mul (continuous_const.mul (hφ.continuous.comp (continuous_pm σ))))
  rw [hsum] at h1
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  have hc : (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hμ : ∫ x, g x * φ x ∂μN n = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hc
    · exact h
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Cube n)]
  · simpa [smul_eq_mul, mul_comm] using hμ
  · intro x hx; rw [hout x hx, zero_smul]

/-- **Separation on the cube.** -/
theorem sep_line (w : Cfg n → ℝ) (hw : Continuous w) : Sep (settingF n w hw) := by
  intro v c ψ hψ h
  set g : Cfg n → ℝ := fun x => (LN n v x - c) * ψ x
  have hg : Continuous g := ((continuous_LN v).sub continuous_const).mul hψ.1.continuous
  have hgs : ∀ σ x, g (pm σ x) = sgn σ * g x := by
    intro σ x; simp only [g, LN_pm, hψ.2.1 σ x]; ring
  have h0 := eq_zero_of_integral_alt hg hgs fun φ hφ => h φ hφ
  exact (ae_restrict_iff' measurableSet_cube).2 (ae_of_all _ fun x hx => h0 x hx)

/-- **Rigidity on the cube.** -/
theorem rigidL_line (w : Cfg n → ℝ) (hw : Continuous w) : RigidL (settingF n w hw) one := by
  intro v c h
  have hO : EqOn (LN n v) (fun _ => c) (Cube n) :=
    Measure.eqOn_open_of_ae_eq h isOpen_cube (continuous_LN v).continuousOn continuousOn_const
  have hN : (0 : ℝ) < n + 1 := by positivity
  have h1 : ∀ t ∈ Ioo (0 : ℝ) 1, Box.ext v t = c / (n + 1) := by
    intro t ht
    have := hO (show (fun _ => t : Cfg n) ∈ Cube n from fun _ _ => ht)
    simp only [LN, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at this
    rw [eq_div_iff hN.ne']
    push_cast at this
    linarith
  have hC : EqOn (Box.ext v) (fun _ => c / (n + 1)) (Icc 0 1) :=
    EqOn.of_subset_closure h1 (continuous_ext v).continuousOn continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one])
  refine ⟨c / (n + 1), ?_⟩
  ext t
  have := hC t.2
  simp only [Box.ext, projIcc_val] at this
  simp [one, this]

/-! ### Densities -/

/-- The cube of the remaining `n` particles. -/
abbrev Cube' (n : ℕ) : Set (Fin n → ℝ) := Set.pi univ fun _ => Ioo (0 : ℝ) 1

/-- **Fubini on the cube**, splitting off the first particle. -/
lemma integral_cube_cons {F : Cfg n → ℝ} (hF : Continuous F) :
    ∫ x, F x ∂μN n = ∫ t in Ioo (0 : ℝ) 1, ∫ y in Cube' n, F (Fin.cons t y) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he : MeasurePreserving e.symm (volume.prod volume) (volume : Measure (Cfg n)) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hpre : e.symm ⁻¹' Cube n = Ioo (0 : ℝ) 1 ×ˢ Cube' n := by
    ext ⟨t, y⟩
    simp only [mem_preimage, mem_prod, Set.mem_pi, mem_univ, true_implies]
    constructor
    · intro h
      refine ⟨?_, fun i => ?_⟩
      · simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using h 0
      · simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using h i.succ
    · rintro ⟨ht, hy⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using ht
      · simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using hy j
  have h := he.setIntegral_preimage_emb e.symm.measurableEmbedding F (Cube n)
  rw [hpre] at h
  rw [← h, ← Measure.prod_restrict]
  have hcomp : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := by
    rintro ⟨t, y⟩
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  simp only [hcomp]
  refine integral_prod (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2)) ?_
  have hc : Continuous fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2) :=
    hF.comp (by fun_prop)
  rw [Measure.prod_restrict]
  exact (hc.continuousOn.integrableOn_compact
    (isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc))).mono_set
    (prod_mono Ioo_subset_Icc_self (pi_mono fun _ _ => Ioo_subset_Icc_self))

/-- The square of an antisymmetric function is symmetric. -/
lemma sq_pm {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    ψ (pm σ x) * ψ (pm σ x) = ψ x * ψ x := by
  rw [hψ.2.1 σ x]
  linear_combination (ψ x * ψ x) * sgn_mul_self σ

/-- **Densities.** If the one-body densities `ρ(t) = ∫ ψ(t, y)² dy` agree on `(0, 1)`, so do the
norms and the density functionals. -/
theorem dens_eq_of_marginal_line {w : Cfg n → ℝ} {hw : Continuous w} {ψ ψ' : Cfg n → ℝ}
    (hψ : ψ ∈ DomF n) (hψ' : ψ' ∈ DomF n)
    (hρ : ∀ t ∈ Ioo (0 : ℝ) 1, ∫ y in Cube' n, ψ (Fin.cons t y) ^ 2 =
      ∫ y in Cube' n, ψ' (Fin.cons t y) ^ 2) :
    ip (μ := μN n) ψ ψ = ip (μ := μN n) ψ' ψ' ∧
      dens (settingF n w hw) ψ = dens (settingF n w hw) ψ' := by
  -- the integral of `f(x₀) ψ(x)²` only depends on the density
  have key : ∀ f : ℝ → ℝ, Continuous f →
      ∫ x, f (x 0) * (ψ x * ψ x) ∂μN n = ∫ x, f (x 0) * (ψ' x * ψ' x) ∂μN n := by
    intro f hf
    rw [integral_cube_cons (F := fun x => f (x 0) * (ψ x * ψ x))
        ((hf.comp (continuous_apply 0)).mul (hψ.1.continuous.mul hψ.1.continuous)),
      integral_cube_cons (F := fun x => f (x 0) * (ψ' x * ψ' x))
        ((hf.comp (continuous_apply 0)).mul (hψ'.1.continuous.mul hψ'.1.continuous))]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    simp only [Fin.cons_zero]
    rw [integral_const_mul, integral_const_mul]
    have := hρ t ht
    simp only [sq] at this
    rw [this]
  -- relabelling moves `f(xₖ)` to `f(x₀)`
  have swapsq : ∀ φ : Cfg n → ℝ, φ ∈ DomF n → ∀ f : ℝ → ℝ, ∀ k : Fin (n + 1),
      ∫ x, f (x k) * (φ x * φ x) ∂μN n = ∫ x, f (x 0) * (φ x * φ x) ∂μN n := by
    intro φ hφ f k
    rw [← integral_pm (Equiv.swap 0 k)]
    congr 1; funext x
    rw [sq_pm hφ]
    simp
  refine ⟨?_, ?_⟩
  · have := key (fun _ => 1) continuous_const
    simpa [ip] using this
  · funext v
    have hv := continuous_ext v
    simp only [dens, pf]
    change ∫ x, (∑ k, Box.ext v (x k)) * (ψ x * ψ x) ∂μN n =
      ∫ x, (∑ k, Box.ext v (x k)) * (ψ' x * ψ' x) ∂μN n
    have split : ∀ φ : Cfg n → ℝ, φ ∈ DomF n →
        ∫ x, (∑ k, Box.ext v (x k)) * (φ x * φ x) ∂μN n =
          (n + 1) * ∫ x, Box.ext v (x 0) * (φ x * φ x) ∂μN n := by
      intro φ hφ
      have hpt : (fun x : Cfg n => (∑ k, Box.ext v (x k)) * (φ x * φ x)) =
          fun x => ∑ k, Box.ext v (x k) * (φ x * φ x) := by
        funext x; rw [Finset.sum_mul]
      rw [hpt, integral_finsetSum (f := fun k x => Box.ext v (x k) * (φ x * φ x)) _
        fun k _ => integrableN ((hv.comp (continuous_apply k)).mul
        (hφ.1.continuous.mul hφ.1.continuous))]
      simp only [swapsq φ hφ (Box.ext v), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast; ring
    rw [split ψ hψ, split ψ' hψ', key _ hv]

/-- **Hohenberg–Kohn for `n + 1` fermions on a line, conditional on unique continuation.** If
ground states of continuous potentials `v` and `v'` have the same one-body density, and the ground
state of `v` vanishes only on a null set of the cube, then `v - v'` is constant. -/
theorem hk_line_of_ucp {w : Cfg n → ℝ} {hw : Continuous w} {v v' : Pot} {ψ ψ' : Cfg n → ℝ}
    (hψ : IsGS (settingF n w hw) v ψ) (hψ' : IsGS (settingF n w hw) v' ψ')
    (hρ : ∀ t ∈ Ioo (0 : ℝ) 1, ∫ y in Cube' n, ψ (Fin.cons t y) ^ 2 =
      ∫ y in Cube' n, ψ' (Fin.cons t y) ^ 2)
    (hucp : ∀ᵐ x ∂μN n, ψ x ≠ 0) : ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨hn, hd⟩ := dens_eq_of_marginal_line (w := w) (hw := hw) hψ.1 hψ'.1 hρ
  exact hk_of_ucp (sep_line w hw) (rigidL_line w hw) hψ hψ' hn hd hucp

end DFT.Continuum.Line
