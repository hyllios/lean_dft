/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Basic

/-!
# Ground states of `N` particles on a line are classical solutions

For `n + 1` bosons or fermions on `[0, 1]` with a continuous interaction `w` invariant under
relabelling, every ground state `Φ` of the potential `v` solves the Schrödinger equation pointwise
on the open cube: `-ΔΦ + (w + Σₖ v(xₖ) - E) Φ = 0`, with `E = ⟨Φ, HΦ⟩ / ⟨Φ, Φ⟩`.

* `integral_cube_insertNth`: Fubini on the cube, with coordinate `k` innermost.
* `dk_comp_pm`: the chain rule for relabelling, `∂ₖ(f ∘ σ) = (∂_{σ⁻¹ k} f) ∘ σ`.
* `lapN_pm`: the Laplacian of a state has the same exchange symmetry.
* `ibpN`: integration by parts along each coordinate.
* `strong_eq_line`: the strong Schrödinger equation.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box

variable {n : ℕ} {τ : Stat}

/-- **Fubini on the cube**, with coordinate `k` innermost. -/
lemma integral_cube_insertNth {F : Cfg n → ℝ} (hF : Continuous F) (k : Fin (n + 1)) :
    ∫ x, F x ∂μN n = ∫ y in Cube' n, ∫ t in Ioo (0 : ℝ) 1, F (Fin.insertNth k t y) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k
  have he : MeasurePreserving e.symm (volume.prod volume) (volume : Measure (Cfg n)) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm
  have hcomp : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.insertNth k p.1 p.2 := by
    rintro ⟨t, y⟩; rfl
  have hpre : e.symm ⁻¹' Cube n = Ioo (0 : ℝ) 1 ×ˢ Cube' n := by
    ext ⟨t, y⟩
    simp only [mem_preimage, mem_prod, Set.mem_pi, mem_univ, true_implies, hcomp]
    rw [k.forall_iff_succAbove]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have h := he.setIntegral_preimage_emb e.symm.measurableEmbedding F (Cube n)
  rw [hpre] at h
  rw [← h, ← Measure.prod_restrict]
  simp only [hcomp]
  have hc : Continuous fun p : ℝ × (Fin n → ℝ) => F (Fin.insertNth k p.1 p.2) :=
    hF.comp (by fun_prop)
  refine integral_prod_symm (fun p : ℝ × (Fin n → ℝ) => F (Fin.insertNth k p.1 p.2)) ?_
  rw [Measure.prod_restrict]
  exact (hc.continuousOn.integrableOn_compact
    (isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc))).mono_set
    (prod_mono Ioo_subset_Icc_self (pi_mono fun _ _ => Ioo_subset_Icc_self))

/-- The slice along coordinate `k` of a differentiable function. -/
lemma hasDerivAt_insertNth {ψ : Cfg n → ℝ} (hψ : Differentiable ℝ ψ) (k : Fin (n + 1))
    (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ψ (Fin.insertNth k s y)) (dk k ψ (Fin.insertNth k t y)) t := by
  have h := hasDerivAt_slice hψ (Fin.insertNth k (0 : ℝ) y) k t
  simp only [Fin.update_insertNth] at h
  exact h

lemma integral_unit' {f : ℝ → ℝ} : ∫ x in (0 : ℝ)..1, f x = ∫ x in Ioo (0 : ℝ) 1, f x := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- **Integration by parts along coordinate `k`.** -/
lemma ibpN {Φ φ : Cfg n → ℝ} (hΦ : ContDiff ℝ 2 Φ) (hφ : φ ∈ Dom τ n) (k : Fin (n + 1)) :
    ∫ x, dk k Φ x * dk k φ x ∂μN n = -∫ x, dkk k Φ x * φ x ∂μN n := by
  have hdc : Continuous (dk k Φ) := (contDiff_dk hΦ k).continuous
  rw [integral_cube_insertNth (F := fun x => dk k Φ x * dk k φ x) (hdc.mul (cont_dk hφ k)) k,
    integral_cube_insertNth (F := fun x => dkk k Φ x * φ x)
      ((continuous_dkk hΦ k).mul hφ.1.continuous) k, ← integral_neg]
  congr 1; funext y
  have hd1 : Differentiable ℝ (dk k Φ) := (contDiff_dk hΦ k).differentiable one_ne_zero
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun t => dk k Φ (Fin.insertNth k t y)) (u' := fun t => dkk k Φ (Fin.insertNth k t y))
    (v := fun t => φ (Fin.insertNth k t y)) (v' := fun t => dk k φ (Fin.insertNth k t y))
    (fun t _ => hasDerivAt_insertNth hd1 k y t) (fun t _ => hasDerivAt_insertNth (diffF hφ) k y t)
    (((continuous_dkk hΦ k).comp (by fun_prop)).intervalIntegrable _ _)
    (((cont_dk hφ k).comp (by fun_prop)).intervalIntegrable _ _)
  have h0 : φ (Fin.insertNth k 0 y) = 0 := hφ.2.2 _ k (Or.inl (by simp))
  have h1 : φ (Fin.insertNth k 1 y) = 0 := hφ.2.2 _ k (Or.inr (by simp))
  rw [h0, h1, mul_zero, mul_zero, sub_zero, zero_sub, integral_unit', integral_unit'] at h
  rw [h]

/-! ### Relabelling and derivatives -/

/-- Relabelling as a continuous linear map. -/
noncomputable def pmL (σ : Equiv.Perm (Fin (n + 1))) : Cfg n →L[ℝ] Cfg n :=
  { toFun := pm σ
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    cont := continuous_pm σ }

lemma pmL_single (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    pmL σ (Pi.single k 1) = Pi.single (σ⁻¹ k) 1 := by
  funext i
  change (Pi.single k (1 : ℝ) : Cfg n) (σ i) = (Pi.single (σ⁻¹ k) (1 : ℝ) : Cfg n) i
  simp only [Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩

/-- **Chain rule for relabelling.** -/
lemma dk_comp_pm {f : Cfg n → ℝ} (hf : Differentiable ℝ f) (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) (x : Cfg n) :
    dk k (fun y => f (pm σ y)) x = dk (σ⁻¹ k) f (pm σ x) := by
  have e : (fun y => f (pm σ y)) = f ∘ pmL σ := rfl
  simp only [dk, e]
  rw [fderiv_comp x (hf _) (pmL σ).differentiableAt, (pmL σ).fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, pmL_single]
  rfl

lemma dk_fun_comp_pm {f : Cfg n → ℝ} (hf : Differentiable ℝ f) (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) : dk k (fun y => f (pm σ y)) = fun x => dk (σ⁻¹ k) f (pm σ x) :=
  funext (dk_comp_pm hf σ k)

/-- The Laplacian commutes with relabelling. -/
lemma lapN_comp_pm {f : Cfg n → ℝ} (hf : ContDiff ℝ 2 f) (σ : Equiv.Perm (Fin (n + 1)))
    (x : Cfg n) : lapN (fun y => f (pm σ y)) x = lapN f (pm σ x) := by
  simp only [lapN, dkk]
  have hd : ∀ j, Differentiable ℝ (dk j f) := fun j => (contDiff_dk hf j).differentiable one_ne_zero
  have e : ∀ k, dk k (dk k fun y => f (pm σ y)) x = dk (σ⁻¹ k) (dk (σ⁻¹ k) f) (pm σ x) := by
    intro k
    rw [dk_fun_comp_pm (hf.differentiable (by norm_num)) σ k,
      dk_comp_pm (hd (σ⁻¹ k)) σ k x]
  simp only [e]
  exact Equiv.sum_comp σ⁻¹ (fun j => dk j (dk j f) (pm σ x))

/-- **The Laplacian of a state has the same exchange symmetry.** -/
lemma lapN_pm {Φ : Cfg n → ℝ} (hΦ : Φ ∈ Dom τ n) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    lapN Φ (pm σ x) = ch τ σ * lapN Φ x := by
  rw [← lapN_comp_pm hΦ.1 σ x]
  have e : (fun y => Φ (pm σ y)) = ch τ σ • Φ := by funext y; simp [hΦ.2.1 σ y]
  rw [e]
  simp only [lapN, dkk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dk_smul (diffF hΦ), dk_smul ((contDiff_dk hΦ.1 k).differentiable one_ne_zero)]
  rfl

/-- **Ground states of `n + 1` interacting particles are classical solutions** of
`-ΔΦ + (w + Σₖ v(xₖ) - E) Φ = 0` on the open cube. -/
theorem strong_eq_line {w : Cfg n → ℝ} {hw : Continuous w} (hws : ∀ σ x, w (pm σ x) = w x)
    {v : Pot} {Φ : Cfg n → ℝ} (hΦ : IsGS (setting τ n w hw) v Φ) :
    ∀ x ∈ Cube n, -lapN Φ x +
      (w x + LN n v x - Q (setting τ n w hw) v Φ / ip (μ := μN n) Φ Φ) * Φ x = 0 := by
  have hD : Φ ∈ Dom τ n := hΦ.1
  set E := Q (setting τ n w hw) v Φ / ip (μ := μN n) Φ Φ
  set g : Cfg n → ℝ := fun x => -lapN Φ x + (w x + LN n v x - E) * Φ x
  have hc := hD.1.continuous
  have hg : Continuous g :=
    (continuous_lapN hD.1).neg.add (((hw.add (continuous_LN v)).sub continuous_const).mul hc)
  have hgs : ∀ σ x, g (pm σ x) = ch τ σ * g x := by
    intro σ x
    simp only [g, lapN_pm hD, hws, LN_pm, hD.2.1 σ x]
    ring
  refine eq_zero_of_integral_alt hg hgs fun φ hφ => ?_
  have hel := euler_lagrange hΦ hφ
  change h0N n w Φ φ + ∫ x, LN n v x * (Φ x * φ x) ∂μN n = E * ∫ x, Φ x * φ x ∂μN n at hel
  simp only [h0N] at hel
  have hφc := hφ.1.continuous
  have iK : ∀ k ∈ Finset.univ, Integrable (fun x => dk k Φ x * dk k φ x) (μN n) :=
    fun k _ => integrableN ((cont_dk hD k).mul (cont_dk hφ k))
  have jK : ∀ k ∈ Finset.univ, Integrable (fun x => dkk k Φ x * φ x) (μN n) :=
    fun k _ => integrableN ((continuous_dkk hD.1 k).mul hφc)
  have iw := integrableN (hw.mul (hc.mul hφc))
  have iL := integrableN ((continuous_LN v).mul (hc.mul hφc))
  have iP := integrableN (hc.mul hφc)
  have iLap : Integrable (fun x => lapN Φ x * φ x) (μN n) :=
    integrableN ((continuous_lapN hD.1).mul hφc)
  have hkin : ∫ x, ∑ k, dk k Φ x * dk k φ x ∂μN n = -∫ x, lapN Φ x * φ x ∂μN n := by
    rw [integral_finsetSum (f := fun k x => dk k Φ x * dk k φ x) _ iK]
    simp only [ibpN hD.1 hφ]
    have : ∫ x, lapN Φ x * φ x ∂μN n = ∑ k, ∫ x, dkk k Φ x * φ x ∂μN n := by
      rw [← integral_finsetSum (f := fun k x => dkk k Φ x * φ x) _ jK]
      congr 1; funext x; simp only [lapN, Finset.sum_mul]
    rw [this, Finset.sum_neg_distrib]
  have hpt : (fun x => g x * φ x) = fun x =>
      (-(lapN Φ x * φ x) + (w x * (Φ x * φ x) + LN n v x * (Φ x * φ x))) - E * (Φ x * φ x) := by
    funext x; simp only [g]; ring
  rw [hpt,
    integral_sub (f := fun x => -(lapN Φ x * φ x) + (w x * (Φ x * φ x) + LN n v x * (Φ x * φ x)))
      (g := fun x => E * (Φ x * φ x)) (iLap.neg.add (iw.add iL)) (iP.const_mul E),
    integral_add (f := fun x => -(lapN Φ x * φ x))
      (g := fun x => w x * (Φ x * φ x) + LN n v x * (Φ x * φ x)) iLap.neg (iw.add iL),
    integral_add (f := fun x => w x * (Φ x * φ x)) (g := fun x => LN n v x * (Φ x * φ x)) iw iL,
    integral_neg, integral_const_mul]
  rw [hkin] at hel
  linarith

end DFT.Continuum.Line
