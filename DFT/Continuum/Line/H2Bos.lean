/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.DensC1

/-!
# Bosons: `H²` regularity, `C¹` densities, meagreness

The bosonic counterpart of `Line/H2` and `Line/DensC1`. Test the weak equation with the symmetrised
sine mode `Σ_σ s_{m∘σ}`, which is a bosonic `H¹₀` state. For a symmetric ground state and a
relabelling-invariant potential all `N!` terms agree, so again `λ_m c_m + ⟨s_m, VΨ⟩ = E c_m` and
`Σ_m λ_m² c_m² < ∞`. The rest (`dens_eq_KS`, `meagre_C1Dens`) holds for either statistics.

* `smdSym`, `smdSym_mem`: the symmetrised mode.
* `int_dW_smdSym`, `h0W_smdSym`.
* **`coef_EL_bos`**, **`summable_lam_sq_bos`**.
* **`gs_dens_C1_stat`**, **`vrep_meagre`**, **`ensvrep_meagre`**, **`nonvrep_residual`**: for
  bosons or fermions with continuous `v` and continuous relabelling-invariant `w`, the interacting
  `v`-representable densities are meagre and the non-`v`-representable ones residual.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ}

/-- The symmetrised sine mode `Σ_σ s_{m∘σ}`. -/
noncomputable def smdSym (m : Fin (n + 1) → ℕ) (x : Cfg n) : ℝ :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), smd (pmI σ m) x

lemma smdSym_pm (m : Fin (n + 1) → ℕ) (τ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    smdSym m (pm τ x) = smdSym m x := by
  simp only [smdSym, smd_pm', pmI_pmI]
  exact Equiv.sum_comp (Equiv.mulRight τ⁻¹) (fun σ => smd (pmI σ m) x)

lemma isWD_smdSym (m : Fin (n + 1) → ℕ) (k : Fin (n + 1)) :
    MemLp (smdSym m) 2 (μN n) ∧
      IsWD k (smdSym m) (fun x => ∑ σ : Equiv.Perm (Fin (n + 1)),
        π * ((pmI σ m) k + 1) * cmd k (pmI σ m) x) :=
  IsWD.sum Finset.univ (fun σ _ => memLp_cont (continuous_smd (pmI σ m)))
    (fun σ _ => isWD_smd k (pmI σ m))

lemma smdSym_mem (m : Fin (n + 1) → ℕ) : smdSym m ∈ DomW .bos n :=
  ⟨(isWD_smdSym m 0).1, fun k => ⟨_, (isWD_smdSym m k).2⟩,
    fun σ _ => ae_of_all _ fun x => by rw [smdSym_pm]; simp⟩

/-- `∫ ∂ₖΨ ∂ₖ(Σ_σ s_{m∘σ}) = Σ_σ π²((m∘σ)_k + 1)² c_{m∘σ}`. -/
lemma int_dW_smdSym {Ψ : Cfg n → ℝ} (hΨ : H1W Ψ) (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) :
    ∫ x, dW k Ψ x * dW k (smdSym m) x ∂μN n =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (π * ((pmI σ m) k + 1)) ^ 2 * cN (pmI σ m) Ψ := by
  have h1 := dW_ae_eq (isWD_smdSym m k).2
  have hG : ∀ σ : Equiv.Perm (Fin (n + 1)),
      dW k (smd (pmI σ m)) =ᵐ[μN n] fun x => π * ((pmI σ m) k + 1) * cmd k (pmI σ m) x :=
    fun σ => dW_ae_eq (isWD_smd k (pmI σ m))
  have hint : ∀ σ : Equiv.Perm (Fin (n + 1)), Integrable
      (fun x => dW k Ψ x * (π * ((pmI σ m) k + 1) * cmd k (pmI σ m) x)) (μN n) :=
    fun σ => int_mul_L2 (memLp_dW_H hΨ k) (memLp_cont ((contDiff_cmd k _).continuous.const_mul _))
  rw [integral_congr_ae (show (fun x => dW k Ψ x * dW k (smdSym m) x) =ᵐ[μN n]
    fun x => ∑ σ : Equiv.Perm (Fin (n + 1)), dW k Ψ x *
      (π * ((pmI σ m) k + 1) * cmd k (pmI σ m) x) from
    h1.mono fun x hx => by simp only [hx, Finset.mul_sum]),
    integral_finsetSum _ fun σ _ => hint σ]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← int_dW_smd hΨ k (pmI σ m)]
  refine integral_congr_ae ?_
  filter_upwards [hG σ] with x hx
  rw [hx]

lemma h0W_smdSym {w : Cfg n → ℝ} {Ψ : Cfg n → ℝ} (hΨ : H1W Ψ) (m : Fin (n + 1) → ℕ) :
    h0W n w Ψ (smdSym m) = (∑ σ : Equiv.Perm (Fin (n + 1)), lam (pmI σ m) * cN (pmI σ m) Ψ) +
      ∫ x, w x * (Ψ x * smdSym m x) ∂μN n := by
  simp only [h0W, int_dW_smdSym hΨ]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.sum_mul, lam, ksq]
  push_cast
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Coefficients of a relabelling-invariant function are invariant. -/
lemma cN_pmI_of_symm {f : Cfg n → ℝ} (hf : ∀ σ, ∀ᵐ x ∂μN n, f (pm σ x) = f x)
    (σ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) : cN (pmI σ m) f = cN m f := by
  rw [cN_eq, cN_eq, ← integral_pm σ]
  refine integral_congr_ae ?_
  filter_upwards [hf σ] with x hx
  simp only [smd_pm, hx]

variable {w : Cfg n → ℝ} {hw : Continuous w}

/-- **The coefficient equation for bosons.** -/
theorem coef_EL_bos (hws : ∀ σ x, w (pm σ x) = w x) {v : Pot} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW .bos n w hw) v Ψ) (m : Fin (n + 1) → ℕ) :
    lam m * cN m Ψ + cN m (fun x => (LN n v x + w x) * Ψ x) =
      Q (settingW .bos n w hw) v Ψ / ip (μ := μN n) Ψ Ψ * cN m Ψ := by
  set E := Q (settingW .bos n w hw) v Ψ / ip (μ := μN n) Ψ Ψ
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hV : Continuous V := (continuous_LN v).add hw
  have hΨs : ∀ σ, ∀ᵐ x ∂μN n, Ψ (pm σ x) = Ψ x := fun σ => by
    filter_upwards [hΨ.1.2.2 σ trivial] with x hx
    rw [hx]; simp
  have hVΨs : ∀ σ, ∀ᵐ x ∂μN n, (fun x => V x * Ψ x) (pm σ x) = V x * Ψ x := fun σ => by
    filter_upwards [hΨs σ] with x hx
    simp only [V, LN_pm, hws, hx]
  have hc : ∀ σ : Equiv.Perm (Fin (n + 1)), cN (pmI σ m) Ψ = cN m Ψ :=
    fun σ => cN_pmI_of_symm hΨs σ m
  have hcV : ∀ σ : Equiv.Perm (Fin (n + 1)), cN (pmI σ m) (fun x => V x * Ψ x) =
      cN m (fun x => V x * Ψ x) := fun σ => cN_pmI_of_symm hVΨs σ m
  have hel := euler_lagrange hΨ (smdSym_mem m)
  change h0W n w Ψ (smdSym m) + ∫ x, LN n v x * (Ψ x * smdSym m x) ∂μN n =
    E * ∫ x, Ψ x * smdSym m x ∂μN n at hel
  rw [h0W_smdSym (h1W_of_mem hΨ.1)] at hel
  -- expand the integrals over the symmetrised mode
  have hsplit : ∀ F : Cfg n → ℝ, Continuous F →
      ∫ x, F x * (Ψ x * smdSym m x) ∂μN n =
        ∑ σ : Equiv.Perm (Fin (n + 1)), cN (pmI σ m) (fun x => F x * Ψ x) := fun F hF => by
    have hi : ∀ σ : Equiv.Perm (Fin (n + 1)),
        Integrable (fun x => F x * (Ψ x * smd (pmI σ m) x)) (μN n) := fun σ => by
      obtain ⟨C, hC⟩ := ae_bound_cont hF
      exact (int_mul_L2 hΨ.1.1 (memLp_cont (continuous_smd _))).bdd_mul hF.aestronglyMeasurable hC
    simp only [smdSym, Finset.mul_sum]
    rw [integral_finsetSum _ fun σ _ => hi σ]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [cN_eq]; congr 1; funext x; ring
  have h1 := hsplit w hw
  have h2 := hsplit (LN n v) (continuous_LN v)
  have h3 := hsplit (fun _ => 1) continuous_const
  simp only [one_mul] at h3
  have h3' : ∫ x, Ψ x * smdSym m x ∂μN n = ∑ σ : Equiv.Perm (Fin (n + 1)), cN (pmI σ m) Ψ := by
    rw [← h3]
  rw [h1, h2, h3'] at hel
  simp only [hc, lam_pm] at hel
  have hwV : ∀ σ : Equiv.Perm (Fin (n + 1)),
      cN (pmI σ m) (fun x => w x * Ψ x) + cN (pmI σ m) (fun x => LN n v x * Ψ x) =
        cN m (fun x => V x * Ψ x) := fun σ => by
    rw [← hcV σ, cN_eq, cN_eq, cN_eq,
      ← integral_add (int_mul_L2 (memLp_cont (continuous_smd _)) (memLp_mul_cont hw hΨ.1.1))
        (int_mul_L2 (memLp_cont (continuous_smd _)) (memLp_mul_cont (continuous_LN v) hΨ.1.1))]
    congr 1; funext x; simp only [V]; ring
  have hsum : (∑ σ : Equiv.Perm (Fin (n + 1)), lam m * cN m Ψ) +
      ∑ σ : Equiv.Perm (Fin (n + 1)), cN (pmI σ m) (fun x => w x * Ψ x) +
      ∑ σ : Equiv.Perm (Fin (n + 1)), cN (pmI σ m) (fun x => LN n v x * Ψ x) =
      (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) *
        (lam m * cN m Ψ + cN m (fun x => V x * Ψ x)) := by
    rw [add_assoc, ← Finset.sum_add_distrib]
    simp only [hwV, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hrhs : E * ∑ σ : Equiv.Perm (Fin (n + 1)), cN m Ψ =
      (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) * (E * cN m Ψ) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  rw [hsum, hrhs] at hel
  have hpos : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin (n + 1))) := by
    exact_mod_cast Fintype.card_pos
  exact mul_left_cancel₀ hpos.ne' hel

/-- **`H²` regularity for bosons**: `Σ_m λ_m² c_m² < ∞`. -/
theorem summable_lam_sq_bos (hws : ∀ σ x, w (pm σ x) = w x) {v : Pot} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW .bos n w hw) v Ψ) :
    Summable fun m => lam m ^ 2 * cN m Ψ ^ 2 := by
  set E := Q (settingW .bos n w hw) v Ψ / ip (μ := μN n) Ψ Ψ
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hV : Continuous V := (continuous_LN v).add hw
  have hs1 := (parsevalW hΨ.1.1).summable
  have hs2 := (parsevalW (memLp_mul_cont hV hΨ.1.1)).summable
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((hs1.mul_left (2 * E ^ 2)).add (hs2.mul_left 2))
  have h := coef_EL_bos hws hΨ m
  have e : lam m ^ 2 * cN m Ψ ^ 2 = (E * cN m Ψ - cN m (fun x => V x * Ψ x)) ^ 2 := by
    rw [← h]; ring
  rw [e]
  nlinarith [sq_nonneg (E * cN m Ψ + cN m (fun x => V x * Ψ x))]

/-! ### Both statistics -/

variable {τ : Stat}

lemma summable_lam_sq_stat (hws : ∀ σ x, w (pm σ x) = w x) {v : Pot} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW τ n w hw) v Ψ) : Summable fun m => lam m ^ 2 * cN m Ψ ^ 2 := by
  cases τ
  · exact summable_lam_sq_bos hws hΨ
  · exact summable_lam_sq hws hΨ

/-- **The density of an interacting ground state has a `C¹` profile** (bosons or fermions). -/
theorem gs_dens_C1_stat (hws : ∀ σ x, w (pm σ x) = w x) {v : Pot} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW τ n w hw) v Ψ) : C1Dens (dens (settingW τ n w hw) Ψ) := by
  have hcl := summable_lam_sq_stat hws hΨ
  refine ⟨KS (fun m => cN m Ψ), KD (fun m => cN m Ψ), (continuous_KD hcl).continuousOn,
    fun t _ => (hasDerivAt_KS hcl t).hasDerivWithinAt, KS_zero, KS_one, dens_eq_KS hΨ.1 hcl⟩

/-- **Interacting `v`-representable densities are meagre** in the space of `N`-representable
densities: `N` bosons or fermions on `[0, 1]`, continuous `v`, continuous relabelling-invariant
`w`. -/
theorem vrep_meagre (hws : ∀ σ x, w (pm σ x) = w x) :
    IsMeagre {x : SN n | PureVRep (settingW τ n w hw) (rhoF x)} :=
  meagre_C1Dens.mono fun x hx => by
    obtain ⟨v, ψ, hψ, -, hd⟩ := hx
    change C1Dens (rhoF (x : L2I))
    rw [← hd]
    exact gs_dens_C1_stat hws hψ

/-- The same for ground-state ensembles. -/
theorem ensvrep_meagre (hws : ∀ σ x, w (pm σ x) = w x) :
    IsMeagre {x : SN n | EnsVRep (settingW τ n w hw) (rhoF x)} :=
  (vrep_meagre (τ := τ) (hw := hw) hws).mono fun _ hx => (ensVRep_iff_W_cont _).1 hx

/-- **Non-`v`-representable densities are residual, hence dense** (bosons or fermions). -/
theorem nonvrep_residual (hws : ∀ σ x, w (pm σ x) = w x) :
    Dense {x : SN n | ¬ EnsVRep (settingW τ n w hw) (rhoF x)} := by
  have : CompleteSpace (SN n) := (isClosed_SN n).completeSpace_coe
  exact dense_of_mem_residual (ensvrep_meagre (τ := τ) (hw := hw) hws)

end DFT.Continuum.Line
