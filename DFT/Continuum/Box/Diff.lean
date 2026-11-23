/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Dense

/-!
# v-representable densities are dense (one particle in a box)

The converse of the Hellmann–Feynman inequality: every supergradient of the ground-state energy
`E` at `v` is the density of the ground state of `v`. With Brøndsted–Rockafellar (`Box/Dense`),
pure v-representable densities are dense, in the dual norm of `C([0, 1])`, among all densities of
finite Lieb functional.

No spectral gap is needed: the ground state is the shooting solution `ψ_{E*}`, and by Gronwall it
moves by `O(‖δv‖)` when `v` moves (`E*` is `1`-Lipschitz). So ground-state densities depend
continuously on `v`, and `E` is Gâteaux differentiable with derivative the ground-state density.

* `fsh`, `Nsh`: the shooting ground state on `[0, 1]` and its weighted integrals `∫ h ψ_{E*}²`.
* `exists_gsN`: a normalised ground state with density `∫ u ψ_{E*}² / ∫ ψ_{E*}²` and energy `E*`;
  `estar_eq_gsEr`: `E* = E`.
* `fsh_close`: `|ψ_{E*(v')} - ψ_{E*(v)}| ≤ C ‖v' - v‖` on `[0, 1]`.
* `tendsto_Nsh`: the weighted integrals are continuous along lines `v + t u`.
* **`supergrad_eq`**: a supergradient of `E` at `v` is the density of a ground state of `v`.
* **`dense_pureVRep`**: every density of finite Lieb functional is a dual-norm limit of pure
  v-representable densities; `dense_pureVRep_of_nst` for N-representable ones.
-/

namespace DFT

namespace Continuum

namespace Box

open MeasureTheory Set Filter Topology

/-- The (unnormalised) shooting ground state of `v`. -/
noncomputable def fsh (v : Pot) (s : ℝ) : ℝ := (sol v (Estar v) s).1

lemma continuousOn_fsh (v : Pot) : ContinuousOn (fsh v) (Icc 0 1) := (continuousOn_sol v _).fst

/-- The weighted integral `∫ h ψ_{E*}²`. -/
noncomputable def Nsh (v : Pot) (h : ℝ → ℝ) : ℝ := ∫ s, h s * fsh v s ^ 2 ∂μ1

lemma integrable_mu1_of_continuousOn {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 1)) :
    Integrable F μ1 :=
  (hF.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- A normalised ground state of `v` built from the shooting solution. -/
theorem exists_gsN (v : Pot) : ∃ ψ, IsNGS setting v ψ ∧ Q setting v ψ = Estar v ∧
    0 < Nsh v (fun _ => 1) ∧ ∀ u : Pot, dens setting ψ u = Nsh v (ext u) / Nsh v (fun _ => 1) := by
  obtain ⟨ψe, hD, heq, hQ, hpos, hlow⟩ := gs_data v
  have hcongr : ∀ h : ℝ → ℝ, ∫ s, h s * ψe s ^ 2 ∂μ1 = Nsh v h := fun h =>
    integral_congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [heq x ⟨by linarith [hx.1], by linarith [hx.2]⟩]; rfl)
  have hip : ip (μ := μ1) ψe ψe = Nsh v (fun _ => 1) := by
    rw [ip_eq_sq, ← hcongr]; simp only [one_mul]
  set D := Nsh v (fun _ => 1)
  have hDpos : 0 < D := hip ▸ hpos
  set c := (Real.sqrt D)⁻¹
  have hc2 : c * c = D⁻¹ := by
    simp only [c]; rw [← mul_inv, Real.mul_self_sqrt hDpos.le]
  have hc2' : c * c * ip (μ := μ1) ψe ψe = 1 := by rw [hc2, hip, inv_mul_cancel₀ hDpos.ne']
  have hcD : c • ψe ∈ Dom := Dom.smul_mem c hD
  have hQc : Q setting v (c • ψe) = Estar v := by
    rw [Q_smul_self (S := setting) v c hD, hQ]
    calc c * c * (Estar v * ip (μ := μ1) ψe ψe) = Estar v * (c * c * ip (μ := μ1) ψe ψe) := by
          ring
      _ = Estar v := by rw [hc2', mul_one]
  refine ⟨c • ψe, ⟨⟨hcD, by rw [ip_smul_self, hc2']⟩, fun φ hφ => ?_⟩, hQc, hDpos, fun u => ?_⟩
  · rw [hQc]
    have := hlow φ hφ.1
    rwa [hφ.2, mul_one] at this
  · rw [dens_eq_sq]
    simp only [Pi.smul_apply, smul_eq_mul]
    have : ∫ t, ext u t * (c * ψe t) ^ 2 ∂μ1 = (c * c) * ∫ t, ext u t * ψe t ^ 2 ∂μ1 := by
      rw [← integral_const_mul]; congr 1; funext t; ring
    rw [this, hcongr, hc2, div_eq_inv_mul]

/-- The shooting energy is the ground-state energy. -/
theorem estar_eq_gsEr (v : Pot) : Estar v = gsEr v := by
  obtain ⟨ψ, hψ, hQ, -⟩ := exists_gsN v
  rw [gsEr_eq_of_isNGS hψ, hQ]

lemma estar_lipschitz (v w : Pot) : |Estar v - Estar w| ≤ ‖v - w‖ := by
  rw [estar_eq_gsEr, estar_eq_gsEr]; exact gsEr_lipschitz v w

lemma gronwall_le {K a t : ℝ} (hK : 0 < K) (ha : 0 ≤ a) (ht : t ∈ Icc (0 : ℝ) 1) :
    gronwallBound 0 K a t ≤ a * ((Real.exp K - 1) / K) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  simp only [zero_mul, zero_add]
  have he : Real.exp (K * t) - 1 ≤ Real.exp K - 1 := by
    have : K * t ≤ K := by nlinarith [ht.2]
    linarith [Real.exp_le_exp.mpr this]
  calc a / K * (Real.exp (K * t) - 1) ≤ a / K * (Real.exp K - 1) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = a * ((Real.exp K - 1) / K) := by ring

/-- A bound for the shooting ground state on `[0, 1]`. -/
lemma fsh_bound (v : Pot) : ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc (0 : ℝ) 1, ‖sol v (Estar v) s‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_sol v (Estar v))
  exact ⟨max M 0, le_max_right _ _, fun s hs => (hM s hs).trans (le_max_left _ _)⟩

/-- **The shooting ground state is Lipschitz in the potential** (uniformly on `[0, 1]`). -/
theorem fsh_close (v : Pot) : ∃ C, 0 ≤ C ∧ ∀ v' : Pot, ‖v' - v‖ ≤ 1 →
    ∀ s ∈ Icc (0 : ℝ) 1, |fsh v' s - fsh v s| ≤ C * ‖v' - v‖ := by
  obtain ⟨M, hM0, hM⟩ := fsh_bound v
  set E := Estar v
  set K := 1 + (‖v‖ + 1 + (|E| + 1))
  have hK : 0 < K := by positivity
  have heK : 0 ≤ (Real.exp K - 1) / K := by
    have : 0 ≤ Real.exp K - 1 := by linarith [Real.add_one_le_exp K]
    positivity
  refine ⟨2 * M * ((Real.exp K - 1) / K), by positivity, fun v' hv' s hs => ?_⟩
  set E' := Estar v'
  have hE' : |E' - E| ≤ ‖v' - v‖ := estar_lipschitz v' v
  have hB : ∀ t ∈ Icc (0 : ℝ) 1, |Wof v' E' t| ≤ ‖v‖ + 1 + (|E| + 1) := by
    intro t _
    have h1 := abs_ext_le v' t
    have h2 : ‖v'‖ ≤ ‖v‖ + 1 := by linarith [norm_sub_norm_le v' v]
    have h3 : |E'| ≤ |E| + 1 := by linarith [abs_sub_abs_le_abs_sub E' E]
    calc |Wof v' E' t| = |ext v' t - E'| := rfl
      _ ≤ |ext v' t| + |E'| := abs_sub _ _
      _ ≤ _ := by linarith
  have hε : ∀ t ∈ Icc (0 : ℝ) 1, |Wof v' E' t - Wof v E t| ≤ 2 * ‖v' - v‖ := by
    intro t _
    have h1 := abs_ext_le (v' - v) t
    have hx : Wof v' E' t - Wof v E t = ext (v' - v) t - (E' - E) := by
      simp only [Wof, ext, ContinuousMap.sub_apply]; ring
    rw [hx]
    calc |ext (v' - v) t - (E' - E)| ≤ |ext (v' - v) t| + |E' - E| := abs_sub _ _
      _ ≤ _ := by linarith
  have h := sol_dist_le (by rw [sol_zero, sol_zero]) (sol_deriv v' E') (sol_deriv v E) hB hM hε s hs
  have hg := gronwall_le hK (by positivity : 0 ≤ 2 * ‖v' - v‖ * M) hs
  calc |fsh v' s - fsh v s| ≤ ‖sol v' E' s - sol v E s‖ := fst_le_norm _ _
    _ ≤ _ := h.trans hg
    _ = 2 * M * ((Real.exp K - 1) / K) * ‖v' - v‖ := by ring

/-- Weighted integrals of squares of close functions are close. -/
lemma int_sq_close {h f g : ℝ → ℝ} (hh : ContinuousOn h (Icc 0 1)) (hf : ContinuousOn f (Icc 0 1))
    (hg : ContinuousOn g (Icc 0 1)) {H δ M : ℝ} (hH : ∀ s ∈ Icc (0 : ℝ) 1, |h s| ≤ H)
    (hδ : ∀ s ∈ Icc (0 : ℝ) 1, |f s - g s| ≤ δ) (hM : ∀ s ∈ Icc (0 : ℝ) 1, |g s| ≤ M) :
    |∫ s, h s * f s ^ 2 ∂μ1 - ∫ s, h s * g s ^ 2 ∂μ1| ≤ H * (δ * (2 * M + δ)) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0 h0)
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0 h0)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 h0)
  rw [← integral_sub (f := fun s => h s * f s ^ 2) (g := fun s => h s * g s ^ 2)
    (integrable_mu1_of_continuousOn (hh.mul (hf.pow 2)))
    (integrable_mu1_of_continuousOn (hh.mul (hg.pow 2))), ← Real.norm_eq_abs]
  have hb := norm_setIntegral_le_of_norm_le_const_ae' (μ := volume) (s := Ioo (0 : ℝ) 1)
    (f := fun s => h s * f s ^ 2 - h s * g s ^ 2) (C := H * (δ * (2 * M + δ)))
    (by simp [Real.volume_Ioo]) (Eventually.of_forall fun s hs => ?_)
  · refine hb.trans (le_of_eq ?_)
    simp [Measure.real, Real.volume_Ioo]
  · have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
    have e : h s * f s ^ 2 - h s * g s ^ 2 = h s * ((f s - g s) * (f s + g s)) := by ring
    rw [e, Real.norm_eq_abs, abs_mul, abs_mul]
    have hfg : |f s + g s| ≤ 2 * M + δ := by
      have := abs_add_le (f s - g s + g s) (g s)
      rw [sub_add_cancel] at this
      have := abs_add_le (f s - g s) (g s)
      rw [sub_add_cancel] at this
      linarith [hδ s hs', hM s hs', abs_add_le (f s) (g s)]
    exact mul_le_mul (hH s hs') (mul_le_mul (hδ s hs') hfg (abs_nonneg _) hδ0)
      (by positivity) hH0

/-- The weighted integrals `∫ h ψ_{E*}²` are continuous along lines `v + t u`. -/
theorem tendsto_Nsh (v u : Pot) {h : ℝ → ℝ} (hh : ContinuousOn h (Icc 0 1)) {H : ℝ}
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, |h s| ≤ H) :
    Tendsto (fun t : ℝ => Nsh (v + t • u) h) (𝓝 0) (𝓝 (Nsh v h)) := by
  obtain ⟨C, hC0, hC⟩ := fsh_close v
  obtain ⟨M, hM0, hM⟩ := fsh_bound v
  have hMf : ∀ s ∈ Icc (0 : ℝ) 1, |fsh v s| ≤ M := fun s hs =>
    (show |(sol v (Estar v) s).1| ≤ ‖sol v (Estar v) s‖ by
      rw [← Real.norm_eq_abs]; exact norm_fst_le _).trans (hM s hs)
  have hnorm : ∀ t : ℝ, ‖(v + t • u) - v‖ = |t| * ‖u‖ := fun t => by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  set g : ℝ → ℝ := fun t => H * (C * (|t| * ‖u‖) * (2 * M + C * (|t| * ‖u‖)))
  have hg : Tendsto g (𝓝 0) (𝓝 0) := by
    have : Continuous g := by fun_prop
    simpa [g] using this.tendsto 0
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), |t| * ‖u‖ < 1 := by
    have : Continuous fun t : ℝ => |t| * ‖u‖ := by fun_prop
    exact (this.tendsto 0).eventually_lt_const (by simp)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hg
  filter_upwards [hev] with t ht
  have hle : ‖(v + t • u) - v‖ ≤ 1 := by rw [hnorm]; exact ht.le
  rw [Real.norm_eq_abs]
  refine int_sq_close hh (continuousOn_fsh _) (continuousOn_fsh v) hH (fun s hs => ?_) hMf
  rw [← hnorm]; exact hC _ hle s hs

/-- **Converse of Hellmann–Feynman.** A supergradient of the ground-state energy at `v` is the
density of a normalised ground state of `v`. -/
theorem supergrad_eq {v : Pot} {ρ' : StrongDual ℝ Pot}
    (hρ' : ∀ w, gsEr w ≤ gsEr v + ρ' (w - v)) :
    ∃ ψ, ∃ hψ : IsNGS setting v ψ, ρ' = densL hψ.1 := by
  obtain ⟨ψ, hψ, -, hD, hdens⟩ := exists_gsN v
  have key : ∀ u : Pot, dens setting ψ u ≤ ρ' u := by
    intro u
    have h1 : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 1) := continuousOn_const
    have hr := (tendsto_Nsh v u (continuous_ext u).continuousOn (fun s _ => abs_ext_le u s)).div
      (tendsto_Nsh v u h1 (H := 1) (fun s _ => by simp)) hD.ne'
    rw [← hdens] at hr
    refine le_of_tendsto (hr.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t (ht : t ∈ Ioi (0 : ℝ)) => ?_)
    change Nsh (v + t • u) (ext u) / Nsh (v + t • u) (fun _ => 1) ≤ ρ' u
    obtain ⟨ψt, hψt, -, -, hdt⟩ := exists_gsN (v + t • u)
    rw [← hdt]
    have hE := hρ' (v + t • u)
    rw [gsEr_eq_of_isNGS hψt, Q_shift hψt.1.1 v, add_sub_cancel_left, dens_smul',
      map_smul, smul_eq_mul] at hE
    have hlow := gsEr_le v hψt.1
    have : t * dens setting ψt u ≤ t * ρ' u := by linarith
    exact le_of_mul_le_mul_left this (mem_Ioi.mp ht)
  refine ⟨ψ, hψ, ContinuousLinearMap.ext fun u => le_antisymm ?_ (key u)⟩
  have h := key (-u)
  rw [map_neg, show -u = (-1 : ℝ) • u by simp, dens_smul'] at h
  rw [densL_apply]
  linarith

/-- **v-representable densities are dense.** Every density of finite Lieb functional is within any
`η > 0`, in the dual norm of `C([0, 1])`, of the density of a normalised ground state of some
continuous potential. -/
theorem dense_pureVRep (ρ : StrongDual ℝ Pot) {c : ℝ} (hF : liebF setting ρ ≤ (c : EReal))
    {η : ℝ} (hη : 0 < η) :
    ∃ (v : Pot) (ρ' : StrongDual ℝ Pot), ‖ρ' - ρ‖ ≤ η ∧ PureDens setting v ρ' := by
  obtain ⟨v, ρ', hn, hs, -⟩ := dense_supergrad ρ hF hη
  obtain ⟨ψ, hψ, rfl⟩ := supergrad_eq hs
  refine ⟨v, densL hψ.1, hn, ψ, isGS_of_isNGS (fun φ _ _ => kin_nonneg φ) hψ, hψ.1.2, rfl⟩

/-- Every N-representable density is a dual-norm limit of pure v-representable densities. -/
theorem dense_pureVRep_of_nst {φ : ℝ → ℝ} (hφ : φ ∈ Nst setting) {η : ℝ} (hη : 0 < η) :
    ∃ (v : Pot) (ρ' : StrongDual ℝ Pot), ‖ρ' - densL hφ‖ ≤ η ∧ PureDens setting v ρ' :=
  dense_pureVRep (densL hφ) (liebF_le_h0 hφ) hη

end Box

end Continuum

end DFT
