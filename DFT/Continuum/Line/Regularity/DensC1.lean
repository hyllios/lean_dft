/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.KohnSham.Dense
import DFT.Continuum.Line.KohnSham.MeagreC1
import DFT.Continuum.Line.Regularity.DensSeries
import DFT.Continuum.Line.Regularity.H2

/-!
# Interacting ground-state densities have a `C¹` profile, and are meagre

For a state `Ψ ∈ H¹₀` with sine coefficients `c`, the density is the profile `K` of
`Line/DensSeries`:
`ρ(v) = ∫ v K`. Indeed `ρ(v) = N ⟨Ψ, v(x₀) Ψ⟩ = N B_{v(x₀)}(c, c)`, and the kernel of `v(x₀)` is
diagonal in the indices of the other particles. If moreover `Σ λ² c² < ∞` (the ground state of
`N` fermions, `Line/H2`), `K` is `C¹`. With `Line/MeagreC1`:

* `dens_eq_x0`, `Ker_x0`, `Kc_x0`, `Bf_x0`;
* **`dens_eq_KS`**: `ρ_Ψ(v) = ∫ v K`;
* **`gs_dens_C1`**: the density of an interacting fermionic ground state has a `C¹` profile;
* **`fer_vrep_meagre`**, **`fer_ensvrep_meagre`**: interacting `v`-representable densities of `N`
  fermions (continuous `v`, continuous relabelling-invariant `w`) are meagre in the space of
  `N`-representable densities.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology Sine

variable {n : ℕ} {τ : Stat}

/-! ### The density through one particle -/

lemma dens_eq_x0 {w : Cfg n → ℝ} {hw : Continuous w} {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW τ n)
    (v : C01) : dens (settingW τ n w hw) Ψ v = (n + 1) * ∫ x, iccExt v (x 0) * (Ψ x * Ψ x) ∂μN n := by
  have hv : Continuous fun x : Cfg n => iccExt v (x 0) := (continuous_iccExt v).comp (continuous_apply 0)
  have hF : Integrable (fun x : Cfg n => iccExt v (x 0) * (Ψ x * Ψ x)) (μN n) := by
    obtain ⟨C, hC⟩ := ae_bound_cont hv
    exact (int_mul_L2 hΨ.1 hΨ.1).bdd_mul hv.aestronglyMeasurable hC
  rw [dens_eq_rhoNW hΨ v, integral_cube_cons' hF, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  simp only [Fin.cons_zero, rhoN, marg, integral_const_mul]
  rw [show (fun y => Ψ (Fin.cons t y) * Ψ (Fin.cons t y)) = fun y => Ψ (Fin.cons t y) ^ 2 from
    funext fun y => (sq _).symm]
  ring

/-! ### The kernel of `v(x₀)` -/

lemma Ker_x0 (v : C01) (m' m : Fin (n + 1) → ℕ) :
    Ker (fun x => iccExt v (x 0)) m' m =
      if Fin.tail m' = Fin.tail m then aK v (m' 0) (m 0) else 0 := by
  set f : Fin (n + 1) → ℝ → ℝ := fun j t =>
    if j = 0 then sn (m' 0 + 1) t * (iccExt v t * sn (m 0 + 1) t)
    else sn (m' j + 1) t * sn (m j + 1) t
  have e : (fun x : Cfg n => smd m' x * (iccExt v (x 0) * smd m x)) = fun x => ∏ j, f j (x j) := by
    funext x
    simp only [smd, f, Fin.prod_univ_succ, ↓reduceIte, Fin.succ_ne_zero, Finset.prod_mul_distrib]
    ring
  rw [Ker, e, muN_eq, integral_fintype_prod_eq_prod (f := f), Fin.prod_univ_succ]
  simp only [f, ↓reduceIte, Fin.succ_ne_zero]
  simp only [sn_orthonormal (Nat.succ_pos _) (Nat.succ_pos _), Nat.succ_inj]
  rw [Finset.prod_boole]
  have hiff : (∀ i ∈ (Finset.univ : Finset (Fin n)), m' i.succ = m i.succ) ↔
      Fin.tail m' = Fin.tail m := by
    simp only [Finset.mem_univ, true_implies, funext_iff, Fin.tail]
  by_cases h : Fin.tail m' = Fin.tail m
  · have h2 := hiff.2 h
    simp only [eq_true h2, eq_true h, ↓reduceIte, mul_one]; rfl
  · have h2 : ¬ ∀ i ∈ (Finset.univ : Finset (Fin n)), m' i.succ = m i.succ :=
      fun h' => h (hiff.1 h')
    simp only [eq_false h2, eq_false h, ↓reduceIte, mul_zero]

lemma Kc_x0 (v : C01) (c : (Fin (n + 1) → ℕ) → ℝ) (m' : Fin (n + 1) → ℕ) :
    Kc (fun x => iccExt v (x 0)) c m' = ∑' k, aK v (m' 0) k * c (Fin.cons k (Fin.tail m')) := by
  rw [Kc]
  have hinj : Function.Injective fun k : ℕ => (Fin.cons k (Fin.tail m') : Fin (n + 1) → ℕ) :=
    Fin.cons_left_injective (α := fun _ => ℕ) (Fin.tail m')
  have hsupp : Function.support (fun m => Ker (fun x => iccExt v (x 0)) m' m * c m) ⊆
      Set.range fun k : ℕ => (Fin.cons k (Fin.tail m') : Fin (n + 1) → ℕ) := by
    intro m hm
    refine ⟨m 0, ?_⟩
    by_contra hne
    apply hm
    have ht : Fin.tail m' ≠ Fin.tail m := fun h => hne (by
      change Fin.cons (m 0) (Fin.tail m') = m
      rw [h, Fin.cons_self_tail])
    simp only [Ker_x0, eq_false ht, ↓reduceIte, zero_mul]
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun k => ?_
  simp only [Ker_x0, Fin.tail_cons, ↓reduceIte, Fin.cons_zero]

lemma Bf_x0 (v : C01) {c : (Fin (n + 1) → ℕ) → ℝ} (hc2 : Summable fun m => c m ^ 2) :
    Bf (fun x => iccExt v (x 0)) c c =
      ∑' μ, ∑' k', cc c k' μ * ∑' k, aK v k' k * cc c k μ := by
  obtain ⟨C, hK⟩ := kBd_cont (n := n) ((continuous_iccExt v).comp (continuous_apply 0))
  have hs : Summable fun m => c m * Kc (fun x => iccExt v (x 0)) c m :=
    summable_mul_of_sq hc2 (hK.sq hc2)
  have hs' : Summable fun p => c (consE n p) * Kc (fun x => iccExt v (x 0)) c (consE n p) :=
    (consE n).summable_iff.2 hs
  rw [Bf, ← (consE n).tsum_eq (fun m => c m * Kc (fun x => iccExt v (x 0)) c m),
    hs'.tsum_prod' fun μ => hs'.prod_factor μ]
  refine tsum_congr fun μ => tsum_congr fun k' => ?_
  simp only [consE_apply, Kc_x0, Fin.cons_zero, Fin.tail_cons, cc]

/-! ### The density is the profile `K` -/

variable {w : Cfg n → ℝ} {hw : Continuous w}

/-- **The density is the profile `K`**: `ρ_Ψ(v) = ∫ v K` for `Ψ ∈ H¹₀` with `Σ λ² c² < ∞`. -/
theorem dens_eq_KS {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW τ n)
    (hcl : Summable fun m => lam m ^ 2 * cN m Ψ ^ 2) :
    dens (settingW τ n w hw) Ψ = fun v => ∫ t, iccExt v t * KS (fun m => cN m Ψ) t ∂vol01 := by
  have hc2 : Summable fun m => cN m Ψ ^ 2 := (parsevalW hΨ.1).summable
  funext v
  show _ = ∫ t, iccExt v t * KS (fun m => cN m Ψ) t ∂vol01
  rw [dens_eq_x0 hΨ v, integral_KS hcl v, ← Bf_x0 v hc2,
    Bf_cNW (V := fun x : Cfg n => iccExt v (x 0)) ((continuous_iccExt v).comp (continuous_apply 0)) hΨ.1]

/-- **The density of an interacting fermionic ground state has a `C¹` profile.** -/
theorem gs_dens_C1 (hws : ∀ σ x, w (pm σ x) = w x) {v : C01} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW .fer n w hw) v Ψ) : C1Dens (dens (settingW .fer n w hw) Ψ) := by
  have hcl := summable_lam_sq hws hΨ
  have hc2 : Summable fun m => cN m Ψ ^ 2 := (parsevalW hΨ.1.1).summable
  refine ⟨KS (fun m => cN m Ψ), KD (fun m => cN m Ψ), (continuous_KD hcl).continuousOn,
    fun t _ => (hasDerivAt_KS hcl t).hasDerivWithinAt, KS_zero, KS_one, dens_eq_KS hΨ.1 hcl⟩

/-- **Interacting `v`-representable densities of `N` fermions are meagre** in the space of
`N`-representable densities (continuous `v`, continuous relabelling-invariant `w`). -/
theorem fer_vrep_meagre (hws : ∀ σ x, w (pm σ x) = w x) :
    IsMeagre {x : SN n | PureVRep (settingW .fer n w hw) (rhoF x)} :=
  meagre_C1Dens.mono fun x hx => by
    obtain ⟨v, ψ, hψ, -, hd⟩ := hx
    change C1Dens (rhoF (x : L2I))
    rw [← hd]
    exact gs_dens_C1 hws hψ

/-- The same for ground-state ensembles. -/
theorem fer_ensvrep_meagre (hws : ∀ σ x, w (pm σ x) = w x) :
    IsMeagre {x : SN n | EnsVRep (settingW .fer n w hw) (rhoF x)} :=
  (fer_vrep_meagre (hw := hw) hws).mono fun _ hx => (ensVRep_iff_W_cont _).1 hx

/-- **Non-`v`-representable densities are residual, hence dense.** -/
theorem fer_nonvrep_dense (hws : ∀ σ x, w (pm σ x) = w x) :
    Dense {x : SN n | ¬ EnsVRep (settingW .fer n w hw) (rhoF x)} := by
  have : CompleteSpace (SN n) := (isClosed_SN n).completeSpace_coe
  exact dense_of_mem_residual (fer_ensvrep_meagre (hw := hw) hws)

end DFT.Continuum.Line
