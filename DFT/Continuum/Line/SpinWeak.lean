/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.LiebMattisTotal
import DFT.Continuum.Line.YoungPos

/-!
# The Lieb–Mattis theorem for spin-orbital states of finite kinetic energy

The spin results of `Line/LiebMattisTotal` are for spin-orbital states with `C²` components.
Here the components only have finite kinetic energy: they lie in `W0 n`, the `L²` functions with
weak first derivatives and zero boundary values (`H¹₀` of the cube, no exchange symmetry).

* `IsWD.pm`, `dW_pm`: weak derivatives under relabelling.
* `BQW`, `BipW`: the energy `Σ_k ∫ ∂_k f ∂_k g + ∫ (Σ v + w) f g` and the `L²` product on `W0`,
  bilinear, unchanged under a.e. modification, invariant under relabelling.
* `FermW`, `EigW`: fermionic antisymmetry and `S² Ψ = λ Ψ`, almost everywhere.
* `sector_lb_W`: a function of `W0` with a.e. mixed symmetry `(a, N - a)` has energy at least
  `E(a, N - a)` per norm (through its sine coefficients, as for `tl_ae_gs`).
* `EspinW`: the lowest energy at total spin `S` over these states.
* **`EspinW_eq`**: it equals the `C²` value `EspinT`, the ground-state energy of the spatial sector
  `S_z = S`; **`lieb_mattis_total_W`**: `E(S) < E(S + 1)`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine Function

variable {n : ℕ} {a : ℕ}

/-! ### The space `H¹₀` without symmetry -/

/-- `L²` functions with weak first derivatives and zero boundary values. -/
def W0 (n : ℕ) : Submodule ℝ (Cfg n → ℝ) where
  carrier := {Φ | MemLp Φ 2 (μN n) ∧ ∀ k, ∃ G, IsWD k Φ G}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun k => by
      obtain ⟨G, hG⟩ := ha.2 k
      obtain ⟨H, hH⟩ := hb.2 k
      exact ⟨_, IsWD.add ha.1 hb.1 hG hH⟩⟩
  zero_mem' := ⟨MemLp.zero, fun k => ⟨0, IsWD.zero k⟩⟩
  smul_mem' c a ha := ⟨ha.1.const_smul c, fun k => by
      obtain ⟨G, hG⟩ := ha.2 k
      exact ⟨_, IsWD.const_mul c hG⟩⟩

section W0

variable {Φ Ψ : Cfg n → ℝ}

lemma memLp_dW0 (hΦ : Φ ∈ W0 n) (k : Fin (n + 1)) : MemLp (dW k Φ) 2 (μN n) :=
  (dW_spec (hΦ.2 k)).1

lemma dW_add0 (hΦ : Φ ∈ W0 n) (hΨ : Ψ ∈ W0 n) (k : Fin (n + 1)) :
    dW k (Φ + Ψ) =ᵐ[μN n] dW k Φ + dW k Ψ :=
  dW_ae_eq (IsWD.add hΦ.1 hΨ.1 (dW_spec (hΦ.2 k)) (dW_spec (hΨ.2 k)))

lemma dW_smul0 (hΦ : Φ ∈ W0 n) (c : ℝ) (k : Fin (n + 1)) :
    dW k (c • Φ) =ᵐ[μN n] c • dW k Φ :=
  dW_ae_eq (IsWD.const_mul c (dW_spec (hΦ.2 k)))

lemma IsWD.congr {k : Fin (n + 1)} {G : Cfg n → ℝ} (h : IsWD k Φ G) (hΦΨ : Φ =ᵐ[μN n] Ψ) :
    IsWD k Ψ G := by
  refine ⟨h.1, fun φ hφ => ?_⟩
  rw [← h.2 φ hφ]
  refine integral_congr_ae ?_
  filter_upwards [hΦΨ] with x hx
  rw [hx]

lemma dW_congr (hΦ : Φ ∈ W0 n) (hΦΨ : Φ =ᵐ[μN n] Ψ) (k : Fin (n + 1)) :
    dW k Ψ =ᵐ[μN n] dW k Φ :=
  dW_ae_eq ((dW_spec (hΦ.2 k)).congr hΦΨ)

end W0

/-! ### Relabelling -/

lemma mpN (σ : Equiv.Perm (Fin (n + 1))) : MeasurePreserving (pm σ) (μN n) (μN n) := by
  have h := (mp_pm σ).restrict_preimage_emb
    (by rw [← coe_pmE]; exact (pmE σ).measurableEmbedding) (Cube n)
  have hpre : pm σ ⁻¹' Cube n = Cube n := by ext x; exact pm_mem_cube
  rwa [hpre] at h

lemma ae_pm {P : Cfg n → Prop} (h : ∀ᵐ x ∂μN n, P x) (σ : Equiv.Perm (Fin (n + 1))) :
    ∀ᵐ x ∂μN n, P (pm σ x) :=
  (mpN σ).quasiMeasurePreserving.ae h

lemma ae_cube : ∀ᵐ x ∂μN n, x ∈ Cube n := ae_restrict_mem measurableSet_cube

/-- **Weak derivatives under relabelling.** -/
lemma IsWD.comp_pm {k : Fin (n + 1)} {f G : Cfg n → ℝ} (σ : Equiv.Perm (Fin (n + 1)))
    (h : IsWD (σ⁻¹ k) f G) : IsWD k (fun x => f (pm σ x)) (fun x => G (pm σ x)) := by
  refine ⟨h.1.comp_measurePreserving (mpN σ), fun φ hφ => ?_⟩
  set ψ : Cfg n → ℝ := fun y => φ (pm σ⁻¹ y)
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_pm σ⁻¹)
  have hφψ : (fun x => ψ (pm σ x)) = φ := funext fun x => by simp only [ψ, pm_inv_pm]
  have hd : ∀ x, dk k φ x = dk (σ⁻¹ k) ψ (pm σ x) := fun x => by
    have := dk_comp_pm (hψ.differentiable one_ne_zero) σ k x
    rwa [hφψ] at this
  calc ∫ x, f (pm σ x) * dk k φ x ∂μN n
      = ∫ x, (fun y => f y * dk (σ⁻¹ k) ψ y) (pm σ x) ∂μN n := by simp only [hd]
    _ = ∫ y, f y * dk (σ⁻¹ k) ψ y ∂μN n := integral_pm σ (fun y => f y * dk (σ⁻¹ k) ψ y)
    _ = -∫ y, G y * ψ y ∂μN n := h.2 ψ hψ
    _ = -∫ x, G (pm σ x) * φ x ∂μN n := by
      rw [← integral_pm σ (fun y => G y * ψ y)]
      simp only [ψ, pm_inv_pm]

lemma comp_pm_mem_W0 {f : Cfg n → ℝ} (hf : f ∈ W0 n) (σ : Equiv.Perm (Fin (n + 1))) :
    (fun x => f (pm σ x)) ∈ W0 n :=
  ⟨hf.1.comp_measurePreserving (mpN σ), fun k => ⟨_, (dW_spec (hf.2 (σ⁻¹ k))).comp_pm σ⟩⟩

lemma dW_pm {f : Cfg n → ℝ} (hf : f ∈ W0 n) (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    dW k (fun x => f (pm σ x)) =ᵐ[μN n] fun x => dW (σ⁻¹ k) f (pm σ x) :=
  dW_ae_eq ((dW_spec (hf.2 (σ⁻¹ k))).comp_pm σ)

/-! ### `C²` states -/

lemma isWD_dk0 {Φ : Cfg n → ℝ} (hΦ : Φ ∈ D0 n) (k : Fin (n + 1)) : IsWD k Φ (dk k Φ) := by
  obtain ⟨h2, hw⟩ := mem_D0.1 hΦ
  have hcd : Continuous (dk k Φ) := (contDiff_dk h2 k).continuous
  refine ⟨memLp_cont hcd, fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ k
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  rw [integral_cube_ins (F := fun x => Φ x * dk k φ x) k (integrableN (h2.continuous.mul hd)),
    integral_cube_ins (F := fun x => dk k Φ x * φ x) k (integrableN (hcd.mul hφ.continuous)),
    ← integral_neg]
  refine setIntegral_congr_fun measurableSet_cube' fun y _ => ?_
  simp only [integral_Ioo_eq_interval]
  have hc : ∀ {g : Cfg n → ℝ}, Continuous g →
      IntervalIntegrable (fun t => g (Fin.insertNth k t y)) volume 0 1 := fun hg =>
    (hg.comp (continuous_ins k y)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t => Φ (Fin.insertNth k t y)) (v := fun t => φ (Fin.insertNth k t y))
    (fun t _ => hasDerivAt_ins (h2.differentiable (by norm_num)) k y t)
    (fun t _ => hasDerivAt_ins hφd k y t) (hc hcd) (hc hd)]
  have w0 : Φ (Fin.insertNth k 0 y) = 0 := hw _ k (Or.inl (by simp))
  have w1 : Φ (Fin.insertNth k 1 y) = 0 := hw _ k (Or.inr (by simp))
  rw [w0, w1]; ring

lemma D0_le_W0 : D0 n ≤ W0 n := fun _ hΦ =>
  ⟨memLp_cont (mem_D0.1 hΦ).1.continuous, fun k => ⟨_, isWD_dk0 hΦ k⟩⟩

/-! ### Energy and norm -/

/-- The kinetic form. -/
noncomputable def kinB (f g : Cfg n → ℝ) : ℝ := ∑ k, ∫ x, dW k f x * dW k g x ∂μN n

/-- The potential form. -/
noncomputable def potB (V f g : Cfg n → ℝ) : ℝ := ∫ x, V x * (f x * g x) ∂μN n

section forms

variable {f f' g : Cfg n → ℝ}

lemma kinB_symm (f g : Cfg n → ℝ) : kinB f g = kinB g f := by
  simp only [kinB]; congr 1; funext k; congr 1; funext x; ring

lemma potB_symm (V f g : Cfg n → ℝ) : potB V f g = potB V g f := by
  simp only [potB]; congr 1; funext x; ring

lemma kinB_add (hf : f ∈ W0 n) (hf' : f' ∈ W0 n) (hg : g ∈ W0 n) :
    kinB (f + f') g = kinB f g + kinB f' g := by
  simp only [kinB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← integral_add (int_mul_L2 (memLp_dW0 hf k) (memLp_dW0 hg k))
    (int_mul_L2 (memLp_dW0 hf' k) (memLp_dW0 hg k))]
  refine integral_congr_ae ?_
  filter_upwards [dW_add0 hf hf' k] with x hx
  simp only [hx, Pi.add_apply]; ring

lemma kinB_smul (hf : f ∈ W0 n) (c : ℝ) : kinB (c • f) g = c * kinB f g := by
  simp only [kinB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [dW_smul0 hf c k] with x hx
  simp only [hx, Pi.smul_apply, smul_eq_mul]; ring

lemma potB_add {V : Cfg n → ℝ} (hV : Continuous V) (hf : f ∈ W0 n) (hf' : f' ∈ W0 n)
    (hg : g ∈ W0 n) : potB V (f + f') g = potB V f g + potB V f' g := by
  obtain ⟨C, hC⟩ := ae_bound_cont hV
  simp only [potB]
  rw [← integral_add ((int_mul_L2 hf.1 hg.1).bdd_mul hV.aestronglyMeasurable hC)
    ((int_mul_L2 hf'.1 hg.1).bdd_mul hV.aestronglyMeasurable hC)]
  congr 1; funext x; simp only [Pi.add_apply]; ring

lemma potB_smul (V : Cfg n → ℝ) (c : ℝ) : potB V (c • f) g = c * potB V f g := by
  simp only [potB]
  rw [← integral_const_mul]; congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma kinB_congr (hf : f ∈ W0 n) (hg : g ∈ W0 n) {f₁ g₁ : Cfg n → ℝ} (h1 : f =ᵐ[μN n] f₁)
    (h2 : g =ᵐ[μN n] g₁) : kinB f₁ g₁ = kinB f g := by
  simp only [kinB]
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  filter_upwards [dW_congr hf h1 k, dW_congr hg h2 k] with x hx hy
  rw [hx, hy]

lemma potB_congr (V : Cfg n → ℝ) {f₁ g₁ : Cfg n → ℝ} (h1 : f =ᵐ[μN n] f₁)
    (h2 : g =ᵐ[μN n] g₁) : potB V f₁ g₁ = potB V f g := by
  simp only [potB]
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with x hx hy
  rw [hx, hy]

end forms

section bil

variable (w : Cfg n → ℝ) (hw : Continuous w) (v : Pot)

/-- The potential `Σ v(x_k) + w`. -/
noncomputable def Vt : Cfg n → ℝ := fun x => LN n v x + w x

omit hw in
lemma continuous_Vt (hw : Continuous w) : Continuous (Vt w v) := (continuous_LN v).add hw

/-- The energy form on `W0`. -/
noncomputable def BQW : W0 n →ₗ[ℝ] W0 n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => kinB (f : Cfg n → ℝ) g + potB (Vt w v) f g)
    (fun f f' g => by
      simp only [Submodule.coe_add]
      rw [kinB_add f.2 f'.2 g.2, potB_add (continuous_Vt w v hw) f.2 f'.2 g.2]; ring)
    (fun c f g => by
      simp only [Submodule.coe_smul, smul_eq_mul]
      rw [kinB_smul f.2, potB_smul]; ring)
    (fun f g g' => by
      simp only [Submodule.coe_add]
      rw [kinB_symm _ (_ + _), potB_symm _ _ (_ + _), kinB_add g.2 g'.2 f.2,
        potB_add (continuous_Vt w v hw) g.2 g'.2 f.2, kinB_symm (g : Cfg n → ℝ),
        kinB_symm (g' : Cfg n → ℝ), potB_symm _ (g : Cfg n → ℝ), potB_symm _ (g' : Cfg n → ℝ)]
      ring)
    (fun c f g => by
      simp only [Submodule.coe_smul, smul_eq_mul]
      rw [kinB_symm _ (c • _), potB_symm _ _ (c • _), kinB_smul g.2, potB_smul,
        kinB_symm (g : Cfg n → ℝ), potB_symm _ (g : Cfg n → ℝ)]
      ring)

/-- The `L²` product on `W0`. -/
noncomputable def BipW : W0 n →ₗ[ℝ] W0 n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => ∫ x, (f : Cfg n → ℝ) x * (g : Cfg n → ℝ) x ∂μN n)
    (fun f f' g => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact integral_add (int_mul_L2 f.2.1 g.2.1) (int_mul_L2 f'.2.1 g.2.1))
    (fun c f g => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun f g g' => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (int_mul_L2 f.2.1 g.2.1) (int_mul_L2 f.2.1 g'.2.1))
    (fun c f g => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
      exact integral_const_mul c _)

lemma BQW_apply (f g : W0 n) :
    BQW w hw v f g = kinB (f : Cfg n → ℝ) g + potB (Vt w v) f g := rfl

lemma BipW_apply (f g : W0 n) :
    BipW f g = ∫ x, (f : Cfg n → ℝ) x * (g : Cfg n → ℝ) x ∂μN n := rfl

lemma BipW_symm (f g : W0 n) : BipW f g = BipW g f := by
  simp only [BipW_apply]; congr 1; funext x; ring

lemma BipW_self_nonneg (f : W0 n) : 0 ≤ BipW f f :=
  integral_nonneg fun _ => mul_self_nonneg _

lemma BQW_congr {f f' g g' : W0 n} (h1 : (f : Cfg n → ℝ) =ᵐ[μN n] f')
    (h2 : (g : Cfg n → ℝ) =ᵐ[μN n] g') : BQW w hw v f' g' = BQW w hw v f g := by
  rw [BQW_apply, BQW_apply, kinB_congr f.2 g.2 h1 h2, potB_congr _ h1 h2]

lemma BipW_congr {f f' g g' : W0 n} (h1 : (f : Cfg n → ℝ) =ᵐ[μN n] f')
    (h2 : (g : Cfg n → ℝ) =ᵐ[μN n] g') : BipW f' g' = BipW f g := by
  rw [BipW_apply, BipW_apply]
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with x hx hy
  rw [hx, hy]

lemma ae_zero_of_BipW {f : W0 n} (h : BipW f f = 0) : (f : Cfg n → ℝ) =ᵐ[μN n] 0 := by
  rw [BipW_apply, integral_eq_zero_iff_of_nonneg (fun _ => mul_self_nonneg _)
    (int_mul_L2 f.2.1 f.2.1)] at h
  filter_upwards [h] with x hx
  exact mul_self_eq_zero.1 hx

lemma BQW_zero_of_BipW {f : W0 n} (h : BipW f f = 0) : BQW w hw v f f = 0 := by
  have h0 := ae_zero_of_BipW h
  rw [BQW_congr w hw v (f := 0) (g := 0) (f' := f) (g' := f) h0.symm h0.symm]
  simp

lemma BQW_pm (hws : ∀ σ x, w (pm σ x) = w x) (f : W0 n) (σ : Equiv.Perm (Fin (n + 1))) :
    BQW w hw v ⟨_, comp_pm_mem_W0 f.2 σ⟩ ⟨_, comp_pm_mem_W0 f.2 σ⟩ = BQW w hw v f f := by
  rw [BQW_apply, BQW_apply]
  congr 1
  · simp only [kinB]
    have e : ∀ k, ∫ x, dW k (fun y => (f : Cfg n → ℝ) (pm σ y)) x *
        dW k (fun y => (f : Cfg n → ℝ) (pm σ y)) x ∂μN n =
        ∫ x, dW (σ⁻¹ k) (f : Cfg n → ℝ) x * dW (σ⁻¹ k) (f : Cfg n → ℝ) x ∂μN n := fun k => by
      rw [← integral_pm σ (fun x => dW (σ⁻¹ k) (f : Cfg n → ℝ) x * dW (σ⁻¹ k) f x)]
      refine integral_congr_ae ?_
      filter_upwards [dW_pm f.2 σ k] with x hx
      rw [hx]
    simp only [e]
    exact Equiv.sum_comp σ⁻¹ (fun j => ∫ x, dW j (f : Cfg n → ℝ) x * dW j f x ∂μN n)
  · simp only [potB]
    rw [← integral_pm σ (fun x => Vt w v x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x))]
    congr 1; funext x
    simp only [Vt, LN_pm, hws]

lemma BipW_pm (f : W0 n) (σ : Equiv.Perm (Fin (n + 1))) :
    BipW ⟨_, comp_pm_mem_W0 f.2 σ⟩ ⟨_, comp_pm_mem_W0 f.2 σ⟩ = BipW f f := by
  rw [BipW_apply, BipW_apply]
  exact integral_pm σ (fun x => (f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x)

/-- On `C²` states the weak energy is the classical one. -/
lemma BQW_eq_BQ (f : D0 n) :
    BQW w hw v ⟨f, D0_le_W0 f.2⟩ ⟨f, D0_le_W0 f.2⟩ = BQ w hw v f f := by
  have h2 := (mem_D0.1 f.2).1
  have hcd : ∀ k, Continuous (dk k (f : Cfg n → ℝ)) := fun k => (contDiff_dk h2 k).continuous
  rw [BQW_apply, BQ_apply]
  simp only [kinB, potB, h0N, Vt]
  rw [integral_finsetSum (f := fun k x => dk k (f : Cfg n → ℝ) x * dk k (f : Cfg n → ℝ) x) _
    fun k _ => integrableN ((hcd k).mul (hcd k))]
  have hc := h2.continuous
  rw [show (fun x => (LN n v x + w x) * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x)) =
      fun x => w x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x) +
        LN n v x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x) from funext fun x => by ring,
    integral_add (f := fun x => w x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x))
      (g := fun x => LN n v x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x))
      (integrableN (hw.mul (hc.mul hc))) (integrableN ((continuous_LN v).mul (hc.mul hc)))]
  rw [← add_assoc]
  congr 2
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  filter_upwards [dW_ae_eq (isWD_dk0 f.2 k)] with x hx
  rw [hx]

end bil

/-! ### Spin-orbital states of finite kinetic energy -/

/-- Evaluation at a point. -/
noncomputable def evW (x : Cfg n) : W0 n →ₗ[ℝ] ℝ := (LinearMap.proj x).comp (W0 n).subtype

@[simp] lemma evW_apply (x : Cfg n) (f : W0 n) : evW x f = (f : Cfg n → ℝ) x := rfl

/-- Fermionic antisymmetry, almost everywhere. -/
def FermW (u : SpinC n → W0 n) : Prop :=
  ∀ᵐ x ∂μN n, ∀ σ s, evW (pm σ x) (u (rel σ s)) = sgn σ * evW x (u s)

/-- `S² Ψ = λ Ψ`, almost everywhere. -/
def EigW (lam : ℝ) (u : SpinC n → W0 n) : Prop :=
  ∀ᵐ x ∂μN n, ∀ s, evW x (S2 u s) = lam * evW x (u s)

lemma FermW_Sp {u : SpinC n → W0 n} (hu : FermW u) : FermW (Sp u) := by
  filter_upwards [hu] with x hx
  intro σ s
  rw [Sp_map, Sp_map, Sp_rel]
  have e : (fun t => evW (pm σ x) (u (rel σ t))) = fun t => sgn σ * evW x (u t) := by
    funext t; exact hx σ t
  rw [e]
  change Sp ((sgn σ) • fun t => evW x (u t)) s = _
  rw [map_smul]; rfl

lemma FermW_Pc {u : SpinC n → W0 n} (hu : FermW u) (c : ℕ) : FermW (Pc c u) := by
  filter_upwards [hu] with x hx
  intro σ s
  simp only [Pc_apply, nup_rel]
  split_ifs
  · exact hx σ s
  · simp

lemma EigW_Sp {lam : ℝ} {u : SpinC n → W0 n} (h : EigW lam u) : EigW lam (Sp u) := by
  filter_upwards [h] with x hx
  intro s
  have hc := congrArg (fun T : Module.End ℝ (SpinC n → W0 n) => T u s)
    (S2_comm_Sp (n := n) (V := W0 n))
  simp only [Module.End.mul_apply] at hc
  rw [hc, Sp_map, Sp_map]
  rw [show (fun t => evW x (S2 u t)) = lam • fun t => evW x (u t) from funext fun t => hx t,
    map_smul]
  rfl

lemma EigW_Pc {lam : ℝ} {u : SpinC n → W0 n} (h : EigW lam u) (c : ℕ) : EigW lam (Pc c u) := by
  filter_upwards [h] with x hx
  intro s
  rw [S2_Pc, Pc_map, Pc_map]
  simp only [Pc_apply]
  split_ifs
  · exact hx s
  · simp

lemma ae_S2 {lam : ℝ} {u : SpinC n → W0 n} (h : EigW lam u) (s : SpinC n) :
    ((S2 u s : W0 n) : Cfg n → ℝ) =ᵐ[μN n] ((lam • u s : W0 n) : Cfg n → ℝ) := by
  filter_upwards [h] with x hx
  have := hx s
  simpa using this

/-- The component at `sc c` of a fermionic state has a.e. mixed symmetry `(c, N - c)`. -/
lemma sym_sc_W {u : SpinC n → W0 n} (hu : FermW u) (c : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : YG c σ) : ∀ᵐ x ∂μN n,
      (u (sc n c) : Cfg n → ℝ) (pm σ x) = sgn σ * (u (sc n c) : Cfg n → ℝ) x := by
  filter_upwards [hu] with x hx
  have := hx σ (sc n c)
  rwa [(rel_sc_iff σ).2 hσ] at this

/-- **Sector reduction** for forms that see only a.e. classes and are relabelling invariant. -/
lemma sector_reduce_W (B : W0 n →ₗ[ℝ] W0 n →ₗ[ℝ] ℝ)
    (hBc : ∀ f f' : W0 n, (f : Cfg n → ℝ) =ᵐ[μN n] f' → B f' f' = B f f)
    (hB : ∀ (f : W0 n) σ, B ⟨_, comp_pm_mem_W0 f.2 σ⟩ ⟨_, comp_pm_mem_W0 f.2 σ⟩ = B f f)
    {u : SpinC n → W0 n} (hu : FermW u) {c : ℕ} (hc : Pc c u = u) :
    ∑ s, B (u s) (u s) =
      ((Finset.univ.filter fun s : SpinC n => nup s = c).card : ℝ) *
        B (u (sc n c)) (u (sc n c)) := by
  classical
  have hz : ∀ s, nup s ≠ c → u s = 0 := fun s hs => by
    rw [← hc]; simp [Pc_apply, hs]
  have hterm : ∀ s, nup s = c → B (u s) (u s) = B (u (sc n c)) (u (sc n c)) := by
    intro s hs
    obtain ⟨τ, hτ⟩ := exists_rel_sc hs
    set g : W0 n := ⟨_, comp_pm_mem_W0 (u (sc n c)).2 τ⁻¹⟩
    have he : ((sgn τ • g : W0 n) : Cfg n → ℝ) =ᵐ[μN n] (u s : Cfg n → ℝ) := by
      have h := ae_pm hu τ⁻¹
      filter_upwards [h] with y hy
      have := hy τ (sc n c)
      rw [pm_pm_inv, hτ] at this
      simp only [evW_apply] at this
      simp only [g, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [this]
    rw [hBc _ _ he, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, hB, ← mul_assoc,
      sgn_mul_self, one_mul]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : SpinC n => nup s = c)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun s : SpinC n => ¬ nup s = c)
    fun s hs => by rw [hz s (Finset.mem_filter.1 hs).2]; simp, add_zero]
  rw [Finset.sum_congr rfl fun s hs => hterm s (Finset.mem_filter.1 hs).2,
    Finset.sum_const, nsmul_eq_mul]

/-! ### The sector bound for `H¹₀` functions of mixed symmetry -/

section sector

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} (hws : ∀ σ x, w (pm σ x) = w x)
  {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
  (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x)
include hws hF hVF

/-- **A finite-kinetic-energy function of mixed symmetry `(a, N - a)` has energy at least
`E(a, N - a)` per norm.** -/
theorem sector_lb_W {Φ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a) w hw) v Φ) {f : Cfg n → ℝ}
    (hf : f ∈ W0 n) (hsym : ∀ σ, YG a σ → ∀ᵐ x ∂μN n, f (pm σ x) = sgn σ * f x) :
    Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ * ∫ x, f x * f x ∂μN n ≤
      kinB f f + potB (Vt w v) f f := by
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hVc : Continuous V := (continuous_LN v).add hw
  have hVs : ∀ σ x, V (pm σ x) = V x := fun σ x => by simp only [V, LN_pm, hws]
  obtain ⟨b, hb0, hbS, hK, hG⟩ := kernel_of_smooth hVc hF hVF
  -- `E(a) ≤ E0`
  obtain ⟨a0, ha0, hmin0⟩ := exists_min hb0 hbS hK (V := V) (exists_adm_ymix (n := n) a)
  obtain ⟨hΦ0, hc0⟩ := ser_min2S hb0 hbS hK hVs ha0 hmin0 (by norm_num) (by norm_num) hG
  have hip0 : ip (μ := μN n) (ser a0) (ser a0) = 1 := by
    rw [ip_eq_tsum hΦ0.1.continuous]; simp only [hc0]; exact ha0.norm
  have hQ0 : Q (settingS (ymix a) w hw) v (ser a0) = E0 V (ymix a) := by
    rw [Q_eq_Fn_S hw v hΦ0, funext hc0, hmin0]
  have hE : Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ ≤ E0 V (ymix a) := by
    have := hΦ.2.2 (ser a0) hΦ0
    rw [hip0, mul_one, hQ0] at this
    rw [div_le_iff₀ hΦ.2.1]; linarith
  -- the coefficients of `f`
  set c : (Fin (n + 1) → ℕ) → ℝ := fun m => cN m f
  have hsymc : InS (ymix (n := n) a) c := fun σ hσ m => by
    change cN (pmI σ m) f = sgn σ * cN m f
    rw [cN_eq, cN_eq, ← integral_pm σ, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hsym σ hσ] with x hx
    simp only [smd_pm]
    rw [hx]; ring
  have hkin : ∀ s : Finset (Fin (n + 1) → ℕ), ∑ m ∈ s, lam m * c m ^ 2 ≤ kinB f f :=
    sum_lam_le_wd (G := fun k => dW k f) fun k => dW_spec (hf.2 k)
  have hsum := summable_of_sum_le (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg _)) hkin
  have hD : Dir (ymix (n := n) a) c := ⟨(parsevalW hf.1).summable, hsum, hsymc⟩
  have h1 := Fn_ge hb0 hbS hK hD
  rw [(parsevalW hf.1).tsum_eq] at h1
  have hFn : Fn V c ≤ kinB f f + potB (Vt w v) f f := by
    rw [Fn, Bf_cNW (V := V) hVc hf.1,
      show potB (Vt w v) f f = ∫ x, V x * (f x * f x) ∂μN n from rfl]
    gcongr
    exact Summable.tsum_le_of_sum_le hsum hkin
  have hsq : ∫ x, f x ^ 2 ∂μN n = ∫ x, f x * f x ∂μN n := by simp only [sq]
  rw [hsq] at h1
  have hint : 0 ≤ ∫ x, f x * f x ∂μN n := integral_nonneg fun _ => mul_self_nonneg _
  calc Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ * ∫ x, f x * f x ∂μN n
      ≤ E0 V (ymix a) * ∫ x, f x * f x ∂μN n := mul_le_mul_of_nonneg_right hE hint
    _ ≤ _ := h1.trans hFn

end sector

/-! ### The theorem -/

section main

variable (w : Cfg n → ℝ) (hw : Continuous w) (v : Pot)

/-- The energy of a spin-orbital state of finite kinetic energy. -/
noncomputable def QSW (u : SpinC n → W0 n) : ℝ := ∑ s, BQW w hw v (u s) (u s)

/-- Its norm. -/
noncomputable def ipSW (u : SpinC n → W0 n) : ℝ := ∑ s, BipW (u s) (u s)

/-- Fermionic finite-kinetic-energy spin-orbital states of total spin `S = a - N/2`. -/
def SpinClassW (a : ℕ) (u : SpinC n → W0 n) : Prop :=
  FermW u ∧ 0 < ipSW u ∧ EigW (lamS n a) u

/-- **`E(S)` over states of finite kinetic energy.** -/
noncomputable def EspinW (a : ℕ) : EReal :=
  ⨅ (u : SpinC n → W0 n) (_ : SpinClassW a u), ((QSW w hw v u / ipSW u : ℝ) : EReal)

/-- The inclusion of `C²` states. -/
noncomputable def ιW : D0 n →ₗ[ℝ] W0 n := Submodule.inclusion D0_le_W0

variable {w hw v}

/-- Enlarging the state space can only lower `E(S)`. -/
theorem EspinW_le_EspinT : EspinW w hw v a ≤ EspinT w hw v a := by
  refine le_iInf₂ fun u hu => ?_
  set u' : SpinC n → W0 n := fun s => ιW (u s)
  have hQ : QSW w hw v u' = QS w hw v u :=
    Finset.sum_congr rfl fun s _ => BQW_eq_BQ w hw v (u s)
  have hI : ipSW u' = ipS u := Finset.sum_congr rfl fun s _ => rfl
  have hF' : FermW u' := ae_of_all _ fun x σ s => hu.1 σ s x
  have hE' : EigW (lamS n a) u' := by
    filter_upwards [ae_cube] with x hx
    intro s
    have e : S2 u' s = ιW (S2 u s) := (S2_map ιW u s).symm
    rw [e]
    exact hu.2.2 s x hx
  have h := iInf₂_le (f := fun (u : SpinC n → W0 n) (_ : SpinClassW a u) =>
    ((QSW w hw v u / ipSW u : ℝ) : EReal)) u' ⟨hF', by rw [hI]; exact hu.2.1, hE'⟩
  rw [hQ, hI] at h
  exact h

variable (hws : ∀ σ x, w (pm σ x) = w x)
  {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
  (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x)
include hws hF hVF

/-- **The lower bound** for finite-kinetic-energy states of total spin `S' = a' - N/2 ≥ 0`. -/
theorem lower_bound_W {a' : ℕ} (ha' : ((n : ℝ) + 1) / 2 ≤ a') (ha'N : a' ≤ n + 1)
    {Φ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a') w hw) v Φ)
    {u : SpinC n → W0 n} (hFu : FermW u) (heig : EigW (lamS n a') u) :
    Q (settingS (ymix a') w hw) v Φ / ip (μ := μN n) Φ Φ * ipSW u ≤ QSW w hw v u := by
  refine multiplet_lb (BQW w hw v) BipW BipW_symm BipW_self_nonneg
    (fun f h => BQW_zero_of_BipW w hw v h)
    (fun u => FermW u ∧ EigW (lamS n a') u) (fun u hu => ⟨FermW_Sp hu.1, EigW_Sp hu.2⟩)
    (fun u c hu => ⟨FermW_Pc hu.1 c, EigW_Pc hu.2 c⟩) ha' (fun u hu s => ?_) (fun u hu s => ?_)
    (fun φ hφ hc => ?_) ⟨hFu, heig⟩
  · rw [BQW_congr w hw v (f := u s) (g := lamS n a' • u s) (f' := u s) (g' := S2 u s)
      (Filter.EventuallyEq.refl _ _) (ae_S2 hu.2 s).symm, map_smul, smul_eq_mul]
  · rw [BipW_congr (f := u s) (g := lamS n a' • u s) (f' := u s) (g' := S2 u s)
      (Filter.EventuallyEq.refl _ _) (ae_S2 hu.2 s).symm, map_smul, smul_eq_mul]
  · rw [sector_reduce_W (BQW w hw v) (fun f f' h => BQW_congr w hw v h h)
        (BQW_pm w hw v hws) hφ.1 hc,
      sector_reduce_W BipW (fun f f' h => BipW_congr h h) BipW_pm hφ.1 hc]
    have h := sector_lb_W hws hF hVF hΦ (φ (sc n a')).2 (sym_sc_W hφ.1 a')
    have hK := (card_sector_pos (n := n) (c := a') ha'N).le
    rw [BQW_apply, BipW_apply]
    nlinarith

/-- **`E(S)` over finite-kinetic-energy states is the ground-state energy of the spatial sector
`S_z = S`** (`a ≥ b ≥ 1`), the same as over `C²` states. -/
theorem EspinW_eq {b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a)
    {Φ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a) w hw) v Φ) :
    EspinW w hw v a = ((Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ : ℝ) : EReal) := by
  refine le_antisymm ?_ (le_iInf₂ fun u hu => ?_)
  · rw [← Espin_total_eq hws hF hVF hab hb1 hba hΦ]; exact EspinW_le_EspinT
  · refine EReal.coe_le_coe_iff.2 ?_
    have hlb := lower_bound_W hws hF hVF (a' := a) (by
      have : (b : ℝ) ≤ a := by exact_mod_cast hba
      have : (a : ℝ) + b = n + 1 := by exact_mod_cast hab
      linarith) (by omega) hΦ hu.1 hu.2.2
    rw [le_div_iff₀ hu.2.1]; linarith

/-- **The Lieb–Mattis theorem for states of finite kinetic energy**: `E(S) < E(S + 1)` for
`S ≥ 0`. -/
theorem lieb_mattis_total_W {b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a) :
    EspinW w hw v a < EspinW w hw v (a + 1) := by
  obtain ⟨Φ, hΦ, -⟩ := exists_isGS_smoothS a hws hF hVF (hw := hw)
  obtain ⟨Ψ, hΨ, -⟩ := exists_isGS_smoothS (a + 1) hws hF hVF (hw := hw)
  have hlm := lieb_mattis hws hF hVF hab hb1 hba hΦ hΨ
  rw [EspinW_eq hws hF hVF hab hb1 hba hΦ]
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hlm) (le_iInf₂ fun u hu => ?_)
  refine EReal.coe_le_coe_iff.2 ?_
  have hlb := lower_bound_W hws hF hVF (a' := a + 1) (by
    have : (b : ℝ) ≤ a := by exact_mod_cast hba
    have : (a : ℝ) + b = n + 1 := by exact_mod_cast hab
    push_cast; linarith) (by omega) hΨ hu.1 hu.2.2
  rw [le_div_iff₀ hu.2.1]; linarith

end main

end DFT.Continuum.Line
