/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.SpinBridge
import DFT.Continuum.Line.HardCore
import DFT.Continuum.Line.WeakHK

/-!
# Spin-orbital states of finite kinetic energy

Spin-orbital states whose components only have finite kinetic energy: they lie in `W0 n`, the `L²`
functions with weak first derivatives and zero boundary values (`H¹₀` of the cube, no exchange
symmetry).

* `lamS`, `sum_sectors`, `multiplet_lb`: the multiplet lower bound along `S₊`, for any pair of
  bilinear forms.

* `IsWD.pm`, `dW_pm`: weak derivatives under relabelling.
* `BQW`, `BipW`: the energy `Σ_k ∫ ∂_k f ∂_k g + ∫ (Σ v + w) f g` and the `L²` product on `W0`,
  bilinear, unchanged under a.e. modification, invariant under relabelling.
* `FermW`, `EigW`: fermionic antisymmetry and `S² Ψ = λ Ψ`, almost everywhere.
* `EspinW`: the lowest energy at total spin `S` over these states (computed in
  `Line/LiebMattisTotalW`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine Function

variable {n : ℕ} {a : ℕ}

/-- `S(S+1)` with `S = a - N/2`. -/
noncomputable def lamS (n a : ℕ) : ℝ :=
  ((a : ℝ) - ((n : ℝ) + 1) / 2) * ((a : ℝ) - ((n : ℝ) + 1) / 2 + 1)

/-! ### The multiplet lower bound, for any pair of forms -/

section multiplet

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma sum_sectors (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u : SpinC n → V) :
    ∑ s, B (u s) (u s) = ∑ c ∈ Finset.range (n + 2), ∑ s, B (Pc c u s) (Pc c u s) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pc_apply]
  have : ∀ c, B (if nup s = c then u s else 0) (if nup s = c then u s else 0) =
      if nup s = c then B (u s) (u s) else 0 := fun c => by split_ifs <;> simp
  simp only [this]
  have hs : nup s ∈ Finset.range (n + 2) := Finset.mem_range.2 (by have := nup_le s; omega)
  simp only [Finset.sum_ite_eq, hs, ite_true]

/-- **The lower bound along a multiplet** of total spin `S' = a' - N/2 ≥ 0`, abstractly: a class
`P` of states of total spin `S'`, closed under `S₊` and the sector projections, with energy and
norm forms; if the top sector `S_z = S'` satisfies `E' ‖·‖ ≤ energy`, so does every state. -/
theorem multiplet_lb (BQ' Bi' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hBis : ∀ f g, Bi' f g = Bi' g f)
    (hnn : ∀ f, 0 ≤ Bi' f f) (hz : ∀ f, Bi' f f = 0 → BQ' f f = 0)
    (P : (SpinC n → V) → Prop) (hPSp : ∀ u, P u → P (Sp u))
    (hPPc : ∀ u c, P u → P (Pc c u)) {a' : ℕ} (ha' : ((n : ℝ) + 1) / 2 ≤ a')
    (hQ2 : ∀ u, P u → ∀ s, BQ' (u s) (S2 u s) = lamS n a' * BQ' (u s) (u s))
    (hI2 : ∀ u, P u → ∀ s, Bi' (u s) (S2 u s) = lamS n a' * Bi' (u s) (u s)) {E' : ℝ}
    (hbase : ∀ u, P u → Pc a' u = u → E' * ∑ s, Bi' (u s) (u s) ≤ ∑ s, BQ' (u s) (u s))
    {u : SpinC n → V} (hu : P u) : E' * ∑ s, Bi' (u s) (u s) ≤ ∑ s, BQ' (u s) (u s) := by
  set S' : ℝ := (a' : ℝ) - ((n : ℝ) + 1) / 2
  have hS' : 0 ≤ S' := by simp only [S']; linarith
  have hlam : lamS n a' = S' * (S' + 1) := rfl
  have hsn : ∀ φ : SpinC n → V, 0 ≤ ∑ s, Bi' (φ s) (φ s) := fun φ =>
    Finset.sum_nonneg fun s _ => hnn _
  have hzero : ∀ φ : SpinC n → V, ∑ s, Bi' (φ s) (φ s) = 0 → ∑ s, BQ' (φ s) (φ s) = 0 :=
    fun φ h => Finset.sum_eq_zero fun s hs =>
      hz _ ((Finset.sum_eq_zero_iff_of_nonneg fun s _ => hnn (φ s)).1 h s hs)
  -- sectors at and below the top
  have key : ∀ k c (φ : SpinC n → V), c + k = a' → P φ → Pc c φ = φ →
      E' * ∑ s, Bi' (φ s) (φ s) ≤ ∑ s, BQ' (φ s) (φ s) := by
    intro k
    induction k with
    | zero =>
      intro c φ hck hφ hc
      simp only [add_zero] at hck
      subst hck
      exact hbase φ hφ hc
    | succ k ih =>
      intro c φ hck hφ hc
      rcases (hsn φ).eq_or_lt with h0 | hpos
      · rw [← h0, hzero φ h0.symm, mul_zero]
      set M : ℝ := (c : ℝ) - ((n : ℝ) + 1) / 2
      have hSM : S' - M = k + 1 := by
        simp only [S', M]; have : (c : ℝ) + (k + 1 : ℕ) = a' := by exact_mod_cast hck
        push_cast at this; linarith
      have hm := ladder_Sm_gen Bi' hc (hI2 φ hφ) hBis
      have hp := ladder_Sp_gen Bi' hc (hI2 φ hφ)
      have hq := ladder_Sp_gen BQ' hc (hQ2 φ hφ)
      have hcm : 0 ≤ lamS n a' - M ^ 2 + M := by
        have := hsn (Sm φ)
        rw [hm] at this
        exact nonneg_of_mul_nonneg_left this hpos
      have hcp : 0 < lamS n a' - M ^ 2 - M := by
        rw [hlam] at hcm ⊢
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      have hIH := ih (c + 1) (Sp φ) (by omega) (hPSp φ hφ) (by rw [← Sp_Pc, hc])
      rw [hp, hq, ← mul_assoc, mul_comm E', mul_assoc] at hIH
      exact le_of_mul_le_mul_left hIH hcp
  -- sectors above the top are empty
  have above : ∀ c, a' < c → ∑ s, Bi' (Pc c u s) (Pc c u s) = 0 := by
    intro c hc
    have hφ := hPPc u c hu
    have hp := ladder_Sp_gen Bi' (Pc_Pc c u) (hI2 _ hφ)
    set M : ℝ := (c : ℝ) - ((n : ℝ) + 1) / 2
    have hMS : S' < M := by
      simp only [S', M]; have : (a' : ℝ) < c := by exact_mod_cast hc
      linarith
    have hneg : lamS n a' - M ^ 2 - M < 0 := by rw [hlam]; nlinarith
    have hnn' := hsn (Sp (Pc c u))
    rw [hp] at hnn'
    exact le_antisymm (nonpos_of_mul_nonneg_right hnn' hneg) (hsn _)
  have hsec : ∀ c ∈ Finset.range (n + 2),
      E' * ∑ s, Bi' (Pc c u s) (Pc c u s) ≤ ∑ s, BQ' (Pc c u s) (Pc c u s) := by
    intro c _
    by_cases hc : c ≤ a'
    · exact key (a' - c) c (Pc c u) (by omega) (hPPc u c hu) (Pc_Pc c u)
    · have h0 := above c (by omega)
      rw [h0, hzero _ h0, mul_zero]
  rw [sum_sectors BQ', sum_sectors Bi', Finset.mul_sum]
  exact Finset.sum_le_sum hsec

end multiplet

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

end main

end DFT.Continuum.Line
