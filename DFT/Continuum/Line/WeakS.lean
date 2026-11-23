/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Realize
import DFT.Continuum.Line.Young

/-!
# `H¹₀` states of a general symmetry type

`DomW τ` (`Line/Weak`) is for bosons and fermions. Here the exchange symmetry is any `SymT`: a set
`G` of relabellings and a character `χ` with `Φ(σx) = χ(σ) Φ(x)` a.e. for `σ ∈ G`. The main case
is the Young symmetry `ymix a` (antisymmetric within the first `a` and within the last `N - a`
particles), the spatial part of a spin-½ state with `a` spins up.

* `DomWS s`, `settingWS s w hw` (same energy form `h0W` and potential map `LN` as `settingW`);
* `DomW_eq_DomWS`: `DomW τ = DomWS τ.toSym`;
* `QWS_eq`, `h0WS_null`, `isGS_WS_of_isNGS`, `cN_pmWS`, `adm_cNWS`, `Fn_le_QWS`, `serWS_mem`;
* **`exists_isNGS_WS_cont`**: a normalised `H¹₀` ground state exists for every continuous `v` and
  continuous `w`, whenever the symmetry type admits a normalised coefficient sequence (for Young
  symmetries, `exists_adm_ymix`); **`exists_isNGS_WY_cont`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ}

/-! ### Weak derivatives of `H¹` functions -/

section h1

variable {Φ Ψ : Cfg n → ℝ}

lemma memLp_dW_H (hΦ : H1W Φ) (k : Fin (n + 1)) : MemLp (dW k Φ) 2 (μN n) := (dW_spec (hΦ.2 k)).1

lemma dW_add_H (hΦ : H1W Φ) (hΨ : H1W Ψ) (k : Fin (n + 1)) :
    dW k (Φ + Ψ) =ᵐ[μN n] dW k Φ + dW k Ψ :=
  dW_ae_eq (IsWD.add hΦ.1 hΨ.1 (dW_spec (hΦ.2 k)) (dW_spec (hΨ.2 k)))

lemma dW_smul_H (hΦ : H1W Φ) (c : ℝ) (k : Fin (n + 1)) : dW k (c • Φ) =ᵐ[μN n] c • dW k Φ :=
  dW_ae_eq (IsWD.const_mul c (dW_spec (hΦ.2 k)))

end h1

/-! ### The state space and the setting -/

/-- `H¹₀` states of symmetry type `s`. -/
def DomWS (s : SymT n) : Submodule ℝ (Cfg n → ℝ) where
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

lemma h1W_of_memS {s : SymT n} {Φ : Cfg n → ℝ} (h : Φ ∈ DomWS s) : H1W Φ := ⟨h.1, h.2.1⟩

/-- The two statistics are symmetry types. -/
lemma DomW_eq_DomWS (τ : Stat) : DomW τ n = DomWS τ.toSym := by
  ext Φ
  exact ⟨fun h => ⟨h.1, h.2.1, fun σ _ => h.2.2 σ⟩, fun h => ⟨h.1, h.2.1, fun σ => h.2.2 σ trivial⟩⟩

/-- `N` particles with exchange symmetry `s` on a line, with all finite-kinetic-energy states. -/
noncomputable def settingWS (s : SymT n) (w : Cfg n → ℝ) (hw : Continuous w) :
    Setting (μN n) Pot where
  D := DomWS s
  h0 := h0W n w
  h0_add a ha b hb c hc := by
    have hk : ∀ k, ∫ x, dW k (a + b) x * dW k c x ∂μN n =
        ∫ x, dW k a x * dW k c x ∂μN n + ∫ x, dW k b x * dW k c x ∂μN n := fun k => by
      rw [← integral_add (int_mul_L2 (memLp_dW_H (h1W_of_memS ha) k)
        (memLp_dW_H (h1W_of_memS hc) k))
        (int_mul_L2 (memLp_dW_H (h1W_of_memS hb) k) (memLp_dW_H (h1W_of_memS hc) k))]
      refine integral_congr_ae ?_
      filter_upwards [dW_add_H (h1W_of_memS ha) (h1W_of_memS hb) k] with x hx
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
      filter_upwards [dW_smul_H (h1W_of_memS ha) r k] with x hx
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

section setting

variable {s : SymT n} {w : Cfg n → ℝ} {hw : Continuous w}

/-- `Q = T + ∫ V ψ²` with `V = Σ_k v(x_k) + w`. -/
lemma QWS_eq (v : Pot) {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomWS s) :
    Q (settingWS s w hw) v Ψ = kinW Ψ + ∫ x, (LN n v x + w x) * (Ψ x * Ψ x) ∂μN n := by
  change h0W n w Ψ Ψ + ∫ x, LN n v x * (Ψ x * Ψ x) ∂μN n = _
  have hsq := int_mul_L2 hΨ.1 hΨ.1
  obtain ⟨C1, hC1⟩ := ae_bound_cont (n := n) (continuous_LN v)
  obtain ⟨C2, hC2⟩ := ae_bound_cont (n := n) hw
  rw [show (fun x => (LN n v x + w x) * (Ψ x * Ψ x)) =
      fun x => LN n v x * (Ψ x * Ψ x) + w x * (Ψ x * Ψ x) from funext fun x => by ring,
    integral_add (hsq.bdd_mul (continuous_LN v).aestronglyMeasurable hC1)
      (hsq.bdd_mul hw.aestronglyMeasurable hC2)]
  simp only [h0W, kinW]; ring

omit hw in
/-- On null states the energy form is nonnegative. -/
lemma h0WS_null (hw : Continuous w) {φ : Cfg n → ℝ} (hφ : φ ∈ DomWS s)
    (h0 : ip (μ := μN n) φ φ = 0) : 0 ≤ (settingWS s w hw).h0 φ φ := by
  have hz : (fun x => φ x * φ x) =ᵐ[μN n] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (φ x)) (int_mul_L2 hφ.1 hφ.1)).1 h0
  have hw0 : ∫ x, w x * (φ x * φ x) ∂μN n = 0 := by
    rw [integral_eq_zero_of_ae]
    filter_upwards [hz] with x hx
    simp only [Pi.zero_apply] at hx ⊢; rw [hx, mul_zero]
  change 0 ≤ h0W n w φ φ
  rw [h0W, hw0, add_zero]
  exact Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => mul_self_nonneg _

/-- Normalised minimisers are ground states. -/
lemma isGS_WS_of_isNGS {v : Pot} {Φ : Cfg n → ℝ} (h : IsNGS (settingWS s w hw) v Φ) :
    IsGS (settingWS s w hw) v Φ :=
  isGS_of_isNGS (fun _ hφ h0 => h0WS_null hw hφ h0) h

end setting

/-! ### Coefficients -/

section coeff

variable {s : SymT n}

lemma cN_pmWS {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomWS s) {σ : Equiv.Perm (Fin (n + 1))} (hσ : s.G σ)
    (m : Fin (n + 1) → ℕ) : cN (pmI σ m) Φ = s.χ σ * cN m Φ := by
  rw [cN_eq, cN_eq, ← integral_pm σ, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hΦ.2.2 σ hσ] with x hx
  simp only [smd_pm, hx]; ring

lemma adm_cNWS {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomWS s) (h1 : ∫ x, Ψ x ^ 2 ∂μN n = 1) :
    Adm s fun m => cN m Ψ :=
  { sq := (parsevalW hΨ.1).summable
    kin := summable_of_sum_le (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg _))
      (sum_lam_le (h1W_of_memS hΨ))
    sym := fun σ hσ m => cN_pmWS hΨ hσ m
    norm := by rw [← h1]; exact (parsevalW hΨ.1).tsum_eq }

lemma Fn_le_QWS {w : Cfg n → ℝ} {hw : Continuous w} (v : Pot) {Ψ : Cfg n → ℝ}
    (hΨ : Ψ ∈ DomWS s) :
    Fn (fun x => LN n v x + w x) (fun m => cN m Ψ) ≤ Q (settingWS s w hw) v Ψ := by
  rw [Fn, Bf_cNW (V := fun x => LN n v x + w x) ((continuous_LN v).add hw) hΨ.1, QWS_eq v hΨ]
  gcongr
  exact Summable.tsum_le_of_sum_le (summable_of_sum_le
    (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg _)) (sum_lam_le (h1W_of_memS hΨ)))
    (sum_lam_le (h1W_of_memS hΨ))

variable {a : (Fin (n + 1) → ℕ) → ℝ}

/-- The series inherits the symmetry of its coefficients (a.e.). -/
theorem serWS_pm (hs : Summable fun m => a m ^ 2) (hsym : InS s a)
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : s.G σ) :
    ∀ᵐ x ∂μN n, serW a (pm σ x) = s.χ σ * serW a x := by
  refine ae_eq_of_cN_eq (memLp_comp_pm memLp_serW σ) (memLp_serW.const_mul _) fun m => ?_
  have h1 : cN m (fun x => serW a (pm σ x)) = cN (pmI σ m) (serW a) := by
    rw [cN_eq, cN_eq, ← integral_pm σ (fun x => smd (pmI σ m) x * serW a x)]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [smd_pm])
  have h2 : cN m (fun x => s.χ σ * serW a x) = s.χ σ * cN m (serW a) := by
    rw [cN_eq, cN_eq, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [h1, h2, cN_serW hs, cN_serW hs]
  exact hsym σ hσ m

/-- **Admissible coefficient sequences are `H¹₀` states** of the same symmetry type. -/
theorem serWS_mem (ha : Dir s a) : serW a ∈ DomWS s :=
  ⟨memLp_serW, fun k => ⟨_, isWD_serW ha.sq ha.kin k⟩, fun _ hσ => serWS_pm ha.sq ha.sym hσ⟩

end coeff

/-! ### Ground states for continuous potentials -/

/-- **Ground states exist in `H¹₀`** for every continuous `v` and continuous `w`, for any symmetry
type that admits a normalised coefficient sequence. -/
theorem exists_isNGS_WS_cont {s : SymT n} (hne : ∃ c : (Fin (n + 1) → ℕ) → ℝ, Adm s c)
    {w : Cfg n → ℝ} (hw : Continuous w) (v : Pot) :
    ∃ Φ, IsNGS (settingWS s w hw) v Φ := by
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hV : Continuous V := (continuous_LN v).add hw
  obtain ⟨B, hB⟩ := (isCompact_univ_pi fun _ => isCompact_Icc :
    IsCompact (CubeC n)).exists_bound_of_continuousOn hV.continuousOn
  have hK := kBd_of_continuous hV (B := B) fun x hx => by simpa [Real.norm_eq_abs] using hB x hx
  obtain ⟨a, ha, hmin⟩ := hK.exists_min hne
  have hD := serWS_mem ha.toDir
  have hcN : (fun m => cN m (serW a)) = a := funext (cN_serW ha.sq)
  have hip : ip (μ := μN n) (serW a) (serW a) = 1 := by
    have h := parsevalW (memLp_serW (a := a))
    calc ip (μ := μN n) (serW a) (serW a) = ∫ x, serW a x ^ 2 ∂μN n :=
          integral_congr_ae (ae_of_all _ fun x => by simp [sq])
      _ = ∑' m, cN m (serW a) ^ 2 := h.tsum_eq.symm
      _ = 1 := by simp only [cN_serW ha.sq]; exact ha.norm
  have hQ : Q (settingWS s w hw) v (serW a) = E0 V s := by
    rw [QWS_eq v hD, kinW_serW ha.toDir, ← hmin, Fn, ← Bf_cNW hV memLp_serW, hcN]
  refine ⟨serW a, ⟨hD, hip⟩, fun Ψ hΨ => ?_⟩
  rw [hQ]
  have h1 : ∫ x, Ψ x ^ 2 ∂μN n = 1 := by
    rw [← hΨ.2]; simp only [ip]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
  exact (csInf_le (hK.bddBelow_Fn s) ⟨_, adm_cNWS hΨ.1 h1, rfl⟩).trans (Fn_le_QWS v hΨ.1)

/-- **Ground states of mixed symmetry `(a, N - a)` exist in `H¹₀`** for every continuous `v` and
continuous `w`. -/
theorem exists_isNGS_WY_cont (a : ℕ) {w : Cfg n → ℝ} (hw : Continuous w) (v : Pot) :
    ∃ Φ, IsNGS (settingWS (ymix a) w hw) v Φ :=
  exists_isNGS_WS_cont (exists_adm_ymix a) hw v

end DFT.Continuum.Line
