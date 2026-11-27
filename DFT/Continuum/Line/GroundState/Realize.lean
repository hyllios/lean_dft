/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.GroundState.WeakHK
import DFT.Continuum.Sine.Cont
import DFT.Continuum.Sine.Exists

/-!
# Ground states in `H¹₀` for continuous potentials

The converse of `Line/Complete`: every admissible coefficient sequence `a` (square summable, finite
kinetic energy `Σ λ_m a_m²`, exchange symmetry `τ`) is the sequence of sine coefficients of an
`H¹₀` state, with exactly that kinetic energy.

* `serW a = Σ_m a_m s_m`, the sum in `L²` of the cube (the `s_m` are a Hilbert basis);
* its weak derivatives are `dserW k a = Σ_m π(m_k+1) a_m c^k_m` (the `c^k_m` are orthonormal),
  checked term by term against `C¹` test functions: `∂ₖ s_m = π(m_k+1) c^k_m` and `s_m` vanishes on
  the walls (`isWD_smd`);
* `serW_mem`, `cN_serW`, `kinW_serW`.

With the coefficient-space minimiser for continuous potentials (`Sine/Cont`) this gives
**`exists_isNGS_W_cont`**: for every continuous `v` and continuous interaction `w`, the `H¹₀`
Hamiltonian has a normalised ground state, with no smoothness assumption.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology Sine

variable {n : ℕ} {τ : Stat}

/-! ### Orthonormal series in a Hilbert space -/

lemma orth_series {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {v : ι → E} (hv : Orthonormal ℝ v) {c : ι → ℝ} (hc : Summable fun i => c i ^ 2) :
    HasSum (fun i => c i • v i) (∑' i, c i • v i) ∧
      (∀ j, inner ℝ (v j) (∑' i, c i • v i) = c j) ∧
      HasSum (fun i => c i ^ 2) (‖∑' i, c i • v i‖ ^ 2) := by
  classical
  have hs : Summable fun i => c i • v i := by
    have := (hv.orthogonalFamily.summable_iff_norm_sq_summable (fun i => (c i : ℝ))).2
      (by simpa [Real.norm_eq_abs, sq_abs] using hc)
    simpa [LinearIsometry.toSpanSingleton_apply] using this
  have hinner : ∀ j, inner ℝ (v j) (∑' i, c i • v i) = c j := fun j => by
    have h := hs.hasSum.mapL (innerSL ℝ (v j))
    have e : (fun i => innerSL ℝ (v j) (c i • v i)) = fun i => if i = j then c j else 0 := by
      funext i
      rw [innerSL_apply_apply, inner_smul_right, orthonormal_iff_ite.1 hv j i]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Ne.symm hij, hij]
    rw [e, innerSL_apply_apply] at h
    exact h.unique (hasSum_ite_eq j (c j))
  refine ⟨hs.hasSum, hinner, ?_⟩
  have h := hs.hasSum.mapL (innerSL ℝ (∑' i, c i • v i))
  have e : (fun i => innerSL ℝ (∑' i, c i • v i) (c i • v i)) = fun i => c i ^ 2 := by
    funext i; rw [innerSL_apply_apply, inner_smul_right, real_inner_comm, hinner, sq]
  rw [e, innerSL_apply_apply, real_inner_self_eq_norm_sq] at h
  exact h

/-! ### Integration by parts for the sines -/

/-- Integration by parts: a `C¹` function vanishing on the walls has its classical derivatives as
weak derivatives. -/
lemma isWD_of_C1 {Φ : Cfg n → ℝ} (hC1 : ContDiff ℝ 1 Φ)
    (hface : ∀ x k, (x k = 0 ∨ x k = 1) → Φ x = 0) (k : Fin (n + 1)) : IsWD k Φ (dk k Φ) := by
  have hdc : Continuous (dk k Φ) := continuous_dk_of_C1 hC1 k
  refine ⟨memLp_cont hdc, fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ k
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  rw [integral_cube_ins (F := fun x => Φ x * dk k φ x) k (integrableN (hC1.continuous.mul hd)),
    integral_cube_ins (F := fun x => dk k Φ x * φ x) k (integrableN (hdc.mul hφ.continuous)),
    ← integral_neg]
  refine setIntegral_congr_fun measurableSet_cube' fun y _ => ?_
  simp only [integral_Ioo_eq_interval]
  have hc : ∀ {g : Cfg n → ℝ}, Continuous g →
      IntervalIntegrable (fun t => g (Fin.insertNth k t y)) volume 0 1 := fun hg =>
    (hg.comp (continuous_ins k y)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t => Φ (Fin.insertNth k t y)) (v := fun t => φ (Fin.insertNth k t y))
    (fun t _ => hasDerivAt_ins (hC1.differentiable one_ne_zero) k y t)
    (fun t _ => hasDerivAt_ins hφd k y t) (hc hdc) (hc hd)]
  have w0 : Φ (Fin.insertNth k 0 y) = 0 := hface _ k (Or.inl (by simp))
  have w1 : Φ (Fin.insertNth k 1 y) = 0 := hface _ k (Or.inr (by simp))
  rw [w0, w1]; ring

lemma isWD_of_C2 {Φ : Cfg n → ℝ} (hC : ContDiff ℝ 2 Φ)
    (hface : ∀ x k, (x k = 0 ∨ x k = 1) → Φ x = 0) (k : Fin (n + 1)) : IsWD k Φ (dk k Φ) :=
  isWD_of_C1 (hC.of_le (by norm_num)) hface k

/-- `∂ₖ s_m = π(m_k+1) c^k_m`. -/
lemma dk_smd (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (x : Cfg n) :
    dk k (smd m) x = π * (m k + 1) * cmd k m x := by
  have h := dk_smd_update m x k (x k)
  rw [Function.update_eq_self] at h
  have hc : cmd k m x = cs (m k) (x k) * ∏ j ∈ Finset.univ.erase k, sn (m j + 1) (x j) := by
    rw [cmd, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    congr 1
    · simp [cfac]
    · exact Finset.prod_congr rfl fun j hj => by simp [cfac, Finset.ne_of_mem_erase hj]
  rw [h, hc, cs]; push_cast; ring

lemma isWD_smd (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) :
    IsWD k (smd m) (fun x => π * (m k + 1) * cmd k m x) := by
  have h := isWD_of_C2 (contDiff_smd m) (fun x j hj => smd_face m x j hj) k
  have e : dk k (smd m) = fun x => π * (m k + 1) * cmd k m x := funext (dk_smd k m)
  rwa [e] at h

/-! ### The series and its weak derivatives -/

/-- `c^k_m` as an element of `L²`. -/
noncomputable def cL (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) : HN n :=
  (memLp_cont (contDiff_cmd k m).continuous).toLp

lemma inner_toLp_toLp {f g : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) (hg : MemLp g 2 (μN n)) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μN n := by
  rw [inner_toLp_left]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hg] with x hx
  rw [hx]

lemma cL_orthonormal (k : Fin (n + 1)) : Orthonormal ℝ (cL (n := n) k) := by
  rw [orthonormal_iff_ite]
  intro m m'
  rw [cL, cL, inner_toLp_toLp, cmd_orthonormal]

/-- The sine series `Σ_m a_m s_m` (a representative of its `L²` sum). -/
noncomputable def serW (a : (Fin (n + 1) → ℕ) → ℝ) : Cfg n → ℝ :=
  ((∑' m, a m • eN m : HN n) : Cfg n → ℝ)

/-- The candidate weak derivative `Σ_m π(m_k+1) a_m c^k_m`. -/
noncomputable def dserW (k : Fin (n + 1)) (a : (Fin (n + 1) → ℕ) → ℝ) : Cfg n → ℝ :=
  ((∑' m, (π * (m k + 1) * a m) • cL k m : HN n) : Cfg n → ℝ)

lemma sq_le_lam (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (x : ℝ) :
    (π * (m k + 1) * x) ^ 2 ≤ lam m * x ^ 2 := by
  have hk : ((m k : ℝ) + 1) ^ 2 ≤ (ksq m : ℝ) := by
    simp only [ksq]; push_cast
    exact Finset.single_le_sum (f := fun j => ((m j : ℝ) + 1) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ k)
  simp only [lam]
  have : (π * (m k + 1) * x) ^ 2 = π ^ 2 * ((m k : ℝ) + 1) ^ 2 * x ^ 2 := by ring
  rw [this]
  gcongr

lemma summable_dcoef {a : (Fin (n + 1) → ℕ) → ℝ} (hk : Summable fun m => lam m * a m ^ 2)
    (k : Fin (n + 1)) : Summable fun m => (π * (m k + 1) * a m) ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => sq_le_lam k m (a m)) hk

variable {a : (Fin (n + 1) → ℕ) → ℝ}

lemma cN_serW (hs : Summable fun m => a m ^ 2) (m : Fin (n + 1) → ℕ) : cN m (serW a) = a m := by
  rw [cN_eq, serW, ← inner_eN]
  exact (orth_series eN_orthonormal hs).2.1 m

lemma memLp_serW : MemLp (serW a) 2 (μN n) := Lp.memLp _

/-- `∫ F ψ = ⟨ψ, F⟩` for continuous `ψ`. -/
lemma integral_mul_cont_eq_inner (F : HN n) {ψ : Cfg n → ℝ} (hψ : Continuous ψ) :
    ∫ x, (F : Cfg n → ℝ) x * ψ x ∂μN n = inner ℝ ((memLp_cont hψ).toLp ψ) F := by
  rw [inner_toLp_left]
  exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)

/-- **The weak derivative of the series.** -/
theorem isWD_serW (hs : Summable fun m => a m ^ 2) (hk : Summable fun m => lam m * a m ^ 2)
    (k : Fin (n + 1)) : IsWD k (serW a) (dserW k a) := by
  refine ⟨Lp.memLp _, fun φ hφ => ?_⟩
  have hψ := continuous_dk_of_C1 hφ k
  have h1 := ((orth_series eN_orthonormal hs).1).mapL (innerSL ℝ ((memLp_cont hψ).toLp (dk k φ)))
  have h2 := ((orth_series (cL_orthonormal k) (summable_dcoef hk k)).1).mapL
    (innerSL ℝ ((memLp_cont hφ.continuous).toLp φ))
  simp only [innerSL_apply_apply, inner_smul_right] at h1 h2
  rw [serW, dserW, integral_mul_cont_eq_inner _ hψ, integral_mul_cont_eq_inner _ hφ.continuous]
  refine h1.unique ?_
  have e : (fun m => a m * inner ℝ ((memLp_cont hψ).toLp (dk k φ)) (eN m)) =
      fun m => -((π * (m k + 1) * a m) * inner ℝ ((memLp_cont hφ.continuous).toLp φ) (cL k m)) := by
    funext m
    rw [eN, cL, inner_toLp_toLp, inner_toLp_toLp]
    have hw := (isWD_smd k m).2 φ hφ
    have e1 : ∫ x, dk k φ x * smd m x ∂μN n = ∫ x, smd m x * dk k φ x ∂μN n :=
      integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    have e2 : ∫ x, π * (↑(m k) + 1) * cmd k m x * φ x ∂μN n =
        π * (↑(m k) + 1) * ∫ x, φ x * cmd k m x ∂μN n := by
      rw [← integral_const_mul]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
    rw [e1, hw, e2]; ring
  rw [e]
  exact h2.neg

lemma memLp_comp_pm {f : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) (σ : Equiv.Perm (Fin (n + 1))) :
    MemLp (fun x => f (pm σ x)) 2 (μN n) := by
  have hmp : MeasurePreserving (pm σ) (μN n) (μN n) := by
    have h := (mp_pm (n := n) σ).restrict_preimage (s := Cube n) measurableSet_cube
    have hpre : pm σ ⁻¹' Cube n = Cube n := by ext x; exact pm_mem_cube
    rwa [hpre] at h
  exact hf.comp_measurePreserving hmp

/-- The series inherits the exchange symmetry of its coefficients (a.e.). -/
theorem serW_pm {s : SymT n} (hs : Summable fun m => a m ^ 2) (hsym : InS s a)
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
theorem serW_mem {s : SymT n} (ha : Dir s a) : serW a ∈ DomWS s :=
  ⟨memLp_serW, fun k => ⟨_, isWD_serW ha.sq ha.kin k⟩, fun _ hσ => serW_pm ha.sq ha.sym hσ⟩

/-- The weak kinetic energy of the series is `Σ λ_m a_m²`. -/
theorem kinW_serW {s : SymT n} (ha : Dir s a) : kinW (serW a) = ∑' m, lam m * a m ^ 2 := by
  have hk : ∀ k, ∫ x, dW k (serW a) x * dW k (serW a) x ∂μN n =
      ∑' m, (π * (m k + 1) * a m) ^ 2 := fun k => by
    have hd := dW_ae_eq (isWD_serW ha.sq ha.kin k)
    have e : ∫ x, dW k (serW a) x * dW k (serW a) x ∂μN n =
        ∫ x, dserW k a x * dserW k a x ∂μN n :=
      integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx])
    rw [e, dserW, (orth_series (cL_orthonormal k) (summable_dcoef ha.kin k)).2.2.tsum_eq,
      ← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (ae_of_all _ fun x => by simp [sq])
  rw [kinW, Finset.sum_congr rfl fun k _ => hk k,
    ← Summable.tsum_finsetSum fun k _ => summable_dcoef ha.kin k]
  refine tsum_congr fun m => ?_
  simp only [lam, ksq]; push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### Ground states for continuous potentials -/

/-- **Ground states exist in `H¹₀` for every continuous potential**, for any symmetry type that
admits a normalised coefficient sequence (no smoothness, no symmetry assumption on `w`). -/
theorem exists_isNGS_WS_cont {s : SymT n} (hne : ∃ c : (Fin (n + 1) → ℕ) → ℝ, Adm s c)
    {w : Cfg n → ℝ} (hw : Continuous w) (v : C01) :
    ∃ Φ, IsNGS (settingWS s w hw) v Φ := by
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hV : Continuous V := (continuous_LN v).add hw
  obtain ⟨B, hB⟩ := (isCompact_univ_pi fun _ => isCompact_Icc :
    IsCompact (CubeC n)).exists_bound_of_continuousOn hV.continuousOn
  have hK := kBd_of_continuous hV (B := B) fun x hx => by simpa [Real.norm_eq_abs] using hB x hx
  obtain ⟨a, ha, hmin⟩ := hK.exists_min hne
  have hD := serW_mem ha.toDir
  have hcN : (fun m => cN m (serW a)) = a := funext (cN_serW ha.sq)
  have hip : ip (μ := μN n) (serW a) (serW a) = 1 := by
    have h := parsevalW (memLp_serW (a := a))
    calc ip (μ := μN n) (serW a) (serW a) = ∫ x, serW a x ^ 2 ∂μN n :=
          integral_congr_ae (ae_of_all _ fun x => by simp [sq])
      _ = ∑' m, cN m (serW a) ^ 2 := h.tsum_eq.symm
      _ = 1 := by simp only [cN_serW ha.sq]; exact ha.norm
  have hQ : Q (settingWS s w hw) v (serW a) = E0 V s := by
    rw [QW_eq v hD, kinW_serW ha.toDir, ← hmin, Fn, ← Bf_cNW hV memLp_serW, hcN]
  refine ⟨serW a, ⟨hD, hip⟩, fun Ψ hΨ => ?_⟩
  rw [hQ]
  have h1 : ∫ x, Ψ x ^ 2 ∂μN n = 1 := by
    rw [← hΨ.2]; simp only [ip]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
  exact (csInf_le (hK.bddBelow_Fn s) ⟨_, adm_cNW hΨ.1 h1, rfl⟩).trans (Fn_le_QW v hΨ.1)

/-- **Ground states exist in `H¹₀` for every continuous potential**, bosons or fermions. -/
theorem exists_isNGS_W_cont {w : Cfg n → ℝ} (hw : Continuous w) (v : C01) :
    ∃ Φ, IsNGS (settingW τ n w hw) v Φ :=
  exists_isNGS_WS_cont (exists_adm τ) hw v

end DFT.Continuum.Line
