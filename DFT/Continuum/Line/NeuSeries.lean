/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.NeuWeak

/-!
# Cosine series and the kinetic energy with Neumann walls

* `sP k m = √2 sin(π(m_k+1)x_k) Π_{j≠k} c_{m_j}(x_j)`: orthonormal, vanishes on the faces
  `x_k ∈ {0, 1}`, and `∂ₖ sP k m = π(m_k+1) c_{m⁺}` with `m⁺ = bumpC k m` (`m_k` raised by one).
* **`bessel_dWN`**: `Σ_m (π(m_k+1) ⟨c_{m⁺}, Φ⟩)² ≤ ∫ |∂ₖΦ|²`.
* `lamC m = π² Σ_j m_j²`; **`sum_lamC_le`**: `Σ_{m ∈ T} λᶜ_m ⟨c_m, Φ⟩² ≤ T(Φ)`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine Spectral

variable {n : ℕ}

/-! ### The functions `sP k m` -/

/-- Raise the `k`-th index by one. -/
def bumpC (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) : Fin (n + 1) → ℕ :=
  Function.update m k (m k + 1)

lemma bumpC_injective (k : Fin (n + 1)) : Function.Injective (bumpC k) := by
  intro m m' h
  funext j
  have := congrFun h j
  by_cases hj : j = k
  · subst hj; simp [bumpC] at this; omega
  · simpa [bumpC, hj] using this

lemma bumpC_self (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) : bumpC k m k = m k + 1 := by simp [bumpC]

lemma mem_range_bump {k : Fin (n + 1)} {m : Fin (n + 1) → ℕ} (h : m k ≠ 0) :
    m ∈ Set.range (bumpC k) :=
  ⟨Function.update m k (m k - 1), by
    funext j; by_cases hj : j = k
    · subst hj; simp [bumpC]; omega
    · simp [bumpC, hj]⟩

/-- The factors of `sP k m`. -/
noncomputable def sfac (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (j : Fin (n + 1)) : ℝ → ℝ :=
  if j = k then sn (m k + 1) else cn (m j)

/-- `√2 sin(π(m_k+1)x_k) Π_{j≠k} c_{m_j}(x_j)`. -/
noncomputable def sP (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (x : Cfg n) : ℝ :=
  ∏ j, sfac k m j (x j)

lemma contDiff_cn (k : ℕ) : ContDiff ℝ 1 (cn k) := by
  cases k with
  | zero => exact contDiff_const
  | succ k => unfold cn cs; fun_prop

lemma contDiff_sfac (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (j : Fin (n + 1)) :
    ContDiff ℝ 1 (sfac k m j) := by
  unfold sfac; split_ifs
  · unfold sn; fun_prop
  · exact contDiff_cn _

lemma contDiff_sP (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) : ContDiff ℝ 1 (sP k m) :=
  contDiff_prod fun j _ => (contDiff_sfac k m j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j).contDiff

lemma contDiff_cP (m : Fin (n + 1) → ℕ) : ContDiff ℝ 1 (cP m) :=
  contDiff_prod fun j _ => (contDiff_cn (m j)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j).contDiff

lemma sP_face (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (x : Cfg n) (hx : x k = 0 ∨ x k = 1) :
    sP k m x = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  simp only [sfac, ↓reduceIte, sn]
  rcases hx with h | h <;> rw [h]
  · simp
  · have := Real.sin_nat_mul_pi (m k + 1)
    push_cast at this ⊢
    rw [mul_one, mul_comm π, this]; simp

lemma testN_sP (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) : TestN k (sP k m) :=
  ⟨contDiff_sP k m, fun x hx => sP_face k m x hx⟩

lemma sP_orthonormal (k : Fin (n + 1)) (m m' : Fin (n + 1) → ℕ) :
    ∫ x, sP k m x * sP k m' x ∂μN n = if m = m' then 1 else 0 := by
  have e : (fun x => sP k m x * sP k m' x) =
      fun x => ∏ j, (sfac k m j (x j) * sfac k m' j (x j)) := by
    funext x; simp only [sP, Finset.prod_mul_distrib]
  rw [e, muN_eq, integral_fintype_prod_eq_prod (f := fun j t => sfac k m j t * sfac k m' j t)]
  have hj : ∀ j, ∫ t, sfac k m j t * sfac k m' j t ∂μ1 = if m j = m' j then 1 else 0 := by
    intro j
    by_cases hjk : j = k
    · subst hjk
      simp only [sfac, ↓reduceIte, sn_orthonormal (Nat.succ_pos _) (Nat.succ_pos _)]
      exact if_congr (by omega) rfl rfl
    · simp only [sfac, hjk, ↓reduceIte, cn_orthonormal]
  simp only [hj]
  by_cases h : m = m'
  · subst h; simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- `∂ₖ sP k m = π(m_k+1) c_{bumpC k m}`. -/
lemma dk_sP (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (x : Cfg n) :
    dk k (sP k m) x = π * (m k + 1) * cP (bumpC k m) x := by
  have h1 := hasDerivAt_slice ((contDiff_sP k m).differentiable one_ne_zero) x k (x k)
  rw [Function.update_eq_self] at h1
  set R := ∏ j ∈ Finset.univ.erase k, cn (m j) (x j)
  have hslice : (fun s => sP k m (Function.update x k s)) = fun s => sn (m k + 1) s * R := by
    funext s
    simp only [sP]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    simp only [sfac, ↓reduceIte, Function.update_self, R]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk := Finset.ne_of_mem_erase hj
    simp [hjk]
  have hsn : HasDerivAt (sn (m k + 1)) (π * (m k + 1) * cn (m k + 1) (x k)) (x k) := by
    have h := (((hasDerivAt_id (x k)).const_mul (π * ((m k + 1 : ℕ) : ℝ))).sin).const_mul √2
    refine h.congr_deriv ?_
    simp only [cn, cs, id]; push_cast; ring
  have h2 : HasDerivAt (fun s => sP k m (Function.update x k s))
      (π * (m k + 1) * cn (m k + 1) (x k) * R) (x k) := by
    rw [hslice]; exact hsn.mul_const R
  have hR : R = ∏ j ∈ Finset.univ.erase k, cn (bumpC k m j) (x j) :=
    Finset.prod_congr rfl fun j hj => by simp [bumpC, Finset.ne_of_mem_erase hj]
  rw [h1.unique h2, cP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), bumpC_self, ← hR]
  ring

/-! ### Bessel's inequality -/

/-- **Bessel for the weak derivative**: `Σ_{m ∈ s} (π(m_k+1) ⟨c_{m⁺}, Φ⟩)² ≤ ∫ |∂ₖΦ|²`. -/
lemma bessel_dWN {Φ : Cfg n → ℝ} (hΦ : H1NW Φ) (k : Fin (n + 1))
    (s : Finset (Fin (n + 1) → ℕ)) :
    ∑ m ∈ s, (π * (m k + 1) * cC (bumpC k m) Φ) ^ 2 ≤ ∫ x, dWN k Φ x * dWN k Φ x ∂μN n := by
  have hW := dWN_spec (hΦ.2 k)
  set v : (Fin (n + 1) → ℕ) → HN n := fun m => (memLp_cont (contDiff_sP k m).continuous).toLp
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro m m'
    simp only [v]
    rw [inner_toLp_left, ← sP_orthonormal k m m']
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_cont (contDiff_sP k m').continuous)] with x hx
    rw [hx]
  set G : HN n := hW.1.toLp (dWN k Φ)
  have hinner : ∀ m, inner ℝ (v m) G = -(π * (m k + 1) * cC (bumpC k m) Φ) := fun m => by
    simp only [v, G]
    rw [inner_toLp_left]
    have e : ∫ x, sP k m x * (hW.1.toLp (dWN k Φ) : Cfg n → ℝ) x ∂μN n =
        ∫ x, dWN k Φ x * sP k m x ∂μN n := integral_congr_ae (by
      filter_upwards [MemLp.coeFn_toLp hW.1] with x hx; rw [hx, mul_comm])
    rw [e, ← neg_neg (∫ x, dWN k Φ x * sP k m x ∂μN n), ← hW.2 _ (testN_sP k m)]
    simp only [dk_sP]
    rw [cC, ← integral_const_mul]
    congr 1; congr 1; funext x; ring
  have h := hv.sum_inner_products_le (x := G) (s := s)
  simp only [hinner, Real.norm_eq_abs, abs_neg, sq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [norm_sq_toLp]; congr 1; funext x; ring

/-- The cosine eigenvalues `λᶜ_m = π² Σ_j m_j²`. -/
noncomputable def lamC (m : Fin (n + 1) → ℕ) : ℝ := π ^ 2 * ∑ j, ((m j : ℝ)) ^ 2

lemma lamC_nonneg (m : Fin (n + 1) → ℕ) : 0 ≤ lamC m := by unfold lamC; positivity

/-- **Kinetic energy controls the cosine coefficients**: `Σ_{m ∈ T} λᶜ_m ⟨c_m, Φ⟩² ≤ T(Φ)`. -/
theorem sum_lamC_le {Φ : Cfg n → ℝ} (hΦ : H1NW Φ) (T : Finset (Fin (n + 1) → ℕ)) :
    ∑ m ∈ T, lamC m * cC m Φ ^ 2 ≤ kinN Φ := by
  have e : ∑ m ∈ T, lamC m * cC m Φ ^ 2 =
      ∑ k, ∑ m ∈ T, π ^ 2 * (m k : ℝ) ^ 2 * cC m Φ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [lamC, Finset.mul_sum, Finset.sum_mul]
  rw [e, kinN]
  refine Finset.sum_le_sum fun k _ => ?_
  classical
  have hinj : Set.InjOn (bumpC k) (bumpC k ⁻¹' ↑T) := (bumpC_injective k).injOn
  have hpre := Finset.sum_preimage (bumpC k) T hinj
    (fun m => π ^ 2 * (m k : ℝ) ^ 2 * cC m Φ ^ 2) fun m _ hm => by
      have : m k = 0 := by
        by_contra h; exact hm (mem_range_bump h)
      simp [this]
  rw [← hpre]
  refine le_of_eq_of_le (b := ∑ m ∈ T.preimage (bumpC k) hinj,
    (π * (m k + 1) * cC (bumpC k m) Φ) ^ 2) ?_ (bessel_dWN hΦ k _)
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [bumpC_self]; push_cast; ring

/-- `λ_m ≤ 2 λᶜ_m + 2π²N`: the sine eigenvalues are controlled by the cosine ones. -/
lemma lam_le_lamC (m : Fin (n + 1) → ℕ) : lam m ≤ 2 * lamC m + 2 * π ^ 2 * (n + 1) := by
  simp only [lam, lamC, ksq]
  push_cast
  have h : ∑ j, ((m j : ℝ) + 1) ^ 2 ≤ 2 * ∑ j, (m j : ℝ) ^ 2 + 2 * (n + 1) := by
    have : ∑ j : Fin (n + 1), ((m j : ℝ) + 1) ^ 2 ≤ ∑ j : Fin (n + 1), (2 * (m j : ℝ) ^ 2 + 2) :=
      Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg ((m j : ℝ) - 1)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    linarith
  nlinarith [pi_pos]

/-! ### Derivatives of the product cosines -/

lemma slice_cP (m : Fin (n + 1) → ℕ) (x : Cfg n) (k : Fin (n + 1)) :
    (fun s => cP m (Function.update x k s)) =
      fun s => cn (m k) s * ∏ j ∈ Finset.univ.erase k, cn (m j) (x j) := by
  funext s
  simp only [cP]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  simp [Finset.ne_of_mem_erase hj]

lemma dk_cP_zero {k : Fin (n + 1)} {m : Fin (n + 1) → ℕ} (hm : m k = 0) (x : Cfg n) :
    dk k (cP m) x = 0 := by
  have h1 := hasDerivAt_slice ((contDiff_cP m).differentiable one_ne_zero) x k (x k)
  rw [Function.update_eq_self, slice_cP, hm] at h1
  have h2 : HasDerivAt (fun s => cn 0 s * ∏ j ∈ Finset.univ.erase k, cn (m j) (x j)) 0 (x k) := by
    simp only [cn, one_mul]; exact hasDerivAt_const _ _
  exact h1.unique h2

/-- `∂ₖ c_{bumpC k m} = -π(m_k+1) sP k m`. -/
lemma dk_cP_bump (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (x : Cfg n) :
    dk k (cP (bumpC k m)) x = -(π * (m k + 1)) * sP k m x := by
  have h1 := hasDerivAt_slice ((contDiff_cP (bumpC k m)).differentiable one_ne_zero) x k (x k)
  rw [Function.update_eq_self, slice_cP, bumpC_self] at h1
  set R := ∏ j ∈ Finset.univ.erase k, cn (bumpC k m j) (x j)
  have hcs : HasDerivAt (cn (m k + 1)) (-(π * (m k + 1)) * sn (m k + 1) (x k)) (x k) := by
    have h := (((hasDerivAt_id (x k)).const_mul (π * ((m k : ℝ) + 1))).cos).const_mul √2
    refine h.congr_deriv ?_
    simp only [sn, id]; push_cast; ring
  have hR : R = ∏ j ∈ Finset.univ.erase k, sfac k m j (x j) :=
    Finset.prod_congr rfl fun j hj => by
      simp [bumpC, sfac, Finset.ne_of_mem_erase hj]
  rw [h1.unique (hcs.mul_const R), sP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← hR]
  simp only [sfac, ↓reduceIte]
  ring

/-! ### Cosine series -/

variable {a : (Fin (n + 1) → ℕ) → ℝ}

/-- `sP k m` as an element of `L²`. -/
noncomputable def sL (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) : HN n :=
  (memLp_cont (contDiff_sP k m).continuous).toLp

lemma sL_orthonormal (k : Fin (n + 1)) : Orthonormal ℝ (sL (n := n) k) := by
  rw [orthonormal_iff_ite]
  intro m m'
  rw [sL, sL, inner_toLp_toLp, sP_orthonormal]

/-- The cosine series `Σ_m a_m c_m` (a representative of its `L²` sum). -/
noncomputable def serN (a : (Fin (n + 1) → ℕ) → ℝ) : Cfg n → ℝ :=
  ((∑' m, a m • eC m : HN n) : Cfg n → ℝ)

/-- The candidate weak derivative `-Σ_m π(m_k+1) a_{bumpC k m} sP k m`. -/
noncomputable def dserN (k : Fin (n + 1)) (a : (Fin (n + 1) → ℕ) → ℝ) : Cfg n → ℝ :=
  ((∑' m, (-(π * (m k + 1) * a (bumpC k m))) • sL k m : HN n) : Cfg n → ℝ)

lemma sq_le_lamC_bump (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (x : ℝ) :
    (π * (m k + 1) * x) ^ 2 ≤ lamC (bumpC k m) * x ^ 2 := by
  have hk : ((m k : ℝ) + 1) ^ 2 ≤ ∑ j, ((bumpC k m j : ℕ) : ℝ) ^ 2 := by
    have := Finset.single_le_sum (f := fun j => ((bumpC k m j : ℕ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)
    simpa [bumpC_self] using this
  simp only [lamC]
  have : (π * (m k + 1) * x) ^ 2 = π ^ 2 * ((m k : ℝ) + 1) ^ 2 * x ^ 2 := by ring
  rw [this]
  gcongr

lemma summable_dcoefN (hk : Summable fun m => lamC m * a m ^ 2) (k : Fin (n + 1)) :
    Summable fun m => (-(π * (m k + 1) * a (bumpC k m))) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => ?_)
    (hk.comp_injective (bumpC_injective k))
  rw [neg_sq]; exact sq_le_lamC_bump k m _

lemma memLp_serN : MemLp (serN a) 2 (μN n) := Lp.memLp _

lemma cC_serN (hs : Summable fun m => a m ^ 2) (m : Fin (n + 1) → ℕ) : cC m (serN a) = a m := by
  rw [cC, serN, ← inner_eC]
  exact (orth_series eC_orthonormal hs).2.1 m

/-- **The weak derivative of the cosine series.** -/
theorem isWDN_serN (hs : Summable fun m => a m ^ 2) (hk : Summable fun m => lamC m * a m ^ 2)
    (k : Fin (n + 1)) : IsWDN k (serN a) (dserN k a) := by
  refine ⟨Lp.memLp _, fun φ hφ => ?_⟩
  have hψ := continuous_dk_of_C1 hφ.1 k
  have h1 := ((orth_series eC_orthonormal hs).1).mapL (innerSL ℝ ((memLp_cont hψ).toLp (dk k φ)))
  have h2 := ((orth_series (sL_orthonormal k) (summable_dcoefN hk k)).1).mapL
    (innerSL ℝ ((memLp_cont hφ.1.continuous).toLp φ))
  simp only [innerSL_apply_apply, inner_smul_right] at h1 h2
  rw [serN, dserN, integral_mul_cont_eq_inner _ hψ, integral_mul_cont_eq_inner _ hφ.1.continuous]
  refine h1.unique ?_
  -- the coefficients of `serN a` against `∂ₖφ`
  have hc : ∀ m', inner ℝ ((memLp_cont hψ).toLp (dk k φ)) (eC m') =
      -∫ x, dk k (cP m') x * φ x ∂μN n := fun m' => by
    rw [eC, inner_toLp_toLp]
    have hw := (isWDN_of_C1 (contDiff_cP m') k).2 φ hφ
    rw [← hw]
    exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  set f : (Fin (n + 1) → ℕ) → ℝ := fun m' => a m' * inner ℝ ((memLp_cont hψ).toLp (dk k φ)) (eC m')
  have hf0 : ∀ m', m' ∉ Set.range (bumpC k) → f m' = 0 := fun m' hm' => by
    have hz : m' k = 0 := by by_contra h; exact hm' (mem_range_bump h)
    simp only [f, hc, dk_cP_zero hz, zero_mul, integral_zero, neg_zero, mul_zero]
  rw [← (bumpC_injective k).hasSum_iff hf0]
  have e : f ∘ bumpC k = fun m => -((-(π * (m k + 1) * a (bumpC k m))) *
      inner ℝ ((memLp_cont hφ.1.continuous).toLp φ) (sL k m)) := by
    funext m
    simp only [Function.comp_apply, f, hc, dk_cP_bump, sL, inner_toLp_toLp]
    have : ∫ x, -(π * (m k + 1)) * sP k m x * φ x ∂μN n =
        -(π * (m k + 1)) * ∫ x, φ x * sP k m x ∂μN n := by
      rw [← integral_const_mul]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
    rw [this]; ring
  rw [e]
  exact h2.neg

/-! ### Exchange symmetry -/

lemma cP_pm (σ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) (x : Cfg n) :
    cP (pmI σ m) (pm σ x) = cP m x := by
  simp only [cP, pmI, pm_apply]
  exact Equiv.prod_comp σ (fun i => cn (m i) (x i))

lemma cC_pmNS {s : SymT n} {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomNS s) {σ : Equiv.Perm (Fin (n + 1))}
    (hσ : s.G σ) (m : Fin (n + 1) → ℕ) : cC (pmI σ m) Φ = s.χ σ * cC m Φ := by
  rw [cC, cC, ← integral_pm σ, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hΦ.2.2 σ hσ] with x hx
  simp only [cP_pm, hx]; ring

/-- `L²` functions with the same cosine coefficients agree a.e. -/
lemma ae_eq_of_cC_eq {f g : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) (hg : MemLp g 2 (μN n))
    (h : ∀ m, cC m f = cC m g) : f =ᵐ[μN n] g := by
  have hz : hf.toLp f - hg.toLp g = 0 := eC_complete _ fun m => by
    rw [inner_sub_right, inner_eC_toLp, inner_eC_toLp, h, sub_self]
  rw [sub_eq_zero] at hz
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x h1 h2
  rw [← h1, ← h2, hz]

/-- Admissible cosine sequences: square summable, finite kinetic energy, exchange symmetry. -/
structure DirN (s : SymT n) (c : (Fin (n + 1) → ℕ) → ℝ) : Prop where
  sq : Summable fun m => c m ^ 2
  kin : Summable fun m => lamC m * c m ^ 2
  sym : InS s c

/-- The cosine coefficients of a Neumann state are admissible. -/
lemma dirN_cC {s : SymT n} {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomNS s) : DirN s fun m => cC m Φ where
  sq := (parsevalCW hΦ.1).summable
  kin := summable_of_sum_le (fun m => mul_nonneg (lamC_nonneg m) (sq_nonneg _))
    (sum_lamC_le (h1NW_of_mem hΦ))
  sym := fun _ hσ m => cC_pmNS hΦ hσ m

lemma tsum_lamC_le {s : SymT n} {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomNS s) :
    ∑' m, lamC m * cC m Φ ^ 2 ≤ kinN Φ :=
  Real.tsum_le_of_sum_le (fun m => mul_nonneg (lamC_nonneg m) (sq_nonneg _))
    (sum_lamC_le (h1NW_of_mem hΦ))

/-- The series inherits the exchange symmetry of its coefficients (a.e.). -/
theorem serN_pm {s : SymT n} (hs : Summable fun m => a m ^ 2) (hsym : InS s a)
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : s.G σ) :
    ∀ᵐ x ∂μN n, serN a (pm σ x) = s.χ σ * serN a x := by
  refine ae_eq_of_cC_eq (memLp_comp_pm memLp_serN σ) (memLp_serN.const_mul _) fun m => ?_
  have h1 : cC m (fun x => serN a (pm σ x)) = cC (pmI σ m) (serN a) := by
    rw [cC, cC, ← integral_pm σ (fun x => cP (pmI σ m) x * serN a x)]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [cP_pm])
  have h2 : cC m (fun x => s.χ σ * serN a x) = s.χ σ * cC m (serN a) := by
    rw [cC, cC, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [h1, h2, cC_serN hs, cC_serN hs]
  exact hsym σ hσ m

/-- **Admissible cosine sequences are Neumann states** of the same symmetry type. -/
theorem serN_mem {s : SymT n} (ha : DirN s a) : serN a ∈ DomNS s :=
  ⟨memLp_serN, fun k => ⟨_, isWDN_serN ha.sq ha.kin k⟩, fun _ hσ => serN_pm ha.sq ha.sym hσ⟩

/-- The kinetic energy of the series is `Σ λᶜ_m a_m²`. -/
theorem kinN_serN {s : SymT n} (ha : DirN s a) : kinN (serN a) = ∑' m, lamC m * a m ^ 2 := by
  have hk : ∀ k, ∫ x, dWN k (serN a) x * dWN k (serN a) x ∂μN n =
      ∑' m, π ^ 2 * (m k : ℝ) ^ 2 * a m ^ 2 := fun k => by
    have hd := dWN_ae_eq (isWDN_serN ha.sq ha.kin k)
    have e : ∫ x, dWN k (serN a) x * dWN k (serN a) x ∂μN n =
        ∫ x, dserN k a x * dserN k a x ∂μN n :=
      integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx])
    have h3 := (orth_series (sL_orthonormal k) (summable_dcoefN ha.kin k)).2.2
    rw [e, dserN, ← real_inner_self_eq_norm_sq, L2.inner_def] at *
    have h4 : HasSum (fun m => (-(π * (m k + 1) * a (bumpC k m))) ^ 2)
        (∫ x, ((∑' m, (-(π * (m k + 1) * a (bumpC k m))) • sL k m : HN n) : Cfg n → ℝ) x *
          ((∑' m, (-(π * (m k + 1) * a (bumpC k m))) • sL k m : HN n) : Cfg n → ℝ) x ∂μN n) := by
      convert h3 using 1
    have hz : ∀ m', m' ∉ Set.range (bumpC k) → π ^ 2 * (m' k : ℝ) ^ 2 * a m' ^ 2 = 0 :=
      fun m' hm' => by
        have hz : m' k = 0 := by by_contra h; exact hm' (mem_range_bump h)
        simp [hz]
    have h5 := ((bumpC_injective k).hasSum_iff hz).1 (h4.congr_fun fun m => by
      simp only [Function.comp_apply, bumpC_self, neg_sq]; push_cast; ring)
    exact h5.tsum_eq.symm
  have hsk : ∀ k : Fin (n + 1), Summable fun m => π ^ 2 * (m k : ℝ) ^ 2 * a m ^ 2 := fun k =>
    Summable.of_nonneg_of_le (fun m => by positivity) (fun m => by
      have : π ^ 2 * (m k : ℝ) ^ 2 ≤ lamC m := by
        simp only [lamC]
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
          (f := fun j => ((m j : ℕ) : ℝ) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k))
          (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)) ha.kin
  rw [kinN, Finset.sum_congr rfl fun k _ => hk k, ← Summable.tsum_finsetSum fun k _ => hsk k]
  refine tsum_congr fun m => ?_
  simp only [lamC, Finset.mul_sum, Finset.sum_mul]

end DFT.Continuum.Line
