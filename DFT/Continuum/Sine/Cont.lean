/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Min

/-!
# Continuous potentials act boundedly on coefficient sequences

For a continuous `V` with `|V| ≤ B` on the closed cube, the kernel `K(m', m) = ⟨s_{m'}, V s_m⟩`
satisfies the abstract `ℓ²` bound `KBd V (B²)`, without any smoothness:

* rows: `Σ_m K(m', m)² = ∫ (V s_{m'})²` (Parseval for the continuous function `V s_{m'}`);
* finitely supported `c`: `(Kc)_{m'} = ⟨s_{m'}, V φ⟩` with `φ = Σ c_m s_m` continuous, so
  `Σ (Kc)² = ∫ (Vφ)² ≤ B² ∫ φ² = B² Σ c²`;
* general `c ∈ ℓ²`: truncate to the boxes `T_K` and pass to the limit (`lim_sum_le`).

Hence the direct method in coefficient space (`KBd.exists_min`) applies to
every continuous potential: `exists_min_cont`.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology SturmLiouville Line Real

variable {n : ℕ}

lemma Ker_eq_cf (V : Cfg n → ℝ) (m' m : Fin (n + 1) → ℕ) :
    Ker V m' m = cf m (fun x => V x * smd m' x) := Ker_eq_cN V m' m

lemma ae_cubeC : ∀ᵐ x ∂piM (n + 1), x ∈ CubeC n := by
  rw [piM_eq_Icc]
  exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Icc)

section cont

variable {V : Cfg n → ℝ} (hV : Continuous V) {B : ℝ} (hB : ∀ x ∈ CubeC n, |V x| ≤ B)
include hV

/-- The rows of the kernel are square summable. -/
lemma summable_Ker_sq (m' : Fin (n + 1) → ℕ) : Summable fun m => Ker V m' m ^ 2 := by
  have h := hasSum_sq_cube (d := n + 1) (f := fun x => V x * smd m' x) (hV.mul (continuous_smd m'))
  simp only [← Ker_eq_cf] at h
  exact h.summable

lemma summable_Ker_mul_cont {c : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (m' : Fin (n + 1) → ℕ) : Summable fun m => Ker V m' m * c m :=
  summable_mul_of_sq (summable_Ker_sq hV m') hc

/-- The finite combination `Σ_{m ∈ T} c_m s_m`. -/
noncomputable def finSer (T : Finset (Fin (n + 1) → ℕ)) (c : (Fin (n + 1) → ℕ) → ℝ)
    (x : Cfg n) : ℝ := ∑ m ∈ T, c m * smd m x

omit hV in
lemma continuous_finSer (T : Finset (Fin (n + 1) → ℕ)) (c : (Fin (n + 1) → ℕ) → ℝ) :
    Continuous (finSer T c) :=
  continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_smd m)

omit hV in
lemma cf_finSer {T : Finset (Fin (n + 1) → ℕ)} {c : (Fin (n + 1) → ℕ) → ℝ}
    (hT : ∀ m ∉ T, c m = 0) (m : Fin (n + 1) → ℕ) : cf m (finSer T c) = c m := by
  simp only [cf, finSer, Finset.mul_sum]
  rw [integral_finsetSum T (f := fun m' x => smd m x * (c m' * smd m' x)) fun m' _ =>
    integrable_piM ((continuous_smd m).mul (continuous_const.mul (continuous_smd m')))]
  have e : ∀ m' ∈ T, ∫ x, smd m x * (c m' * smd m' x) ∂piM (n + 1) =
      c m' * (if m = m' then 1 else 0) := fun m' _ => by
    rw [← smd_orthonormal, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [Finset.sum_congr rfl e]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (hT m h).symm

lemma Kc_finSer {T : Finset (Fin (n + 1) → ℕ)} {c : (Fin (n + 1) → ℕ) → ℝ}
    (hT : ∀ m ∉ T, c m = 0) (m' : Fin (n + 1) → ℕ) :
    Kc V c m' = cf m' (fun x => V x * finSer T c x) := by
  rw [Kc, tsum_eq_sum (s := T) fun m hm => by simp [hT m hm]]
  simp only [Ker, cf, finSer, Finset.mul_sum]
  rw [integral_finsetSum T (f := fun m x => smd m' x * (V x * (c m * smd m x)))
    fun m _ => integrable_piM ((continuous_smd m').mul
    (hV.mul (continuous_const.mul (continuous_smd m))))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [muN_eq, ← integral_mul_const]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

include hB in
/-- The bound for finitely supported sequences. -/
lemma Kc_fin_bound {T : Finset (Fin (n + 1) → ℕ)} {c : (Fin (n + 1) → ℕ) → ℝ}
    (hT : ∀ m ∉ T, c m = 0) :
    Summable (fun m' => Kc V c m' ^ 2) ∧ ∑' m', Kc V c m' ^ 2 ≤ B ^ 2 * ∑' m, c m ^ 2 := by
  set φ := finSer T c
  have hφ : Continuous φ := continuous_finSer T c
  have h1 := hasSum_sq_cube (d := n + 1) (f := fun x => V x * φ x) (hV.mul hφ)
  have h2 := hasSum_sq_cube (d := n + 1) (f := φ) hφ
  have e1 : (fun m' => cf m' (fun x => V x * φ x) ^ 2) = fun m' => Kc V c m' ^ 2 :=
    funext fun m' => by rw [Kc_finSer hV hT]
  have e2 : (fun m => cf m φ ^ 2) = fun m => c m ^ 2 := funext fun m => by rw [cf_finSer hT]
  rw [e1] at h1
  rw [e2] at h2
  refine ⟨h1.summable, ?_⟩
  rw [h1.tsum_eq, h2.tsum_eq, ← integral_const_mul]
  refine integral_mono_ae (integrable_piM ((hV.mul hφ).mul (hV.mul hφ)))
    (integrable_piM (continuous_const.mul (hφ.mul hφ))) ?_
  filter_upwards [ae_cubeC] with x hx
  have hv : V x ^ 2 ≤ B ^ 2 := sq_le_sq' (abs_le.1 (hB x hx)).1 (abs_le.1 (hB x hx)).2
  nlinarith [mul_self_nonneg (φ x)]

omit hV in
lemma box_mono {K K' : ℕ} (h : K ≤ K') : box (n := n) K ⊆ box K' := by
  intro m hm
  simp only [box, Fintype.mem_piFinset, Finset.mem_range] at hm ⊢
  exact fun j => lt_of_lt_of_le (hm j) h

include hB in
/-- **Continuous potentials satisfy the `ℓ²` kernel bound** with constant `B²`. -/
theorem kBd_of_continuous : KBd V (B ^ 2) := by
  have hrow : ∀ {c : (Fin (n + 1) → ℕ) → ℝ}, Summable (fun m => c m ^ 2) → ∀ m',
      Summable fun m => Ker V m' m * c m := fun hc m' => summable_Ker_mul_cont hV hc m'
  -- truncations
  set tr : ℕ → ((Fin (n + 1) → ℕ) → ℝ) → (Fin (n + 1) → ℕ) → ℝ :=
    fun K c m => if m ∈ box K then c m else 0 with htr
  have htr0 : ∀ K c, ∀ m ∉ box (n := n) K, tr K c m = 0 := fun K c m hm => by simp [htr, hm]
  have hgen : ∀ {c : (Fin (n + 1) → ℕ) → ℝ}, Summable (fun m => c m ^ 2) →
      Summable (fun m' => Kc V c m' ^ 2) ∧ ∑' m', Kc V c m' ^ 2 ≤ B ^ 2 * ∑' m, c m ^ 2 := by
    intro c hc
    have hlim : ∀ m', Tendsto (fun K => Kc V (tr K c) m') atTop (𝓝 (Kc V c m')) := by
      intro m'
      have e : ∀ K, Kc V (tr K c) m' = ∑ m ∈ box K, Ker V m' m * c m := fun K => by
        rw [Kc, tsum_eq_sum (s := box K) fun m hm => by simp [htr0 K c m hm]]
        exact Finset.sum_congr rfl fun m hm => by simp [htr, hm]
      simp only [e]
      have hbox : Tendsto (fun K : ℕ => box (n := n) K) atTop atTop := by
        refine tendsto_atTop_atTop.2 fun T => ⟨T.sup fun m => Finset.univ.sup m + 1,
          fun K hK m hm => box_mono ((Finset.le_sup hm).trans hK) (mem_box_sup m)⟩
      exact ((hrow hc m').hasSum).comp hbox
    have hb0 : 0 ≤ B := (abs_nonneg _).trans (hB (fun _ => 0) fun _ _ => ⟨le_rfl, zero_le_one⟩)
    have hfin : ∀ K, Summable (fun m' => Kc V (tr K c) m' ^ 2) ∧
        ∑' m', Kc V (tr K c) m' ^ 2 ≤ B ^ 2 * ∑' m, c m ^ 2 := fun K => by
      obtain ⟨hs, hle⟩ := Kc_fin_bound hV hB (htr0 K c)
      refine ⟨hs, hle.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg B))⟩
      refine Summable.tsum_le_tsum (fun m => ?_) (summable_of_ne_finset_zero (s := box K)
        fun m hm => by simp [htr0 K c m hm]) hc
      by_cases hm : m ∈ box K
      · simp [htr, hm]
      · simp [htr, hm, sq_nonneg]
    have := lim_sum_le (w := fun _ => 1) hlim (fun _ => zero_le_one)
      (fun K => by simpa using (hfin K).1) (fun K => by simpa using (hfin K).2)
    simpa using this
  exact ⟨sq_nonneg B, fun hc m' => hrow hc m', fun hc => (hgen hc).1, fun hc => (hgen hc).2⟩

end cont

/-- **The coefficient-space minimiser exists for every continuous potential.** -/
theorem exists_min_cont {V : Cfg n → ℝ} (hV : Continuous V) {τ : SymT n}
    (hne : ∃ c : (Fin (n + 1) → ℕ) → ℝ, Adm τ c) : ∃ c, Adm τ c ∧ Fn V c = E0 V τ := by
  obtain ⟨B, hB⟩ := (isCompact_univ_pi fun _ => isCompact_Icc :
    IsCompact (CubeC n)).exists_bound_of_continuousOn hV.continuousOn
  exact (kBd_of_continuous hV (B := B) fun x hx => by
    simpa [Real.norm_eq_abs] using hB x hx).exists_min hne

end DFT.Continuum.Sine
