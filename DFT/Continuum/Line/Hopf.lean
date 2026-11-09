/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Basic
import DFT.Continuum.Pair.MaxPrinciple

/-!
# Hopf's lemma in `n + 1` dimensions: no sign change through critical zeros

A `C²` function on a connected open set of `ℝ^(n+1)` that is a supersolution of `-Δ + c`
(`c ≥ 0`) wherever it is positive, and whose gradient vanishes at each of its zeros, is either
positive on the whole set or nonpositive on the whole set. This is the `n + 1`-dimensional version
of `DFT.Continuum.Pair.pos_or_nonpos` (which is stated on the square).

* `Neu`: the squared Euclidean distance; `Ndist_sq_le_eu`, `Neu_le_dist_sq`: comparison with the
  sup distance of `Cfg n`.
* `Ndkk_nonneg_of_isLocalMin`: the second-derivative test, coordinate by coordinate.
* `Nbarrier`, `lapN_Nbarrier`: the Hopf barrier `e^{-α|x - y|²} - K` and its Laplacian.
* `local_nonpos_on`: near a zero, `u ≤ 0` (Hopf's lemma on the largest Euclidean ball inside
  `{u > 0}`, with the barrier and weak comparison on an annulus).
* `pos_or_nonpos_on`: the global statement, by connectedness.
-/

namespace DFT.Continuum.Line

open Set Filter Topology Metric

variable {n : ℕ}

/-! ### Slices and second derivatives -/

/-- A partial derivative is the derivative of the slice. -/
lemma Ndk_eq {ψ : Cfg n → ℝ} (hψ : Differentiable ℝ ψ) {x : Cfg n} {k : Fin (n + 1)} {a : ℝ}
    (h : HasDerivAt (fun s => ψ (Function.update x k s)) a (x k)) : dk k ψ x = a := by
  have := hasDerivAt_slice hψ x k (x k)
  rw [Function.update_eq_self] at this
  exact this.unique h

/-- **Second-derivative test** along coordinate `k`. -/
lemma Ndkk_nonneg_of_isLocalMin {ψ : Cfg n → ℝ} (hψ : ContDiff ℝ 2 ψ) {q : Cfg n}
    (hq : IsLocalMin ψ q) (k : Fin (n + 1)) : 0 ≤ dkk k ψ q := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (dk k ψ) := (contDiff_dk hψ k).differentiable one_ne_zero
  have hg : Continuous fun s : ℝ => Function.update q k s :=
    continuous_const.update k continuous_id
  have hq' : IsLocalMin ψ (Function.update q k (q k)) := by rwa [Function.update_eq_self]
  have := Pair.deriv2_nonneg_of_isLocalMin (f := fun s => ψ (Function.update q k s))
    (f' := fun s => dk k ψ (Function.update q k s))
    (f'' := fun s => dkk k ψ (Function.update q k s)) (x0 := q k)
    (fun s => hasDerivAt_slice hd q k s) (fun s => hasDerivAt_slice hd1 q k s)
    ((continuous_dkk hψ k).comp hg).continuousAt (hq'.comp_continuous hg.continuousAt)
  simpa [Function.update_eq_self] using this

/-! ### Linearity -/

lemma Ndk_sub_mul {ψ φ : Cfg n → ℝ} (hψ : Differentiable ℝ ψ) (hφ : Differentiable ℝ φ) (ε : ℝ)
    (k : Fin (n + 1)) : dk k (fun x => ψ x - ε * φ x) = fun x => dk k ψ x - ε * dk k φ x := by
  funext x
  exact Ndk_eq (hψ.sub (hφ.const_mul ε))
    ((hasDerivAt_slice hψ x k (x k)).sub ((hasDerivAt_slice hφ x k (x k)).const_mul ε))
    |>.trans (by rw [Function.update_eq_self])

lemma NlapN_sub_mul {ψ φ : Cfg n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hφ : ContDiff ℝ 2 φ) (ε : ℝ)
    (x : Cfg n) : lapN (fun x => ψ x - ε * φ x) x = lapN ψ x - ε * lapN φ x := by
  have d1 : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have d2 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  simp only [lapN, dkk, Ndk_sub_mul d1 d2,
    fun k => Ndk_sub_mul ((contDiff_dk hψ k).differentiable one_ne_zero)
      ((contDiff_dk hφ k).differentiable one_ne_zero) ε k]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-! ### The squared Euclidean distance -/

/-- The squared Euclidean distance from `y` to `x`. -/
def Neu (y x : Cfg n) : ℝ := ∑ k, (x k - y k) ^ 2

lemma continuous_Neu (y : Cfg n) : Continuous (Neu y) :=
  continuous_finsetSum _ fun k _ => ((continuous_apply k).sub continuous_const).pow 2

lemma Neu_nonneg (y x : Cfg n) : 0 ≤ Neu y x := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma Neu_update (y x : Cfg n) (k : Fin (n + 1)) (s : ℝ) :
    Neu y (Function.update x k s) = Neu y x + ((s - y k) ^ 2 - (x k - y k) ^ 2) := by
  have : Neu y (Function.update x k s) - Neu y x = (s - y k) ^ 2 - (x k - y k) ^ 2 := by
    rw [Neu, Neu, ← Finset.sum_sub_distrib, Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [Function.update_of_ne hj]
    · simp
  linarith

lemma Neu_segment (y p : Cfg n) (s : ℝ) : Neu y (y + s • (p - y)) = s ^ 2 * Neu y p := by
  simp only [Neu, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma Ndist_sq_le_eu (p q : Cfg n) : dist p q ^ 2 ≤ Neu q p := by
  have h : dist p q ≤ Real.sqrt (Neu q p) := by
    refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun k => ?_
    rw [Real.dist_eq, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => (p j - q j) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ k))
  calc dist p q ^ 2 ≤ Real.sqrt (Neu q p) ^ 2 := pow_le_pow_left₀ dist_nonneg h 2
    _ = Neu q p := Real.sq_sqrt (Neu_nonneg q p)

lemma Neu_le_dist_sq (p q : Cfg n) : Neu q p ≤ (n + 1) * dist p q ^ 2 := by
  have h : ∀ k, (p k - q k) ^ 2 ≤ dist p q ^ 2 := fun k => by
    rw [← sq_abs, ← Real.dist_eq]
    exact pow_le_pow_left₀ dist_nonneg (dist_le_pi_dist p q k) 2
  calc Neu q p ≤ ∑ _k : Fin (n + 1), dist p q ^ 2 := Finset.sum_le_sum fun k _ => h k
    _ = (n + 1) * dist p q ^ 2 := by simp

lemma Ndist_lt_of_eu_lt {p q : Cfg n} {s : ℝ} (hs : 0 ≤ s) (h : Neu q p < s ^ 2) :
    dist p q < s := by
  have h1 := Ndist_sq_le_eu p q
  by_contra h2
  push Not at h2
  nlinarith [dist_nonneg (x := p) (y := q)]

/-- The intermediate value theorem along a segment. -/
lemma Nexists_zero_segment {u : Cfg n → ℝ} (hu : Continuous u) {y p : Cfg n} (hy : 0 < u y)
    (hp : u p < 0) : ∃ s ∈ Ioo (0 : ℝ) 1, u (y + s • (p - y)) = 0 := by
  set g : ℝ → ℝ := fun s => u (y + s • (p - y))
  have hg : Continuous g := hu.comp (continuous_const.add (continuous_id.smul continuous_const))
  have h0 : g 0 = u y := by simp [g]
  have h1 : g 1 = u p := by simp [g]
  obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc' zero_le_one hg.continuousOn
    (show (0 : ℝ) ∈ Icc (g 1) (g 0) by rw [h0, h1]; exact ⟨hp.le, hy.le⟩)
  refine ⟨s, ⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2 ?_⟩, hgs⟩
  · rintro rfl; rw [h0] at hgs; linarith
  · rintro rfl; rw [h1] at hgs; linarith

/-! ### The barrier -/

/-- The Hopf barrier `e^{-α|x - y|²} - K`. -/
noncomputable def Nbarrier (α : ℝ) (y : Cfg n) (K : ℝ) (x : Cfg n) : ℝ :=
  Real.exp (-α * Neu y x) - K

/-- Its partial derivative along coordinate `k`. -/
noncomputable def Nbark (α : ℝ) (y : Cfg n) (k : Fin (n + 1)) (x : Cfg n) : ℝ :=
  -2 * α * (x k - y k) * Real.exp (-α * Neu y x)

lemma contDiff_Nbarrier (α : ℝ) (y : Cfg n) (K : ℝ) : ContDiff ℝ 2 (Nbarrier α y K) :=
  (Real.contDiff_exp.comp (contDiff_const.mul (ContDiff.sum fun k _ =>
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) k).contDiff).sub
      contDiff_const).pow 2))).sub contDiff_const

/-- The exponent along a slice. -/
lemma hasDerivAt_Nexpo (α : ℝ) (y x : Cfg n) (k : Fin (n + 1)) :
    HasDerivAt (fun s => -α * (Neu y x + ((s - y k) ^ 2 - (x k - y k) ^ 2)))
      (-α * (2 * (x k - y k))) (x k) := by
  have := ((((hasDerivAt_id (x k)).sub_const (y k)).pow 2).sub_const
    ((x k - y k) ^ 2)).const_add (Neu y x)
  convert this.const_mul (-α) using 1 <;> first | (funext s; simp) | norm_num

lemma Ndk_barrier (α : ℝ) (y : Cfg n) (K : ℝ) (k : Fin (n + 1)) :
    dk k (Nbarrier α y K) = Nbark α y k := by
  funext x
  refine Ndk_eq ((contDiff_Nbarrier α y K).differentiable (by norm_num)) ?_
  convert (hasDerivAt_Nexpo α y x k).exp.sub_const K using 1
  · funext s; simp only [Nbarrier, Neu_update]
  · simp only [Nbark, sub_self, add_zero]; ring

lemma Ndkk_barrier (α : ℝ) (y : Cfg n) (K : ℝ) (k : Fin (n + 1)) (x : Cfg n) :
    dkk k (Nbarrier α y K) x =
      (4 * α ^ 2 * (x k - y k) ^ 2 - 2 * α) * Real.exp (-α * Neu y x) := by
  have hd : Differentiable ℝ (Nbark α y k) := by
    rw [← Ndk_barrier α y K k]
    exact (contDiff_dk (contDiff_Nbarrier α y K) k).differentiable one_ne_zero
  simp only [dkk, Ndk_barrier]
  refine Ndk_eq hd ?_
  have h2 : HasDerivAt (fun s => -2 * α * (s - y k)) (-2 * α) (x k) := by
    simpa using ((hasDerivAt_id (x k)).sub_const (y k)).const_mul (-2 * α)
  convert h2.mul (hasDerivAt_Nexpo α y x k).exp using 1
  · funext s; simp only [Nbark, Neu_update, Function.update_self, Pi.mul_apply]
  · simp only [sub_self, add_zero]; ring

lemma lapN_Nbarrier (α : ℝ) (y : Cfg n) (K : ℝ) (x : Cfg n) :
    lapN (Nbarrier α y K) x =
      (4 * α ^ 2 * Neu y x - 2 * (n + 1) * α) * Real.exp (-α * Neu y x) := by
  simp only [lapN, Ndkk_barrier]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Neu]
  ring

/-- The barrier inequality: `-Δh + c h < 0` on the annulus. -/
lemma Nbarrier_neg {α R2 C e c N : ℝ} (hN : 0 < N) (hα1 : 1 ≤ α)
    (hαR : 4 * N + 2 * C ≤ α * R2) (hC : 0 ≤ C) (he : R2 / 4 ≤ e) (hc0 : 0 ≤ c) (hcC : c ≤ C) :
    -((4 * α ^ 2 * e - 2 * N * α) * Real.exp (-α * e)) +
      c * (Real.exp (-α * e) - Real.exp (-α * R2)) < 0 := by
  have hE := Real.exp_pos (-α * e)
  have hK := Real.exp_pos (-α * R2)
  have h1 : α * (4 * N + 2 * C) ≤ α * (α * R2) := mul_le_mul_of_nonneg_left hαR (by linarith)
  have h2 : α ^ 2 * R2 ≤ 4 * α ^ 2 * e := by nlinarith [sq_nonneg α]
  have hkey : -4 * α ^ 2 * e + 2 * N * α + c < 0 := by nlinarith
  nlinarith [mul_pos hE (show 0 < -(-4 * α ^ 2 * e + 2 * N * α + c) by linarith),
    mul_nonneg hc0 hK.le]

/-- `e^a - e^b ≥ e^b (a - b)`, along the segment towards the centre. -/
lemma Nexp_growth {α R2 t : ℝ} (hα : 0 ≤ α) (hR2 : 0 ≤ R2) (ht : t ∈ Ioc (0 : ℝ) (1 / 2)) :
    Real.exp (-α * R2) * (α * R2 * t) ≤
      Real.exp (-α * ((1 - t) ^ 2 * R2)) - Real.exp (-α * R2) := by
  set K := Real.exp (-α * R2)
  have h1 := Real.add_one_le_exp (-α * ((1 - t) ^ 2 * R2) - -α * R2)
  have h2 : Real.exp (-α * ((1 - t) ^ 2 * R2)) =
      K * Real.exp (-α * ((1 - t) ^ 2 * R2) - -α * R2) := by
    simp only [K]; rw [← Real.exp_add]; ring_nf
  rw [h2]
  have hK : 0 < K := Real.exp_pos _
  have hge : α * R2 * t ≤ -α * ((1 - t) ^ 2 * R2) - -α * R2 := by
    have key : -α * ((1 - t) ^ 2 * R2) - -α * R2 - α * R2 * t =
        α * R2 * (t * (1 - t)) := by ring
    have hnn' : 0 ≤ α * R2 * (t * (1 - t)) :=
      mul_nonneg (mul_nonneg hα hR2) (mul_nonneg ht.1.le (by linarith [ht.2]))
    linarith
  nlinarith

/-- A function with vanishing derivative at a zero `x1` cannot grow linearly along a ray from
`x1`. -/
lemma Nhopf_contra {u : Cfg n → ℝ} (hud : Differentiable ℝ u) {x1 d : Cfg n} (hx1u : u x1 = 0)
    (hgrad0 : fderiv ℝ u x1 = 0) {κ : ℝ} (hκ : 0 < κ)
    (hlin : ∀ t ∈ Ioc (0 : ℝ) (1 / 2), κ * t ≤ u (x1 + t • d)) : False := by
  have hfd : HasFDerivAt u (0 : Cfg n →L[ℝ] ℝ) x1 := by
    rw [← hgrad0]; exact (hud x1).hasFDerivAt
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hfd
  set η := κ / (2 * (‖d‖ + 1))
  have hη : 0 < η := by positivity
  have hev := hlo.def hη
  have htend : Tendsto (fun t : ℝ => t • d) (𝓝 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t • d) (𝓝 0) (𝓝 ((0 : ℝ) • d)) :=
      (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const d
    rwa [zero_smul] at h
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp (htend.eventually hev)
  set t := min (δ / 2) (1 / 2)
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have htδ : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hb := hδb htδ
  simp only [hx1u, zero_apply, sub_zero, Real.norm_eq_abs] at hb
  have hl := hlin t ⟨ht0, min_le_right _ _⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hb
  have hu_le : u (x1 + t • d) ≤ η * (t * ‖d‖) := (le_abs_self _).trans hb
  have : η * (t * ‖d‖) < κ * t := by
    simp only [η]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg d, mul_pos hκ ht0, mul_nonneg (mul_pos hκ ht0).le (norm_nonneg d)]
  linarith

/-! ### Hopf's lemma -/

/-- **Local Hopf lemma.** Near a zero of `u` in an open set `U`, `u ≤ 0`, provided `u` is a
supersolution of `-Δ + c` (`c ≥ 0`) where it is positive and its gradient vanishes at its
zeros. -/
theorem local_nonpos_on {U : Set (Cfg n)} (hU : IsOpen U) {u c : Cfg n → ℝ} (hu : ContDiff ℝ 2 u)
    (hc : Continuous c) (hc0 : ∀ x, 0 ≤ c x)
    (hsup : ∀ x ∈ U, 0 < u x → 0 ≤ -lapN u x + c x * u x)
    (hgrad : ∀ x ∈ U, u x = 0 → ∀ k, dk k u x = 0) {z : Cfg n} (hz : z ∈ U) (h0 : u z = 0) :
    ∀ᶠ x in 𝓝 z, u x ≤ 0 := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  set N : ℝ := (n : ℝ) + 1
  have hN1 : 1 ≤ N := by simp only [N]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hN : 0 < N := by linarith
  obtain ⟨r0, hr0, hr0s⟩ := Metric.isOpen_iff.mp hU z hz
  set r := r0 / 2
  have hr : 0 < r := by positivity
  have hB : closedBall z r ⊆ U := (closedBall_subset_ball (by simp only [r]; linarith)).trans hr0s
  by_contra hne
  obtain ⟨y, hyu, hyb⟩ := ((Filter.not_eventually.mp hne).and_eventually
    (ball_mem_nhds z (show 0 < r / (4 * N) by positivity))).exists
  have hyz : dist y z < r / (4 * N) := hyb
  have hNd : N * dist z y < r / 4 := by
    rw [dist_comm]
    rw [lt_div_iff₀ (by positivity)] at hyz
    linarith
  have hyz' : dist y z < r / 4 := by
    have := le_mul_of_one_le_left (dist_nonneg (x := z) (y := y)) hN1
    rw [dist_comm]
    linarith
  have hypos : 0 < u y := lt_of_not_ge hyu
  -- the closest zero of `u` to `y`
  set Z' := closedBall z r ∩ {p | u p = 0}
  have hZc : IsCompact Z' :=
    (isCompact_closedBall z r).inter_right (isClosed_eq hu.continuous continuous_const)
  have hZn : Z'.Nonempty := ⟨z, mem_closedBall_self hr.le, h0⟩
  obtain ⟨x1, hx1Z, hx1min⟩ := hZc.exists_isMinOn hZn (continuous_Neu y).continuousOn
  set R2 := Neu y x1
  have hx1u : u x1 = 0 := hx1Z.2
  have hR2z : R2 ≤ Neu y z := hx1min ⟨mem_closedBall_self hr.le, h0⟩
  have hR2small : R2 < (r / 2) ^ 2 := by
    have h1 := Neu_le_dist_sq z y
    have h2 : N * dist z y ^ 2 ≤ (N * dist z y) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    have h3 : (N * dist z y) ^ 2 < (r / 4) ^ 2 :=
      pow_lt_pow_left₀ hNd (mul_nonneg hN.le dist_nonneg) two_ne_zero
    have h4 : (r / 4) ^ 2 < (r / 2) ^ 2 := by nlinarith
    change R2 ≤ _ at hR2z
    have : Neu y z ≤ N * dist z y ^ 2 := h1
    linarith
  have hR2pos : 0 < R2 := by
    rcases (Neu_nonneg y x1).lt_or_eq with h | h
    · exact h
    · exfalso
      have : dist x1 y ^ 2 ≤ R2 := Ndist_sq_le_eu x1 y
      have h' : R2 = 0 := h.symm
      rw [h'] at this
      have hd : dist x1 y = 0 := by nlinarith [dist_nonneg (x := x1) (y := y)]
      rw [dist_eq_zero.mp hd] at hx1u
      linarith
  -- points closer to `y` than `R` lie in the small ball around `z`
  have hnear : ∀ p, Neu y p ≤ R2 → dist p z < 3 * r / 4 := by
    intro p hp
    have := Ndist_lt_of_eu_lt (s := r / 2) (by positivity) (lt_of_le_of_lt hp hR2small)
    linarith [dist_triangle p y z]
  have hinU : ∀ p, Neu y p ≤ R2 → p ∈ U := fun p hp =>
    hB (mem_closedBall.mpr (by linarith [hnear p hp]))
  -- no zero strictly inside the Euclidean ball around `y`
  have hnz : ∀ p, Neu y p < R2 → u p ≠ 0 := by
    intro p hp h
    have := hx1min ⟨mem_closedBall.mpr (by linarith [hnear p hp.le]), h⟩
    exact absurd this (not_le.mpr hp)
  -- hence `u > 0` inside and `u ≥ 0` on the closed ball (intermediate values on segments)
  have hnn : ∀ p, Neu y p ≤ R2 → 0 ≤ u p := by
    intro p hp
    by_contra hneg
    push Not at hneg
    obtain ⟨s, hs, hzero⟩ := Nexists_zero_segment hu.continuous hypos hneg
    have : Neu y (y + s • (p - y)) < R2 := by
      rw [Neu_segment]
      have hs2 : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
      rcases (Neu_nonneg y p).lt_or_eq with hep' | hep'
      · nlinarith
      · rw [← hep']; simpa using hR2pos
    exact hnz _ this hzero
  have hposin : ∀ p, Neu y p < R2 → 0 < u p := fun p hp =>
    lt_of_le_of_ne (hnn p hp.le) (Ne.symm (hnz p hp))
  -- the gradient vanishes at `x1`
  have hx1U : x1 ∈ U := hinU x1 le_rfl
  have hgrad0 : fderiv ℝ u x1 = 0 := fderiv_eq_zero_of_dk (hgrad x1 hx1U hx1u)
  -- the annulus
  set Abar := {p | R2 / 4 ≤ Neu y p ∧ Neu y p ≤ R2}
  have hAc : IsCompact Abar := by
    refine (isCompact_closedBall y r).of_isClosed_subset
      ((isClosed_le continuous_const (continuous_Neu y)).inter
        (isClosed_le (continuous_Neu y) continuous_const)) fun p hp => ?_
    have hd := Ndist_lt_of_eu_lt (s := r / 2) (by positivity) (lt_of_le_of_lt hp.2 hR2small)
    exact mem_closedBall.mpr (by linarith)
  -- the inner sphere and the minimum of `u` on it
  set Cin := {p | Neu y p = R2 / 4}
  have hCc : IsCompact Cin :=
    hAc.of_isClosed_subset (isClosed_eq (continuous_Neu y) continuous_const)
      fun p hp => ⟨hp.ge, by rw [mem_ofPred_eq] at hp; linarith⟩
  have hCn : Cin.Nonempty := by
    refine ⟨Function.update y 0 (y 0 + Real.sqrt (R2 / 4)), ?_⟩
    simp only [Cin, mem_ofPred_eq, Neu_update, add_sub_cancel_left, sub_self]
    rw [Real.sq_sqrt (by positivity)]
    simp [Neu]
  obtain ⟨pm, hpmC, hpmmin⟩ := hCc.exists_isMinOn hCn hu.continuous.continuousOn
  set m := u pm
  have hm : 0 < m := hposin pm (by rw [hpmC]; linarith)
  set ε := m / 2
  have hε : 0 < ε := by positivity
  -- the bound on `c`
  obtain ⟨C0, hC0⟩ := hAc.exists_bound_of_continuousOn hc.continuousOn
  set C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hcC : ∀ p ∈ Abar, c p ≤ C := fun p hp =>
    ((le_abs_self (c p)).trans (by simpa [Real.norm_eq_abs] using hC0 p hp)).trans
      (le_max_left _ _)
  set α := max 1 ((4 * N + 2 * C) / R2)
  have hα1 : 1 ≤ α := le_max_left _ _
  have hαR : 4 * N + 2 * C ≤ α * R2 := by
    have := le_max_right 1 ((4 * N + 2 * C) / R2)
    rw [div_le_iff₀ hR2pos] at this
    exact this
  set K := Real.exp (-α * R2)
  set h := Nbarrier α y K
  set w : Cfg n → ℝ := fun p => u p - ε * h p
  have hw : ContDiff ℝ 2 w := hu.sub (contDiff_const.mul (contDiff_Nbarrier α y K))
  have hlapw : ∀ p, lapN w p = lapN u p - ε * lapN h p := fun p =>
    NlapN_sub_mul hu (contDiff_Nbarrier α y K) ε p
  have hh1 : ∀ p, h p ≤ 1 := by
    intro p
    have : Real.exp (-α * Neu y p) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [Neu_nonneg y p]
    simp only [h, Nbarrier]; linarith [Real.exp_pos (-α * R2)]
  -- weak comparison on the annulus
  have hcomp : ∀ p ∈ Abar, 0 ≤ w p := by
    obtain ⟨q, hqA, hqmin⟩ := hAc.exists_isMinOn ⟨pm, by rw [mem_ofPred_eq, hpmC]; constructor <;>
      linarith⟩ hw.continuous.continuousOn
    intro p hp
    refine le_trans ?_ (hqmin hp)
    by_contra hneg
    push Not at hneg
    rcases hqA.1.lt_or_eq with hlo | hlo
    · rcases hqA.2.lt_or_eq with hhi | hhi
      · -- interior point: a local minimum of `w`, where `u > 0`
        have hopen : IsOpen {p | R2 / 4 < Neu y p ∧ Neu y p < R2} :=
          (isOpen_lt continuous_const (continuous_Neu y)).inter
            (isOpen_lt (continuous_Neu y) continuous_const)
        have hlmin : IsLocalMin w q :=
          Filter.eventually_of_mem (hopen.mem_nhds ⟨hlo, hhi⟩) fun p hp =>
            hqmin ⟨hp.1.le, hp.2.le⟩
        have hlap0 : 0 ≤ lapN w q :=
          Finset.sum_nonneg fun k _ => Ndkk_nonneg_of_isLocalMin hw hlmin k
        have hLu := hsup q (hinU q hqA.2) (hposin q hhi)
        have hbar := Nbarrier_neg (c := c q) (e := Neu y q) hN hα1 hαR hC hqA.1 (hc0 q)
          (hcC q hqA)
        rw [← lapN_Nbarrier α y K q] at hbar
        rw [hlapw q] at hlap0
        have hwq : w q = u q - ε * h q := rfl
        have hhq : h q = Real.exp (-α * Neu y q) - Real.exp (-α * R2) := rfl
        rw [← hhq] at hbar
        nlinarith [hc0 q]
      · -- outer sphere: `h = 0`
        have : h q = 0 := by simp only [h, Nbarrier, K, hhi, sub_self]
        have := hnn q hqA.2
        simp only [w] at hneg
        rw [‹h q = 0›] at hneg
        linarith
    · -- inner sphere: `u ≥ m > ε ≥ ε h`
      have hq' : q ∈ Cin := hlo.symm
      have := hpmmin hq'
      simp only [w] at hneg
      have e2 : m ≤ u q := ‹u pm ≤ u q›
      have e1 : ε * h q ≤ ε := mul_le_of_le_one_right hε.le (hh1 q)
      have e3 : ε = m / 2 := rfl
      linarith
  -- Hopf: `u` grows linearly from `x1` towards `y`, contradicting `∇u(x1) = 0`
  set d := y - x1
  set κ := ε * K * (α * R2)
  have hκ : 0 < κ := by positivity
  have hlin : ∀ t ∈ Ioc (0 : ℝ) (1 / 2), κ * t ≤ u (x1 + t • d) := by
    intro t ht
    have heu : Neu y (x1 + t • d) = (1 - t) ^ 2 * R2 := by
      simp only [Neu, R2, d, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hA : x1 + t • d ∈ Abar := by
      rw [mem_ofPred_eq, heu]
      have ha : 1 / 4 ≤ (1 - t) ^ 2 := by nlinarith [ht.1, ht.2]
      have hb : (1 - t) ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_right ha hR2pos.le]
      · nlinarith [mul_le_mul_of_nonneg_right hb hR2pos.le]
    have hwge := hcomp _ hA
    simp only [w, h, Nbarrier] at hwge
    rw [heu] at hwge
    have hexp := mul_le_mul_of_nonneg_left (Nexp_growth (α := α) (by linarith) hR2pos.le ht) hε.le
    have e : κ * t = ε * (K * (α * R2 * t)) := by simp only [κ]; ring
    linarith
  exact Nhopf_contra hud hx1u hgrad0 hκ hlin

/-- **No sign change through critical zeros.** A `C²` function on a connected open set
`U ⊆ ℝ^(n+1)` that is a supersolution of `-Δ + c` (`c ≥ 0`) where it is positive, and whose
gradient vanishes at every zero, is either positive on the whole of `U` or nonpositive on the
whole of `U`. -/
theorem pos_or_nonpos_on {U : Set (Cfg n)} (hU : IsOpen U) (hconn : IsPreconnected U)
    {u c : Cfg n → ℝ} (hu : ContDiff ℝ 2 u) (hc : Continuous c) (hc0 : ∀ x, 0 ≤ c x)
    (hsup : ∀ x ∈ U, 0 < u x → 0 ≤ -lapN u x + c x * u x)
    (hgrad : ∀ x ∈ U, u x = 0 → ∀ k, dk k u x = 0) :
    (∀ x ∈ U, 0 < u x) ∨ ∀ x ∈ U, u x ≤ 0 := by
  set A := {p | ∀ᶠ q in 𝓝 p, u q ≤ 0}
  set B := {p | 0 < u p}
  have hA : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hBo : IsOpen B := isOpen_lt continuous_const hu.continuous
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_iff]
    intro p ⟨hpA, hpB⟩
    exact absurd hpB (not_lt.mpr hpA.self_of_nhds)
  have hcover : U ⊆ A ∪ B := by
    intro p hp
    rcases lt_trichotomy (u p) 0 with hneg | hz | hpos
    · left
      exact (hu.continuous.continuousAt.eventually_lt continuousAt_const hneg).mono
        fun q hq => hq.le
    · exact Or.inl (local_nonpos_on hU hu hc hc0 hsup hgrad hp hz)
    · exact Or.inr hpos
  rcases hconn.subset_or_subset hA hBo hdisj hcover with h | h
  · exact Or.inr fun p hp => (h hp).self_of_nhds
  · exact Or.inl fun p hp => h hp

end DFT.Continuum.Line
