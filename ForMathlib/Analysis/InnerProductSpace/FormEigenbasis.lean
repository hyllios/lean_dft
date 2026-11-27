/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint
import ForMathlib.Analysis.InnerProductSpace.CompactEigenbasis
import ForMathlib.Order.FiniteSublevel

/-!
# The eigenbasis of a semibounded form with compact domain

Let `J : V → H` be a compact injective map with dense range between real Hilbert spaces (the
"form domain" `V` sits inside `H`), `H` infinite-dimensional, and let `q` be a bounded symmetric
bilinear form on `V` with `q(f, f) ≥ c ‖f‖² - C ‖J f‖²`, `c > 0`. Then `H` has a Hilbert basis
`(b_k)_{k ∈ ℕ}` with `b_k = J e_k`, `e_k ∈ V`, and there are `λ₀ ≤ λ₁ ≤ ⋯ → ∞` with
`q(e_k, g) = λ_k ⟪J e_k, J g⟫` for all `g ∈ V` (**`exists_formEigenbasis`**), together with the
variational bound

`Σ_{j<N} λ_j ⟪b_j, J ψ⟫² + λ_N (‖J ψ‖² - Σ_{j<N} ⟪b_j, J ψ⟫²) ≤ q(ψ, ψ)`.

The shifted form `a = q + C ⟪J ·, J ·⟫` is coercive. By Lax–Milgram, `f ∈ H` gives `u_f ∈ V` with
`a(u_f, g) = ⟪f, J g⟫`, and `K f = J u_f` is compact, symmetric, positive and injective on `H`
(`CompactEigenbasis`); its eigenvalues `μ > 0` give `λ = 1/μ - C`, enumerated by
`exists_equiv_nat_monotone`. For the bound write `ψ = Σ_{j<N} c_j e_j + r`: the two parts are
`a`-orthogonal, and `a(r, r) ≥ ‖J r‖² / μ_N` follows from `‖J r‖² = a(u, r)` with `u = u_{J r}`,
`a(u, u) = ⟪J r, K J r⟫ ≤ μ_N ‖J r‖²` (Parseval) and `0 ≤ a(r - u/μ_N, r - u/μ_N)`.
-/

open Filter Topology Module ContinuousLinearMap
open scoped InnerProductSpace

namespace FormEigenbasis

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (J : V →L[ℝ] H) (q : V →L[ℝ] V →L[ℝ] ℝ) (C : ℝ)

/-- The pulled-back inner product `(f, g) ↦ ⟪J f, J g⟫` as a continuous bilinear form. -/
noncomputable def pullInner : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun f g => ⟪J f, J g⟫_ℝ)
      (fun f₁ f₂ g => by rw [map_add, inner_add_left])
      (fun c f g => by rw [map_smul, real_inner_smul_left, smul_eq_mul])
      (fun f g₁ g₂ => by rw [map_add, inner_add_right])
      (fun c f g => by rw [map_smul, real_inner_smul_right, smul_eq_mul]))
    (‖J‖ * ‖J‖) fun f g => by
      simp only [LinearMap.mk₂_apply, Real.norm_eq_abs]
      calc |⟪J f, J g⟫_ℝ| ≤ ‖J f‖ * ‖J g‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖J‖ * ‖f‖) * (‖J‖ * ‖g‖) :=
            mul_le_mul (J.le_opNorm f) (J.le_opNorm g) (norm_nonneg _) (by positivity)
        _ = ‖J‖ * ‖J‖ * ‖f‖ * ‖g‖ := by ring

lemma pullInner_apply (f g : V) : pullInner J f g = ⟪J f, J g⟫_ℝ := rfl

/-- The shifted form `a(f, g) = q(f, g) + C ⟪J f, J g⟫`. -/
noncomputable def shiftForm : V →L[ℝ] V →L[ℝ] ℝ := q + C • pullInner J

lemma shiftForm_apply (f g : V) : shiftForm J q C f g = q f g + C * ⟪J f, J g⟫_ℝ := by
  simp [shiftForm, pullInner_apply]

variable [CompleteSpace V] [CompleteSpace H] {J q C}
variable {c : ℝ} (hc : 0 < c) (hcoer : ∀ f, c * ‖f‖ ^ 2 ≤ q f f + C * ‖J f‖ ^ 2)

omit [CompleteSpace V] [CompleteSpace H] in
include hc hcoer in
lemma isCoercive_shiftForm : IsCoercive (shiftForm J q C) :=
  ⟨c, hc, fun u => by
    rw [shiftForm_apply, real_inner_self_eq_norm_sq]; nlinarith [hcoer u]⟩

omit [CompleteSpace V] [CompleteSpace H] in
include hcoer in
lemma shiftForm_self_ge (f : V) : c * ‖f‖ ^ 2 ≤ shiftForm J q C f f := by
  rw [shiftForm_apply, real_inner_self_eq_norm_sq]; exact hcoer f

/-- The solution operator `f ↦ u_f`, `a(u_f, g) = ⟪f, J g⟫`. -/
noncomputable def solve : H →L[ℝ] V :=
  ((isCoercive_shiftForm hc hcoer).continuousLinearEquivOfBilin.symm : V →L[ℝ] V).comp
    (adjoint J)

lemma shiftForm_solve (f : H) (g : V) : shiftForm J q C (solve hc hcoer f) g = ⟪f, J g⟫_ℝ := by
  rw [← (isCoercive_shiftForm hc hcoer).continuousLinearEquivOfBilin_apply, solve]
  simp [adjoint_inner_left]

/-- The compact operator `K = J ∘ solve`. -/
noncomputable def resolv : H →L[ℝ] H := J.comp (solve hc hcoer)

variable (hsymm : ∀ f g, q f g = q g f)

omit [CompleteSpace V] [CompleteSpace H] in
include hsymm in
lemma shiftForm_symm (f g : V) : shiftForm J q C f g = shiftForm J q C g f := by
  rw [shiftForm_apply, shiftForm_apply, hsymm, real_inner_comm]

include hsymm in
lemma inner_resolv (f h : H) : ⟪resolv hc hcoer f, h⟫_ℝ = ⟪f, resolv hc hcoer h⟫_ℝ := by
  simp only [resolv, comp_apply]
  rw [real_inner_comm, ← shiftForm_solve hc hcoer h, shiftForm_symm hsymm, shiftForm_solve]

lemma inner_resolv_self (f : H) :
    ⟪resolv hc hcoer f, f⟫_ℝ = shiftForm J q C (solve hc hcoer f) (solve hc hcoer f) := by
  rw [resolv, comp_apply, real_inner_comm, shiftForm_solve]

variable (hJc : IsCompactOperator J) (hJinj : Function.Injective J) (hJd : DenseRange J)

include hJc in
lemma isCompactOperator_resolv : IsCompactOperator (resolv hc hcoer) :=
  hJc.comp_clm (solve hc hcoer)

include hJinj hJd in
lemma resolv_injective (f : H) (hf : resolv hc hcoer f = 0) : f = 0 := by
  have hu : solve hc hcoer f = 0 := hJinj (by simpa [resolv] using hf)
  have hperp : ∀ g, ⟪f, J g⟫_ℝ = 0 := fun g => by
    rw [← shiftForm_solve hc hcoer f g, hu, map_zero, zero_apply]
  have : ∀ x, ⟪f, x⟫_ℝ = 0 := fun x =>
    hJd.induction_on x (isClosed_eq (continuous_const.inner continuous_id) continuous_const) hperp
  simpa using this f

end FormEigenbasis

open FormEigenbasis CompactEigenbasis in
/-- **Eigenbasis of a semibounded form with compact domain.** -/
theorem exists_formEigenbasis {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (hH : ¬ FiniteDimensional ℝ H) {J : V →L[ℝ] H} (hJc : IsCompactOperator J)
    (hJinj : Function.Injective J) (hJd : DenseRange J) {q : V →L[ℝ] V →L[ℝ] ℝ}
    (hsymm : ∀ f g, q f g = q g f) {c C : ℝ} (hc : 0 < c)
    (hcoer : ∀ f, c * ‖f‖ ^ 2 ≤ q f f + C * ‖J f‖ ^ 2) :
    ∃ (e : ℕ → V) (lam : ℕ → ℝ) (b : HilbertBasis ℕ ℝ H), Monotone lam ∧
      Tendsto lam atTop atTop ∧ (∀ k, J (e k) = b k) ∧
      (∀ k g, q (e k) g = lam k * ⟪J (e k), J g⟫_ℝ) ∧
      ∀ (N : ℕ) (ψ : V), ∑ j ∈ Finset.range N, lam j * ⟪b j, J ψ⟫_ℝ ^ 2 +
        lam N * (‖J ψ‖ ^ 2 - ∑ j ∈ Finset.range N, ⟪b j, J ψ⟫_ℝ ^ 2) ≤ q ψ ψ := by
  classical
  set K := resolv hc hcoer
  have hK := isCompactOperator_resolv hc hcoer hJc
  have hKs : (K : H →ₗ[ℝ] H).IsSymmetric := fun f h => inner_resolv hc hcoer hsymm f h
  have hKi := resolv_injective hc hcoer hJinj hJd
  set bb := eigenBasis hK hKs hKi
  set μ : EIdx K → ℝ := fun i => (i.1 : ℝ)
  have hKb : ∀ i, K (bb i) = μ i • bb i := fun i => by
    rw [eigenBasis_coe]; exact eigVec_apply hK hKi i
  -- the eigenvalues are positive
  have hμpos : ∀ i, 0 < μ i := fun i => by
    have hu : solve hc hcoer (bb i) ≠ 0 := fun h0 => by
      have : K (bb i) = 0 := by
        change J (solve hc hcoer (bb i)) = 0; rw [h0, map_zero]
      rw [hKb, smul_eq_zero] at this
      rcases this with h | h
      · exact eval_ne_zero hKi i.1 h
      · exact (bb.orthonormal.ne_zero i) h
    have h1 := inner_resolv_self hc hcoer (bb i)
    rw [hKb, real_inner_smul_left, real_inner_self_eq_norm_sq, bb.orthonormal.1 i] at h1
    have h2 := shiftForm_self_ge hcoer (solve hc hcoer (bb i))
    have h3 : 0 < ‖solve hc hcoer (bb i)‖ := norm_pos_iff.2 hu
    have h4 := mul_pos hc (pow_pos h3 2)
    simp only [one_pow, mul_one] at h1
    linarith
  -- the index type is infinite
  have hinf : Infinite (EIdx K) := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    have := Fintype.ofFinite (EIdx K)
    exact hH (Module.Finite.of_basis bb.toOrthonormalBasis.toBasis)
  -- enumerate by increasing `1/μ`
  have hsub : ∀ t, {i | (μ i)⁻¹ ≤ t}.Finite := fun t => by
    rcases le_or_gt t 0 with ht | ht
    · refine Set.finite_empty.subset fun i hi => ?_
      exact absurd hi (not_le.2 (lt_of_le_of_lt ht (inv_pos.2 (hμpos i))))
    · refine (finite_ge hK hKs hKi (inv_pos.2 ht)).subset fun i hi => ?_
      have hi' : (μ i)⁻¹ ≤ t := hi
      exact (inv_le_comm₀ (hμpos i) ht).1 hi'
  obtain ⟨σ, hσm, hσt⟩ := exists_equiv_nat_monotone (fun i => (μ i)⁻¹) hsub
  set B : ℕ → H := fun k => bb (σ k)
  have hBon : Orthonormal ℝ B := bb.orthonormal.comp σ σ.injective
  have hBsp : ⊤ ≤ (Submodule.span ℝ (Set.range B)).topologicalClosure := by
    have : Set.range B = Set.range bb := by
      ext x; simp only [B, Set.mem_range]
      exact ⟨fun ⟨k, hk⟩ => ⟨σ k, hk⟩, fun ⟨i, hi⟩ => ⟨σ.symm i, by simp [hi]⟩⟩
    rw [this, bb.dense_span]
  set b : HilbertBasis ℕ ℝ H := HilbertBasis.mk hBon hBsp
  have hb : ∀ k, b k = B k := fun k => by simp [b]
  set m : ℕ → ℝ := fun k => μ (σ k)
  have hm : ∀ k, 0 < m k := fun k => hμpos _
  have hmanti : Antitone m := fun k l hkl => by
    have := hσm hkl
    simp only [Function.comp_apply] at this
    exact (inv_le_inv₀ (hm k) (hm l)).1 this
  set lam : ℕ → ℝ := fun k => (m k)⁻¹ - C
  set e : ℕ → V := fun k => (m k)⁻¹ • solve hc hcoer (B k)
  have hKB : ∀ k, K (B k) = m k • B k := fun k => hKb (σ k)
  have hJe : ∀ k, J (e k) = B k := fun k => by
    have : J (solve hc hcoer (B k)) = m k • B k := hKB k
    simp only [e, map_smul, this, smul_smul, inv_mul_cancel₀ (hm k).ne', one_smul]
  have hae : ∀ k g, shiftForm J q C (e k) g = (m k)⁻¹ * ⟪B k, J g⟫_ℝ := fun k g => by
    simp only [e, map_smul, smul_apply, smul_eq_mul, shiftForm_solve]
  have heig : ∀ k g, q (e k) g = lam k * ⟪J (e k), J g⟫_ℝ := fun k g => by
    have := hae k g
    rw [shiftForm_apply, hJe] at this
    rw [hJe, sub_mul]; linarith
  refine ⟨e, lam, b, fun k l hkl => by simpa [lam] using hσm hkl, ?_, fun k => by rw [hJe, hb],
    heig, ?_⟩
  · exact tendsto_atTop_add_const_right _ (-C) hσt |>.congr fun k => by simp [lam, m, sub_eq_add_neg]
  -- the variational bound
  intro N ψ
  set x := J ψ
  set cj : ℕ → ℝ := fun j => ⟪B j, x⟫_ℝ
  set s : V := ∑ j ∈ Finset.range N, cj j • e j
  set r : V := ψ - s
  set a := shiftForm J q C
  have hJs : J s = ∑ j ∈ Finset.range N, cj j • B j := by simp [s, hJe]
  have hinB : ∀ j l, ⟪B j, B l⟫_ℝ = if j = l then 1 else 0 := orthonormal_iff_ite.1 hBon
  have hBsum : ∀ j < N, ⟪B j, ∑ l ∈ Finset.range N, cj l • B l⟫_ℝ = cj j := fun j hj => by
    simp only [inner_sum, inner_smul_right, hinB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_range, hj, ite_true]
  have hBr : ∀ j < N, ⟪B j, J r⟫_ℝ = 0 := fun j hj => by
    have hJr : J r = x - ∑ l ∈ Finset.range N, cj l • B l := by
      simp only [r, map_sub, hJs, x]
    rw [hJr, inner_sub_right, hBsum j hj]
    simp [cj]
  -- `a(s, ·)` against `r` vanishes, and `a(s, s) = Σ c_j² / m_j`
  have has : ∀ g, a s g = ∑ j ∈ Finset.range N, cj j * ((m j)⁻¹ * ⟪B j, J g⟫_ℝ) := fun g => by
    simp only [s, a, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, hae]
  have hasr : a s r = 0 := by
    rw [has]; exact Finset.sum_eq_zero fun j hj => by
      rw [hBr j (Finset.mem_range.1 hj)]; ring
  have hass : a s s = ∑ j ∈ Finset.range N, (m j)⁻¹ * cj j ^ 2 := by
    rw [has, hJs]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hBsum j (Finset.mem_range.1 hj)]
    ring
  have hsymm_a : ∀ f g, a f g = a g f := shiftForm_symm hsymm
  have hψ : a ψ ψ = a s s + a r r := by
    have hψe : ψ = s + r := by simp [r]
    rw [hψe]
    simp only [map_add, add_apply, hasr, hsymm_a r s]
    ring
  -- `a(r, r) ≥ ‖J r‖² / m_N`
  set y := J r
  set u := solve hc hcoer y
  have hyy : ⟪y, y⟫_ℝ = a u r := (shiftForm_solve hc hcoer y r).symm
  have hspec : a u u ≤ m N * ‖y‖ ^ 2 := by
    have h1 : a u u = ⟪K y, y⟫_ℝ := (inner_resolv_self hc hcoer y).symm
    have hS1 := b.hasSum_inner_mul_inner y (K y)
    have hS2 := b.hasSum_inner_mul_inner y y
    have hterm : ∀ k, ⟪y, b k⟫_ℝ * ⟪b k, K y⟫_ℝ ≤ m N * (⟪y, b k⟫_ℝ * ⟪b k, y⟫_ℝ) := fun k => by
      have hK' : ⟪b k, K y⟫_ℝ = m k * ⟪b k, y⟫_ℝ := by
        rw [← inner_resolv hc hcoer hsymm (b k) y, hb, hKB, real_inner_smul_left]
      rw [hK', real_inner_comm y (b k)]
      rcases lt_or_ge k N with hk | hk
      · have : ⟪y, b k⟫_ℝ = 0 := by rw [real_inner_comm, hb]; exact hBr k hk
        rw [this]; simp
      · nlinarith [hmanti hk, sq_nonneg ⟪y, b k⟫_ℝ]
    have := hasSum_le hterm hS1 (hS2.mul_left (m N))
    rw [h1, real_inner_comm, ← real_inner_self_eq_norm_sq]
    linarith
  have har : ‖y‖ ^ 2 / m N ≤ a r r := by
    have hpos := shiftForm_self_ge hcoer (r - (m N)⁻¹ • u)
    have hexp : a (r - (m N)⁻¹ • u) (r - (m N)⁻¹ • u) =
        a r r - 2 * (m N)⁻¹ * a u r + (m N)⁻¹ ^ 2 * a u u := by
      simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, hsymm_a r u]
      ring
    have hnn : 0 ≤ a (r - (m N)⁻¹ • u) (r - (m N)⁻¹ • u) :=
      le_trans (by positivity) hpos
    rw [hexp, ← hyy, real_inner_self_eq_norm_sq] at hnn
    have hmN := hm N
    have : (m N)⁻¹ ^ 2 * a u u ≤ (m N)⁻¹ * ‖y‖ ^ 2 := by
      calc (m N)⁻¹ ^ 2 * a u u ≤ (m N)⁻¹ ^ 2 * (m N * ‖y‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hspec (by positivity)
        _ = (m N)⁻¹ * ‖y‖ ^ 2 := by field_simp
    rw [div_eq_inv_mul]
    linarith
  -- Pythagoras: `‖J r‖² = ‖J ψ‖² - Σ c_j²`
  have hpy : ‖y‖ ^ 2 = ‖x‖ ^ 2 - ∑ j ∈ Finset.range N, cj j ^ 2 := by
    have hx : x = J s + y := by simp only [y, r, x, map_sub]; abel
    have hsy : ⟪J s, y⟫_ℝ = 0 := by
      rw [hJs, sum_inner]
      exact Finset.sum_eq_zero fun j hj => by
        rw [real_inner_smul_left, hBr j (Finset.mem_range.1 hj), mul_zero]
    have hss : ‖J s‖ ^ 2 = ∑ j ∈ Finset.range N, cj j ^ 2 := by
      rw [hJs, ← real_inner_self_eq_norm_sq, sum_inner]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [real_inner_smul_left, hBsum j (Finset.mem_range.1 hj)]
      ring
    rw [hx, norm_add_sq_real, hsy, hss]
    ring
  -- assemble
  have hq : q ψ ψ = a ψ ψ - C * ‖x‖ ^ 2 := by
    rw [shiftForm_apply, real_inner_self_eq_norm_sq]; ring
  rw [hq, hψ, hass]
  have hl : ∀ j, lam j = (m j)⁻¹ - C := fun j => rfl
  simp only [hb, hl]
  have hdiv : ‖y‖ ^ 2 / m N = (m N)⁻¹ * (‖x‖ ^ 2 - ∑ j ∈ Finset.range N, cj j ^ 2) := by
    rw [hpy, div_eq_inv_mul]
  have hsum : ∑ j ∈ Finset.range N, ((m j)⁻¹ - C) * ⟪B j, x⟫_ℝ ^ 2 =
      ∑ j ∈ Finset.range N, (m j)⁻¹ * cj j ^ 2 - C * ∑ j ∈ Finset.range N, cj j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [cj]; ring
  rw [hsum]
  nlinarith [har, hdiv]
