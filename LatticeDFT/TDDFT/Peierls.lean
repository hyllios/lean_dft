/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.TDDFT.FluxGround
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Lattice TDDFT with Peierls phases, starting from a ground state

A magnetic field enters a lattice model through Peierls phases: the hopping `t_ab` becomes
`t_ab e^{iθ φ_ab}`, with an antisymmetric phase pattern `φ` and a field strength `θ`. Its real
part `t cos(θφ)` and imaginary part `t sin(θφ)` both depend nonlinearly on `θ`, so the polynomial
argument of `FluxGround` does not apply. Instead the doubled Krylov determinants are *real-analytic*
in `θ`, and nonzero at `θ = 0`; by the principle of isolated zeros they vanish only on a closed
discrete set of field strengths.

* `hstarC_of_hstar_analytic`: for an analytic family `A θ + i B θ` with `B 0 = 0` whose real
  Krylov polynomials are nonzero at `θ = 0`, the doubled Krylov polynomials are nonzero outside a
  closed discrete set `Λ ∌ 0` (finite in every bounded interval).
* `generic_peierls_ground_mem_omegaC`: spinless lattice fermions on a connected graph with
  common-sign hopping and Peierls phases. Outside a closed discrete set of field strengths, and
  outside a closed, nowhere dense, null set of potentials, every ground state lies in `Ω`.
-/

namespace LatticeDFT

open Matrix Set MeasureTheory Filter Topology

section analytic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entries of powers of an analytic matrix family are analytic. -/
lemma analyticAt_pow_apply {H : ℝ → Matrix ι ι ℝ} {θ : ℝ}
    (hH : ∀ i j, AnalyticAt ℝ (fun x => H x i j) θ) (k : ℕ) (i j : ι) :
    AnalyticAt ℝ (fun x => (H x ^ k) i j) θ := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero]
    exact analyticAt_const
  | succ k ih =>
    simp only [pow_succ]
    exact Finset.analyticAt_fun_sum _ fun l _ => (ih i l).mul (hH l j)

/-- The determinant of an analytic matrix family is analytic. -/
lemma analyticAt_det {H : ℝ → Matrix ι ι ℝ} {θ : ℝ}
    (hH : ∀ i j, AnalyticAt ℝ (fun x => H x i j) θ) :
    AnalyticAt ℝ (fun x => (H x).det) θ := by
  simp only [det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hH _ _)

/-- A set with no accumulation points meets every bounded interval in a finite set. -/
lemma finite_inter_Icc_of_discrete {Λ : Set ℝ} (h : ∀ θ₀, ∀ᶠ θ in 𝓝[≠] θ₀, θ ∉ Λ) (a b : ℝ) :
    (Λ ∩ Icc a b).Finite := by
  by_contra hinf
  obtain ⟨x, -, hx⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc inter_subset_right
  rw [accPt_iff_frequently_nhdsNE] at hx
  exact hx ((h x).mono fun θ hθ hm => hθ hm.1)

end analytic

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **Generic field strengths for an analytic flux family.** If `A θ` and `B θ` depend
analytically on `θ`, `B 0 = 0`, and the real Krylov polynomials of `A 0` are nonzero, then the
doubled Krylov polynomials of `A θ + i B θ` are nonzero for all `θ` outside a closed set `Λ` with
no accumulation points and not containing `0`. -/
theorem hstarC_of_hstar_analytic {A B : ℝ → Matrix C C ℝ}
    (hA : ∀ θ i j, AnalyticAt ℝ (fun x => A x i j) θ)
    (hB : ∀ θ i j, AnalyticAt ℝ (fun x => B x i j) θ) (hB0 : B 0 = 0)
    {n : V → C → ℝ} {ord : C → ℕ} (hstar : ∀ c, krylovPoly (A 0) n c ord ≠ 0) :
    ∃ Λ : Set ℝ, IsClosed Λ ∧ 0 ∉ Λ ∧ (∀ θ₀, ∀ᶠ θ in 𝓝[≠] θ₀, θ ∉ Λ) ∧
      ∀ θ ∉ Λ, ∀ c, krylovPolyC (A θ) (B θ) n c ord ≠ 0 := by
  -- a potential at which all real Krylov determinants of `A 0` are nonzero
  set Q := ∏ c, krylovPoly (A 0) n c ord
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hstar c
  obtain ⟨v0, hv0⟩ : ∃ v0, MvPolynomial.eval v0 Q ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (MvPolynomial.funext fun v => by simpa using h v)
  have hv0c : ∀ c, (kry (hamN (A 0) n v0) c ord).det ≠ 0 := by
    intro c hc
    apply hv0
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [eval_krylovPoly]; exact hc)
  -- the product of the doubled Krylov determinants at `v0`, as a function of `θ`
  set g : ℝ → ℝ := fun θ => ∏ c, (kryC (hamN (dblH (A θ) (B θ)) (dblN n) v0) c ord).det
  have hent : ∀ θ p q, AnalyticAt ℝ (fun x => hamN (dblH (A x) (B x)) (dblN n) v0 p q) θ := by
    rintro θ ⟨a, x⟩ ⟨b, y⟩
    simp only [hamN]
    refine AnalyticAt.add ?_ analyticAt_const
    cases x <;> cases y
    · exact hA θ a b
    · exact (hB θ a b).neg
    · exact hB θ a b
    · exact hA θ a b
  have hg : ∀ θ, AnalyticAt ℝ g θ := by
    intro θ
    refine Finset.analyticAt_fun_prod _ fun c _ => analyticAt_det fun i j => ?_
    exact analyticAt_pow_apply (hent θ) _ _ _
  have hg0 : g 0 ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
    rw [hB0, hamN_dbl, det_kryC_zero]
    exact pow_ne_zero 2 (hv0c c)
  have hcont : Continuous g := continuous_iff_continuousAt.2 fun θ => (hg θ).continuousAt
  refine ⟨{θ | g θ = 0}, isClosed_eq hcont continuous_const, hg0, fun θ₀ => ?_,
    fun θ hθ c hc => hθ ?_⟩
  · by_contra hfr
    rw [not_eventually] at hfr
    have hfr' : ∃ᶠ θ in 𝓝[≠] θ₀, g θ = 0 := hfr.mono fun θ h => by simpa using h
    have hgA : AnalyticOnNhd ℝ g univ := fun x _ => hg x
    have := hgA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ θ₀) hfr'
    exact hg0 (this (mem_univ 0))
  · change ∏ c, _ = 0
    refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
    rw [← eval_krylovPolyC, hc, map_zero]

section fermions

variable {M N : ℕ}

lemma gamma_neg (h : Matrix (Fin M) (Fin M) ℝ) :
    (Γ (-h) : Matrix (Conf M N) (Conf M N) ℝ) = -Γ h := by
  rw [← neg_one_smul ℝ h, gamma_smul, neg_one_smul]

/-- Second quantisation commutes with transposition. -/
lemma gamma_transpose (h : Matrix (Fin M) (Fin M) ℝ) :
    (Γ h : Matrix (Conf M N) (Conf M N) ℝ)ᵀ = Γ hᵀ := by
  ext s s'
  rw [Matrix.transpose_apply, gamma_leibniz, gamma_leibniz]
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))]
  apply Finset.sum_congr rfl; intro σ _
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv]
  congr 1
  rw [← Equiv.sum_comp σ]
  apply Finset.sum_congr rfl; intro j0 _
  have e1 : σ⁻¹ (σ j0) = j0 := by simp
  rw [e1, Matrix.transpose_apply]
  congr 1
  rw [← Equiv.prod_comp σ]
  apply Finset.prod_congr rfl; intro j _
  have e2 : σ⁻¹ (σ j) = j := by simp
  rw [e2]
  by_cases hj : j = j0
  · simp [hj]
  · have : σ j ≠ σ j0 := fun h' => hj (σ.injective h')
    simp [hj, this, eq_comm]

/-- Entries of the second quantisation of an analytic family are analytic. -/
lemma analyticAt_gamma_apply {h : ℝ → Matrix (Fin M) (Fin M) ℝ} {θ : ℝ}
    (hh : ∀ a b, AnalyticAt ℝ (fun x => h x a b) θ) (s s' : Conf M N) :
    AnalyticAt ℝ (fun x => (Γ (h x) : Matrix (Conf M N) (Conf M N) ℝ) s s') θ := by
  simp only [Γ]
  exact Finset.analyticAt_fun_sum _ fun k _ => Finset.analyticAt_fun_sum _ fun b _ =>
    (hh _ _).mul analyticAt_const

/-- Real part of the Peierls Hamiltonian: hopping `t_ab cos(θ φ_ab)`, plus the interaction. The
full Hamiltonian is `Γ(-t e^{iθφ}) + Vint = peierlsRe + i peierlsIm`. -/
noncomputable def peierlsRe (G : SimpleGraph (Fin M)) [DecidableRel G.Adj]
    (t φ : Fin M → Fin M → ℝ) (Vint : Conf M N → ℝ) (θ : ℝ) : Matrix (Conf M N) (Conf M N) ℝ :=
  H0Fw G (fun a b => t a b * Real.cos (θ * φ a b)) Vint

/-- Imaginary part of the Peierls Hamiltonian: hopping `t_ab sin(θ φ_ab)`. -/
noncomputable def peierlsIm (G : SimpleGraph (Fin M)) [DecidableRel G.Adj]
    (t φ : Fin M → Fin M → ℝ) (θ : ℝ) : Matrix (Conf M N) (Conf M N) ℝ :=
  Γ (-hopM G (fun a b => t a b * Real.sin (θ * φ a b)))

lemma peierlsRe_zero (G : SimpleGraph (Fin M)) [DecidableRel G.Adj]
    (t φ : Fin M → Fin M → ℝ) (Vint : Conf M N → ℝ) : peierlsRe G t φ Vint 0 = H0Fw G t Vint := by
  simp [peierlsRe]

lemma peierlsIm_zero (G : SimpleGraph (Fin M)) [DecidableRel G.Adj]
    (t φ : Fin M → Fin M → ℝ) : (peierlsIm G t φ 0 : Matrix (Conf M N) (Conf M N) ℝ) = 0 := by
  have : hopM G (fun a b => t a b * Real.sin (0 * φ a b)) = 0 := by
    ext a b; simp [hopM]
  rw [peierlsIm, this, neg_zero, ← zero_smul ℝ (0 : Matrix (Fin M) (Fin M) ℝ), gamma_smul,
    zero_smul]

lemma peierlsRe_isSymm (G : SimpleGraph (Fin M)) [DecidableRel G.Adj]
    {t φ : Fin M → Fin M → ℝ} (ht : ∀ a b, t a b = t b a) (hφ : ∀ a b, φ b a = -φ a b)
    (Vint : Conf M N → ℝ) (θ : ℝ) : (peierlsRe G t φ Vint θ).IsSymm :=
  H0Fw_isSymm G (fun a b => by rw [ht a b, hφ a b, mul_neg, Real.cos_neg]) Vint

lemma peierlsIm_antisymm (G : SimpleGraph (Fin M)) [DecidableRel G.Adj]
    {t φ : Fin M → Fin M → ℝ} (ht : ∀ a b, t a b = t b a) (hφ : ∀ a b, φ b a = -φ a b) (θ : ℝ) :
    (peierlsIm G t φ θ : Matrix (Conf M N) (Conf M N) ℝ)ᵀ = -peierlsIm G t φ θ := by
  have hT : (hopM G (fun a b => t a b * Real.sin (θ * φ a b)))ᵀ =
      -hopM G (fun a b => t a b * Real.sin (θ * φ a b)) := by
    ext a b
    rw [transpose_apply, Matrix.neg_apply]
    simp only [hopM]
    by_cases h : G.Adj a b
    · simp only [h, h.symm, ↓reduceIte, ht b a, hφ b a, mul_neg, Real.sin_neg, neg_neg]
    · have h' : ¬ G.Adj b a := fun h' => h h'.symm
      simp only [h, h', ↓reduceIte, neg_zero]
  rw [peierlsIm, gamma_transpose, transpose_neg, hT, gamma_neg, gamma_neg]

lemma analyticAt_peierlsRe (G : SimpleGraph (Fin M)) [DecidableRel G.Adj]
    (t φ : Fin M → Fin M → ℝ) (Vint : Conf M N → ℝ) (θ : ℝ) (s s' : Conf M N) :
    AnalyticAt ℝ (fun x => peierlsRe G t φ Vint x s s') θ := by
  simp only [peierlsRe, H0Fw]
  refine AnalyticAt.add (analyticAt_gamma_apply (fun a b => ?_) s s') analyticAt_const
  change AnalyticAt ℝ (fun x => -(hopM G (fun a b => t a b * Real.cos (x * φ a b)) a b)) θ
  simp only [hopM]
  split_ifs
  · exact (analyticAt_const.mul (Real.analyticAt_cos.comp
      (analyticAt_id.mul analyticAt_const))).neg
  · exact analyticAt_const

lemma analyticAt_peierlsIm (G : SimpleGraph (Fin M)) [DecidableRel G.Adj]
    (t φ : Fin M → Fin M → ℝ) (θ : ℝ) (s s' : Conf M N) :
    AnalyticAt ℝ (fun x => (peierlsIm G t φ x : Matrix (Conf M N) (Conf M N) ℝ) s s') θ := by
  simp only [peierlsIm]
  refine analyticAt_gamma_apply (fun a b => ?_) s s'
  change AnalyticAt ℝ (fun x => -(hopM G (fun a b => t a b * Real.sin (x * φ a b)) a b)) θ
  simp only [hopM]
  split_ifs
  · exact (analyticAt_const.mul (Real.analyticAt_sin.comp
      (analyticAt_id.mul analyticAt_const))).neg
  · exact analyticAt_const

/-- **TDDFT with a magnetic field from the ground state, lattice fermions.** Spinless fermions on a
connected graph, symmetric hopping `t` of a common sign, any interaction, and Peierls phases
`e^{iθ φ_ab}` with any antisymmetric pattern `φ`. There is a closed set `Λ` of field strengths, not
containing `0`, without accumulation points (so finite in every bounded interval), such that for
`θ ∉ Λ`, outside a closed, nowhere dense, Lebesgue-null set of potentials, every (complex) ground
state lies in `Ω`; `td_existence_complex`, `td_uniqueness_complex` and `td_global_complex` then
apply to it. -/
theorem generic_peierls_ground_mem_omegaC [NeZero M] {G : SimpleGraph (Fin M)}
    [DecidableRel G.Adj] (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a)
    {s : ℝ} (hts : ∀ a b, G.Adj a b → 0 < s * t a b) {φ : Fin M → Fin M → ℝ}
    (hφ : ∀ a b, φ b a = -φ a b) (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ) :
    ∃ Λ : Set ℝ, IsClosed Λ ∧ 0 ∉ Λ ∧ (∀ θ₀, ∀ᶠ θ in 𝓝[≠] θ₀, θ ∉ Λ) ∧
      (∀ a b, (Λ ∩ Icc a b).Finite) ∧ ∀ θ ∉ Λ,
        ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
          ∀ v ∉ Z, ∀ ψ, IsGroundStateC (peierlsRe G t φ Vint θ) (peierlsIm G t φ θ) occF v ψ →
            ψ ∈ omegaC (peierlsRe G t φ Vint θ) (peierlsIm G t φ θ) occF := by
  set ord : Conf M N → ℕ := fun j => (Fintype.equivFin (Conf M N) j : ℕ)
  obtain ⟨Λ, hcl, h0, hdisc, hgen⟩ := hstarC_of_hstar_analytic (n := occF) (ord := ord)
    (A := peierlsRe G t φ Vint) (B := peierlsIm G t φ)
    (fun θ i j => analyticAt_peierlsRe G t φ Vint θ i j)
    (fun θ i j => analyticAt_peierlsIm G t φ θ i j) (peierlsIm_zero G t φ)
    (fun c => by rw [peierlsRe_zero]; exact hstar_lattice_fermions_w hG hts c Vint)
  exact ⟨Λ, hcl, h0, hdisc, finite_inter_Icc_of_discrete hdisc, fun θ hθ =>
    generic_ground_mem_omegaC (peierlsRe_isSymm G htsym hφ Vint θ)
      (peierlsIm_antisymm G htsym hφ θ) (rigid_occF hN0 hNM) (hgen θ hθ)⟩

end fermions

end LatticeDFT
