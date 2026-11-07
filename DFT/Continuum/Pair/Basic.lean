/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Basic

/-!
# Two particles in a box

Two particles on `[0, 1]` with hard walls, an interaction `w(x₁, x₂)`, and a one-body potential `v`
acting as `v(x₁) + v(x₂)`. The configuration space is the square `(0, 1)²`; states are `C²`
functions of exchange symmetry `σ = ±1` (bosons `σ = 1`, fermions `σ = -1`) vanishing on the
walls. The kinetic energy is `∫ |∇ψ|²`.

Everything in `hk_of_ucp` is proved here except unique continuation, which in two dimensions is a
genuine PDE fact (the zero set of a ground state of `-Δ + V` has measure zero; classically a
Carleman/Aronszajn-type unique continuation theorem). It stays an explicit hypothesis.

* `sep_pair`: separation, from the fundamental lemma on the square, after symmetrising test
  functions.
* `rigidL_pair`: a continuous `v` with `v(x) + v(y)` a.e. constant on the square is constant.
* `dens_eq_of_marginal`: equal one-body densities `ρ(x) = ∫ ψ(x, y)² dy` give equal density
  functionals (Fubini and exchange symmetry).
* `hk_pair_of_ucp`: **Hohenberg–Kohn for two particles in a box**, conditional on unique
  continuation of the ground state.
-/

namespace DFT

namespace Continuum

namespace Pair

open MeasureTheory Set Filter Topology Box

/-- The open square. -/
abbrev Sq : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1

/-- Lebesgue measure on the square. -/
noncomputable abbrev μ2 : Measure (ℝ × ℝ) := volume.restrict Sq

/-- The form domain: `C²`, exchange symmetry `σ`, vanishing on the walls `x₁ = 0, 1` (hence, by
symmetry, also on `x₂ = 0, 1`). -/
def Dom2 (σ : ℝ) : Submodule ℝ (ℝ × ℝ → ℝ) where
  carrier := {ψ | ContDiff ℝ 2 ψ ∧ (∀ p, ψ p.swap = σ * ψ p) ∧ (∀ y, ψ (0, y) = 0) ∧
    ∀ y, ψ (1, y) = 0}
  add_mem' ha hb := ⟨ha.1.add hb.1, fun p => by simp [ha.2.1 p, hb.2.1 p]; ring,
    fun y => by simp [ha.2.2.1 y, hb.2.2.1 y], fun y => by simp [ha.2.2.2 y, hb.2.2.2 y]⟩
  zero_mem' := ⟨contDiff_const, fun _ => by simp, fun _ => rfl, fun _ => rfl⟩
  smul_mem' r _ ha := ⟨ha.1.const_smul r, fun p => by simp [ha.2.1 p]; ring,
    fun y => by simp [ha.2.2.1 y], fun y => by simp [ha.2.2.2 y]⟩

/-- Partial derivatives. -/
noncomputable def d1 (ψ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ ψ p (1, 0)
noncomputable def d2 (ψ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ ψ p (0, 1)

/-- Second partial derivatives `∂₁₁ψ` and `∂₂₂ψ`, and the Laplacian. -/
noncomputable def d11 (ψ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ (d1 ψ) p (1, 0)
noncomputable def d22 (ψ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ (d2 ψ) p (0, 1)
noncomputable def lap (ψ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := d11 ψ p + d22 ψ p

lemma contDiff_d1 {ψ : ℝ × ℝ → ℝ} (h : ContDiff ℝ 2 ψ) : ContDiff ℝ 1 (d1 ψ) :=
  (h.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma contDiff_d2 {ψ : ℝ × ℝ → ℝ} (h : ContDiff ℝ 2 ψ) : ContDiff ℝ 1 (d2 ψ) :=
  (h.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma continuous_d11 {ψ : ℝ × ℝ → ℝ} (h : ContDiff ℝ 2 ψ) : Continuous (d11 ψ) :=
  ((contDiff_d1 h).continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma continuous_d22 {ψ : ℝ × ℝ → ℝ} (h : ContDiff ℝ 2 ψ) : Continuous (d22 ψ) :=
  ((contDiff_d2 h).continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma continuous_lap {ψ : ℝ × ℝ → ℝ} (h : ContDiff ℝ 2 ψ) : Continuous (lap ψ) :=
  (continuous_d11 h).add (continuous_d22 h)

lemma integrable2 {F : ℝ × ℝ → ℝ} (hF : Continuous F) : Integrable F μ2 :=
  (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

section domain

variable {σ : ℝ} {ψ : ℝ × ℝ → ℝ}

lemma diff2 (h : ψ ∈ Dom2 σ) : Differentiable ℝ ψ := h.1.differentiable (by norm_num)

lemma cont_d1 (h : ψ ∈ Dom2 σ) : Continuous (d1 ψ) :=
  (h.1.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma cont_d2 (h : ψ ∈ Dom2 σ) : Continuous (d2 ψ) :=
  (h.1.continuous_fderiv (by norm_num)).clm_apply continuous_const

end domain

/-- The coupling `v(x₁) + v(x₂)`. -/
noncomputable def L2 : Pot →ₗ[ℝ] (ℝ × ℝ → ℝ) where
  toFun v := fun p => Box.ext v p.1 + Box.ext v p.2
  map_add' a b := by funext p; simp only [Box.ext, ContinuousMap.add_apply, Pi.add_apply]; ring
  map_smul' r a := by
    funext p; simp only [Box.ext, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      Pi.smul_apply]; ring

lemma continuous_L2 (v : Pot) : Continuous (L2 v) :=
  ((continuous_ext v).comp continuous_fst).add ((continuous_ext v).comp continuous_snd)

/-- The energy form without potential: kinetic energy plus interaction `w`. -/
noncomputable def h02 (w : ℝ × ℝ → ℝ) (ψ φ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p, (d1 ψ p * d1 φ p + d2 ψ p * d2 φ p) ∂μ2 + ∫ p, w p * (ψ p * φ p) ∂μ2

/-- Two particles in a box as a Hohenberg–Kohn setting. -/
noncomputable def setting2 (σ : ℝ) (w : ℝ × ℝ → ℝ) (hw : Continuous w) :
    Setting μ2 Pot where
  D := Dom2 σ
  h0 := h02 w
  h0_add a ha b hb c hc := by
    have e1 : d1 (a + b) = d1 a + d1 b := by
      funext p; simp [d1, fderiv_add (diff2 ha p) (diff2 hb p)]
    have e2 : d2 (a + b) = d2 a + d2 b := by
      funext p; simp [d2, fderiv_add (diff2 ha p) (diff2 hb p)]
    simp only [h02, e1, e2, Pi.add_apply]
    have ia := integrable2 (((cont_d1 ha).mul (cont_d1 hc)).add ((cont_d2 ha).mul (cont_d2 hc)))
    have ib := integrable2 (((cont_d1 hb).mul (cont_d1 hc)).add ((cont_d2 hb).mul (cont_d2 hc)))
    have ja := integrable2 (hw.mul (ha.1.continuous.mul hc.1.continuous))
    have jb := integrable2 (hw.mul (hb.1.continuous.mul hc.1.continuous))
    have h1 : ∫ p, ((d1 a p + d1 b p) * d1 c p + (d2 a p + d2 b p) * d2 c p) ∂μ2 =
        ∫ p, (d1 a p * d1 c p + d2 a p * d2 c p) ∂μ2 +
          ∫ p, (d1 b p * d1 c p + d2 b p * d2 c p) ∂μ2 := by
      rw [← integral_add (f := fun p => d1 a p * d1 c p + d2 a p * d2 c p)
        (g := fun p => d1 b p * d1 c p + d2 b p * d2 c p) ia ib]
      congr 1; funext p; ring
    have h2 : ∫ p, w p * ((a p + b p) * c p) ∂μ2 =
        ∫ p, w p * (a p * c p) ∂μ2 + ∫ p, w p * (b p * c p) ∂μ2 := by
      rw [← integral_add (f := fun p => w p * (a p * c p)) (g := fun p => w p * (b p * c p)) ja jb]
      congr 1; funext p; ring
    rw [h1, h2]; ring
  h0_smul r a ha c hc := by
    have e1 : d1 (r • a) = r • d1 a := by
      funext p; simp [d1, fderiv_const_smul (diff2 ha p) r]
    have e2 : d2 (r • a) = r • d2 a := by
      funext p; simp [d2, fderiv_const_smul (diff2 ha p) r]
    simp only [h02, e1, e2, Pi.smul_apply, smul_eq_mul]
    have h1 : ∫ p, (r * d1 a p * d1 c p + r * d2 a p * d2 c p) ∂μ2 =
        r * ∫ p, (d1 a p * d1 c p + d2 a p * d2 c p) ∂μ2 := by
      rw [← integral_const_mul]; congr 1; funext p; ring
    have h2 : ∫ p, w p * (r * a p * c p) ∂μ2 = r * ∫ p, w p * (a p * c p) ∂μ2 := by
      rw [← integral_const_mul]; congr 1; funext p; ring
    rw [h1, h2]; ring
  h0_symm ψ _ φ _ := by
    simp only [h02]
    congr 1
    · congr 1; funext p; ring
    · congr 1; funext p; ring
  L := L2
  int_L v ψ φ hψ hφ := integrable2 ((continuous_L2 v).mul (hψ.1.continuous.mul hφ.1.continuous))
  int_sq ψ φ hψ hφ := integrable2 (hψ.1.continuous.mul hφ.1.continuous)

/-- Exchange of the particles preserves the measure on the square. -/
lemma integral_swap (F : ℝ × ℝ → ℝ) : ∫ p, F p.swap ∂μ2 = ∫ p, F p ∂μ2 := by
  have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := volume)).setIntegral_preimage_emb MeasurableEquiv.prodComm.measurableEmbedding F Sq
  rw [Set.preimage_swap_prod] at h
  exact h

/-- **Separation on the square** (for symmetric or antisymmetric states). -/
theorem sep_pair (σ : ℝ) (hσ : σ * σ = 1) (w : ℝ × ℝ → ℝ) (hw : Continuous w) :
    Sep (setting2 σ w hw) := by
  intro v c ψ hψ h
  set g : ℝ × ℝ → ℝ := fun p => (L2 v p - c) * ψ p
  have hg : Continuous g := ((continuous_L2 v).sub continuous_const).mul hψ.1.continuous
  have hgs : ∀ p, g p.swap = σ * g p := by
    intro p; simp only [g, L2, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_swap, Prod.snd_swap,
      hψ.2.1 p]; ring
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (U := Sq) (μ := volume)
    (f := g) (isOpen_Ioo.prod isOpen_Ioo) (hg.locallyIntegrable.locallyIntegrableOn _)
    (fun φ hφ _ (hsub : tsupport φ ⊆ Sq) => ?_)
  · exact (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2 hae
  -- symmetrise the test function
  have hout : ∀ p, p ∉ Sq → φ p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport fun h' => hp (hsub h')
  set φs : ℝ × ℝ → ℝ := fun p => φ p + σ * φ p.swap
  have hφs : φs ∈ Dom2 σ := by
    refine ⟨(hφ.of_le (WithTop.coe_le_coe.mpr le_top)).add
      (contDiff_const.mul ((hφ.of_le (WithTop.coe_le_coe.mpr le_top)).comp
        (contDiff_snd.prodMk contDiff_fst))),
      fun p => ?_, fun y => ?_, fun y => ?_⟩
    · simp only [φs, Prod.swap_swap]
      linear_combination (-φ p.swap) * hσ
    · simp only [φs, Prod.swap_prod_mk]
      rw [hout (0, y) (fun h => lt_irrefl _ h.1.1), hout (y, 0) (fun h => lt_irrefl _ h.2.1)]
      ring
    · simp only [φs, Prod.swap_prod_mk]
      rw [hout (1, y) (fun h => lt_irrefl _ h.1.2), hout (y, 1) (fun h => lt_irrefl _ h.2.2)]
      ring
  have h1 := h φs hφs
  have ig := integrable2 (hg.mul (hφ.continuous))
  have ig' := integrable2 (hg.mul (hφ.continuous.comp continuous_swap))
  have hsw : ∫ p, g p * φ p.swap ∂μ2 = σ * ∫ p, g p * φ p ∂μ2 := by
    have := integral_swap (fun p => g p.swap * φ p)
    simp only [Prod.swap_swap] at this
    rw [this, ← integral_const_mul]
    congr 1; funext p; rw [hgs p]; ring
  have hsplit : ∫ p, (L2 v p - c) * ψ p * φs p ∂μ2 =
      ∫ p, g p * φ p ∂μ2 + σ * ∫ p, g p * φ p.swap ∂μ2 := by
    rw [← integral_const_mul, ← integral_add (f := fun p => g p * φ p)
      (g := fun p => σ * (g p * φ p.swap)) ig (ig'.const_mul σ)]
    congr 1; funext p; simp only [φs, g]; ring
  change ∫ p, (L2 v p - c) * ψ p * φs p ∂μ2 = 0 at h1
  rw [hsplit, hsw, ← mul_assoc, hσ, one_mul] at h1
  have hμ : ∫ p, g p * φ p ∂μ2 = 0 := by linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Sq)]
  · simpa [smul_eq_mul, mul_comm] using hμ
  · intro p hp; rw [hout p hp, zero_smul]

/-- **Rigidity on the square.** -/
theorem rigidL_pair (σ : ℝ) (w : ℝ × ℝ → ℝ) (hw : Continuous w) :
    RigidL (setting2 σ w hw) one := by
  intro v c h
  have hO : EqOn (L2 v) (fun _ => c) Sq :=
    Measure.eqOn_open_of_ae_eq h (isOpen_Ioo.prod isOpen_Ioo) (continuous_L2 v).continuousOn
      continuousOn_const
  -- on `(0, 1)`, `v` equals `c/2`
  have h1 : ∀ x ∈ Ioo (0 : ℝ) 1, Box.ext v x = c / 2 := by
    intro x hx
    have hxx := hO (show (x, x) ∈ Sq from ⟨hx, hx⟩)
    simp only [L2, LinearMap.coe_mk, AddHom.coe_mk] at hxx
    linarith
  have hC : EqOn (Box.ext v) (fun _ => c / 2) (Icc 0 1) :=
    EqOn.of_subset_closure h1 (continuous_ext v).continuousOn continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one])
  refine ⟨c / 2, ?_⟩
  ext t
  have := hC t.2
  simp only [Box.ext, projIcc_val] at this
  simp [one, this]

/-- **Densities.** If the one-body densities `ρ(x) = ∫ ψ(x, y)² dy` agree on `(0, 1)`, so do the
norms and the density functionals. -/
theorem dens_eq_of_marginal {σ : ℝ} (hσ : σ * σ = 1) {w : ℝ × ℝ → ℝ} {hw : Continuous w}
    {ψ ψ' : ℝ × ℝ → ℝ} (hψ : ψ ∈ Dom2 σ) (hψ' : ψ' ∈ Dom2 σ)
    (hρ : ∀ x ∈ Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, ψ (x, y) ^ 2 =
      ∫ y in Ioo (0 : ℝ) 1, ψ' (x, y) ^ 2) :
    ip (μ := μ2) ψ ψ = ip (μ := μ2) ψ' ψ' ∧
      dens (setting2 σ w hw) ψ = dens (setting2 σ w hw) ψ' := by
  -- Fubini on the square
  have hprod : (μ2 : Measure (ℝ × ℝ)) =
      (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [Measure.prod_restrict]; rfl
  have fub : ∀ {F : ℝ × ℝ → ℝ}, Continuous F →
      ∫ p, F p ∂μ2 = ∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, F (x, y) := by
    intro F hF
    have hi := integrable2 hF
    rw [hprod] at hi ⊢
    exact integral_prod F hi
  -- the integral of `f(x) ψ(x, y)²` only depends on the density
  have key : ∀ f : ℝ → ℝ, Continuous f →
      ∫ p, f p.1 * (ψ p * ψ p) ∂μ2 = ∫ p, f p.1 * (ψ' p * ψ' p) ∂μ2 := by
    intro f hf
    rw [fub (F := fun p => f p.1 * (ψ p * ψ p))
        ((hf.comp continuous_fst).mul (hψ.1.continuous.mul hψ.1.continuous)),
      fub (F := fun p => f p.1 * (ψ' p * ψ' p))
        ((hf.comp continuous_fst).mul (hψ'.1.continuous.mul hψ'.1.continuous))]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp only
    rw [integral_const_mul, integral_const_mul]
    have := hρ x hx
    simp only [sq] at this
    rw [this]
  -- exchange symmetry moves `f(x₂)` to `f(x₁)`
  have swapsq : ∀ (φ : ℝ × ℝ → ℝ), φ ∈ Dom2 σ → ∀ f : ℝ → ℝ,
      ∫ p, f p.2 * (φ p * φ p) ∂μ2 = ∫ p, f p.1 * (φ p * φ p) ∂μ2 := by
    intro φ hφ f
    rw [← integral_swap]
    congr 1; funext p
    simp only [Prod.snd_swap, hφ.2.1 p]
    linear_combination (f p.1 * φ p * φ p) * hσ
  refine ⟨?_, ?_⟩
  · have := key (fun _ => 1) continuous_const
    simpa [ip] using this
  · funext v
    have hv := continuous_ext v
    simp only [dens, pf]
    change ∫ p, (Box.ext v p.1 + Box.ext v p.2) * (ψ p * ψ p) ∂μ2 =
      ∫ p, (Box.ext v p.1 + Box.ext v p.2) * (ψ' p * ψ' p) ∂μ2
    have split : ∀ φ : ℝ × ℝ → ℝ, φ ∈ Dom2 σ →
        ∫ p, (Box.ext v p.1 + Box.ext v p.2) * (φ p * φ p) ∂μ2 =
          2 * ∫ p, Box.ext v p.1 * (φ p * φ p) ∂μ2 := by
      intro φ hφ
      have i1 := integrable2 ((hv.comp continuous_fst).mul (hφ.1.continuous.mul hφ.1.continuous))
      have i2 := integrable2 ((hv.comp continuous_snd).mul (hφ.1.continuous.mul hφ.1.continuous))
      have hpt : (fun p : ℝ × ℝ => (Box.ext v p.1 + Box.ext v p.2) * (φ p * φ p)) =
          fun p => Box.ext v p.1 * (φ p * φ p) + Box.ext v p.2 * (φ p * φ p) := by
        funext p; ring
      rw [hpt, integral_add (f := fun p => Box.ext v p.1 * (φ p * φ p))
        (g := fun p => Box.ext v p.2 * (φ p * φ p)) i1 i2, swapsq φ hφ (Box.ext v)]
      ring
    rw [split ψ hψ, split ψ' hψ', key _ hv]

/-- **Hohenberg–Kohn for two particles in a box, conditional on unique continuation.** Two
particles on `[0, 1]` (bosons or fermions, any continuous interaction): if ground states of
continuous potentials `v` and `v'` have the same one-body density, and the ground state of `v`
vanishes only on a null set of the square, then `v - v'` is constant. -/
theorem hk_pair_of_ucp {σ : ℝ} (hσ : σ * σ = 1) {w : ℝ × ℝ → ℝ} {hw : Continuous w}
    {v v' : Pot} {ψ ψ' : ℝ × ℝ → ℝ} (hψ : IsGS (setting2 σ w hw) v ψ)
    (hψ' : IsGS (setting2 σ w hw) v' ψ')
    (hρ : ∀ x ∈ Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, ψ (x, y) ^ 2 =
      ∫ y in Ioo (0 : ℝ) 1, ψ' (x, y) ^ 2)
    (hucp : ∀ᵐ p ∂μ2, ψ p ≠ 0) : ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨hn, hd⟩ := dens_eq_of_marginal hσ (w := w) (hw := hw) hψ.1 hψ'.1 hρ
  exact hk_of_ucp (sep_pair σ hσ w hw) (rigidL_pair σ w hw) hψ hψ' hn hd hucp

end Pair

end Continuum

end DFT
