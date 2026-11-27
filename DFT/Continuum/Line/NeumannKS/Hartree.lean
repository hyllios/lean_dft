/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.NeumannKS.KohnSham

/-!
# Hartree and exchange-correlation for pair interactions (Neumann walls)

For a pair interaction `w(x) = Σ_{i<j} u(x_i, x_j)` with `u ∈ C([0, 1]²)` (`pairW`), the Hartree
energy `E_H(ρ) = ½ ∫∫ u(s, t) ρ(s) ρ(t)` is a continuous quadratic form on `H¹(0, 1)`, hence
Fréchet differentiable, with differential the Hartree potential
`v_H(ρ)(δ) = ½ ∫∫ u (ρ ⊗ δ + δ ⊗ ρ)` (**`hasFDerivAt_hartreeE`**). Subtracting it from `E_Hxc`
leaves the exchange-correlation functional `E_xc = F_w - F_0 - E_H`, Gateaux differentiable on
the `v`-representable densities, and the Kohn–Sham potential splits as
`v_KS = v + v_H(ρ) + v_xc(ρ)` (**`hasDerivAt_xcNH`**).

* `pairW`, `continuous_pairW`.
* `hartreeB`: the bilinear form `(f, g) ↦ ∫∫ u f ⊗ g` on `C([0, 1])`; `hartreeBE` on `H¹(0, 1)`.
* `hartreeE`, `hartreePot`, **`hasFDerivAt_hartreeE`**.
* `xcNH`, **`hasDerivAt_xcNH`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology

variable {n : ℕ} {τ : Stat}

/-- A continuous function on `[0, 1]²` read on `ℝ²`, constant along the normal directions outside
the square. -/
noncomputable def sqExt (u : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ)) (s t : ℝ) : ℝ :=
  u (projIcc 0 1 zero_le_one s, projIcc 0 1 zero_le_one t)

lemma continuous_sqExt (u : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ)) :
    Continuous (Function.uncurry (sqExt u)) :=
  u.continuous.comp ((continuous_projIcc.comp continuous_fst).prodMk
    (continuous_projIcc.comp continuous_snd))

lemma abs_sqExt_le (u : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ)) (s t : ℝ) : |sqExt u s t| ≤ ‖u‖ := by
  rw [← Real.norm_eq_abs]; exact u.norm_coe_le_norm _

/-- **A pair interaction** `w(x) = Σ_{i<j} u(x_i, x_j)`. -/
noncomputable def pairW (u : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ)) : Cfg n → ℝ := fun x =>
  ∑ p ∈ Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2),
    sqExt u (x p.1) (x p.2)

lemma continuous_pairW (u : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ)) :
    Continuous (pairW (n := n) u) :=
  continuous_finsetSum _ fun p _ =>
    (continuous_sqExt u).comp ((continuous_apply p.1).prodMk (continuous_apply p.2) :
      Continuous fun x : Cfg n => (x p.1, x p.2))

/-! ### The Hartree form -/

section form

variable (u : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ))

/-- The integrand `u(s, t) f(s) g(t)` of the Hartree form. -/
noncomputable def hartreeInt (f g : C01) (p : ℝ × ℝ) : ℝ :=
  sqExt u p.1 p.2 * (iccExt f p.1 * iccExt g p.2)

lemma integrable_hartreeInt (f g : C01) : Integrable (hartreeInt u f g) (vol01.prod vol01) :=
  integrable_prod_mu1 (F := fun s t => sqExt u s t * (iccExt f s * iccExt g t))
    ((continuous_sqExt u).mul (((continuous_iccExt f).comp continuous_fst).mul
      ((continuous_iccExt g).comp continuous_snd)))

/-- **The Hartree form** `(f, g) ↦ ∫∫ u(s, t) f(s) g(t)` on `C([0, 1])`, bounded by `‖u‖`. -/
noncomputable def hartreeB : C01 →L[ℝ] C01 →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun f g => ∫ p, hartreeInt u f g p ∂(vol01.prod vol01))
      (fun f₁ f₂ g => by
        rw [← integral_add (integrable_hartreeInt u _ _) (integrable_hartreeInt u _ _)]
        congr 1; funext p; simp only [hartreeInt, iccExt_add]; ring)
      (fun c f g => by
        rw [smul_eq_mul, ← integral_const_mul]
        congr 1; funext p; simp only [hartreeInt, iccExt_smul]; ring)
      (fun f g₁ g₂ => by
        rw [← integral_add (integrable_hartreeInt u _ _) (integrable_hartreeInt u _ _)]
        congr 1; funext p; simp only [hartreeInt, iccExt_add]; ring)
      (fun c f g => by
        rw [smul_eq_mul, ← integral_const_mul]
        congr 1; funext p; simp only [hartreeInt, iccExt_smul]; ring))
    ‖u‖ fun f g => by
      simp only [LinearMap.mk₂_apply]
      calc ‖∫ p, hartreeInt u f g p ∂(vol01.prod vol01)‖
          ≤ ‖u‖ * ‖f‖ * ‖g‖ * (vol01.prod vol01).real univ :=
            norm_integral_le_of_norm_le_const (Eventually.of_forall fun p => by
              simp only [hartreeInt, norm_mul, Real.norm_eq_abs]
              have h1 := abs_sqExt_le u p.1 p.2
              have h2 := abs_ext_le f p.1
              have h3 := abs_ext_le g p.2
              have := mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) (norm_nonneg _))
                (by positivity) (norm_nonneg _)
              linarith)
        _ = ‖u‖ * ‖f‖ * ‖g‖ := by rw [vol01_prod_real_univ, mul_one]

lemma hartreeB_apply (f g : C01) :
    hartreeB u f g = ∫ p, sqExt u p.1 p.2 * (iccExt f p.1 * iccExt g p.2) ∂(vol01.prod vol01) :=
  rfl

/-- The Hartree form on `H¹(0, 1)`. -/
noncomputable def hartreeBE : H1E →L[ℝ] H1E →L[ℝ] ℝ := (hartreeB u).bilinearComp evE evE

/-- **The Hartree energy** `E_H(ρ) = ½ ∫∫ u(s, t) ρ(s) ρ(t)`. -/
noncomputable def hartreeE (ρ : H1E) : ℝ := (1 / 2 : ℝ) * hartreeBE u ρ ρ

/-- **The Hartree potential** `v_H(ρ)(δ) = ½ ∫∫ u (ρ ⊗ δ + δ ⊗ ρ)`. -/
noncomputable def hartreePot (ρ : H1E) : PotH :=
  (1 / 2 : ℝ) • (hartreeBE u ρ + (hartreeBE u).flip ρ)

/-- **The Hartree energy is Fréchet differentiable**, with differential the Hartree potential. -/
theorem hasFDerivAt_hartreeE (ρ : H1E) : HasFDerivAt (hartreeE u) (hartreePot u ρ) ρ := by
  have h := ((hartreeBE u).hasFDerivAt (x := ρ)).clm_apply (hasFDerivAt_id ρ)
  refine (h.const_mul (1 / 2 : ℝ)).congr_fderiv ?_
  ext δ
  simp [hartreePot]

end form

/-! ### The exchange-correlation functional -/

/-- **The exchange-correlation functional** `E_xc = F_w - F_0 - E_H` for a pair interaction. -/
noncomputable def xcNH (τ : Stat) (u : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ)) (ρ : H1E) : ℝ :=
  hxcNH τ (pairW (n := n) u) ρ - hartreeE u ρ

/-- **Differentiability of `E_xc`; the Kohn–Sham potential splits as `v + v_H + v_xc`.** At a
density that is the ground-state density of `v` for the pair interaction `Σ u(x_i, x_j)` and of
`v_s` without interaction, `E_xc` has derivative `v_s(δ) - v(δ) - v_H(ρ)(δ)` along every `δ` of
mass zero. -/
theorem hasDerivAt_xcNH (u : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ)) {v vs : PotH}
    {Ψ Ψs : Cfg n → ℝ} (hΨ : IsGSNH τ (pairW u) v Ψ) (hΨs : IsGSNH τ 0 vs Ψs)
    (hρ : rhoE τ Ψs = rhoE τ Ψ) {δ : H1E} (hδ : ellE δ = 0) :
    HasDerivAt (fun ε : ℝ => xcNH (n := n) τ u (rhoE τ Ψ + ε • δ))
      (vs δ - v δ - hartreePot u (rhoE τ Ψ) δ) 0 := by
  have h1 := hasDerivAt_hxcNH (continuous_pairW u) hΨ hΨs hρ hδ
  have hline : HasDerivAt (fun ε : ℝ => rhoE τ Ψ + ε • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add (rhoE τ Ψ)
  have h2 := (hasFDerivAt_hartreeE u (rhoE τ Ψ)).comp_hasDerivAt_of_eq 0 hline (by simp)
  exact h1.sub h2

end DFT.Continuum.Line
