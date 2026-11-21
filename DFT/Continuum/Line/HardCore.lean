/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Represent
import DFT.Continuum.Line.Lieb
import DFT.Continuum.Sine.Exists
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Basic.Real.Sign

/-!
# Hard-core bosons on a line (Tonks–Girardeau)

`N = n + 1` bosons on `[0, 1]` with an infinitely strong contact repulsion: the wave function is
symmetric and vanishes whenever two particles meet. Girardeau's map multiplies by the sign of the
Vandermonde product,

  `A(x) = sign ∏_{i<j} (x_j - x_i)`,

which is `±1` away from collisions, locally constant there, and changes sign as a fermionic wave
function does. So `ψ ↦ A ψ` sends fermionic states to symmetric states vanishing at contact, and
preserves `|ψ|²`, the gradient almost everywhere, hence every energy and every density.

* `gA`: Girardeau's sign; `gA_pm`, `gA_mul_self`, `gA_eventually`.
* `DomHC`: the hard-core domain, the image of the fermionic domain under `mulA`.
  `mem_DomHC_iff`: intrinsically, `φ` vanishes at collisions and `A φ` is a fermionic `C²` state.
  `DomHC_pm`, `DomHC_wall`: hard-core states are symmetric and vanish on the walls.
* `settingHC`: hard-core bosons, with the usual kinetic energy `∫ |∇φ|²` (the gradient exists off
  the null collision set) plus interaction `w`.
* `Q_mulA`, `ip_mulA`, `dens_mulA`, `gsE_hc`, `liebF_hc`: the Girardeau map preserves energies,
  norms, densities, ground-state energies and the Lieb functional.
* `isGS_hc_iff`: ground states correspond.
* `hk_hardcore_line`, `lieb_hardcore_line`, `gs_unique_hardcore`: **Hohenberg–Kohn, Lieb and
  ground-state uniqueness for hard-core bosons**, for any continuous symmetric interaction.
* `tonks_girardeau`: **the Tonks–Girardeau gas.** Without further interaction, `A · det φ_j(x_i)`
  built from the `N` lowest orbitals is a hard-core ground state, `|A det| = |det|`, and its
  density is the free-fermion density `Σ_j φ_j²`.
* `exists_unique_gs_hardcore`, `nrep_hardcore`, `liebF_hc_ne_top`: existence (cosine class), and
  `N`-representability of `N g²`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box

variable {n : ℕ}

/-! ### Girardeau's sign -/

/-- The Vandermonde product `∏_{i<j} (x_j - x_i)`, as a determinant. -/
noncomputable def vdm (x : Cfg n) : ℝ := (Matrix.vandermonde x).det

/-- Girardeau's sign `A(x) = sign ∏_{i<j} (x_j - x_i)`. -/
noncomputable def gA (x : Cfg n) : ℝ := Real.sign (vdm x)

lemma vdm_ne_zero_iff {x : Cfg n} : vdm x ≠ 0 ↔ Function.Injective x :=
  Matrix.det_vandermonde_ne_zero_iff

lemma continuous_vdm : Continuous (vdm (n := n)) := by
  unfold vdm
  exact Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).pow _)

lemma vdm_pm (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : vdm (pm σ x) = sgn σ * vdm x := by
  have : Matrix.vandermonde (pm σ x) = (Matrix.vandermonde x).submatrix σ id := rfl
  rw [vdm, this, Matrix.det_permute, vdm, sgn]

lemma sgn_eq_or (σ : Equiv.Perm (Fin (n + 1))) : sgn σ = 1 ∨ sgn σ = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [sgn, h]

lemma gA_pm (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : gA (pm σ x) = sgn σ * gA x := by
  rw [gA, gA, vdm_pm]
  rcases sgn_eq_or σ with h | h <;> simp [h, Real.sign_neg]

lemma gA_eq_zero {x : Cfg n} (hx : ¬ Function.Injective x) : gA x = 0 := by
  rw [gA, show vdm x = 0 by by_contra h; exact hx (vdm_ne_zero_iff.1 h), Real.sign_zero]

lemma gA_mul_self {x : Cfg n} (hx : Function.Injective x) : gA x * gA x = 1 := by
  rcases Real.sign_apply_eq_of_ne_zero _ (vdm_ne_zero_iff.2 hx) with h | h <;>
    simp [gA, h]

lemma abs_gA_le (x : Cfg n) : |gA x| ≤ 1 := by
  rcases Real.sign_apply_eq (vdm x) with h | h | h <;> simp [gA, h]

/-- Away from collisions, `A` is locally constant. -/
lemma gA_eventually {x : Cfg n} (hx : Function.Injective x) : ∀ᶠ y in 𝓝 x, gA y = gA x := by
  have h0 := vdm_ne_zero_iff.2 hx
  rcases h0.lt_or_gt with h | h
  · filter_upwards [continuous_vdm.continuousAt.eventually (gt_mem_nhds h)] with y hy
    simp [gA, Real.sign_of_neg hy, Real.sign_of_neg h]
  · filter_upwards [continuous_vdm.continuousAt.eventually (lt_mem_nhds h)] with y hy
    simp [gA, Real.sign_of_pos hy, Real.sign_of_pos h]

/-- Almost every configuration has no collision. -/
lemma ae_injective : ∀ᵐ x ∂μN n, Function.Injective x := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (mu_collision (n := n))] with x hx
  exact Far.injective le_rfl (not_not.1 hx)

/-! ### The Girardeau map -/

/-- Multiplication by Girardeau's sign. -/
noncomputable def mulA : (Cfg n → ℝ) →ₗ[ℝ] (Cfg n → ℝ) where
  toFun ψ := fun x => gA x * ψ x
  map_add' a b := by funext x; simp [mul_add]
  map_smul' r a := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma mulA_apply (ψ : Cfg n → ℝ) (x : Cfg n) : mulA ψ x = gA x * ψ x := rfl

lemma DomF_collision {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) {x : Cfg n} (hx : ¬ Function.Injective x) :
    ψ x = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, x i = x j ∧ i ≠ j := by
    by_contra h; push Not at h; exact hx fun i j hij => by_contra fun hne => hne (h i j hij)
  exact eq_zero_of_collision hψ hne hij

/-- `A² ψ φ = ψ φ` pointwise when `ψ` is fermionic. -/
lemma mulA_mul_mulA {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) (φ : Cfg n → ℝ) (x : Cfg n) :
    mulA ψ x * mulA φ x = ψ x * φ x := by
  by_cases hx : Function.Injective x
  · rw [mulA_apply, mulA_apply, show gA x * ψ x * (gA x * φ x) = (gA x * gA x) * (ψ x * φ x) by
      ring, gA_mul_self hx, one_mul]
  · simp [mulA_apply, gA_eq_zero hx, DomF_collision hψ hx]

lemma mulA_mulA {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) : mulA (mulA ψ) = ψ := by
  funext x
  have := mulA_mul_mulA hψ (fun _ => 1) x
  by_cases hx : Function.Injective x
  · rw [mulA_apply, mulA_apply, ← mul_assoc, gA_mul_self hx, one_mul]
  · simp [mulA_apply, gA_eq_zero hx, DomF_collision hψ hx]

lemma sq_mulA {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) (x : Cfg n) : mulA ψ x ^ 2 = ψ x ^ 2 := by
  rw [sq, sq, mulA_mul_mulA hψ]

/-- Off collisions, the partial derivatives of `A ψ` are `A` times those of `ψ`. -/
lemma dk_mulA {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) {x : Cfg n} (hx : Function.Injective x)
    (k : Fin (n + 1)) : dk k (mulA ψ) x = gA x * dk k ψ x := by
  have he : (mulA ψ : Cfg n → ℝ) =ᶠ[𝓝 x] fun y => gA x * ψ y := by
    filter_upwards [gA_eventually hx] with y hy
    rw [mulA_apply, hy]
  simp only [dk, he.fderiv_eq, fderiv_const_mul ((diffF hψ) x), FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]

/-! ### The hard-core domain -/

/-- Hard-core bosonic states: Girardeau images of fermionic `C²` states. -/
noncomputable def DomHC (n : ℕ) : Submodule ℝ (Cfg n → ℝ) := (DomF n).map mulA

lemma mulA_mem {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) : mulA ψ ∈ DomHC n := ⟨ψ, hψ, rfl⟩

lemma mulA_mem_DomF {φ : Cfg n → ℝ} (hφ : φ ∈ DomHC n) : mulA φ ∈ DomF n := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  rwa [mulA_mulA hψ]

lemma eq_mulA {φ : Cfg n → ℝ} (hφ : φ ∈ DomHC n) : φ = mulA (mulA φ) := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  rw [mulA_mulA hψ]

/-- **Intrinsic description of the hard-core domain**: `φ` vanishes at every collision and `A φ`
is a fermionic `C²` state. -/
theorem mem_DomHC_iff {φ : Cfg n → ℝ} :
    φ ∈ DomHC n ↔ mulA φ ∈ DomF n ∧ ∀ x, ¬ Function.Injective x → φ x = 0 := by
  constructor
  · intro hφ
    refine ⟨mulA_mem_DomF hφ, fun x hx => ?_⟩
    obtain ⟨ψ, -, rfl⟩ := hφ
    rw [mulA_apply, gA_eq_zero hx, zero_mul]
  · rintro ⟨h, hz⟩
    refine ⟨mulA φ, h, funext fun x => ?_⟩
    by_cases hx : Function.Injective x
    · change gA x * (gA x * φ x) = φ x
      rw [← mul_assoc, gA_mul_self hx, one_mul]
    · change gA x * (gA x * φ x) = φ x
      rw [hz x hx, mul_zero, mul_zero]

/-- Hard-core states are symmetric. -/
lemma DomHC_pm {φ : Cfg n → ℝ} (hφ : φ ∈ DomHC n) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    φ (pm σ x) = φ x := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  rw [mulA_apply, mulA_apply, gA_pm, anti hψ, show sgn σ * gA x * (sgn σ * ψ x) =
    (sgn σ * sgn σ) * (gA x * ψ x) by ring, sgn_mul_self, one_mul]

/-- Hard-core states vanish on the walls. -/
lemma DomHC_wall {φ : Cfg n → ℝ} (hφ : φ ∈ DomHC n) (x : Cfg n) (k : Fin (n + 1))
    (hk : x k = 0 ∨ x k = 1) : φ x = 0 := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  rw [mulA_apply, hψ.2.2 x k hk, mul_zero]

/-! ### The hard-core setting -/

section setting

variable {w : Cfg n → ℝ} {hw : Continuous w}

lemma h0N_mulA {ψ φ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) (hφ : φ ∈ DomF n) :
    h0N n w (mulA ψ) (mulA φ) = h0N n w ψ φ := by
  unfold h0N
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [ae_injective] with x hx
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dk_mulA hψ hx, dk_mulA hφ hx, show gA x * dk k ψ x * (gA x * dk k φ x) =
      (gA x * gA x) * (dk k ψ x * dk k φ x) by ring, gA_mul_self hx, one_mul]
  · simp only [mulA_mul_mulA hψ]

variable (n w hw) in
/-- **Hard-core bosons** on `[0, 1]` with interaction `w`: symmetric states vanishing at contact,
with energy `∫ |∇φ|² + ∫ w φ²` (the gradient exists off the null collision set). -/
noncomputable def settingHC : Setting (μN n) Pot where
  D := DomHC n
  h0 := h0N n w
  h0_add a ha b hb c hc := by
    obtain ⟨a, ha, rfl⟩ := ha; obtain ⟨b, hb, rfl⟩ := hb; obtain ⟨c, hc, rfl⟩ := hc
    rw [← map_add, h0N_mulA ((DomF n).add_mem ha hb) hc, h0N_mulA ha hc, h0N_mulA hb hc]
    exact (setting .fer n w hw).h0_add a ha b hb c hc
  h0_smul r a ha c hc := by
    obtain ⟨a, ha, rfl⟩ := ha; obtain ⟨c, hc, rfl⟩ := hc
    rw [← map_smul, h0N_mulA ((DomF n).smul_mem r ha) hc, h0N_mulA ha hc]
    exact (setting .fer n w hw).h0_smul r a ha c hc
  h0_symm a ha c hc := by
    obtain ⟨a, ha, rfl⟩ := ha; obtain ⟨c, hc, rfl⟩ := hc
    rw [h0N_mulA ha hc, h0N_mulA hc ha]
    exact (setting .fer n w hw).h0_symm a ha c hc
  L := LN n
  int_L v a b ha hb := by
    obtain ⟨a, ha, rfl⟩ := ha; obtain ⟨b, hb, rfl⟩ := hb
    simp only [mulA_mul_mulA ha]
    exact (setting .fer n w hw).int_L v a b ha hb
  int_sq a b ha hb := by
    obtain ⟨a, ha, rfl⟩ := ha; obtain ⟨b, hb, rfl⟩ := hb
    simp only [mulA_mul_mulA ha]
    exact (setting .fer n w hw).int_sq a b ha hb

/-- Hard-core bosons with no further interaction: the Tonks–Girardeau gas. -/
noncomputable abbrev freeHC (n : ℕ) : Setting (μN n) Pot :=
  settingHC n (fun _ => 0) continuous_const

/-! ### The Girardeau map preserves everything -/

variable {ψ φ : Cfg n → ℝ}

lemma ip_mulA (hψ : ψ ∈ DomF n) : ip (μ := μN n) (mulA ψ) (mulA φ) = ip (μ := μN n) ψ φ := by
  simp only [ip, mulA_mul_mulA hψ]

lemma pf_mulA (hψ : ψ ∈ DomF n) (v : Pot) :
    pf (settingHC n w hw) v (mulA ψ) (mulA φ) = pf (setting .fer n w hw) v ψ φ := by
  simp only [pf, mulA_mul_mulA hψ]; rfl

lemma dens_mulA (hψ : ψ ∈ DomF n) :
    dens (settingHC n w hw) (mulA ψ) = dens (setting .fer n w hw) ψ :=
  funext fun v => pf_mulA hψ v

lemma h0_mulA (hψ : ψ ∈ DomF n) (hφ : φ ∈ DomF n) :
    (settingHC n w hw).h0 (mulA ψ) (mulA φ) = (setting .fer n w hw).h0 ψ φ :=
  h0N_mulA hψ hφ

lemma Q_mulA (hψ : ψ ∈ DomF n) (v : Pot) :
    Q (settingHC n w hw) v (mulA ψ) = Q (setting .fer n w hw) v ψ := by
  rw [Q, Q, h0_mulA hψ hψ, pf_mulA hψ]

/-- **Ground states correspond** under the Girardeau map. -/
theorem isGS_mulA_iff (hψ : ψ ∈ DomF n) (v : Pot) :
    IsGS (settingHC n w hw) v (mulA ψ) ↔ IsGS (setting .fer n w hw) v ψ := by
  constructor
  · rintro ⟨-, hpos, hmin⟩
    rw [ip_mulA hψ] at hpos
    refine ⟨hψ, hpos, fun χ hχ => ?_⟩
    have := hmin (mulA χ) (mulA_mem hχ)
    rwa [Q_mulA hψ, Q_mulA hχ, ip_mulA hψ, ip_mulA hχ] at this
  · rintro ⟨-, hpos, hmin⟩
    refine ⟨mulA_mem hψ, by rwa [ip_mulA hψ], fun χ hχ => ?_⟩
    obtain ⟨χ, hχ, rfl⟩ := hχ
    rw [Q_mulA hψ, Q_mulA hχ, ip_mulA hψ, ip_mulA hχ]
    exact hmin χ hχ

theorem isGS_hc_iff {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomHC n) (v : Pot) :
    IsGS (settingHC n w hw) v Φ ↔ IsGS (setting .fer n w hw) v (mulA Φ) := by
  conv_lhs => rw [eq_mulA hΦ]
  exact isGS_mulA_iff (mulA_mem_DomF hΦ) v

lemma mulA_mem_Nst (hψ : ψ ∈ Nst (setting .fer n w hw)) : mulA ψ ∈ Nst (settingHC n w hw) :=
  ⟨mulA_mem hψ.1, by rw [ip_mulA hψ.1]; exact hψ.2⟩

lemma mulA_mem_Nst_F {Φ : Cfg n → ℝ} (hΦ : Φ ∈ Nst (settingHC n w hw)) :
    mulA Φ ∈ Nst (setting .fer n w hw) := by
  refine ⟨mulA_mem_DomF hΦ.1, ?_⟩
  have := hΦ.2
  rwa [eq_mulA hΦ.1, ip_mulA (mulA_mem_DomF hΦ.1)] at this

/-- The ground-state energies agree. -/
theorem gsE_hc (v : Pot) : gsE (settingHC n w hw) v = gsE (setting .fer n w hw) v := by
  refine le_antisymm (le_iInf₂ fun ψ hψ => ?_) (le_iInf₂ fun Φ hΦ => ?_)
  · rw [← Q_mulA hψ.1]
    exact iInf₂_le _ (mulA_mem_Nst hψ)
  · rw [eq_mulA hΦ.1, Q_mulA (mulA_mem_DomF hΦ.1)]
    exact iInf₂_le _ (mulA_mem_Nst_F hΦ)

/-- **The Lieb functionals of hard-core bosons and of fermions coincide.** -/
theorem liebF_hc (ρ : Pot → ℝ) : liebF (settingHC n w hw) ρ = liebF (setting .fer n w hw) ρ := by
  simp only [liebF, gsE_hc]

lemma isNGS_hc_iff {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomHC n) (v : Pot) :
    IsNGS (settingHC n w hw) v Φ ↔ IsNGS (setting .fer n w hw) v (mulA Φ) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨mulA_mem_Nst_F h1, fun χ hχ => ?_⟩
    have := h2 _ (mulA_mem_Nst hχ)
    rwa [eq_mulA hΦ, Q_mulA (mulA_mem_DomF hΦ), Q_mulA hχ.1] at this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun χ hχ => ?_⟩
    · have := mulA_mem_Nst h1; rwa [← eq_mulA hΦ] at this
    · rw [eq_mulA hΦ, eq_mulA hχ.1, Q_mulA (mulA_mem_DomF hΦ), Q_mulA (mulA_mem_DomF hχ.1)]
      exact h2 _ (mulA_mem_Nst_F hχ)

end setting

/-! ### Hohenberg–Kohn, Lieb and uniqueness for hard-core bosons -/

section theorems

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot}

/-- **Hohenberg–Kohn for `N` hard-core bosons on a line.** With any continuous interaction
invariant under relabelling, ground states of `v` and `v'` with the same one-body density force
`v - v'` to be constant. -/
theorem hk_hardcore_line (hws : ∀ σ x, w (pm σ x) = w x) {v' : Pot} {Φ Φ' : Cfg n → ℝ}
    (hΦ : IsGS (settingHC n w hw) v Φ) (hΦ' : IsGS (settingHC n w hw) v' Φ')
    (hρ : ∀ t ∈ Ioo (0 : ℝ) 1, ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 =
      ∫ y in Cube' n, Φ' (Fin.cons t y) ^ 2) : ∃ k : ℝ, v - v' = k • one := by
  refine hk_interacting_fermions_line hws ((isGS_hc_iff hΦ.1 v).1 hΦ)
    ((isGS_hc_iff hΦ'.1 v').1 hΦ') fun t ht => ?_
  have e : ∀ {Ψ : Cfg n → ℝ}, Ψ ∈ DomHC n → ∀ y : Fin n → ℝ,
      mulA Ψ (Fin.cons t y) ^ 2 = Ψ (Fin.cons t y) ^ 2 := fun hΨ y => by
    conv_rhs => rw [eq_mulA hΨ]
    rw [sq_mulA (mulA_mem_DomF hΨ)]
  simp only [e hΦ.1, e hΦ'.1]
  exact hρ t ht

/-- **Ground states of hard-core bosons are unique** up to a constant factor. -/
theorem gs_unique_hardcore (hws : ∀ σ x, w (pm σ x) = w x) {Φ Ψ : Cfg n → ℝ}
    (hΦ : IsGS (settingHC n w hw) v Φ) (hΨ : IsGS (settingHC n w hw) v Ψ) :
    ∃ c : ℝ, ∀ x ∈ CubeC n, Φ x = c * Ψ x := by
  obtain ⟨c, hc⟩ := gs_unique_line hws ((isGS_hc_iff hΦ.1 v).1 hΦ) ((isGS_hc_iff hΨ.1 v).1 hΨ)
  refine ⟨c, fun x hx => ?_⟩
  rw [eq_mulA hΦ.1, eq_mulA hΨ.1, mulA_apply (mulA Φ), mulA_apply (mulA Ψ), hc x hx]
  ring

/-- **The Lieb functional for `N` hard-core bosons on a line**: at the density of a normalised
ground state `ψ` of `v` it equals `⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient, and every other
subgradient `-v'` has `v - v'` constant. -/
theorem lieb_hardcore_line (hws : ∀ σ x, w (pm σ x) = w x) {ψ : Cfg n → ℝ}
    (hψ : IsNGS (settingHC n w hw) v ψ) :
    liebF (settingHC n w hw) (dens (settingHC n w hw) ψ) =
        (((settingHC n w hw).h0 ψ ψ : ℝ) : EReal) ∧
      (∀ ρ : Pot → ℝ, (((settingHC n w hw).h0 ψ ψ + dens (settingHC n w hw) ψ v - ρ v : ℝ) :
        EReal) ≤ liebF (settingHC n w hw) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ,
        (((settingHC n w hw).h0 ψ ψ + dens (settingHC n w hw) ψ v' - ρ v' : ℝ) : EReal) ≤
          liebF (settingHC n w hw) ρ) →
        ∃ k : ℝ, v - v' = k • one := by
  refine ⟨liebF_of_isNGS hψ, subgrad_of_isNGS hψ, fun v' hsub => ?_⟩
  have hD := hψ.1.1
  have hF := (isNGS_hc_iff hD v).1 hψ
  have hF' := mulA_mem_DomF hD
  refine (lieb_line (τ := .fer) hws hF).2.2 v' fun ρ => ?_
  have := hsub ρ
  rwa [liebF_hc, eq_mulA hD, h0_mulA hF' hF', dens_mulA hF'] at this

/-- Existence and uniqueness of the hard-core ground state, for potentials in the cosine class. -/
theorem exists_unique_gs_hardcore {β : (Fin (n + 1) → ℕ) → ℝ} (hws : ∀ σ x, w (pm σ x) = w x)
    (hβ : ∀ s : ℕ, Summable fun l => |β l| * (1 + (Sine.sz l : ℝ)) ^ s)
    (hV : ∀ x ∈ CubeC n, LN n v x + w x = ∑' l, β l * Sine.cosM l x) :
    ∃ Φ, IsGS (settingHC n w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 ∧
      ∀ Ψ, IsGS (settingHC n w hw) v Ψ → ∃ c : ℝ, ∀ x ∈ CubeC n, Ψ x = c * Φ x := by
  obtain ⟨Φ, hΦ, hip⟩ := Sine.exists_isGS_line (τ := .fer) (hw := hw) hws hβ hV
  have hG := (isGS_mulA_iff hΦ.1 v).2 hΦ
  exact ⟨mulA Φ, hG, by rw [ip_mulA hΦ.1]; exact hip,
    fun Ψ hΨ => gs_unique_hardcore hws hΨ hG⟩

/-- **`N`-representability for hard-core bosons**: every density `N g²` comes from a normalised
hard-core state. -/
theorem nrep_hardcore {g : ℝ → ℝ} (hg : g ∈ Box.Dom) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) :
    ∃ ψ ∈ Nst (settingHC n w hw),
      ∀ v, dens (settingHC n w hw) ψ v = ∫ t, ext v t * ((n + 1) * g t ^ 2) ∂μ1 := by
  obtain ⟨ψ, hψ, hd⟩ := nrep_fer (n := n) (w := w) (hw := hw) hg hnorm
  exact ⟨mulA ψ, mulA_mem_Nst hψ, fun v => by rw [dens_mulA hψ.1, hd]⟩

theorem liebF_hc_ne_top {g : ℝ → ℝ} (hg : g ∈ Box.Dom) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) :
    liebF (settingHC n w hw) (rhoG n g) ≠ ⊤ := by
  rw [liebF_hc]; exact liebF_ne_top hg hnorm

end theorems

/-! ### The Tonks–Girardeau gas -/

/-- **The Tonks–Girardeau gas.** For every continuous potential `v` there are `N` orthonormal
`C²` orbitals `φ_j` (the lowest eigenfunctions of `-d²/dx² + v`) such that `A · det φ_j(x_i)` is a
ground state of `N` hard-core bosons with no further interaction. Its modulus is `|det φ_j(x_i)|`,
its norm is `N!`, and its density is `N!` times the free-fermion density `Σ_j φ_j²`. Every other
ground state is a multiple of it. -/
theorem tonks_girardeau (v : Pot) : ∃ φ : Fin (n + 1) → ℝ → ℝ, (∀ j, φ j ∈ Box.Dom) ∧
    (∀ a b, ∫ t, φ a t * φ b t ∂μ1 = if a = b then 1 else 0) ∧
    IsGS (freeHC n) v (mulA (slater φ)) ∧
    (∀ x, |mulA (slater φ) x| = |slater φ x|) ∧
    ip (μ := μN n) (mulA (slater φ)) (mulA (slater φ)) = (Nat.factorial (n + 1) : ℝ) ∧
    (∀ u, dens (freeHC n) (mulA (slater φ)) u =
      (Nat.factorial (n + 1) : ℝ) * ∫ t, ext u t * ∑ j, φ j t ^ 2 ∂μ1) ∧
    ∀ Ψ, IsGS (freeHC n) v Ψ → ∃ c : ℝ, ∀ x ∈ CubeC n, Ψ x = c * mulA (slater φ) x := by
  obtain ⟨φ, lam, Λ, hφ, hode, hon, hle, hbound⟩ := Spectral.exists_orbitals v n
  have hnorm : ∀ j, ∫ x, φ j x * φ j x ∂μ1 = 1 := fun j => by rw [hon]; simp
  have hD := slater_mem hφ
  have hQ := Q_slater hφ hode
  have hpos := ip_slater_pos hφ hon
  have hlow : ∀ φ' ∈ DomF n, (∑ j, lam j) * ip (μ := μN n) φ' φ' ≤ Q (freeS .fer n) v φ' :=
    fun φ' h => lower_bound_fer h v hφ hbound hle hnorm
  have hGS : IsGS (freeS .fer n) v (slater φ) := ⟨hD, hpos, fun φ' hφ' => by
    rw [hQ]; nlinarith [mul_le_mul_of_nonneg_left (hlow φ' hφ') hpos.le]⟩
  have hG := (isGS_mulA_iff hD v).2 hGS
  have hc : ∀ j, Continuous (φ j) := fun j => (hφ j).1.continuous
  refine ⟨φ, hφ, hon, hG, fun x => ?_, ?_, fun u => ?_, fun Ψ hΨ => gs_unique_hardcore
    (fun _ _ => rfl) hΨ hG⟩
  · rw [← sq_eq_sq_iff_abs_eq_abs, sq_mulA hD]
  · rw [ip_mulA hD]; exact integral_slater_sq hc hon
  · rw [dens_mulA hD]; exact integral_LN_slater hc hon u

end DFT.Continuum.Line
