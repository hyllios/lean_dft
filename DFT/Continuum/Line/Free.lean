/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Lieb
import DFT.Continuum.Box.Ground

/-!
# Free bosons on a line: ground states exist

For `n + 1` non-interacting bosons on `[0, 1]` with a continuous potential `v`, let `ψ₀` be the
one-particle ground state (energy `E₀`, from `Continuum/Box/Ground`). Then
`Ψ(x) = ψ₀(x₀) ⋯ ψ₀(xₙ)` is an `(n + 1)`-boson ground state, so Hohenberg–Kohn and Lieb's form of it
hold with no assumption at all.

* `Q_slices`: the energy above `(n + 1) E` is a sum over coordinates of one-particle slice
  energies (Fubini along each coordinate); this holds for either statistics.
* `lower_bound_free`: every state has energy at least `(n + 1) E₀`.
* `prodS_isGS`: the product state has energy exactly `(n + 1) E₀`, so it is a ground state.
* `hk_free_bosons_line`: **Hohenberg–Kohn for `N` free bosons on a line, unconditional**: ground
  states exist, and equal densities force the potentials to differ by a constant.
* `lieb_free_bosons_line`: Lieb's form, unconditional.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box

variable {n : ℕ} {τ : Stat}

/-- Particles with no interaction. -/
noncomputable abbrev freeS (τ : Stat) (n : ℕ) : Setting (μN n) Pot :=
  setting τ n (fun _ => 0) continuous_const

/-! ### Slices -/

lemma insertNth_eq_add (k : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    (Fin.insertNth k t y : Cfg n) = Fin.insertNth k (0 : ℝ) y + t • (Pi.single k 1 : Cfg n) := by
  funext i
  refine Fin.succAboveCases k ?_ (fun j => ?_) i
  · simp
  · simp [Fin.insertNth_apply_succAbove, Fin.succAbove_ne]

lemma contDiff_insertNth (k : Fin (n + 1)) (y : Fin n → ℝ) {m : WithTop ℕ∞} :
    ContDiff ℝ m (fun t : ℝ => (Fin.insertNth k t y : Cfg n)) := by
  rw [show (fun t : ℝ => (Fin.insertNth k t y : Cfg n)) =
      fun t => Fin.insertNth k (0 : ℝ) y + t • (Pi.single k 1 : Cfg n) from
    funext fun t => insertNth_eq_add k t y]
  exact contDiff_const.add (contDiff_id.smul contDiff_const)

/-- A slice of a state is a one-particle state. -/
lemma slice_mem {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) (k : Fin (n + 1)) (y : Fin n → ℝ) :
    (fun t => φ (Fin.insertNth k t y)) ∈ Box.Dom :=
  ⟨hφ.1.comp (contDiff_insertNth k y), hφ.2.2 _ k (Or.inl (by simp)),
    hφ.2.2 _ k (Or.inr (by simp))⟩

lemma deriv_slice {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) (k : Fin (n + 1)) (y : Fin n → ℝ)
    (t : ℝ) : deriv (fun s => φ (Fin.insertNth k s y)) t = dk k φ (Fin.insertNth k t y) :=
  (hasDerivAt_insertNth (diffF hφ) k y t).deriv

variable (v : Pot)

/-- The slice energy density along coordinate `k`: `(∂ₖφ)² + (v(xₖ) - E) φ²`. -/
noncomputable def sk (E : ℝ) (k : Fin (n + 1)) (φ : Cfg n → ℝ) (x : Cfg n) : ℝ :=
  dk k φ x ^ 2 + Wof v E (x k) * φ x ^ 2

lemma continuous_sk (E : ℝ) (k : Fin (n + 1)) {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) :
    Continuous (sk v E k φ) :=
  ((cont_dk hφ k).pow 2).add (((continuous_Wof v E).comp (continuous_apply k)).mul
    (hφ.1.continuous.pow 2))

/-- **The energy splits into slice energies**: `Q(φ) - (n+1) E ‖φ‖² = Σₖ ∫ sₖ`. -/
lemma Q_slices (E : ℝ) {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) :
    Q (freeS τ n) v φ - (n + 1) * E * ip (μ := μN n) φ φ = ∑ k, ∫ x, sk v E k φ x ∂μN n := by
  have hc := hφ.1.continuous
  have i1 := integrableN (cont_kin hφ hφ)
  have i2 := integrableN ((continuous_LN v).mul (hc.mul hc))
  have i3 := integrableN (hc.mul hc)
  rw [← integral_finsetSum _ fun k _ => integrableN (continuous_sk v E k hφ)]
  have hpt : (fun x => ∑ k, sk v E k φ x) = fun x =>
      ((∑ k, dk k φ x * dk k φ x) + LN n v x * (φ x * φ x)) - (n + 1) * E * (φ x * φ x) := by
    funext x
    simp only [sk, Wof, LN, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_add_distrib,
      ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring_nf
  rw [hpt, integral_sub (f := fun x => (∑ k, dk k φ x * dk k φ x) + LN n v x * (φ x * φ x))
    (g := fun x => (n + 1) * E * (φ x * φ x)) (i1.add i2) (i3.const_mul _),
    integral_add (f := fun x => ∑ k, dk k φ x * dk k φ x)
      (g := fun x => LN n v x * (φ x * φ x)) i1 i2, integral_const_mul]
  simp only [Q, freeS, setting, h0N, pf, ip, zero_mul, integral_zero, add_zero]

/-- A slice energy is a one-particle energy above `E`. -/
lemma slice_energy (E : ℝ) (k : Fin (n + 1)) {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) :
    ∫ x, sk v E k φ x ∂μN n = ∫ y in Cube' n,
      (Q Box.setting v (fun t => φ (Fin.insertNth k t y)) -
        E * ip (μ := μ1) (fun t => φ (Fin.insertNth k t y))
          (fun t => φ (Fin.insertNth k t y))) := by
  rw [integral_cube_insertNth (continuous_sk v E k hφ) k]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) fun y _ => ?_
  rw [Q_sub_eq v E (slice_mem hφ k y)]
  simp only [sk, deriv_slice hφ k y, Fin.insertNth_apply_same]

/-- **Lower bound.** Every state has energy at least `(n + 1) E₀`. -/
theorem lower_bound_free {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) :
    (n + 1) * Estar v * ip (μ := μN n) φ φ ≤ Q (freeS τ n) v φ := by
  obtain ⟨-, -, -, -, -, hlow⟩ := gs_data v
  have h := Q_slices v (Estar v) hφ
  have hs : 0 ≤ ∑ k, ∫ x, sk v (Estar v) k φ x ∂μN n := Finset.sum_nonneg fun k _ => by
    rw [slice_energy v _ k hφ]
    refine integral_nonneg fun y => ?_
    have := hlow _ (slice_mem hφ k y)
    show (0 : ℝ) ≤ Q Box.setting v (fun t => φ (Fin.insertNth k t y)) -
      Estar v * ip (μ := μ1) (fun t => φ (Fin.insertNth k t y)) (fun t => φ (Fin.insertNth k t y))
    linarith
  linarith

/-! ### The product state -/

/-- The product state `ψ(x₀) ⋯ ψ(xₙ)`. -/
noncomputable def prodS (ψ : ℝ → ℝ) (x : Cfg n) : ℝ := ∏ k, ψ (x k)

lemma prodS_mem {ψ : ℝ → ℝ} (hψ : ψ ∈ Box.Dom) : prodS (n := n) ψ ∈ DomB n :=
  ⟨contDiff_prod fun k _ => hψ.1.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) k).contDiff,
    fun σ x => by
      simp only [prodS, pm_apply, ch_bos, one_mul]
      exact Equiv.prod_comp σ (fun k => ψ (x k)),
    fun x k hk => Finset.prod_eq_zero (Finset.mem_univ k) (by
      rcases hk with h | h <;> rw [h]
      exacts [hψ.2.1, hψ.2.2])⟩

lemma prodS_insertNth (ψ : ℝ → ℝ) (k : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    prodS ψ (Fin.insertNth k t y : Cfg n) = ψ t * ∏ j, ψ (y j) := by
  simp only [prodS]
  rw [Fin.prod_univ_succAbove _ k]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

lemma volume_cube : volume (Cube n) = 1 := by
  rw [Real.volume_pi_Ioo]; simp

/-- A continuous function positive on the cube has positive integral. -/
lemma integral_pos_of_pos {F : Cfg n → ℝ} (hF : Continuous F) (hpos : ∀ x ∈ Cube n, 0 < F x) :
    0 < ∫ x, F x ∂μN n := by
  rw [integral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_cube).2 (ae_of_all _ fun x hx => (hpos x hx).le))
    (integrableN hF)]
  rw [Measure.restrict_apply' measurableSet_cube]
  have : Function.support F ∩ Cube n = Cube n :=
    inter_eq_right.2 fun x hx => (hpos x hx).ne'
  rw [this, volume_cube]
  exact one_pos

/-- **The product of one-particle ground states is an `(n + 1)`-boson ground state**, with energy
`(n + 1) E₀`. -/
theorem prodS_isGS : ∃ Ψ, IsGS (freeS .bos n) v Ψ ∧
    Q (freeS .bos n) v Ψ = (n + 1) * Estar v * ip (μ := μN n) Ψ Ψ := by
  obtain ⟨ψ, hD, hψeq, hQ, -, -⟩ := gs_data v
  set E := Estar v
  have hΨ : prodS (n := n) ψ ∈ DomB n := prodS_mem hD
  have hψpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < ψ t := fun t ht => by
    rw [hψeq t ⟨by linarith [ht.1], by linarith [ht.2]⟩]; exact star_pos v t ht
  have h1d : ∫ x, (deriv ψ x ^ 2 + Wof v E x * ψ x ^ 2) ∂μ1 = 0 := by
    rw [← Q_sub_eq v E hD, hQ]; ring
  have hslices : ∀ k, ∫ x, sk v E k (prodS ψ) x ∂μN n = 0 := by
    intro k
    rw [slice_energy v E k hΨ]
    refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
    set c := ∏ j, ψ (y j)
    have hs : (fun t => prodS ψ (Fin.insertNth k t y : Cfg n)) = fun t => ψ t * c := by
      funext t; exact prodS_insertNth ψ k t y
    have hsm : (fun t => ψ t * c) ∈ Box.Dom := hs ▸ slice_mem hΨ k y
    simp only [Pi.zero_apply]
    rw [hs, Q_sub_eq v E hsm]
    have : ∀ x, deriv (fun t => ψ t * c) x ^ 2 + Wof v E x * (ψ x * c) ^ 2 =
        c ^ 2 * (deriv ψ x ^ 2 + Wof v E x * ψ x ^ 2) := by
      intro x; rw [deriv_mul_const (diff_of_mem hD x)]; ring
    simp only [this, integral_const_mul, h1d, mul_zero]
  have hQΨ : Q (freeS .bos n) v (prodS ψ) =
      (n + 1) * E * ip (μ := μN n) (prodS ψ) (prodS ψ) := by
    have := Q_slices v E hΨ
    simp only [hslices, Finset.sum_const_zero] at this
    linarith
  have hposΨ : 0 < ip (μ := μN n) (prodS (n := n) ψ) (prodS ψ) :=
    integral_pos_of_pos (hΨ.1.continuous.mul hΨ.1.continuous) fun x hx =>
      mul_self_pos.2 (Finset.prod_ne_zero_iff.2 fun k _ => (hψpos _ (hx k (mem_univ _))).ne')
  refine ⟨prodS ψ, ⟨hΨ, hposΨ, fun φ hφ => ?_⟩, hQΨ⟩
  rw [hQΨ]
  nlinarith [mul_le_mul_of_nonneg_left (lower_bound_free v hφ) hposΨ.le]

/-! ### Unconditional theorems -/

/-- **Hohenberg–Kohn for `N` free bosons on a line, unconditional.** Every continuous potential has
an `(n + 1)`-boson ground state, and ground states of two continuous potentials with the same
one-body density force the potentials to differ by a constant. -/
theorem hk_free_bosons_line (v v' : Pot) :
    (∃ Φ, IsGS (freeS .bos n) v Φ) ∧ ∀ Φ Φ', IsGS (freeS .bos n) v Φ →
      IsGS (freeS .bos n) v' Φ' →
      (∀ t ∈ Ioo (0 : ℝ) 1, ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 =
        ∫ y in Cube' n, Φ' (Fin.cons t y) ^ 2) → ∃ k : ℝ, v - v' = k • one :=
  ⟨(prodS_isGS v).imp fun _ h => h.1, fun _ _ h h' hρ =>
    hk_interacting_bosons_line (fun _ _ => rfl) h h' hρ⟩

/-- **Normalised ground states exist** for `N` free bosons. -/
theorem exists_isNGS_free : ∃ ψ, IsNGS (freeS .bos n) v ψ := by
  obtain ⟨Ψ, hΨ, hQΨ⟩ := prodS_isGS (n := n) v
  obtain ⟨hD, hpos, -⟩ := hΨ
  set c := (Real.sqrt (ip (μ := μN n) Ψ Ψ))⁻¹
  have hs : 0 < Real.sqrt (ip (μ := μN n) Ψ Ψ) := Real.sqrt_pos.mpr hpos
  have hc2 : c * c * ip (μ := μN n) Ψ Ψ = 1 := by
    simp only [c]; field_simp; rw [Real.sq_sqrt hpos.le]
  have hcD : c • Ψ ∈ DomB n := (DomB n).smul_mem c hD
  refine ⟨c • Ψ, ⟨hcD, by rw [ip_smul_self, hc2]⟩, fun φ hφ => ?_⟩
  rw [Q_smul_self (S := freeS .bos n) v c hD, hQΨ]
  have := lower_bound_free (τ := .bos) v hφ.1
  rw [hφ.2, mul_one] at this
  calc c * c * ((n + 1) * Estar v * ip (μ := μN n) Ψ Ψ) =
        (n + 1) * Estar v * (c * c * ip (μ := μN n) Ψ Ψ) := by ring
    _ = (n + 1) * Estar v := by rw [hc2, mul_one]
    _ ≤ Q (freeS .bos n) v φ := this

/-- **The Lieb functional for `N` free bosons on a line, unconditional.** For every continuous
potential `v` there is a normalised ground state `ψ`; at its density the Lieb functional equals the
kinetic energy of `ψ`, `-v` is a subgradient, and every other subgradient `-v'` has `v - v'`
constant. -/
theorem lieb_free_bosons_line : ∃ ψ, IsNGS (freeS .bos n) v ψ ∧
    liebF (freeS .bos n) (dens (freeS .bos n) ψ) = (((freeS .bos n).h0 ψ ψ : ℝ) : EReal) ∧
    (∀ ρ : Pot → ℝ, (((freeS .bos n).h0 ψ ψ + dens (freeS .bos n) ψ v - ρ v : ℝ) : EReal) ≤
      liebF (freeS .bos n) ρ) ∧
    ∀ v' : Pot, (∀ ρ : Pot → ℝ,
      (((freeS .bos n).h0 ψ ψ + dens (freeS .bos n) ψ v' - ρ v' : ℝ) : EReal) ≤
        liebF (freeS .bos n) ρ) → ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨ψ, hψ⟩ := exists_isNGS_free (n := n) v
  exact ⟨ψ, hψ, lieb_line (fun _ _ => rfl) hψ⟩

end DFT.Continuum.Line
