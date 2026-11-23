/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.Bridge.FrustratedSquareCertificates
import DFT.Lattice.Generic.ShortestPathSign

/-!
# Generic Hohenberg–Kohn on the square with one negative bond

`N` spinless fermions (`0 < N < 4`) on the 4-cycle `sqG` with symmetric hopping, `t₀₁ < 0` and
`t₁₂, t₂₃, t₃₀ > 0` (arbitrary magnitudes), and any configuration-diagonal interaction. This sign
pattern is not gauge-equivalent to a common sign (`cycle4_no_common_sign`) and is not
`ShortestPathSigned` (`square_not_shortestPathSigned`), so `generic_hk_lattice_fermions_w` and
`generic_hk_lattice_fermions_shortest` do not apply. The proof goes through the strong-potential
limit instead: for every configuration the leading coefficient of the free Krylov determinant along
a suitable direction is, up to sign, an explicit polynomial in the four magnitudes with coefficients
of one sign (`Bridge.FrustratedSquareCertificates`), and this gives (H*) for every interaction
(`krylovPoly_ne_zero_of_table`).

* `hopM_sqHop`, `H0Fw_sqHop`: symmetric hopping on the square is `sqHop t₀₁ t₁₂ t₂₃ t₃₀`;
* `hstar_frustrated_square`, `generic_hk_frustrated_square`, `exists_poly_frustrated_square`,
  `dimH_nonUVDens_frustrated_square` and its primed form;
* with orbital sign changes, every sign pattern with nonzero hopping: `square_gauge`,
  `generic_hk_square_of_ne_zero`, `exists_poly_square_of_ne_zero`,
  `dimH_nonUVDens_square_of_ne_zero`.
-/

namespace DFT

open Matrix MvPolynomial

namespace Bridge.Square

/-- On the edges of the square, symmetric hopping is `sqHop t₀₁ t₁₂ t₂₃ t₃₀`. -/
lemma hopM_sqHop {t : Fin 4 → Fin 4 → ℝ} (htsym : ∀ a b, t a b = t b a) :
    hopM sqG t = hopM sqG (sqHop (t 0 1) (t 1 2) (t 2 3) (t 3 0)) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [hopM, sqG, sqHop, htsym 1 0, htsym 3 0, htsym 2 1, htsym 3 2]

lemma H0Fw_sqHop {N : ℕ} {t : Fin 4 → Fin 4 → ℝ} (htsym : ∀ a b, t a b = t b a)
    (Vint : Conf 4 N → ℝ) :
    H0Fw sqG t Vint = H0Fw sqG (sqHop (t 0 1) (t 1 2) (t 2 3) (t 3 0)) Vint := by
  unfold H0Fw
  rw [hopM_sqHop htsym]

/-- **(H*) on the square with one negative bond.** For `0 < N < 4`, symmetric hopping with
`t₀₁ < 0` and `t₁₂, t₂₃, t₃₀ > 0`, every configuration `c` and every configuration-diagonal
interaction, the Krylov polynomial of `c` is nonzero. -/
theorem hstar_frustrated_square {N : ℕ} {t : Fin 4 → Fin 4 → ℝ} (htsym : ∀ a b, t a b = t b a)
    (h01 : t 0 1 < 0) (h12 : 0 < t 1 2) (h23 : 0 < t 2 3) (h30 : 0 < t 3 0) (hN0 : 0 < N)
    (hN4 : N < 4) (c : Conf 4 N) (Vint : Conf 4 N → ℝ) :
    krylovPoly (H0Fw sqG t Vint) occF c (fun j => (Fintype.equivFin (Conf 4 N) j : ℕ)) ≠ 0 := by
  rw [H0Fw_sqHop htsym]
  have hp : 0 < -t 0 1 := neg_pos.mpr h01
  interval_cases N
  · simpa using hstar_sqHop_one hp h12 h23 h30 c Vint
  · simpa using hstar_sqHop_two hp h12 h23 h30 c Vint
  · simpa using hstar_sqHop_three hp h12 h23 h30 c Vint

/-- **Generic Hohenberg–Kohn theorem on the square with one negative bond.** For `0 < N < 4`,
symmetric hopping with `t₀₁ < 0` and `t₁₂, t₂₃, t₃₀ > 0` and any configuration-diagonal
interaction, the potentials with a non-uniquely v-representable ground state lie in a closed,
nowhere dense, Lebesgue-null set. -/
theorem generic_hk_frustrated_square {N : ℕ} {t : Fin 4 → Fin 4 → ℝ}
    (htsym : ∀ a b, t a b = t b a) (h01 : t 0 1 < 0) (h12 : 0 < t 1 2) (h23 : 0 < t 2 3)
    (h30 : 0 < t 3 0) (hN0 : 0 < N) (hN4 : N < 4) (Vint : Conf 4 N → ℝ) :
    ∃ Z : Set (Fin 4 → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUV (H0Fw sqG t Vint) occF v} ⊆ Z :=
  generic_hk_ae (H0Fw_isSymm sqG htsym Vint) (rigid_occF hN0 hN4) _
    (fun c => hstar_frustrated_square htsym h01 h12 h23 h30 hN0 hN4 c Vint)

/-- A nonzero polynomial vanishing on the exceptional potentials of the square with one negative
bond. -/
theorem exists_poly_frustrated_square {N : ℕ} {t : Fin 4 → Fin 4 → ℝ}
    (htsym : ∀ a b, t a b = t b a) (h01 : t 0 1 < 0) (h12 : 0 < t 1 2) (h23 : 0 < t 2 3)
    (h30 : 0 < t 3 0) (hN0 : 0 < N) (hN4 : N < 4) (Vint : Conf 4 N → ℝ) :
    ∃ P : MvPolynomial (Fin 4) ℝ, P ≠ 0 ∧
      ∀ v, NonUV (H0Fw sqG t Vint) (occF : Fin 4 → Conf 4 N → ℝ) v → eval v P = 0 := by
  classical
  set ord : Conf 4 N → ℕ := fun j => (Fintype.equivFin (Conf 4 N) j : ℕ)
  refine ⟨∏ c, krylovPoly (H0Fw sqG t Vint) occF c ord,
    Finset.prod_ne_zero_iff.mpr
      (fun c _ => hstar_frustrated_square htsym h01 h12 h23 h30 hN0 hN4 c Vint),
    fun v hv => ?_⟩
  obtain ⟨c, hc⟩ :=
    nonUV_imp_krylov_zero (H0Fw_isSymm sqG htsym Vint) (rigid_occF hN0 hN4) hv ord
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) hc

/-- **Non-uv densities on the square with one negative bond**: Hausdorff dimension at most
`4 − 3 = 1`. -/
theorem dimH_nonUVDens_frustrated_square {N : ℕ} {t : Fin 4 → Fin 4 → ℝ}
    (htsym : ∀ a b, t a b = t b a) (h01 : t 0 1 < 0) (h12 : 0 < t 1 2) (h23 : 0 < t 2 3)
    (h30 : 0 < t 3 0) (hN0 : 0 < N) (hN4 : N < 4) (Vint : Conf 4 N → ℝ) :
    dimH (NonUVDens (H0Fw sqG t Vint) (occF : Fin 4 → Conf 4 N → ℝ)) ≤ (4 : ENNReal) - 3 := by
  obtain ⟨P, hP, hPZ⟩ := exists_poly_frustrated_square htsym h01 h12 h23 h30 hN0 hN4 Vint
  simpa using dimH_nonUVDens_le (H0Fw_isSymm sqG htsym Vint) ⟨N, sum_occF_eq⟩ hP hPZ

/-- `dimH_nonUVDens_frustrated_square` in the form `dimH + 3 ≤ 4` (when there are non-uv densities
at all). -/
theorem dimH_nonUVDens_frustrated_square' {N : ℕ} {t : Fin 4 → Fin 4 → ℝ}
    (htsym : ∀ a b, t a b = t b a) (h01 : t 0 1 < 0) (h12 : 0 < t 1 2) (h23 : 0 < t 2 3)
    (h30 : 0 < t 3 0) (hN0 : 0 < N) (hN4 : N < 4) (Vint : Conf 4 N → ℝ)
    (hne : (NonUVDens (H0Fw sqG t Vint) (occF : Fin 4 → Conf 4 N → ℝ)).Nonempty) :
    dimH (NonUVDens (H0Fw sqG t Vint) (occF : Fin 4 → Conf 4 N → ℝ)) + 3 ≤ 4 := by
  obtain ⟨P, hP, hPZ⟩ := exists_poly_frustrated_square htsym h01 h12 h23 h30 hN0 hN4 Vint
  simpa using dimH_nonUVDens (H0Fw_isSymm sqG htsym Vint) ⟨N, sum_occF_eq⟩ hP hPZ hne

/-! ### Every sign pattern, by orbital sign changes -/

/-- `1` for positive numbers, `-1` otherwise. -/
private noncomputable def sgn1 (x : ℝ) : ℝ := if 0 < x then 1 else -1

private lemma sgn1_mul_self (x : ℝ) : sgn1 x * sgn1 x = 1 := by
  unfold sgn1; split_ifs <;> norm_num

private lemma sgn1_mul_pos {x : ℝ} (hx : x ≠ 0) : 0 < sgn1 x * x := by
  unfold sgn1
  split_ifs with h
  · linarith
  · have : x < 0 := lt_of_le_of_ne (not_lt.mp h) hx
    linarith

/-- **Orbital sign changes on the square.** If `t₁₂, t₂₃, t₃₀ ≠ 0`, signs `σ_i = ±1` make the
bonds `1 2`, `2 3`, `3 0` positive; the bond `0 1` then carries the sign of
`t₀₁ t₁₂ t₂₃ t₃₀` (`gaugeHop_cycle`). -/
theorem square_gauge {t : Fin 4 → Fin 4 → ℝ} (h12 : t 1 2 ≠ 0) (h23 : t 2 3 ≠ 0)
    (h30 : t 3 0 ≠ 0) :
    ∃ σ : Fin 4 → ℝ, (∀ i, σ i * σ i = 1) ∧ 0 < gaugeHop σ t 1 2 ∧ 0 < gaugeHop σ t 2 3 ∧
      0 < gaugeHop σ t 3 0 := by
  refine ⟨![1, sgn1 (t 3 0) * sgn1 (t 2 3) * sgn1 (t 1 2), sgn1 (t 3 0) * sgn1 (t 2 3),
    sgn1 (t 3 0)], fun i => ?_, ?_, ?_, ?_⟩
  · fin_cases i
    · norm_num
    · change sgn1 (t 3 0) * sgn1 (t 2 3) * sgn1 (t 1 2) *
        (sgn1 (t 3 0) * sgn1 (t 2 3) * sgn1 (t 1 2)) = 1
      linear_combination (sgn1 (t 2 3) * sgn1 (t 2 3) * (sgn1 (t 1 2) * sgn1 (t 1 2))) *
          sgn1_mul_self (t 3 0) + sgn1 (t 1 2) * sgn1 (t 1 2) * sgn1_mul_self (t 2 3) +
        sgn1_mul_self (t 1 2)
    · change sgn1 (t 3 0) * sgn1 (t 2 3) * (sgn1 (t 3 0) * sgn1 (t 2 3)) = 1
      linear_combination sgn1 (t 2 3) * sgn1 (t 2 3) * sgn1_mul_self (t 3 0) +
        sgn1_mul_self (t 2 3)
    · exact sgn1_mul_self _
  · have e : gaugeHop ![1, sgn1 (t 3 0) * sgn1 (t 2 3) * sgn1 (t 1 2),
        sgn1 (t 3 0) * sgn1 (t 2 3), sgn1 (t 3 0)] t 1 2 =
        (sgn1 (t 3 0) * sgn1 (t 3 0)) * (sgn1 (t 2 3) * sgn1 (t 2 3)) * (sgn1 (t 1 2) * t 1 2) := by
      simp only [gaugeHop]
      change sgn1 (t 3 0) * sgn1 (t 2 3) * sgn1 (t 1 2) * (sgn1 (t 3 0) * sgn1 (t 2 3)) * t 1 2 = _
      ring
    rw [e, sgn1_mul_self, sgn1_mul_self, one_mul, one_mul]
    exact sgn1_mul_pos h12
  · have e : gaugeHop ![1, sgn1 (t 3 0) * sgn1 (t 2 3) * sgn1 (t 1 2),
        sgn1 (t 3 0) * sgn1 (t 2 3), sgn1 (t 3 0)] t 2 3 =
        (sgn1 (t 3 0) * sgn1 (t 3 0)) * (sgn1 (t 2 3) * t 2 3) := by
      simp only [gaugeHop]
      change sgn1 (t 3 0) * sgn1 (t 2 3) * sgn1 (t 3 0) * t 2 3 = _
      ring
    rw [e, sgn1_mul_self, one_mul]
    exact sgn1_mul_pos h23
  · have e : gaugeHop ![1, sgn1 (t 3 0) * sgn1 (t 2 3) * sgn1 (t 1 2),
        sgn1 (t 3 0) * sgn1 (t 2 3), sgn1 (t 3 0)] t 3 0 = sgn1 (t 3 0) * t 3 0 := by
      simp only [gaugeHop]
      change sgn1 (t 3 0) * 1 * t 3 0 = _
      ring
    rw [e]
    exact sgn1_mul_pos h30

/-- The product of the hopping around the square is gauge invariant. -/
lemma gaugeHop_cycle {σ : Fin 4 → ℝ} (hσ : ∀ i, σ i * σ i = 1) (t : Fin 4 → Fin 4 → ℝ) :
    gaugeHop σ t 0 1 * gaugeHop σ t 1 2 * gaugeHop σ t 2 3 * gaugeHop σ t 3 0 =
      t 0 1 * t 1 2 * t 2 3 * t 3 0 := by
  simp only [gaugeHop]
  linear_combination (t 0 1 * t 1 2 * t 2 3 * t 3 0) *
    ((σ 1 * σ 1) * (σ 2 * σ 2) * (σ 3 * σ 3) * hσ 0 + (σ 2 * σ 2) * (σ 3 * σ 3) * hσ 1 +
      (σ 3 * σ 3) * hσ 2 + hσ 3)

lemma gaugeHop_symm {t : Fin 4 → Fin 4 → ℝ} (htsym : ∀ a b, t a b = t b a) (σ : Fin 4 → ℝ) :
    ∀ a b, gaugeHop σ t a b = gaugeHop σ t b a := by
  intro a b; simp only [gaugeHop]; rw [htsym a b]; ring

/-- In the gauge of `square_gauge`, the sign of the bond `0 1` is that of `t₀₁ t₁₂ t₂₃ t₃₀`. -/
private lemma gauge01_sign {σ : Fin 4 → ℝ} (hσ : ∀ i, σ i * σ i = 1) {t : Fin 4 → Fin 4 → ℝ}
    (g12 : 0 < gaugeHop σ t 1 2) (g23 : 0 < gaugeHop σ t 2 3) (g30 : 0 < gaugeHop σ t 3 0) :
    (t 0 1 * t 1 2 * t 2 3 * t 3 0 < 0 → gaugeHop σ t 0 1 < 0) ∧
      (0 < t 0 1 * t 1 2 * t 2 3 * t 3 0 → 0 < gaugeHop σ t 0 1) := by
  have hc := gaugeHop_cycle hσ t
  have hpos : 0 < gaugeHop σ t 1 2 * gaugeHop σ t 2 3 * gaugeHop σ t 3 0 := by positivity
  have e : gaugeHop σ t 0 1 * (gaugeHop σ t 1 2 * gaugeHop σ t 2 3 * gaugeHop σ t 3 0) =
      t 0 1 * t 1 2 * t 2 3 * t 3 0 := by rw [← hc]; ring
  constructor
  · intro h
    by_contra hge
    have : 0 ≤ gaugeHop σ t 0 1 * (gaugeHop σ t 1 2 * gaugeHop σ t 2 3 * gaugeHop σ t 3 0) :=
      mul_nonneg (not_lt.mp hge) hpos.le
    linarith
  · intro h
    by_contra hle
    have : gaugeHop σ t 0 1 * (gaugeHop σ t 1 2 * gaugeHop σ t 2 3 * gaugeHop σ t 3 0) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hle) hpos.le
    linarith

/-- If the four bonds `0 1`, `1 2`, `2 3`, `3 0` are positive, every bond of the square is. -/
private lemma gauge_bonds_pos {σ : Fin 4 → ℝ} {t : Fin 4 → Fin 4 → ℝ}
    (hgsym : ∀ a b, gaugeHop σ t a b = gaugeHop σ t b a) (g01 : 0 < gaugeHop σ t 0 1)
    (g12 : 0 < gaugeHop σ t 1 2) (g23 : 0 < gaugeHop σ t 2 3) (g30 : 0 < gaugeHop σ t 3 0) :
    ∀ a b, sqG.Adj a b → 0 < 1 * (σ a * σ b * t a b) := by
  have hcases : ∀ a b : Fin 4, sqG.Adj a b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
      (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨
      (a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3) := by decide
  intro a b hab
  rw [one_mul]
  change 0 < gaugeHop σ t a b
  rcases hcases a b hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact g01
  · rw [hgsym]; exact g01
  · exact g12
  · rw [hgsym]; exact g12
  · exact g23
  · rw [hgsym]; exact g23
  · exact g30
  · rw [hgsym]; exact g30

/-- **Generic Hohenberg–Kohn theorem on the square for every nonzero hopping.** For `0 < N < 4`,
symmetric hopping that is nonzero on the four bonds, of any signs, and any configuration-diagonal
interaction, the potentials with a non-uniquely v-representable ground state lie in a closed,
nowhere dense, Lebesgue-null set. (Even number of negative bonds: gauge to a common sign;
odd number: gauge to `generic_hk_frustrated_square`.) -/
theorem generic_hk_square_of_ne_zero {N : ℕ} {t : Fin 4 → Fin 4 → ℝ}
    (htsym : ∀ a b, t a b = t b a) (h01 : t 0 1 ≠ 0) (h12 : t 1 2 ≠ 0) (h23 : t 2 3 ≠ 0)
    (h30 : t 3 0 ≠ 0) (hN0 : 0 < N) (hN4 : N < 4) (Vint : Conf 4 N → ℝ) :
    ∃ Z : Set (Fin 4 → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUV (H0Fw sqG t Vint) occF v} ⊆ Z := by
  obtain ⟨σ, hσ, g12, g23, g30⟩ := square_gauge h12 h23 h30
  have hprod : t 0 1 * t 1 2 * t 2 3 * t 3 0 ≠ 0 := by positivity
  obtain ⟨hneg, hpos⟩ := gauge01_sign hσ g12 g23 g30
  have hgsym := gaugeHop_symm htsym σ
  rcases lt_or_gt_of_ne hprod with h | h
  · obtain ⟨Z, h1, h2, h3, h4⟩ :=
      generic_hk_frustrated_square hgsym (hneg h) g12 g23 g30 hN0 hN4 Vint
    exact ⟨Z, h1, h2, h3, fun v hv => h4 ((nonUV_H0Fw_gaugeHop sqG hσ t Vint v).mpr hv)⟩
  · have g01 := hpos h
    exact generic_hk_lattice_fermions_gauge sqG_connected htsym hσ (s := 1)
      (gauge_bonds_pos hgsym g01 g12 g23 g30) hN0 hN4 Vint

/-- A nonzero polynomial vanishing on the exceptional potentials of the square, for every nonzero
hopping. -/
theorem exists_poly_square_of_ne_zero {N : ℕ} {t : Fin 4 → Fin 4 → ℝ}
    (htsym : ∀ a b, t a b = t b a) (h01 : t 0 1 ≠ 0) (h12 : t 1 2 ≠ 0) (h23 : t 2 3 ≠ 0)
    (h30 : t 3 0 ≠ 0) (hN0 : 0 < N) (hN4 : N < 4) (Vint : Conf 4 N → ℝ) :
    ∃ P : MvPolynomial (Fin 4) ℝ, P ≠ 0 ∧
      ∀ v, NonUV (H0Fw sqG t Vint) (occF : Fin 4 → Conf 4 N → ℝ) v → eval v P = 0 := by
  obtain ⟨σ, hσ, g12, g23, g30⟩ := square_gauge h12 h23 h30
  have hprod : t 0 1 * t 1 2 * t 2 3 * t 3 0 ≠ 0 := by positivity
  obtain ⟨hneg, hpos⟩ := gauge01_sign hσ g12 g23 g30
  have hgsym := gaugeHop_symm htsym σ
  obtain ⟨P, hP, hPZ⟩ : ∃ P : MvPolynomial (Fin 4) ℝ, P ≠ 0 ∧
      ∀ v, NonUV (H0Fw sqG (gaugeHop σ t) Vint) (occF : Fin 4 → Conf 4 N → ℝ) v →
        eval v P = 0 := by
    rcases lt_or_gt_of_ne hprod with h | h
    · exact exists_poly_frustrated_square hgsym (hneg h) g12 g23 g30 hN0 hN4 Vint
    · have g01 := hpos h
      exact exists_poly_lattice_fermions_w sqG_connected hgsym (s := 1)
        (fun a b hab => gauge_bonds_pos hgsym g01 g12 g23 g30 a b hab) hN0 hN4 Vint
  exact ⟨P, hP, fun v hv => hPZ v ((nonUV_H0Fw_gaugeHop sqG hσ t Vint v).mpr hv)⟩

/-- **Non-uv densities on the square for every nonzero hopping**: Hausdorff dimension at most
`4 − 3 = 1`. -/
theorem dimH_nonUVDens_square_of_ne_zero {N : ℕ} {t : Fin 4 → Fin 4 → ℝ}
    (htsym : ∀ a b, t a b = t b a) (h01 : t 0 1 ≠ 0) (h12 : t 1 2 ≠ 0) (h23 : t 2 3 ≠ 0)
    (h30 : t 3 0 ≠ 0) (hN0 : 0 < N) (hN4 : N < 4) (Vint : Conf 4 N → ℝ) :
    dimH (NonUVDens (H0Fw sqG t Vint) (occF : Fin 4 → Conf 4 N → ℝ)) ≤ (4 : ENNReal) - 3 := by
  obtain ⟨P, hP, hPZ⟩ := exists_poly_square_of_ne_zero htsym h01 h12 h23 h30 hN0 hN4 Vint
  simpa using dimH_nonUVDens_le (H0Fw_isSymm sqG htsym Vint) ⟨N, sum_occF_eq⟩ hP hPZ

end Bridge.Square

end DFT
