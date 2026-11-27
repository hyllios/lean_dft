/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Scope.Functionals

/-!
# Qubit examples (stage 3)

After Wang–Liebert–Penz–Schilling, §IV.B, §IV.C and Appendix A.

**Bloch sphere and ball.** One qubit with the observables `X, Y, Z` and any `H₀`:
* `blochScope_Bp`: the pure range is the unit sphere; `blochScope_Be`: the ensemble range is the
  closed unit ball; `blochScope_Bp_ne_Be`: so `B_p` need not be convex.

**Double qubit.** Two qubits with the observables `X₁, Y₁, Z₁, Z₂` and `H₀ = X₁X₂ + Y₁Y₂`
(basis `↑↑, ↑↓, ↓↑, ↓↓`):
* `qq_Fp`: `F_p(0, 0, z, 0) = -√(1 - z²)` for `0 < |z| < 1` (Appendix A, eq. (A.12));
* `qq_Fe_le`: `F_e(0, 0, ½, 0) ≤ -√2`, by the mixture `¼|↑↑⟩⟨↑↑| + ¾|Ψ₂⟩⟨Ψ₂|`;
* `qq_Fe_lt_Fp` (Proposition A.1): `F_e < F_p` at `ρ = (0, 0, ½, 0)`;
* `qq_mem_interior`: this `ρ` is an interior point of `B_e` (which contains the product of the Bloch
  ball and `[-1, 1]`, `qq_mem_Be`).
-/

namespace DFT.Scope

open Matrix Complex Set

/-! ### One qubit -/

/-- The Pauli matrices `X, Y, Z`. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -I; I, 0], !![1, 0; 0, -1]]

lemma isHermitian_pauli (i : Fin 3) : (pauli i).IsHermitian := by
  fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;> simp [pauli])

/-- **One qubit as a scope** (Bloch sphere). -/
noncomputable def blochScope (H0 : Matrix (Fin 2) (Fin 2) ℂ) (hH0 : H0.IsHermitian) :
    Scope ℂ (Fin 2) (Fin 3) where
  H0 := H0
  B := pauli
  isHermitian_H0 := hH0
  isHermitian_B := isHermitian_pauli

/-- The Bloch vector of `φ = (a, b)`: `(2 Re(ā b), 2 Im(ā b), |a|² - |b|²)`. -/
def blochVec (φ : Fin 2 → ℂ) : Fin 3 → ℝ :=
  ![2 * ((φ 0).re * (φ 1).re + (φ 0).im * (φ 1).im),
    2 * ((φ 0).re * (φ 1).im - (φ 0).im * (φ 1).re),
    (φ 0).re ^ 2 + (φ 0).im ^ 2 - (φ 1).re ^ 2 - (φ 1).im ^ 2]

lemma expv_pauli (φ : Fin 2 → ℂ) (i : Fin 3) : expv (pauli i) φ = blochVec φ i := by
  fin_cases i <;>
  · simp [expv, pauli, blochVec, dotProduct, mulVec, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im]
    ring

variable {H0 : Matrix (Fin 2) (Fin 2) ℂ} (hH0 : H0.IsHermitian)

lemma blochScope_densPure (φ : Fin 2 → ℂ) : (blochScope H0 hH0).densPure φ = blochVec φ :=
  funext fun i => expv_pauli φ i

lemma unit_two_iff {φ : Fin 2 → ℂ} :
    φ ∈ unitVecs ↔ (φ 0).re ^ 2 + (φ 0).im ^ 2 + (φ 1).re ^ 2 + (φ 1).im ^ 2 = 1 := by
  rw [unitVecs, mem_ofPred_eq, star_dotProduct_self_eq, Fin.sum_univ_two, ← RCLike.ofReal_one,
    RCLike.ofReal_inj]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  constructor <;> intro h <;> linarith

/-- Every point of the unit sphere is the Bloch vector of a unit vector. -/
lemma exists_blochVec {r : Fin 3 → ℝ} (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1) :
    ∃ φ ∈ (unitVecs : Set (Fin 2 → ℂ)), blochVec φ = r := by
  by_cases hz : r 2 = -1
  · have hx : r 0 = 0 := by nlinarith [sq_nonneg (r 0), sq_nonneg (r 1)]
    have hy : r 1 = 0 := by nlinarith [sq_nonneg (r 0), sq_nonneg (r 1)]
    refine ⟨![0, 1], unit_two_iff.2 (by simp), ?_⟩
    funext i; fin_cases i <;> simp [blochVec, hx, hy, hz]
  · have hz1 : 0 < 1 + r 2 := by
      have : r 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (r 0), sq_nonneg (r 1)]
      have : -1 ≤ r 2 := by nlinarith
      exact lt_of_le_of_ne (by linarith) (fun h => hz (by linarith))
    set t := Real.sqrt (2 * (1 + r 2))
    have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
    have ht2 : t ^ 2 = 2 * (1 + r 2) := Real.sq_sqrt (by linarith)
    refine ⟨![((t / 2 : ℝ) : ℂ), ⟨r 0 / t, r 1 / t⟩], unit_two_iff.2 ?_, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ofReal_re, ofReal_im]
      field_simp
      nlinarith
    · funext i
      fin_cases i
      · simp [blochVec]; field_simp
      · simp [blochVec]; field_simp
      · simp [blochVec]; field_simp; nlinarith

/-- The closed unit ball is the convex hull of the unit sphere (in coordinates). -/
lemma ball_subset_of_sphere_subset {K : Set (Fin 3 → ℝ)} (hK : Convex ℝ K)
    (hS : ∀ r : Fin 3 → ℝ, r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1 → r ∈ K) {r : Fin 3 → ℝ}
    (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) : r ∈ K := by
  set n := Real.sqrt (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2)
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hn1 : n ≤ 1 := Real.sqrt_le_one.2 hr
  have hn2 : n ^ 2 = r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 := Real.sq_sqrt (by positivity)
  by_cases hn : n = 0
  · have h0 : r = 0 := by
      have : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 0 := by rw [← hn2, hn]; ring
      funext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (r 0), sq_nonneg (r 1),
        sq_nonneg (r 2)]
    have h1 := hS ![1, 0, 0] (by simp)
    have h2 := hS ![-1, 0, 0] (by simp)
    have := hK h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert this using 1
    rw [h0]; funext i; fin_cases i <;> simp
  · have hnpos : 0 < n := lt_of_le_of_ne hn0 (Ne.symm hn)
    set u : Fin 3 → ℝ := n⁻¹ • r
    have hu : ∀ s : ℝ, s ^ 2 = 1 → s • u ∈ K := fun s hs => hS _ (by
      simp only [u, Pi.smul_apply, smul_eq_mul]
      field_simp
      nlinarith)
    have := hK (hu 1 (by norm_num)) (hu (-1) (by norm_num))
      (by linarith : (0 : ℝ) ≤ (1 + n) / 2) (by linarith : (0 : ℝ) ≤ (1 - n) / 2) (by ring)
    convert this using 1
    funext i
    simp only [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- **The pure range of a qubit is the Bloch sphere.** -/
theorem blochScope_Bp :
    (blochScope H0 hH0).Bp = {r | r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1} := by
  ext r
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    have h := unit_two_iff.1 hφ
    rw [blochScope_densPure]
    show (blochVec φ 0) ^ 2 + (blochVec φ 1) ^ 2 + (blochVec φ 2) ^ 2 = 1
    simp only [blochVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have : ((φ 0).re ^ 2 + (φ 0).im ^ 2 + (φ 1).re ^ 2 + (φ 1).im ^ 2) ^ 2 = 1 := by rw [h]; ring
    nlinarith [this]
  · intro hr
    obtain ⟨φ, hφ, he⟩ := exists_blochVec hr
    exact ⟨φ, hφ, by rw [blochScope_densPure, he]⟩

/-- **The ensemble range of a qubit is the Bloch ball.** -/
theorem blochScope_Be :
    (blochScope H0 hH0).Be = {r | r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1} := by
  have hconv : Convex ℝ {r : Fin 3 → ℝ | r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1} := by
    intro r hr r' hr' a b ha hb hab
    simp only [mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hr hr' ⊢
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg ha hb, sq_nonneg (r 0 - r' 0), sq_nonneg (r 1 - r' 1),
      sq_nonneg (r 2 - r' 2)]
  refine le_antisymm ?_ fun r hr => ?_
  · rw [Be_eq_convexHull_Bp, blochScope_Bp]
    exact convexHull_min (fun r hr => le_of_eq hr) hconv
  · exact ball_subset_of_sphere_subset (blochScope H0 hH0).convex_Be
      (fun r hr => (blochScope H0 hH0).Bp_subset_Be (by rw [blochScope_Bp]; exact hr)) hr

/-- The pure range of a qubit is not convex: `B_p ≠ B_e`. -/
theorem blochScope_Bp_ne_Be : (blochScope H0 hH0).Bp ≠ (blochScope H0 hH0).Be := by
  intro h
  have h0 : (0 : Fin 3 → ℝ) ∈ (blochScope H0 hH0).Be := by rw [blochScope_Be]; simp
  rw [← h, blochScope_Bp] at h0
  simp at h0

/-! ### Two qubits -/

/-- The observables `X₁, Y₁, Z₁, Z₂` on two qubits (basis `↑↑, ↑↓, ↓↑, ↓↓`). -/
def qqObs : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
    !![0, 0, -I, 0; 0, 0, 0, -I; I, 0, 0, 0; 0, I, 0, 0],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1],
    !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]]

/-- `H₀ = X₁X₂ + Y₁Y₂ = 2(|↑↓⟩⟨↓↑| + |↓↑⟩⟨↑↓|)`. -/
def qqH0 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, 0, 2, 0; 0, 2, 0, 0; 0, 0, 0, 0]

/-- **The double-qubit scope** of Appendix A. -/
noncomputable def qqScope : Scope ℂ (Fin 4) (Fin 4) where
  H0 := qqH0
  B := qqObs
  isHermitian_H0 := by ext a b; fin_cases a <;> fin_cases b <;> simp [qqH0]
  isHermitian_B i := by
    fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;> simp [qqObs])

/-- The density of `ψ = (a, b, c, d)`: with `w = ā c + b̄ d`,
`(2 Re w, 2 Im w, |a|² + |b|² - |c|² - |d|², |a|² - |b|² + |c|² - |d|²)`. -/
def qqDens (ψ : Fin 4 → ℂ) : Fin 4 → ℝ :=
  ![2 * ((ψ 0).re * (ψ 2).re + (ψ 0).im * (ψ 2).im + (ψ 1).re * (ψ 3).re + (ψ 1).im * (ψ 3).im),
    2 * ((ψ 0).re * (ψ 2).im - (ψ 0).im * (ψ 2).re + (ψ 1).re * (ψ 3).im - (ψ 1).im * (ψ 3).re),
    Complex.normSq (ψ 0) + Complex.normSq (ψ 1) - Complex.normSq (ψ 2) - Complex.normSq (ψ 3),
    Complex.normSq (ψ 0) - Complex.normSq (ψ 1) + Complex.normSq (ψ 2) - Complex.normSq (ψ 3)]

lemma qqScope_densPure (ψ : Fin 4 → ℂ) : qqScope.densPure ψ = qqDens ψ := by
  funext i
  fin_cases i <;>
  · simp [densPure, qqScope, qqObs, qqDens, expv, dotProduct, mulVec, Fin.sum_univ_four,
      Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    ring

lemma qqScope_expv_H0 (ψ : Fin 4 → ℂ) :
    expv qqScope.H0 ψ = 4 * ((ψ 1).re * (ψ 2).re + (ψ 1).im * (ψ 2).im) := by
  simp [qqScope, qqH0, expv, dotProduct, mulVec, Fin.sum_univ_four, Complex.mul_re]
  ring

lemma unit_four_iff {ψ : Fin 4 → ℂ} : ψ ∈ unitVecs ↔
    Complex.normSq (ψ 0) + Complex.normSq (ψ 1) + Complex.normSq (ψ 2) + Complex.normSq (ψ 3)
      = 1 := by
  rw [unitVecs, mem_ofPred_eq, star_dotProduct_self_eq, Fin.sum_univ_four, ← RCLike.ofReal_one,
    RCLike.ofReal_inj]
  simp only [Complex.sq_norm]

/-- The pure-state lower bound at `(0, 0, z, 0)`, `z ≠ 0`: `⟨H₀⟩ ≥ -√(1 - z²)`. -/
lemma qq_lower {z : ℝ} (hz0 : z ≠ 0) {ψ : Fin 4 → ℂ} (hψ : ψ ∈ unitVecs)
    (hρ : qqScope.densPure ψ = ![0, 0, z, 0]) : -Real.sqrt (1 - z ^ 2) ≤ expv qqScope.H0 ψ := by
  rw [qqScope_densPure] at hρ
  have h1 := unit_four_iff.1 hψ
  have hX := congrFun hρ 0
  have hY := congrFun hρ 1
  have hZ1 := congrFun hρ 2
  have hZ2 := congrFun hρ 3
  simp only [qqDens, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hX hY hZ1 hZ2
  -- `ā c + b̄ d = 0`, hence `|a|²|c|² = |b|²|d|²`
  have hw : starRingEnd ℂ (ψ 0) * ψ 2 = -(starRingEnd ℂ (ψ 1) * ψ 3) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith
  have hAC : Complex.normSq (ψ 0) * Complex.normSq (ψ 2) =
      Complex.normSq (ψ 1) * Complex.normSq (ψ 3) := by
    have := congrArg Complex.normSq hw
    simpa [Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_neg] using this
  set A := Complex.normSq (ψ 0)
  set B := Complex.normSq (ψ 1)
  set C := Complex.normSq (ψ 2)
  set D := Complex.normSq (ψ 3)
  have hB : B = (1 + z) / 4 := by
    have hA : A = (1 + z) / 2 - B := by linarith
    have hC : C = B - z / 2 := by linarith
    have hD : D = 1 / 2 - B := by linarith
    rw [hA, hC, hD] at hAC
    have : z * (B - (1 + z) / 4) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hz0
    linarith
  have hC : C = (1 - z) / 4 := by linarith
  -- `Re(b̄ c)² ≤ |b|²|c|²`
  have hre : ((ψ 1).re * (ψ 2).re + (ψ 1).im * (ψ 2).im) ^ 2 ≤ B * C := by
    simp only [B, C, Complex.normSq_apply]
    nlinarith [sq_nonneg ((ψ 1).re * (ψ 2).im - (ψ 1).im * (ψ 2).re)]
  rw [qqScope_expv_H0]
  have hsq : (4 * ((ψ 1).re * (ψ 2).re + (ψ 1).im * (ψ 2).im)) ^ 2 ≤ 1 - z ^ 2 := by
    rw [hB, hC] at hre; nlinarith
  have := Real.abs_le_sqrt hsq
  linarith [neg_abs_le (4 * ((ψ 1).re * (ψ 2).re + (ψ 1).im * (ψ 2).im))]

/-- **The pure functional of the double qubit** at `(0, 0, z, 0)`, `0 < |z| < 1`:
`F_p = -√(1 - z²)` (Appendix A, eq. (A.12)). -/
theorem qq_Fp {z : ℝ} (hz0 : z ≠ 0) (hz : |z| < 1) :
    qqScope.Fp ![0, 0, z, 0] = ((-Real.sqrt (1 - z ^ 2) : ℝ) : EReal) := by
  have hz1 : 0 ≤ 1 + z := by linarith [neg_abs_le z]
  have hz2 : 0 ≤ 1 - z := by linarith [le_abs_self z]
  refine le_antisymm ?_ (le_iInf₂ fun ψ hψ => EReal.coe_le_coe_iff.2 (qq_lower hz0 hψ.1 hψ.2))
  -- the minimiser `(√(1+z), -√(1+z), √(1-z), √(1-z)) / 2`
  set p := Real.sqrt (1 + z)
  set q := Real.sqrt (1 - z)
  have hp : p ^ 2 = 1 + z := Real.sq_sqrt hz1
  have hq : q ^ 2 = 1 - z := Real.sq_sqrt hz2
  set ψ : Fin 4 → ℂ := ![((p / 2 : ℝ) : ℂ), ((-p / 2 : ℝ) : ℂ), ((q / 2 : ℝ) : ℂ), ((q / 2 : ℝ) : ℂ)]
  have hψ : ψ ∈ unitVecs := by
    rw [unit_four_iff]
    simp [ψ, Complex.normSq_apply]
    nlinarith
  have hρ : qqScope.densPure ψ = ![0, 0, z, 0] := by
    rw [qqScope_densPure]
    funext i
    fin_cases i <;> simp [qqDens, ψ, Complex.normSq_apply] <;> nlinarith
  refine (iInf₂_le ψ ⟨hψ, hρ⟩).trans (le_of_eq ?_)
  rw [qqScope_expv_H0, EReal.coe_eq_coe_iff]
  have hpq : p * q = Real.sqrt (1 - z ^ 2) := by
    rw [← Real.sqrt_mul hz1]; congr 1; ring
  simp [ψ]
  nlinarith [hpq]

/-- `F_e(0, 0, ½, 0) ≤ -√2`, by the mixture `¼|↑↑⟩⟨↑↑| + ¾|Ψ₂⟩⟨Ψ₂|`,
`Ψ₂ = -√(2/3)|↑↓⟩ + (1/√3)|↓↑⟩`. -/
theorem qq_Fe_le : qqScope.Fe ![0, 0, 1 / 2, 0] ≤ ((-Real.sqrt 2 : ℝ) : EReal) := by
  set s := Real.sqrt 6
  set t := Real.sqrt 3
  have hs : s ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have ht : t ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hst : s * t = 3 * Real.sqrt 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpos : 0 ≤ s * t := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hpos' : 0 ≤ 3 * Real.sqrt 2 := by positivity
    nlinarith [sq_nonneg (s * t - 3 * Real.sqrt 2), sq_nonneg (s * t + 3 * Real.sqrt 2)]
  set ψ1 : Fin 4 → ℂ := ![1, 0, 0, 0]
  set ψ2 : Fin 4 → ℂ := ![0, ((-s / 3 : ℝ) : ℂ), ((t / 3 : ℝ) : ℂ), 0]
  have h1 : ψ1 ∈ unitVecs := by rw [unit_four_iff]; simp [ψ1]
  have h2 : ψ2 ∈ unitVecs := by
    rw [unit_four_iff]; simp [ψ2, Complex.normSq_apply]; nlinarith
  set Γ := (1 / 4 : ℝ) • vecMulVec ψ1 (star ψ1) + (3 / 4 : ℝ) • vecMulVec ψ2 (star ψ2)
  have hΓ : Γ ∈ densMats := convex_densMats (pure_mem_densMats h1) (pure_mem_densMats h2)
    (by norm_num) (by norm_num) (by norm_num)
  have hdens : qqScope.dens Γ = ![0, 0, 1 / 2, 0] := by
    rw [qqScope.dens_add, qqScope.dens_smul, qqScope.dens_smul, qqScope.dens_pure,
      qqScope.dens_pure, qqScope_densPure, qqScope_densPure]
    funext i
    fin_cases i <;> simp [qqDens, ψ1, ψ2, Complex.normSq_apply] <;> nlinarith
  have h := qqScope.Fe_le hΓ
  rw [hdens] at h
  refine h.trans (EReal.coe_le_coe_iff.2 (le_of_eq ?_))
  simp only [Γ, trv_add_right, trv_smul_right, trv_pure, qqScope_expv_H0]
  simp [ψ1, ψ2]
  nlinarith [hst]

/-- **Proposition A.1**: for the double qubit, `F_e < F_p` at `ρ = (0, 0, ½, 0)`. -/
theorem qq_Fe_lt_Fp : qqScope.Fe ![0, 0, 1 / 2, 0] < qqScope.Fp ![0, 0, 1 / 2, 0] := by
  refine qq_Fe_le.trans_lt ?_
  rw [qq_Fp (by norm_num) (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num),
    EReal.coe_lt_coe_iff, neg_lt_neg_iff]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- `(r, ±1)` is a pure density of the double qubit for every unit Bloch vector `r`. -/
lemma qq_mem_Bp {r : Fin 3 → ℝ} (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : ![r 0, r 1, r 2, s] ∈ qqScope.Bp := by
  obtain ⟨φ, hφ, he⟩ := exists_blochVec hr
  have hφ1 := unit_two_iff.1 hφ
  have he' := fun i => congrFun he i
  simp only [blochVec] at he'
  have e0 := he' 0
  have e1 := he' 1
  have e2 := he' 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at e0 e1 e2
  rcases hs with rfl | rfl
  · refine ⟨![φ 0, 0, φ 1, 0], ?_, ?_⟩
    · rw [unit_four_iff]; simp [Complex.normSq_apply]; linarith
    · rw [qqScope_densPure]
      funext i
      fin_cases i <;> simp [qqDens, Complex.normSq_apply] <;> linarith
  · refine ⟨![0, φ 0, 0, φ 1], ?_, ?_⟩
    · rw [unit_four_iff]; simp [Complex.normSq_apply]; linarith
    · rw [qqScope_densPure]
      funext i
      fin_cases i <;> simp [qqDens, Complex.normSq_apply] <;> linarith

/-- `(r, s)` with `|r| ≤ 1`, `|s| ≤ 1` is an ensemble density of the double qubit. -/
lemma qq_mem_Be {x : Fin 4 → ℝ} (hr : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤ 1) (hs : |x 3| ≤ 1) :
    x ∈ qqScope.Be := by
  have hslice : ∀ s : ℝ, (s = 1 ∨ s = -1) → ![x 0, x 1, x 2, s] ∈ qqScope.Be := fun s hs' => by
    have hK : Convex ℝ {r : Fin 3 → ℝ | ![r 0, r 1, r 2, s] ∈ qqScope.Be} := by
      intro r hr r' hr' a b ha hb hab
      have := qqScope.convex_Be hr hr' ha hb hab
      show (![(a • r + b • r') 0, (a • r + b • r') 1, (a • r + b • r') 2, s] : Fin 4 → ℝ) ∈
        qqScope.Be
      convert this using 1
      funext i
      fin_cases i <;> simp
      rw [← add_mul, hab, one_mul]
    have := ball_subset_of_sphere_subset hK (fun r hr => qqScope.Bp_subset_Be (qq_mem_Bp hr hs'))
      (r := ![x 0, x 1, x 2]) (by simpa using hr)
    simpa using this
  have h3 := abs_le.1 hs
  have := qqScope.convex_Be (hslice 1 (Or.inl rfl)) (hslice (-1) (Or.inr rfl))
    (by linarith : (0 : ℝ) ≤ (1 + x 3) / 2) (by linarith : (0 : ℝ) ≤ (1 - x 3) / 2) (by ring)
  convert this using 1
  funext i
  fin_cases i <;> simp <;> ring

/-- `(0, 0, ½, 0)` is an interior point of the ensemble range of the double qubit. -/
theorem qq_mem_interior : (![0, 0, 1 / 2, 0] : Fin 4 → ℝ) ∈ interior qqScope.Be := by
  set N : Set (Fin 4 → ℝ) := {x | x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 < 1} ∩ {x | |x 3| < 1}
  have hN : IsOpen N :=
    (isOpen_lt (by fun_prop) continuous_const).inter (isOpen_lt (by fun_prop) continuous_const)
  refine interior_maximal (fun x (hx : x ∈ N) => qq_mem_Be (le_of_lt hx.1) (le_of_lt hx.2)) hN
    ⟨?_, ?_⟩
  · simp only [mem_ofPred_eq]; norm_num
  · simp only [mem_ofPred_eq]; norm_num

end DFT.Scope
