/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.Generic.NullSets
import DFT.Lattice.HK.Gap

/-!
# Generic avoidance of a polynomial condition on gapped ground states

Let `H(θ)` be a symmetric matrix whose entries are real polynomials in parameters `θ ∈ ℝ^V`, and let
`F` be a polynomial in the amplitudes of a state with `F(ψ) = 0 ⇒ F(a ψ) = 0` (for instance a
homogeneous one). The parameters at which some gapped, normalised ground state satisfies `F(ψ) = 0`
form the **bad set**. The theorem `generic_avoid` says that the bad set lies in a closed, nowhere
dense, Lebesgue-null set, provided a single polynomial `R_c` is not identically zero.

The ground state depends on `θ` only through an eigenvalue, which is not polynomial. The eigenvalue
is eliminated in two steps.
* **Adjugate.** For `B = H - E` with `E` the ground-state energy, `B · adj B = det B = 0`, so every
  column of `adj B` lies in the kernel of `B`. A gapped ground state spans that kernel, so the
  column is a multiple of `ψ` (`adj_col_eq_smul`), and `F` vanishes on it.
* **Matrix polynomial.** Let `q_c(E) = F(adj(H - E)_{·c})`, a polynomial in `E` with coefficients
  polynomial in `θ` (`colPoly`). Then `q_c(H) ψ = q_c(E₀) ψ = 0` (`aeval_mulVec_of_eigen`), so
  `R_c = det q_c(H)` vanishes (`eval_elimPoly_eq_zero`). Up to sign `R_c` is the resultant of
  `q_c` and the characteristic polynomial, `Π_j q_c(E_j)` over all eigenvalues.

`R_c ≠ 0` plays the role of hypothesis (H*) in the generic Hohenberg–Kohn theorem. It holds as soon
as, at one parameter point, every eigenvalue is simple and every eigenvector `φ` has `φ_c ≠ 0` and
`F(φ) ≠ 0`.

* `evalMat`, `shiftMat`, `colPoly`, `elimPoly`, `BadSet`.
* `aeval_mulVec_of_eigen`, `eval_elimPoly`, `eval_colPoly_map`, `adj_col_eq_smul`.
* `eval_elimPoly_eq_zero`: **the elimination polynomial vanishes on the bad set**.
* `generic_avoid`: **the bad set is closed-nowhere-dense-null when `R_c ≠ 0`**.
-/

namespace DFT

section

open Matrix Polynomial

variable {C V : Type*} [Fintype C] [DecidableEq C]

/-- The matrix `H(θ)`. -/
noncomputable def evalMat (HP : Matrix C C (MvPolynomial V ℝ)) (θ : V → ℝ) : Matrix C C ℝ :=
  HP.map (MvPolynomial.eval θ)

/-- `H - E`, with `E` the polynomial variable. -/
noncomputable def shiftMat (HP : Matrix C C (MvPolynomial V ℝ)) :
    Matrix C C (MvPolynomial V ℝ)[X] :=
  HP.map Polynomial.C - (Polynomial.X : (MvPolynomial V ℝ)[X]) • 1

/-- `q_c(E) = F(adj(H - E)_{·c})`. -/
noncomputable def colPoly (HP : Matrix C C (MvPolynomial V ℝ)) (F : MvPolynomial C ℝ) (c : C) :
    (MvPolynomial V ℝ)[X] :=
  MvPolynomial.aeval (fun s => adjugate (shiftMat HP) s c) F

/-- The elimination polynomial `R_c = det q_c(H)`. -/
noncomputable def elimPoly (HP : Matrix C C (MvPolynomial V ℝ)) (F : MvPolynomial C ℝ) (c : C) :
    MvPolynomial V ℝ :=
  (Polynomial.aeval HP (colPoly HP F c)).det

/-- Parameters at which some gapped, normalised ground state satisfies `F(ψ) = 0`. -/
def BadSet (HP : Matrix C C (MvPolynomial V ℝ)) (F : MvPolynomial C ℝ) : Set (V → ℝ) :=
  {θ | ∃ ψ : C → ℝ, IsGroundState (evalMat HP θ) ψ ∧ ψ ⬝ᵥ ψ = 1 ∧
    (∃ g : ℝ, 0 < g ∧ ∀ χ, ψ ⬝ᵥ χ = 0 →
      (qf (evalMat HP θ) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (evalMat HP θ) χ) ∧
    MvPolynomial.eval ψ F = 0}

/-- A polynomial in a matrix acts on an eigenvector through the eigenvalue. -/
lemma aeval_mulVec_of_eigen {M : Matrix C C ℝ} {ψ : C → ℝ} {E : ℝ} (h : M *ᵥ ψ = E • ψ)
    (q : ℝ[X]) : Polynomial.aeval M q *ᵥ ψ = q.eval E • ψ := by
  have hpow : ∀ n : ℕ, (M ^ n) *ᵥ ψ = E ^ n • ψ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Matrix.add_mulVec, hp, hq, eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul,
      Matrix.smul_mulVec, hpow, smul_smul, eval_monomial]

/-- Evaluating `R_c` at `θ` gives `det q_c(H(θ))`. -/
lemma eval_elimPoly (HP : Matrix C C (MvPolynomial V ℝ)) (F : MvPolynomial C ℝ) (c : C)
    (θ : V → ℝ) :
    MvPolynomial.eval θ (elimPoly HP F c) =
      (Polynomial.aeval (evalMat HP θ) ((colPoly HP F c).map (MvPolynomial.eval θ))).det := by
  set φ := MvPolynomial.eval θ
  unfold elimPoly
  rw [RingHom.map_det]
  congr 1
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  congr 1
  refine RingHom.ext fun a => ?_
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.algebraMap_matrix_apply]

/-- `q_c` at `θ`, evaluated at `E`, is `F` of the column `c` of `adj(H(θ) - E)`. -/
lemma eval_colPoly_map (HP : Matrix C C (MvPolynomial V ℝ)) (F : MvPolynomial C ℝ) (c : C)
    (θ : V → ℝ) (E : ℝ) :
    ((colPoly HP F c).map (MvPolynomial.eval θ)).eval E =
      MvPolynomial.eval (fun s => adjugate (evalMat HP θ - E • 1) s c) F := by
  rw [eval_map]
  set g : (MvPolynomial V ℝ)[X] →+* ℝ := Polynomial.eval₂RingHom (MvPolynomial.eval θ) E
  change g (colPoly HP F c) = _
  unfold colPoly
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
  have hid : g.comp (algebraMap ℝ (MvPolynomial V ℝ)[X]) = RingHom.id ℝ :=
    RingHom.ext fun r => by simp [g]
  rw [hid]
  have hadj : g.mapMatrix (adjugate (shiftMat HP)) = adjugate (g.mapMatrix (shiftMat HP)) :=
    RingHom.map_adjugate g _
  have hsh : g.mapMatrix (shiftMat HP) = evalMat HP θ - E • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [g, shiftMat, evalMat]
    · simp [g, shiftMat, evalMat, hij]
  rw [hsh] at hadj
  change MvPolynomial.eval₂ (RingHom.id ℝ) (fun s => g (adjugate (shiftMat HP) s c)) F = _
  congr 1
  funext s
  exact congrFun (congrFun hadj s) c

/-- Every column of `adj(H - E₀)` is a multiple of a gapped ground state of energy `E₀`. -/
lemma adj_col_eq_smul {H : Matrix C C ℝ} (hS : H.IsSymm) {ψ : C → ℝ} (hψ : IsGroundState H ψ)
    (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf H ψ + g) * (χ ⬝ᵥ χ) ≤ qf H χ) (c : C) :
    ∃ α : ℝ, (fun s => adjugate (H - qf H ψ • 1) s c) = α • ψ := by
  set E := qf H ψ
  set B := H - E • 1
  have hE : H *ᵥ ψ = E • ψ := by
    have := isGroundState_eigen hS hψ; rwa [hN, div_one] at this
  have hBψ : B *ᵥ ψ = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hE, sub_self]
  have hdet : B.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨ψ, hψ.1, hBψ⟩
  set u : C → ℝ := fun s => adjugate B s c
  have hBu : B *ᵥ u = 0 := by
    funext s
    have := congrFun (congrFun (Matrix.mul_adjugate B) s) c
    rw [hdet, zero_smul, Matrix.mul_apply] at this
    simpa [Matrix.mulVec, dotProduct, u] using this
  have hHu : H *ᵥ u = E • u := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hBu
    exact hBu
  by_cases hu : u = 0
  · exact ⟨0, by rw [zero_smul]; exact hu⟩
  · refine ⟨ψ ⬝ᵥ u, unique_of_gap hS hψ hN hg hgap ⟨hu, fun φ => ?_⟩⟩
    have hqu : qf H u = E * (u ⬝ᵥ u) := by rw [qf, hHu, dotProduct_smul, smul_eq_mul]
    have h1 := hψ.2 φ
    rw [hN, mul_one] at h1
    rw [hqu]
    nlinarith [mul_le_mul_of_nonneg_left h1 (dot_self_nonneg u)]

/-- **The elimination polynomial vanishes on the bad set.** -/
theorem eval_elimPoly_eq_zero {HP : Matrix C C (MvPolynomial V ℝ)} {F : MvPolynomial C ℝ}
    (hS : ∀ θ, (evalMat HP θ).IsSymm)
    (hF : ∀ (a : ℝ) (ψ : C → ℝ), MvPolynomial.eval ψ F = 0 → MvPolynomial.eval (a • ψ) F = 0)
    {θ : V → ℝ} (hθ : θ ∈ BadSet HP F) (c : C) : MvPolynomial.eval θ (elimPoly HP F c) = 0 := by
  obtain ⟨ψ, hψ, hN, ⟨g, hg, hgap⟩, hFψ⟩ := hθ
  have hE : evalMat HP θ *ᵥ ψ = qf (evalMat HP θ) ψ • ψ := by
    have := isGroundState_eigen (hS θ) hψ; rwa [hN, div_one] at this
  obtain ⟨α, hα⟩ := adj_col_eq_smul (hS θ) hψ hN hg hgap c
  rw [eval_elimPoly]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨ψ, hψ.1, ?_⟩
  rw [aeval_mulVec_of_eigen hE, eval_colPoly_map, hα, hF α ψ hFψ, zero_smul]

/-- **Generic avoidance.** If the elimination polynomial for some column `c` is not identically
zero, the parameters at which a gapped ground state satisfies `F(ψ) = 0` lie in a closed, nowhere
dense, Lebesgue-null set. -/
theorem generic_avoid [Fintype V] {HP : Matrix C C (MvPolynomial V ℝ)} {F : MvPolynomial C ℝ}
    (hS : ∀ θ, (evalMat HP θ).IsSymm)
    (hF : ∀ (a : ℝ) (ψ : C → ℝ), MvPolynomial.eval ψ F = 0 → MvPolynomial.eval (a • ψ) F = 0)
    {c : C} (hR : elimPoly HP F c ≠ 0) :
    ∃ Z : Set (V → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      BadSet HP F ⊆ Z := by
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hR
  exact ⟨_, hcl, hint, volume_zeroSet hR, fun θ hθ => eval_elimPoly_eq_zero hS hF hθ c⟩

end

end DFT
