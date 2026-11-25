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
dense, Lebesgue-null set, provided a single polynomial `R_u` is not identically zero.

The ground state depends on `θ` only through an eigenvalue, which is not polynomial. The eigenvalue
is eliminated in two steps.
* **Adjugate.** For `B = H - E` with `E` the ground-state energy, `B · adj B = det B = 0`, so for
  any fixed vector `u` the vector `adj B u` lies in the kernel of `B`. A gapped ground state spans
  that kernel, so `adj B u` is a multiple of `ψ` (`adj_mulVec_eq_smul`), and `F` vanishes on it.
* **Matrix polynomial.** Let `q_u(E) = F(adj(H - E) u)`, a polynomial in `E` with coefficients
  polynomial in `θ` (`colPoly`). Then `q_u(H) ψ = q_u(E₀) ψ = 0` (`aeval_mulVec_of_eigen`), so
  `R_u = det q_u(H)` vanishes (`eval_elimPoly_eq_zero`). Up to sign `R_u` is the resultant of
  `q_u` and the characteristic polynomial, `Π_j q_u(E_j)` over all eigenvalues.

`R_u ≠ 0` plays the role of hypothesis (H*) in the generic Hohenberg–Kohn theorem. It holds as soon
as, at one parameter point, there is an orthonormal eigenbasis `v_j` with distinct eigenvalues,
`v_j · u ≠ 0` and `F(v_j) ≠ 0` (`elimPoly_ne_zero_of_eigenbasis`). The proof uses
`adj(H - E_j) = Π_{k ≠ j} (E_k - E_j) v_j v_jᵀ` (`adj_mulVec_of_eigenbasis`).

* `evalMat`, `shiftMat`, `colPoly`, `elimPoly`, `BadSet`.
* `aeval_mulVec_of_eigen`, `eval_elimPoly`, `eval_colPoly_map`, `adj_mulVec_eq_smul`.
* `eval_elimPoly_eq_zero`: **the elimination polynomial vanishes on the bad set**.
* `generic_avoid`: **the bad set is closed-nowhere-dense-null when `R_u ≠ 0`**.
* `elimPoly_ne_zero_of_eigenbasis`: **a witness criterion for `R_u ≠ 0`**.
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

/-- `q_u(E) = F(adj(H - E) u)`. -/
noncomputable def colPoly (HP : Matrix C C (MvPolynomial V ℝ)) (F : MvPolynomial C ℝ)
    (u : C → ℝ) : (MvPolynomial V ℝ)[X] :=
  MvPolynomial.aeval
    (fun s => (adjugate (shiftMat HP) *ᵥ fun t => Polynomial.C (MvPolynomial.C (u t))) s) F

/-- The elimination polynomial `R_u = det q_u(H)`. -/
noncomputable def elimPoly (HP : Matrix C C (MvPolynomial V ℝ)) (F : MvPolynomial C ℝ)
    (u : C → ℝ) : MvPolynomial V ℝ :=
  (Polynomial.aeval HP (colPoly HP F u)).det

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

/-- Evaluating `R_u` at `θ` gives `det q_u(H(θ))`. -/
lemma eval_elimPoly (HP : Matrix C C (MvPolynomial V ℝ)) (F : MvPolynomial C ℝ) (u : C → ℝ)
    (θ : V → ℝ) :
    MvPolynomial.eval θ (elimPoly HP F u) =
      (Polynomial.aeval (evalMat HP θ) ((colPoly HP F u).map (MvPolynomial.eval θ))).det := by
  set φ := MvPolynomial.eval θ
  unfold elimPoly
  rw [RingHom.map_det]
  congr 1
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  congr 1
  refine RingHom.ext fun a => ?_
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.algebraMap_matrix_apply]

/-- `q_u` at `θ`, evaluated at `E`, is `F(adj(H(θ) - E) u)`. -/
lemma eval_colPoly_map (HP : Matrix C C (MvPolynomial V ℝ)) (F : MvPolynomial C ℝ) (u : C → ℝ)
    (θ : V → ℝ) (E : ℝ) :
    ((colPoly HP F u).map (MvPolynomial.eval θ)).eval E =
      MvPolynomial.eval (adjugate (evalMat HP θ - E • 1) *ᵥ u) F := by
  rw [eval_map]
  set g : (MvPolynomial V ℝ)[X] →+* ℝ := Polynomial.eval₂RingHom (MvPolynomial.eval θ) E
  change g (colPoly HP F u) = _
  unfold colPoly
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
  have hid : g.comp (algebraMap ℝ (MvPolynomial V ℝ)[X]) = RingHom.id ℝ :=
    RingHom.ext fun r => by
      simp only [g, RingHom.comp_apply, Polynomial.algebraMap_apply, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, RingHom.id_apply]
  rw [hid]
  have hadj : g.mapMatrix (adjugate (shiftMat HP)) = adjugate (g.mapMatrix (shiftMat HP)) :=
    RingHom.map_adjugate g _
  have hsh : g.mapMatrix (shiftMat HP) = evalMat HP θ - E • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [g, shiftMat, evalMat]
    · simp [g, shiftMat, evalMat, hij]
  rw [hsh] at hadj
  change MvPolynomial.eval₂ (RingHom.id ℝ)
    (fun s => g ((adjugate (shiftMat HP) *ᵥ
      fun t => Polynomial.C (MvPolynomial.C (u t))) s)) F = _
  congr 1
  funext s
  rw [RingHom.mapMatrix_apply] at hadj
  rw [RingHom.map_mulVec, hadj]
  congr 1
  funext t
  simp [g]

/-- For any `u`, `adj(H - E₀) u` is a multiple of a gapped ground state of energy `E₀`. -/
lemma adj_mulVec_eq_smul {H : Matrix C C ℝ} (hS : H.IsSymm) {ψ : C → ℝ}
    (hψ : IsGroundState H ψ) (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf H ψ + g) * (χ ⬝ᵥ χ) ≤ qf H χ) (u : C → ℝ) :
    ∃ α : ℝ, adjugate (H - qf H ψ • 1) *ᵥ u = α • ψ := by
  set E := qf H ψ
  set B := H - E • 1
  have hE : H *ᵥ ψ = E • ψ := by
    have := isGroundState_eigen hS hψ; rwa [hN, div_one] at this
  have hBψ : B *ᵥ ψ = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hE, sub_self]
  have hdet : B.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨ψ, hψ.1, hBψ⟩
  set w := adjugate B *ᵥ u
  have hBw : B *ᵥ w = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, zero_smul, Matrix.zero_mulVec]
  have hHw : H *ᵥ w = E • w := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hBw
    exact hBw
  by_cases hw : w = 0
  · exact ⟨0, by rw [zero_smul]; exact hw⟩
  · refine ⟨ψ ⬝ᵥ w, unique_of_gap hS hψ hN hg hgap ⟨hw, fun φ => ?_⟩⟩
    have hqw : qf H w = E * (w ⬝ᵥ w) := by rw [qf, hHw, dotProduct_smul, smul_eq_mul]
    have h1 := hψ.2 φ
    rw [hN, mul_one] at h1
    rw [hqw]
    nlinarith [mul_le_mul_of_nonneg_left h1 (dot_self_nonneg w)]

/-- **The elimination polynomial vanishes on the bad set.** -/
theorem eval_elimPoly_eq_zero {HP : Matrix C C (MvPolynomial V ℝ)} {F : MvPolynomial C ℝ}
    (hS : ∀ θ, (evalMat HP θ).IsSymm)
    (hF : ∀ (a : ℝ) (ψ : C → ℝ), MvPolynomial.eval ψ F = 0 → MvPolynomial.eval (a • ψ) F = 0)
    {θ : V → ℝ} (hθ : θ ∈ BadSet HP F) (u : C → ℝ) :
    MvPolynomial.eval θ (elimPoly HP F u) = 0 := by
  obtain ⟨ψ, hψ, hN, ⟨g, hg, hgap⟩, hFψ⟩ := hθ
  have hE : evalMat HP θ *ᵥ ψ = qf (evalMat HP θ) ψ • ψ := by
    have := isGroundState_eigen (hS θ) hψ; rwa [hN, div_one] at this
  obtain ⟨α, hα⟩ := adj_mulVec_eq_smul (hS θ) hψ hN hg hgap u
  rw [eval_elimPoly]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨ψ, hψ.1, ?_⟩
  rw [aeval_mulVec_of_eigen hE, eval_colPoly_map, hα, hF α ψ hFψ, zero_smul]

/-- **Generic avoidance.** If the elimination polynomial for some vector `u` is not identically
zero, the parameters at which a gapped ground state satisfies `F(ψ) = 0` lie in a closed, nowhere
dense, Lebesgue-null set. -/
theorem generic_avoid [Fintype V] {HP : Matrix C C (MvPolynomial V ℝ)} {F : MvPolynomial C ℝ}
    (hS : ∀ θ, (evalMat HP θ).IsSymm)
    (hF : ∀ (a : ℝ) (ψ : C → ℝ), MvPolynomial.eval ψ F = 0 → MvPolynomial.eval (a • ψ) F = 0)
    {u : C → ℝ} (hR : elimPoly HP F u ≠ 0) :
    ∃ Z : Set (V → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      BadSet HP F ⊆ Z := by
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hR
  exact ⟨_, hcl, hint, volume_zeroSet hR, fun θ hθ => eval_elimPoly_eq_zero hS hF hθ u⟩

/-! ### A witness criterion -/

section Witness

variable {v : C → C → ℝ} (hON : ∀ a b, ∑ x, v a x * v b x = if a = b then 1 else 0)
include hON

/-- The matrix with columns `v a`. -/
private def colMat (v : C → C → ℝ) : Matrix C C ℝ := Matrix.of fun x a => v a x

omit [Fintype C] [DecidableEq C] hON in
private lemma colMat_apply (x a : C) : colMat v x a = v a x := rfl

private lemma colMat_tmul : (colMat v)ᵀ * colMat v = 1 := by
  ext a b; simp [Matrix.mul_apply, colMat_apply, hON, Matrix.one_apply]

private lemma colMat_mult : colMat v * (colMat v)ᵀ = 1 := mul_eq_one_comm.mp (colMat_tmul hON)

/-- Expansion in an orthonormal basis indexed by `C`. -/
lemma expand_onb (w : C → ℝ) : w = ∑ a, (v a ⬝ᵥ w) • v a := by
  have h : (colMat v * (colMat v)ᵀ) *ᵥ w = w := by rw [colMat_mult hON, Matrix.one_mulVec]
  conv_lhs => rw [← h]
  rw [← Matrix.mulVec_mulVec]
  funext x
  simp only [Matrix.mulVec, dotProduct, colMat_apply, Matrix.transpose_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- `adj(H - E_b) u = (Π_{j ≠ b} (E_j - E_b)) (v_b · u) v_b` for an orthonormal eigenbasis. -/
lemma adj_mulVec_of_eigenbasis {H : Matrix C C ℝ} {E : C → ℝ}
    (hEig : ∀ a, H *ᵥ v a = E a • v a) (b : C) (u : C → ℝ) :
    adjugate (H - E b • 1) *ᵥ u =
      ((∏ j ∈ Finset.univ.erase b, (E j - E b)) * (v b ⬝ᵥ u)) • v b := by
  have hPt : (colMat v)ᵀ * colMat v = 1 := colMat_tmul hON
  have hPP : colMat v * (colMat v)ᵀ = 1 := colMat_mult hON
  have hHP : H * colMat v = colMat v * diagonal E := by
    ext x a
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    have := congrFun (hEig a) x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [colMat_apply]
    rw [this, mul_comm]
  have hdecomp : H - E b • 1 = colMat v * diagonal (fun j => E j - E b) * (colMat v)ᵀ := by
    have h1 : H = colMat v * diagonal E * (colMat v)ᵀ := by
      rw [← hHP, Matrix.mul_assoc, hPP, Matrix.mul_one]
    have h2 : E b • (1 : Matrix C C ℝ) =
        colMat v * diagonal (fun _ => E b) * (colMat v)ᵀ := by
      rw [show diagonal (fun _ => E b) = E b • (1 : Matrix C C ℝ) by
        ext i j; by_cases hij : i = j <;> simp [hij]]
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP]
    rw [h1, h2, ← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j; by_cases hij : i = j <;> simp [hij]
  have hdet2 : (colMat v).det * (colMat v).det = 1 := by
    have := congrArg Matrix.det hPt
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hadjP : adjugate (colMat v) = (colMat v).det • (colMat v)ᵀ := by
    calc adjugate (colMat v) = adjugate (colMat v) * (colMat v * (colMat v)ᵀ) := by
          rw [hPP, Matrix.mul_one]
      _ = (adjugate (colMat v) * colMat v) * (colMat v)ᵀ := by rw [Matrix.mul_assoc]
      _ = (colMat v).det • (colMat v)ᵀ := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hadjPt : adjugate (colMat v)ᵀ = (colMat v).det • colMat v := by
    rw [← Matrix.adjugate_transpose, hadjP, Matrix.transpose_smul, Matrix.transpose_transpose]
  set κ := ∏ j ∈ Finset.univ.erase b, (E j - E b)
  have hD : adjugate (diagonal (fun j => E j - E b)) = diagonal (Pi.single b κ) := by
    rw [Matrix.adjugate_diagonal]
    congr 1
    funext i
    by_cases hib : i = b
    · subst hib; simp [κ]
    · rw [Pi.single_eq_of_ne hib]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hib, Finset.mem_univ _⟩)
        (sub_self _)
  have hadj : adjugate (H - E b • 1) = κ • vecMulVec (v b) (v b) := by
    rw [hdecomp, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadjPt, hadjP, hD]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hdet2, one_smul]
    ext x y
    rw [Matrix.mul_apply]
    simp only [Matrix.diagonal_mul, colMat_apply, Matrix.transpose_apply, Pi.single_apply,
      Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, mul_ite, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  rw [hadj]
  funext x
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **Witness criterion.** If at some parameter point `H(θ)` has an orthonormal eigenbasis `v_a`
with distinct eigenvalues, `v_a · u ≠ 0` and `F` does not vanish on any nonzero multiple of any
`v_a`, then the elimination polynomial `R_u` is not identically zero. -/
theorem elimPoly_ne_zero_of_eigenbasis {HP : Matrix C C (MvPolynomial V ℝ)}
    {F : MvPolynomial C ℝ} {u : C → ℝ} (θ : V → ℝ) {E : C → ℝ}
    (hEig : ∀ a, evalMat HP θ *ᵥ v a = E a • v a) (hE : Function.Injective E)
    (hF : ∀ a, ∀ α : ℝ, α ≠ 0 → MvPolynomial.eval (α • v a) F ≠ 0)
    (hu : ∀ a, v a ⬝ᵥ u ≠ 0) : elimPoly HP F u ≠ 0 := by
  intro h0
  have h1 := congrArg (MvPolynomial.eval θ) h0
  rw [map_zero, eval_elimPoly] at h1
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1
  set q := (colPoly HP F u).map (MvPolynomial.eval θ)
  set Q := Polynomial.aeval (evalMat HP θ) q
  have hq : ∀ a, q.eval (E a) ≠ 0 := by
    intro a
    rw [eval_colPoly_map, adj_mulVec_of_eigenbasis hON hEig a u]
    apply hF a
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj => ?_) (hu a)
    exact sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hj).1 (hE h)
  have hQv : ∀ a, Q *ᵥ v a = q.eval (E a) • v a := fun a => aeval_mulVec_of_eigen (hEig a) q
  have hcoef : ∀ b, v b ⬝ᵥ w = 0 := by
    intro b
    have hexp := expand_onb hON w
    have hQw : Q *ᵥ w = ∑ a, ((v a ⬝ᵥ w) * q.eval (E a)) • v a := by
      conv_lhs => rw [hexp]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Matrix.mulVec_smul, hQv, smul_smul]
    have hdot := congrArg (v b ⬝ᵥ ·) hQw
    simp only [hw, dotProduct_zero, dotProduct_sum, dotProduct_smul, smul_eq_mul] at hdot
    have hvv : ∀ a, v b ⬝ᵥ v a = if b = a then 1 else 0 := fun a => by
      simpa [dotProduct] using hON b a
    simp only [hvv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true] at hdot
    exact (mul_eq_zero.mp hdot.symm).resolve_right (hq b)
  apply hw0
  rw [expand_onb hON w]
  simp [hcoef]

end Witness

end

end DFT
