/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.ManyBody.NaturalOrbitals

/-!
# Slater states and Wick's theorem

A Slater state is a mode rotation of a configuration, `U(u) |s⟩`, that is the creation string
`c†(φ₀) ⋯ c†(φ_{N-1}) |∅⟩` of orthonormal orbitals. Its one-body matrix `γ` is a projection of rank
`N`, every such projection arises this way, and all its correlation functions are determinants of
`γ` (**Wick's theorem**):
`⟨Ψ, c_{i₀}† ⋯ c_{iₙ₋₁}† c_{jₙ₋₁} ⋯ c_{j₀} Ψ⟩ = det (γ_{i_a j_b})`.

The proof works for any vector `Ψ` and matrix `P` such that `c†(P φ) Ψ = 0` for all `φ` and
`c_i Ψ = c(P e_i) Ψ` (`wick_of_proj`). Then `⟨Ψ, c_{i₀}† X Ψ⟩ = ⟨Ψ, c†(P e_{i₀}) X Ψ⟩`, and moving
`c†(P e_{i₀})` to the right through `X` (where it annihilates `Ψ`) produces the expansion of the
determinant along its first row. For a creation string of orthonormal orbitals `φ_a`, `P` is the
projection `Σ_a φ_a φ_a†` onto the occupied orbitals.

## Main definitions

* `creStr i = c_{i₀}† ⋯ c_{iₙ₋₁}†`, `annStr j = c_{jₙ₋₁} ⋯ c_{j₀}`.
* `slaterState u s = U(u) |s⟩`.

## Main results

* `wick_of_proj`: Wick's theorem for a vector annihilated by `c†(P φ)` and `c((1 - P) φ)`.
* `slaterState_isNState`, `rdm1_slater_proj`: a Slater state is an `N`-particle state, and its
  one-body matrix is a Hermitian projection with trace `N`.
* `exists_slater_of_proj`: every Hermitian projection with trace `N` is the one-body matrix of a
  Slater state.
* `wick_slater` (**Wick's theorem**) and `rdm2_slater`: `D_{ij,kl} = γ_ik γ_jl - γ_il γ_jk`.
-/

namespace QM.ManyBody

open Matrix Finset

variable {M : ℕ}

/-! ### Strings of creation and annihilation operators -/

/-- `c_{i₀}† ⋯ c_{iₙ₋₁}†`. -/
noncomputable def creStr : {n : ℕ} → (Fin n → Fin M) → FockOp M
  | 0, _ => 1
  | _ + 1, i => cre (i 0) * creStr (Fin.tail i)

/-- `c_{jₙ₋₁} ⋯ c_{j₀}`. -/
noncomputable def annStr : {n : ℕ} → (Fin n → Fin M) → FockOp M
  | 0, _ => 1
  | _ + 1, j => annStr (Fin.tail j) * ann (j 0)

lemma creStr_succ {n : ℕ} (i : Fin (n + 1) → Fin M) :
    creStr i = cre (i 0) * creStr (Fin.tail i) := rfl

lemma annStr_succ {n : ℕ} (j : Fin (n + 1) → Fin M) :
    annStr j = annStr (Fin.tail j) * ann (j 0) := rfl

lemma ann_eq_annV (i : Fin M) : ann i = annV (Pi.single i 1) := by
  rw [annV_eq, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

lemma annV_sub (χ ξ : Fin M → ℂ) : annV (χ - ξ) = annV χ - annV ξ := by
  simp only [annV_eq, Pi.sub_apply, star_sub, sub_smul, Finset.sum_sub_distrib]

lemma creV_mul_cre (φ : Fin M → ℂ) (i : Fin M) : creV φ * cre i = -(cre i * creV φ) := by
  rw [eq_neg_iff_add_eq_zero, creV, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, cre_mul_cre_add, smul_zero]

lemma creV_mul_ann (φ : Fin M → ℂ) (j : Fin M) :
    creV φ * ann j = φ j • (1 : FockOp M) - ann j * creV φ := by
  have h := annV_mul_creV_add (Pi.single j 1) φ
  rw [← ann_eq_annV] at h
  have hd : star (Pi.single j (1 : ℂ)) ⬝ᵥ φ = φ j := by
    rw [dotProduct, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  rw [hd] at h
  rw [← h]; abel

lemma creV_mul_creStr (φ : Fin M → ℂ) {n : ℕ} (i : Fin n → Fin M) :
    creV φ * creStr i = (-1 : ℂ) ^ n • (creStr i * creV φ) := by
  induction n with
  | zero => simp [creStr]
  | succ n ih =>
    rw [creStr_succ, ← mul_assoc, creV_mul_cre, neg_mul, mul_assoc, ih, mul_smul_comm, pow_succ]
    simp only [mul_assoc, neg_smul, mul_neg_one]

/-- **Moving `c†(φ)` through annihilators**:
`c†(φ) c_{j_k} ⋯ c_{j₀} = Σ_l (-1)^(k-l) φ_{j_l} (omit l) + (-1)^(k+1) c_{j_k} ⋯ c_{j₀} c†(φ)`. -/
lemma creV_mul_annStr (φ : Fin M → ℂ) {k : ℕ} (j : Fin (k + 1) → Fin M) :
    creV φ * annStr j = ∑ l : Fin (k + 1), ((-1 : ℂ) ^ (k - l) * φ (j l)) • annStr (j ∘ l.succAbove)
      + (-1 : ℂ) ^ (k + 1) • (annStr j * creV φ) := by
  induction k with
  | zero =>
    rw [annStr_succ, Fin.sum_univ_one]
    simp only [annStr, one_mul, creV_mul_ann, Fin.val_zero, Nat.sub_self, pow_zero, one_mul,
      zero_add, pow_one, neg_smul, one_smul]
    abel
  | succ k ih =>
    have hterm : ∀ l : Fin (k + 1),
        annStr (j ∘ (Fin.succ l).succAbove) = annStr (Fin.tail j ∘ l.succAbove) * ann (j 0) := by
      intro l
      have hsub : (j ∘ (Fin.succ l).succAbove) = Fin.cons (j 0) (Fin.tail j ∘ l.succAbove) := by
        funext x
        refine Fin.cases ?_ (fun y => ?_) x
        · simp
        · simp [Fin.succ_succAbove_succ, Fin.tail]
      rw [hsub, annStr_succ]
      rfl
    have h0 : j ∘ (0 : Fin (k + 2)).succAbove = Fin.tail j := by
      funext x; simp [Fin.tail]
    have he : ∀ l : Fin (k + 1), k + 1 - (l + 1) = k - l := fun l => by omega
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [hterm, h0, Fin.val_succ, Fin.val_zero, Nat.sub_zero, he]
    rw [annStr_succ j, ← mul_assoc (creV φ), ih (Fin.tail j), add_mul, Finset.sum_mul,
      smul_mul_assoc, mul_assoc (annStr (Fin.tail j)), creV_mul_ann, mul_sub, mul_smul_comm,
      mul_one]
    simp only [smul_mul_assoc, ← mul_assoc, pow_succ, Fin.tail]
    module

/-! ### Wick's theorem for a projection -/

lemma star_dotProduct_conjTranspose_mulVec (A : FockOp M) (v w : Finset (Fin M) → ℂ) :
    star v ⬝ᵥ (Aᴴ *ᵥ w) = star (A *ᵥ v) ⬝ᵥ w := by
  rw [dotProduct_mulVec, star_mulVec]

/-- **Wick's theorem** for a vector `Ψ` with `c†(P φ) Ψ = 0` and `c_i Ψ = c(P e_i) Ψ`. -/
theorem wick_of_proj {Ψ : Finset (Fin M) → ℂ} {P : Matrix (Fin M) (Fin M) ℂ}
    (h1 : ∀ φ, creV (P *ᵥ φ) *ᵥ Ψ = 0)
    (h2 : ∀ i, ann i *ᵥ Ψ = annV (P *ᵥ Pi.single i 1) *ᵥ Ψ) {n : ℕ} (i j : Fin n → Fin M) :
    star Ψ ⬝ᵥ ((creStr i * annStr j) *ᵥ Ψ) =
      (star Ψ ⬝ᵥ Ψ) * (Matrix.of fun a b => P (j b) (i a)).det := by
  induction n with
  | zero => simp [creStr, annStr]
  | succ n ih =>
    set φ := P *ᵥ Pi.single (i 0) 1 with hφ
    have hcre : cre (i 0) = (ann (i 0))ᴴ := by rw [ann, conjTranspose_conjTranspose]
    rw [creStr_succ, mul_assoc, ← mulVec_mulVec, hcre, star_dotProduct_conjTranspose_mulVec, h2,
      annV, ← star_dotProduct_conjTranspose_mulVec, conjTranspose_conjTranspose, mulVec_mulVec,
      ← mul_assoc, creV_mul_creStr, smul_mul_assoc, mul_assoc, creV_mul_annStr, mul_add,
      Finset.mul_sum]
    simp only [mul_smul_comm, add_mulVec, sum_mulVec, smul_mulVec, dotProduct_add,
      dotProduct_sum, dotProduct_smul, smul_eq_mul]
    have hz : (creStr (Fin.tail i) * (annStr j * creV (P *ᵥ Pi.single (i 0) 1))) *ᵥ Ψ = 0 := by
      rw [← mul_assoc, ← mulVec_mulVec, h1, mulVec_zero]
    rw [hz, dotProduct_zero, mul_zero, add_zero, det_succ_row_zero, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have key : ∀ a b : ℕ, a ≤ b → (-1 : ℂ) ^ b * (-1) ^ (b - a) = (-1) ^ a := by
      intro a b h
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    have hsign : (-1 : ℂ) ^ n * (-1) ^ (n - l) = (-1) ^ (l : ℕ) :=
      key l n (Nat.lt_succ_iff.mp l.2)
    have hφl : (P *ᵥ Pi.single (i 0) 1) (j l) = P (j l) (i 0) := by
      simp [mulVec, dotProduct, Pi.single_apply]
    have hsub : (of fun a b => P ((j ∘ l.succAbove) b) (Fin.tail i a)) =
        (of fun a b => P (j b) (i a)).submatrix Fin.succ l.succAbove := by
      ext a b; simp [Fin.tail]
    rw [ih, hφl, hsub, of_apply, ← hsign]
    ring

/-! ### Creation strings of orthonormal orbitals -/

section Orbitals

variable {N : ℕ} (Φ : Fin N → Fin M → ℂ)

/-- The projection `Σ_a φ_a φ_a†` onto the orbitals. -/
noncomputable def orbProj : Matrix (Fin M) (Fin M) ℂ := of fun x y => ∑ a, Φ a x * star (Φ a y)

lemma orbProj_mulVec (φ : Fin M → ℂ) : orbProj Φ *ᵥ φ = ∑ a, (star (Φ a) ⬝ᵥ φ) • Φ a := by
  funext x
  simp only [orbProj, mulVec, dotProduct, of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.star_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
  ring

open scoped ComplexOrder in
/-- `c†(φ_b)` annihilates the string `c†(φ₀) ⋯ |∅⟩`. -/
lemma creV_mulVec_strV_self (b : Fin N) : creV (Φ b) *ᵥ strV Φ = 0 := by
  have hv : creV (Φ b) *ᵥ strV Φ = strV (Fin.cons (Φ b) Φ : Fin (N + 1) → Fin M → ℂ) := by
    rw [strV_succ]; rfl
  rw [hv]
  have h0 := strV_overlap (Fin.cons (Φ b) Φ : Fin (N + 1) → Fin M → ℂ)
    (Fin.cons (Φ b) Φ : Fin (N + 1) → Fin M → ℂ)
  rw [det_zero_of_row_eq (i := 0) (j := b.succ) (Fin.succ_ne_zero b).symm
    (by funext c; simp [of_apply])] at h0
  exact dotProduct_star_self_eq_zero.mp h0

variable {Φ}

/-- `c(χ)` annihilates the string when `χ` is orthogonal to all orbitals. -/
lemma annV_mulVec_strV_eq_zero {χ : Fin M → ℂ} (hχ : ∀ b, star χ ⬝ᵥ Φ b = 0) :
    annV χ *ᵥ strV Φ = 0 := by
  cases N with
  | zero => rw [strV_zero, annV_mulVec_vac]
  | succ N =>
    rw [annV_mulVec_strV]
    exact Finset.sum_eq_zero fun b _ => by rw [hχ b, mul_zero, zero_smul]

variable (hΦ : ∀ a b, star (Φ a) ⬝ᵥ Φ b = if a = b then 1 else 0)
include hΦ

omit hΦ in
lemma orbProj_h1 (φ : Fin M → ℂ) : creV (orbProj Φ *ᵥ φ) *ᵥ strV Φ = 0 := by
  rw [orbProj_mulVec, creV_sum, sum_mulVec]
  exact Finset.sum_eq_zero fun a _ => by
    rw [creV_smul, smul_mulVec, creV_mulVec_strV_self, smul_zero]

lemma orbProj_h2 (i : Fin M) :
    ann i *ᵥ strV Φ = annV (orbProj Φ *ᵥ Pi.single i 1) *ᵥ strV Φ := by
  rw [← sub_eq_zero, ann_eq_annV, ← sub_mulVec, ← annV_sub]
  refine annV_mulVec_strV_eq_zero fun b => ?_
  rw [orbProj_mulVec, star_sub, sub_dotProduct, star_sum, sum_dotProduct, sub_eq_zero]
  simp only [star_smul, smul_dotProduct, hΦ, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [dotProduct, Pi.single_apply]

lemma strV_norm : star (strV Φ) ⬝ᵥ strV Φ = 1 := by
  rw [strV_overlap]
  have : (of fun a b => star (Φ a) ⬝ᵥ Φ b) = (1 : Matrix (Fin N) (Fin N) ℂ) := by
    ext a b; rw [of_apply, hΦ]; exact (Matrix.one_apply (i := a) (j := b)).symm
  rw [this, det_one]

end Orbitals

/-! ### Slater states -/

/-- **A Slater state** `U(u) |s⟩`. -/
noncomputable def slaterState (u : Matrix (Fin M) (Fin M) ℂ) (s : Finset (Fin M)) : Fock M :=
  modeRotOp u (EuclideanSpace.single s 1)

lemma slaterState_ofLp (u : Matrix (Fin M) (Fin M) ℂ) (s : Finset (Fin M)) :
    (slaterState u s).ofLp = strV (rotOrb u s rfl) := by
  rw [slaterState, modeRotOp, EuclideanSpace.single, PiLp.single, toEuclideanCLM_toLp,
    modeRot_mulVec_single]

lemma rotOrb_orthonormal {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (s : Finset (Fin M)) (a b : Fin s.card) :
    star (rotOrb u s rfl a) ⬝ᵥ rotOrb u s rfl b = if a = b then 1 else 0 := by
  rw [rotOrb, rotOrb, col_overlap hu]
  simp [(s.orderEmbOfFin rfl).injective.eq_iff]

lemma inner_toFockCLM (A : FockOp M) (Ψ : Fock M) :
    inner ℂ Ψ (toFockCLM A Ψ) = star Ψ.ofLp ⬝ᵥ (A *ᵥ Ψ.ofLp) := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ, Ψ = WithLp.toLp 2 ψ := ⟨Ψ.ofLp, rfl⟩
  rw [toEuclideanCLM_toLp, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- A Slater state of `|s|` modes is an `|s|`-particle state. -/
theorem slaterState_isNState {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (s : Finset (Fin M)) : IsNState s.card (slaterState u s) :=
  (isNState_single s).modeRotOp hu

lemma wick_slater_aux {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (s : Finset (Fin M)) {n : ℕ} (i j : Fin n → Fin M) :
    inner ℂ (slaterState u s) (toFockCLM (creStr i * annStr j) (slaterState u s)) =
      (Matrix.of fun a b => orbProj (rotOrb u s rfl) (j b) (i a)).det := by
  rw [inner_toFockCLM, slaterState_ofLp,
    wick_of_proj (orbProj_h1 (Φ := rotOrb u s rfl)) (orbProj_h2 (rotOrb_orthonormal hu s)),
    strV_norm (rotOrb_orthonormal hu s), one_mul]

lemma rdm1_slaterState {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (s : Finset (Fin M)) (a b : Fin M) :
    rdm1 (slaterState u s) a b = orbProj (rotOrb u s rfl) b a := by
  have h := wick_slater_aux hu s ![a] ![b]
  simp only [creStr, annStr, mul_one, one_mul, det_unique, of_apply, Fin.default_eq_zero,
    Matrix.cons_val_fin_one] at h
  rw [rdm1, ← h, map_mul]
  rfl

/-- **Wick's theorem**: the correlation functions of a Slater state are determinants of its
one-body matrix, `⟨Ψ, c_{i₀}† ⋯ c_{iₙ₋₁}† c_{jₙ₋₁} ⋯ c_{j₀} Ψ⟩ = det (γ_{i_a j_b})`. -/
theorem wick_slater {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (s : Finset (Fin M)) {n : ℕ} (i j : Fin n → Fin M) :
    inner ℂ (slaterState u s) (toFockCLM (creStr i * annStr j) (slaterState u s)) =
      (Matrix.of fun a b => rdm1 (slaterState u s) (i a) (j b)).det := by
  rw [wick_slater_aux hu s]
  simp only [rdm1_slaterState hu s]

/-- **The two-body matrix of a Slater state**: `D_{ij,kl} = γ_ik γ_jl - γ_il γ_jk`. -/
theorem rdm2_slater {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (s : Finset (Fin M)) (i j k l : Fin M) :
    rdm2 (slaterState u s) (i, j) (k, l) =
      rdm1 (slaterState u s) i k * rdm1 (slaterState u s) j l -
        rdm1 (slaterState u s) i l * rdm1 (slaterState u s) j k := by
  have h := wick_slater hu s ![i, j] ![k, l]
  rw [det_fin_two] at h
  simp only [of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h, rdm2]
  simp only [creStr, annStr, Fin.tail, mul_one, one_mul]
  simp only [creOp, annOp, map_mul, mul_assoc]
  rfl

/-- **The one-body matrix of a Slater state** is a Hermitian projection with trace `|s|`. -/
theorem rdm1_slater_proj {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (s : Finset (Fin M)) :
    (rdm1 (slaterState u s))ᴴ = rdm1 (slaterState u s) ∧
      rdm1 (slaterState u s) * rdm1 (slaterState u s) = rdm1 (slaterState u s) ∧
      (rdm1 (slaterState u s)).trace = s.card := by
  refine ⟨rdm1_isHermitian _, ?_, trace_rdm1 (slaterState_isNState hu s)⟩
  rw [slaterState, rdm1_modeRotOp hu, rdm1_single]
  have huu : uᵀ * u.map star = 1 := by
    have h := (mem_unitaryGroup_iff').mp hu
    have := congrArg transpose h
    rwa [transpose_mul, transpose_one, star_eq_conjTranspose, conjTranspose, transpose_map,
      transpose_transpose] at this
  have hD : (diagonal fun i => if i ∈ s then (1 : ℂ) else 0) *
      (diagonal fun i => if i ∈ s then (1 : ℂ) else 0) =
      diagonal fun i => if i ∈ s then (1 : ℂ) else 0 := by
    rw [diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp
  calc u.map star * diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) * uᵀ *
        (u.map star * diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) * uᵀ)
      = u.map star * diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) * (uᵀ * u.map star) *
          diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) * uᵀ := by simp only [mul_assoc]
    _ = _ := by rw [huu, mul_one, mul_assoc (u.map star), hD]

/-- **Every Hermitian projection with trace `N` is the one-body matrix of a Slater state.** -/
theorem exists_slater_of_proj {N : ℕ} {γ : Matrix (Fin M) (Fin M) ℂ} (hγ : γᴴ = γ)
    (hP : γ * γ = γ) (htr : γ.trace = N) :
    ∃ v ∈ unitaryGroup (Fin M) ℂ, ∃ s : Finset (Fin M),
      s.card = N ∧ rdm1 (slaterState v s) = γ := by
  have hH : γ.IsHermitian := hγ
  obtain ⟨u, hu, hd⟩ := exists_diag_conj hH
  set ev : Fin M → ℂ := fun k => (hH.eigenvalues k : ℂ)
  have huu : uᵀ * u.map star = 1 := by
    have h := (mem_unitaryGroup_iff').mp hu
    have := congrArg transpose h
    rwa [transpose_mul, transpose_one, star_eq_conjTranspose, conjTranspose, transpose_map,
      transpose_transpose] at this
  have huu' : u.map star * uᵀ = 1 := by
    have h := (mem_unitaryGroup_iff).mp hu
    have := congrArg transpose h
    rwa [transpose_mul, transpose_one, star_eq_conjTranspose, conjTranspose, transpose_map,
      transpose_transpose] at this
  -- the eigenvalues are `0` or `1`
  have hsq : diagonal ev * diagonal ev = diagonal ev := by
    rw [← hd]
    calc u.map star * γ * uᵀ * (u.map star * γ * uᵀ)
          = u.map star * γ * (uᵀ * u.map star) * γ * uᵀ := by
          simp only [mul_assoc]
      _ = _ := by rw [huu, mul_one, mul_assoc (u.map star), hP]
  have hev : ∀ k, ev k = if k ∈ Finset.univ.filter (fun k => ev k = 1) then 1 else 0 := by
    intro k
    have := congrFun (congrFun hsq k) k
    rw [diagonal_mul_diagonal, diagonal_apply_eq, diagonal_apply_eq] at this
    rcases mul_eq_zero.mp (show ev k * (ev k - 1) = 0 by linear_combination this) with h | h
    · simp [h]
    · have h' : ev k = 1 := by linear_combination h
      simp [h']
  set s := Finset.univ.filter (fun k => ev k = 1)
  have hdiag : diagonal ev = diagonal fun k => if k ∈ s then (1 : ℂ) else 0 := by
    congr 1; funext k; exact hev k
  -- γ = uᵀ D ū
  have hγeq : γ = uᵀ * diagonal (fun k => if k ∈ s then (1 : ℂ) else 0) * u.map star := by
    rw [← hdiag, ← hd]
    calc γ = (uᵀ * u.map star) * γ * (uᵀ * u.map star) := by rw [huu, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  have hcard : s.card = N := by
    have h1 : (diagonal fun k => if k ∈ s then (1 : ℂ) else 0).trace = N := by
      rw [← hdiag, ← hd, trace_mul_comm, ← mul_assoc, huu, one_mul, htr]
    rw [trace_diagonal, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      mul_one] at h1
    exact_mod_cast h1
  refine ⟨star u, Unitary.star_mem hu, s, hcard, ?_⟩
  rw [slaterState, rdm1_modeRotOp (Unitary.star_mem hu), rdm1_single, hγeq]
  congr 2
  ext a b; simp [star_eq_conjTranspose]

end QM.ManyBody
