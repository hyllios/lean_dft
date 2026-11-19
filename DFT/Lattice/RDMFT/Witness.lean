/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.RDMFT.Generic

/-!
# An unconditional instance: two fermions on four sites with pair hopping

For two spinless fermions on four sites let `W` be the pair-hopping interaction that moves both
particles to the complementary pair of sites, `W = λ Σ_s |sᶜ⟩⟨s|` with `λ = 240` (`W42`). For this
`W`, the one-body operators `h` whose gapped ground state of `Γ(h) + W` is a Slater determinant (has
idempotent `γ`) lie in a closed, nowhere dense, Lebesgue-null set (`generic_nonidem_W42`).

The hypothesis of `generic_nonidem` is discharged by a witness (`elimPoly_ne_zero_of_eigenbasis`).
At `h = diag a` with `a = (-469/2, 329/2, -7/2, 147/2)` the Hamiltonian splits into three 2 × 2
blocks, `{01, 23}`, `{02, 13}` and `{03, 12}`, with matrices `[[δ, λ], [λ, -δ]]` for
`δ = -70, -238, -161`. Their eigenvectors are rational unit vectors, `(3, 4)/5`, `(5, 12)/13` and
`(8, 15)/17` and their rotations, with the distinct eigenvalues `±250`, `±338`, `±289`. Every
eigenvector has a nonzero Pfaffian `ψ₀₁ψ₂₃ - ψ₀₂ψ₁₃ + ψ₀₃ψ₁₂`, while every Slater determinant has
Pfaffian zero (`pf_slaterSub`, a Plücker relation). Since an idempotent `γ` means a Slater
determinant (`exists_slater_of_idem`), no eigenvector has idempotent `γ`. Each eigenvector also has
nonzero overlap with `u = (1, …, 1)`.

* `c01`, …, `c23`, `cpl`, `W42`, `a42`, `θ42`.
* `pf`, `pf_slaterSub`: the Pfaffian vanishes on Slater determinants.
* `idem_of_eval_idemP_eq_zero`.
* `generic_nonidem_W42`: **the unconditional generic statement for this `W`**.
-/

namespace DFT

namespace Ex42

open Matrix

/-! ### Configurations of two particles on four sites -/

/-- The configuration `{0, 1}`. -/
def c01 : Conf 4 2 := ⟨{0, 1}, by decide⟩
/-- The configuration `{0, 2}`. -/
def c02 : Conf 4 2 := ⟨{0, 2}, by decide⟩
/-- The configuration `{0, 3}`. -/
def c03 : Conf 4 2 := ⟨{0, 3}, by decide⟩
/-- The configuration `{1, 2}`. -/
def c12 : Conf 4 2 := ⟨{1, 2}, by decide⟩
/-- The configuration `{1, 3}`. -/
def c13 : Conf 4 2 := ⟨{1, 3}, by decide⟩
/-- The configuration `{2, 3}`. -/
def c23 : Conf 4 2 := ⟨{2, 3}, by decide⟩

/-- The complementary pair of sites. -/
def cpl (s : Conf 4 2) : Conf 4 2 := ⟨s.1ᶜ, by rw [Finset.card_compl, s.2]; rfl⟩

lemma cpl_cpl (s : Conf 4 2) : cpl (cpl s) = s := Subtype.ext (compl_compl s.1)

lemma eq_cpl_comm {s s' : Conf 4 2} : s' = cpl s ↔ s = cpl s' := by
  constructor
  · rintro rfl; rw [cpl_cpl]
  · rintro rfl; rw [cpl_cpl]

set_option maxRecDepth 4000 in
lemma cases42 (s : Conf 4 2) :
    s = c01 ∨ s = c02 ∨ s = c03 ∨ s = c12 ∨ s = c13 ∨ s = c23 := by
  revert s; decide

lemma univ42 : (Finset.univ : Finset (Conf 4 2)) = {c01, c02, c03, c12, c13, c23} := by decide

lemma cpl_c01 : cpl c01 = c23 := by decide
lemma cpl_c02 : cpl c02 = c13 := by decide
lemma cpl_c03 : cpl c03 = c12 := by decide
lemma cpl_c12 : cpl c12 = c03 := by decide
lemma cpl_c13 : cpl c13 = c02 := by decide
lemma cpl_c23 : cpl c23 = c01 := by decide

/-- A vector on the six configurations. -/
def vec (x01 x02 x03 x12 x13 x23 : ℝ) (s : Conf 4 2) : ℝ :=
  if s = c01 then x01 else if s = c02 then x02 else if s = c03 then x03 else
  if s = c12 then x12 else if s = c13 then x13 else x23

/-! ### The interaction and the witness point -/

/-- Pair hopping to the complementary pair of sites, with strength 240. -/
def W42 : Matrix (Conf 4 2) (Conf 4 2) ℝ := fun s s' => if s' = cpl s then 240 else 0

lemma W42_isSymm : W42.IsSymm := by
  ext s s'
  simp only [Matrix.transpose_apply, W42]
  exact if_congr eq_cpl_comm.symm rfl rfl

/-- The on-site energies of the witness. -/
noncomputable def a42 : Fin 4 → ℝ := ![-469 / 2, 329 / 2, -7 / 2, 147 / 2]

/-- The parameters of the witness, `h = diag a42`. -/
noncomputable def θ42 : Sym2 (Fin 4) → ℝ :=
  Sym2.lift ⟨fun i j => if i = j then a42 i else 0, fun i j => by
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]⟩

lemma symOf_θ42 : symOf θ42 = diagonal a42 := by
  ext i j
  simp [symOf, θ42, Matrix.diagonal_apply]

/-- The diagonal energies `Σ_i a_i n_i`. -/
noncomputable def d42 (s : Conf 4 2) : ℝ := ∑ i, a42 i * occF i s

lemma H42_mulVec (w : Conf 4 2 → ℝ) (s : Conf 4 2) :
    (evalMat (hamRP W42) θ42 *ᵥ w) s = d42 s * w s + 240 * w (cpl s) := by
  rw [evalMat_hamRP, symOf_θ42, hamR, gamma_diagonal, Matrix.add_mulVec, Pi.add_apply,
    Matrix.mulVec_diagonal]
  congr 1
  simp [W42, Matrix.mulVec, dotProduct]

lemma d42_c01 : d42 c01 = -70 := by
  simp [d42, Fin.sum_univ_four, occF, c01, a42]; norm_num
lemma d42_c02 : d42 c02 = -238 := by
  simp [d42, Fin.sum_univ_four, occF, c02, a42]; norm_num
lemma d42_c03 : d42 c03 = -161 := by
  simp [d42, Fin.sum_univ_four, occF, c03, a42]; norm_num
lemma d42_c12 : d42 c12 = 161 := by
  simp [d42, Fin.sum_univ_four, occF, c12, a42]; norm_num
lemma d42_c13 : d42 c13 = 238 := by
  simp [d42, Fin.sum_univ_four, occF, c13, a42]; norm_num
lemma d42_c23 : d42 c23 = 70 := by
  simp [d42, Fin.sum_univ_four, occF, c23, a42]; norm_num

/-- The eigenvectors. -/
noncomputable def ev (b : Conf 4 2) : Conf 4 2 → ℝ :=
  if b = c01 then vec (3 / 5) 0 0 0 0 (4 / 5) else
  if b = c23 then vec (4 / 5) 0 0 0 0 (-3 / 5) else
  if b = c02 then vec 0 (5 / 13) 0 0 (12 / 13) 0 else
  if b = c13 then vec 0 (12 / 13) 0 0 (-5 / 13) 0 else
  if b = c03 then vec 0 0 (8 / 17) (15 / 17) 0 0 else
  vec 0 0 (15 / 17) (-8 / 17) 0 0

/-- The eigenvalues. -/
noncomputable def eval42 : Conf 4 2 → ℝ := vec 250 338 289 (-289) (-338) (-250)

lemma ev_onb (b b' : Conf 4 2) : ∑ x, ev b x * ev b' x = if b = b' then 1 else 0 := by
  rw [univ42]
  rcases cases42 b with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases cases42 b' with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp +decide [ev, vec] <;> norm_num

lemma ev_eigen (b : Conf 4 2) : evalMat (hamRP W42) θ42 *ᵥ ev b = eval42 b • ev b := by
  funext s
  rw [H42_mulVec, Pi.smul_apply, smul_eq_mul]
  rcases cases42 b with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases cases42 s with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp +decide only [cpl_c01, cpl_c02, cpl_c03, cpl_c12, cpl_c13, cpl_c23, d42_c01, d42_c02,
    d42_c03, d42_c12, d42_c13, d42_c23, ev, eval42, vec, ite_true, ite_false] <;> norm_num

lemma eval42_injective : Function.Injective eval42 := by
  intro b b' h
  rcases cases42 b with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases cases42 b' with rfl | rfl | rfl | rfl | rfl | rfl <;>
  first | rfl | (simp +decide [eval42, vec] at h; done) |
    (simp +decide [eval42, vec] at h; norm_num at h)

lemma ev_dot_one (b : Conf 4 2) : ev b ⬝ᵥ (fun _ => (1 : ℝ)) ≠ 0 := by
  simp only [dotProduct, mul_one]
  rw [univ42]
  rcases cases42 b with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp +decide [ev, vec] <;> norm_num

/-! ### The Pfaffian -/

/-- The Pfaffian `ψ₀₁ψ₂₃ - ψ₀₂ψ₁₃ + ψ₀₃ψ₁₂`. -/
def pf (ψ : Conf 4 2 → ℝ) : ℝ := ψ c01 * ψ c23 - ψ c02 * ψ c13 + ψ c03 * ψ c12

lemma pf_smul (c : ℝ) (ψ : Conf 4 2 → ℝ) : pf (c • ψ) = c ^ 2 * pf ψ := by
  simp only [pf, Pi.smul_apply, smul_eq_mul]; ring

/-- The sorted positions of a pair. -/
lemma τs_pair {s : Conf 4 2} {p q : Fin 4} (hs : s.1 = {p, q}) (hpq : p < q) :
    τs s 0 = p ∧ τs s 1 = q := by
  have h0 := τs_mem s 0
  have h1 := τs_mem s 1
  have hlt : τs s 0 < τs s 1 :=
    (Finset.orderEmbOfFin s.1 s.2).strictMono (show (0 : Fin 2) < 1 by decide)
  rw [hs, Finset.mem_insert, Finset.mem_singleton] at h0 h1
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · rw [h0, h1] at hlt; exact absurd hlt (lt_irrefl _)
  · exact ⟨h0, h1⟩
  · rw [h0, h1] at hlt; exact absurd (hlt.trans hpq) (lt_irrefl _)
  · rw [h0, h1] at hlt; exact absurd hlt (lt_irrefl _)

/-- The amplitude of a two-particle Slater determinant on the pair `{p, q}`, `p < q`. -/
lemma slaterSub_pair (φ : Fin 4 → Fin 4 → ℝ) (S : Conf 4 2) {s : Conf 4 2} {p q : Fin 4}
    (hs : s.1 = {p, q}) (hpq : p < q) :
    slaterSub φ S s = φ (τs S 0) p * φ (τs S 1) q - φ (τs S 1) p * φ (τs S 0) q := by
  obtain ⟨h0, h1⟩ := τs_pair hs hpq
  simp only [slaterSub, slaterC, slater, Matrix.det_fin_two, Matrix.of_apply, h0, h1]

/-- **Slater determinants have zero Pfaffian** (the Plücker relation of `Gr(2, 4)`). -/
lemma pf_slaterSub (φ : Fin 4 → Fin 4 → ℝ) (S : Conf 4 2) : pf (slaterSub φ S) = 0 := by
  simp only [pf]
  rw [slaterSub_pair φ S (s := c01) (p := 0) (q := 1) rfl (by decide),
    slaterSub_pair φ S (s := c23) (p := 2) (q := 3) rfl (by decide),
    slaterSub_pair φ S (s := c02) (p := 0) (q := 2) rfl (by decide),
    slaterSub_pair φ S (s := c13) (p := 1) (q := 3) rfl (by decide),
    slaterSub_pair φ S (s := c03) (p := 0) (q := 3) rfl (by decide),
    slaterSub_pair φ S (s := c12) (p := 1) (q := 2) rfl (by decide)]
  ring

lemma pf_ev_ne_zero (b : Conf 4 2) : pf (ev b) ≠ 0 := by
  rcases cases42 b with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp +decide [pf, ev, vec]

end Ex42

open Ex42

/-- A vanishing idempotency polynomial means an idempotent `γ`, for normalised states. -/
lemma idem_of_eval_idemP_eq_zero {M N : ℕ} {ψ : Conf M N → ℝ} (hN : ψ ⬝ᵥ ψ = 1)
    (h : MvPolynomial.eval ψ (idemP (M := M) (N := N)) = 0) : rdm ψ * rdm ψ = rdm ψ := by
  rw [eval_idemP, hN] at h
  ext i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)).mp h i (Finset.mem_univ i)
  have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hi j
    (Finset.mem_univ j)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hij
  linarith

/-- **Interacting ground states are generically not Slater determinants** (unconditional, for
two fermions on four sites with the pair-hopping interaction `W42`). The one-body operators `h`
for which the gapped ground state of `Γ(h) + W42` has idempotent `γ` lie in a closed, nowhere dense,
Lebesgue-null set. -/
theorem generic_nonidem_W42 :
    ∃ Z : Set (Sym2 (Fin 4) → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {θ | ∃ ψ : Conf 4 2 → ℝ, IsGroundState (hamR W42 (symOf θ)) ψ ∧ ψ ⬝ᵥ ψ = 1 ∧
        (∃ g : ℝ, 0 < g ∧ ∀ χ, ψ ⬝ᵥ χ = 0 →
          (qf (hamR W42 (symOf θ)) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (hamR W42 (symOf θ)) χ) ∧
        rdm ψ * rdm ψ = rdm ψ} ⊆ Z := by
  refine generic_nonidem W42_isSymm (u := fun _ => 1) ?_
  refine elimPoly_ne_zero_of_eigenbasis ev_onb θ42 ev_eigen eval42_injective ?_ ev_dot_one
  intro b α hα h
  rw [eval_idemP_smul, mul_eq_zero] at h
  rcases h with h | h
  · exact hα (pow_eq_zero_iff (by norm_num) |>.mp h)
  · have hN : ev b ⬝ᵥ ev b = 1 := by simpa [dotProduct] using ev_onb b b
    obtain ⟨φ, S, c, -, hψ⟩ := exists_slater_of_idem hN (idem_of_eval_idemP_eq_zero hN h)
    apply pf_ev_ne_zero b
    rw [hψ, pf_smul, pf_slaterSub, mul_zero]

end DFT
