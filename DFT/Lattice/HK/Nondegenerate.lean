/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.HK.Gap
import DFT.Lattice.HK.Examples
import DFT.Lattice.HK.SquareWall
import DFT.Lattice.Basic.SingleParticle

/-!
# The counterexamples to strong Hohenberg–Kohn have non-degenerate ground states

The theorems `hk_fails_square`, `hk_fails_triangle` and `hk_fails_frustrated` exhibit one ground
state shared by two potentials that differ by more than a constant. The square and the two-fermion
triangle are the examples of Penz and van Leeuwen (PvL, J. Chem. Phys. 155, 244111 (2021),
Sec. III C: the square's state `Ψ_A` of Eq. (48) with `s = 3/4`; the triangle of Eqs. (42)–(43)).
PvL already state that these shared ground states are non-degenerate and give the two lowest
energies in closed form. New here is the formal proof: each shared ground state is
**non-degenerate** (every ground state is a multiple of it), with an explicit lower bound on the gap
in the variational form of `unique_of_gap` (the minimum of the Rayleigh quotient on the orthogonal
complement of the ground state, minus the ground energy).

Conventions: `H0sq` and `H0tri` are the kinetic matrices (unit hopping) plus `4·I`, as in PvL
Eqs. (42) and (46). Dropping the `4·I` lowers every energy by 4 (the square's ground energy `3/2`
becomes `−5/2`); gaps and non-degeneracy are unaffected.

For the square the gap is pinned down: exactly `1/2` at `v = (3/4, −3/4, −3/4, 3/4)`, and in
`[0.2635, 0.264)` at `v = (5/4, −1/4, −5/4, 1/4)`, so that it rounds to `0.264`. Its exact value
`5/2 − √5 ≈ 0.26393` follows from PvL's `E_B − E_A` (Eqs. (48)–(49)); it is not formalized.

* `eq_smul_of_gap`: `unique_of_gap` for a ground state that is not normalized.
* `square_energy₀`, `square_energy₁`: the ground energy `3/2` of the square at both potentials.
* `square_gap₀`, `square_gap₁`, `triangle_gap₁`, `triangle_gap₂`, `frustrated_gap₀`,
  `frustrated_gap₁`: the gap bounds, with exact sum-of-squares certificates
  (`scripts/gen_nondegenerate.py`).
* `square_gap₀_sharp`: the bound `1/2` is attained; `square_gap₁_lt`: the second gap is below
  `0.264`.
* `H0tri_isSymm`, `frustrated_ground₀`, `frustrated_ground₁`: auxiliary facts.
* `hk_fails_square_nondeg`, `hk_fails_triangle_nondeg`, `hk_fails_frustrated_nondeg`: the three
  counterexamples with the non-degeneracy of the shared ground state in the statement.
-/

namespace DFT

section
open Matrix

variable {C : Type*} [Fintype C]

/-- A ground state with a gap `g > 0` in the variational sense (every vector orthogonal to `ψ` has
Rayleigh quotient at least the energy of `ψ` plus `g`) is non-degenerate: every ground state is a
multiple of it. Same as `unique_of_gap`, without normalizing `ψ`. -/
theorem eq_smul_of_gap {H : Matrix C C ℝ} (hS : H.IsSymm) {ψ : C → ℝ} (hψ : IsGroundState H ψ)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf H ψ / (ψ ⬝ᵥ ψ) + g) * (χ ⬝ᵥ χ) ≤ qf H χ)
    {φ : C → ℝ} (hφ : IsGroundState H φ) : φ = ((ψ ⬝ᵥ φ) / (ψ ⬝ᵥ ψ)) • ψ := by
  classical
  set s := ψ ⬝ᵥ ψ with hs
  have hspos : 0 < s :=
    lt_of_le_of_ne (dot_self_nonneg ψ) (fun h => hψ.1 (dotProduct_self_eq_zero.mp h.symm))
  set E := qf H ψ / s with hEdef
  have hE : H *ᵥ ψ = E • ψ := isGroundState_eigen hS hψ
  have hqψ : qf H ψ = E * s := by rw [hEdef]; field_simp
  set a := (ψ ⬝ᵥ φ) / s with ha
  set χ := φ - a • ψ with hχ
  have hφχ : φ = a • ψ + χ := by rw [hχ]; abel
  have h0 : ψ ⬝ᵥ χ = 0 := by
    rw [hχ, dotProduct_sub, dotProduct_smul, smul_eq_mul, ha, ← hs]; field_simp; ring
  have hsym : ψ ⬝ᵥ (H *ᵥ χ) = (H *ᵥ ψ) ⬝ᵥ χ := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hS.eq]
  have hχψ : χ ⬝ᵥ (H *ᵥ ψ) = 0 := by rw [hE, dotProduct_smul, dotProduct_comm, h0, smul_zero]
  have hψχ : ψ ⬝ᵥ (H *ᵥ χ) = 0 := by rw [hsym, hE, smul_dotProduct, h0, smul_zero]
  have hnorm : φ ⬝ᵥ φ = a ^ 2 * s + χ ⬝ᵥ χ := by
    rw [hφχ]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, h0,
      dotProduct_comm χ ψ, ← hs]
    ring
  have hq : qf H φ = a ^ 2 * qf H ψ + qf H χ := by
    have hqd : qf H ψ = ψ ⬝ᵥ (H *ᵥ ψ) := rfl
    unfold qf
    rw [hφχ]
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hχψ, hψχ, ← hqd]
    ring
  have h1 := hφ.2 ψ
  have h2 := hgap χ h0
  rw [hq, hnorm, hqψ, ← hs] at h1
  have hc0 := dot_self_nonneg χ
  -- h1: (a² E s + qf χ) s ≤ E s (a² s + χ·χ), i.e. qf χ ≤ E χ·χ; with h2 this forces χ·χ ≤ 0
  have hle : qf H χ * s ≤ E * (χ ⬝ᵥ χ) * s := by nlinarith
  have hle' : qf H χ ≤ E * (χ ⬝ᵥ χ) := le_of_mul_le_mul_right hle hspos
  have hcc : χ ⬝ᵥ χ = 0 := by nlinarith
  have hχ0 : χ = 0 := dotProduct_self_eq_zero.mp hcc
  rw [hχ, sub_eq_zero] at hχ0
  exact hχ0

/-- `H0tri` is symmetric. -/
lemma H0tri_isSymm : H0tri.IsSymm := by
  unfold Matrix.IsSymm; ext i j; fin_cases i <;> fin_cases j <;> simp [H0tri]

/-! ### Two fermions on the square (Penz–van Leeuwen, Eq. (48), `Ψ_A` with `s = 3/4`) -/

/-- The energy (Rayleigh quotient) of `(0,2,1,4,2,0)` at `v = (3/4, −3/4, −3/4, 3/4)` is
`3/2` (`−5/2` without the `4·I` of `H0sq`). -/
theorem square_energy₀ :
    qf (hamN H0sq occ4 ![3/4, -3/4, -3/4, 3/4]) ![0, 2, 1, 4, 2, 0] /
      (![0, 2, 1, 4, 2, 0] ⬝ᵥ ![0, 2, 1, 4, 2, 0]) = 3 / 2 := by
  rw [qf_sq]; simp [dotProduct, Fin.sum_univ_succ]; norm_num

/-- The energy (Rayleigh quotient) of `(0,2,1,4,2,0)` at `v = (5/4, −1/4, −5/4, 1/4)` is
`3/2` (`−5/2` without the `4·I` of `H0sq`). -/
theorem square_energy₁ :
    qf (hamN H0sq occ4 ![5/4, -1/4, -5/4, 1/4]) ![0, 2, 1, 4, 2, 0] /
      (![0, 2, 1, 4, 2, 0] ⬝ᵥ ![0, 2, 1, 4, 2, 0]) = 3 / 2 := by
  rw [qf_sq]; simp [dotProduct, Fin.sum_univ_succ]; norm_num

/-- At `v = (3/4, −3/4, −3/4, 3/4)` the ground state `(0,2,1,4,2,0)` has gap `≥ 1/2`. -/
theorem square_gap₀ : ∀ φ : Fin 6 → ℝ, ![0, 2, 1, 4, 2, 0] ⬝ᵥ φ = 0 →
    (qf (hamN H0sq occ4 ![3/4, -3/4, -3/4, 3/4]) ![0, 2, 1, 4, 2, 0] /
        (![0, 2, 1, 4, 2, 0] ⬝ᵥ ![0, 2, 1, 4, 2, 0]) + 1 / 2) * (φ ⬝ᵥ φ) ≤
      qf (hamN H0sq occ4 ![3/4, -3/4, -3/4, 3/4]) φ := by
  intro φ h0
  have h0' : 2 * φ 1 + φ 2 + 4 * φ 3 + 2 * φ 4 = 0 := by
    have := h0; simp [dotProduct, Fin.sum_univ_succ] at this; linarith
  rw [qf_sq, qf_sq]
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [mul_self_eq_zero.mpr h0',
    mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg (1 * φ 0 + (-1/2) * φ 1 + (1/2) * φ 4)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (83/50))
      (sq_nonneg (1 * φ 1 + (-46/83) * φ 2 + (-34/83) * φ 3 + (33/83) * φ 4 + (50/83) * φ 5)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (503/166))
      (sq_nonneg (1 * φ 2 + (-36/503) * φ 3 + (-92/503) * φ 4 + (92/503) * φ 5)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (851/1006))
      (sq_nonneg (1 * φ 3 + (-452/851) * φ 4 + (452/851) * φ 5)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (900/851)) (sq_nonneg (1 * φ 4 + (-1) * φ 5))]

/-- The gap `1/2` at `v = (3/4, −3/4, −3/4, 3/4)` is attained: `(−1,−1,0,0,1,1)` is orthogonal to
the ground state and has energy `3/2 + 1/2 = 2` (with `square_energy₀`, the gap is exactly
`1/2`). -/
theorem square_gap₀_sharp :
    ![0, 2, 1, 4, 2, 0] ⬝ᵥ ![-1, -1, 0, 0, 1, 1] = 0 ∧
      qf (hamN H0sq occ4 ![3/4, -3/4, -3/4, 3/4]) ![-1, -1, 0, 0, 1, 1] =
        (3 / 2 + 1 / 2) * (![-1, -1, 0, 0, 1, 1] ⬝ᵥ ![-1, -1, 0, 0, 1, 1]) := by
  constructor
  · simp [dotProduct, Fin.sum_univ_succ]
  · rw [qf_sq]; simp [dotProduct, Fin.sum_univ_succ]; norm_num

/-- At `v = (5/4, −1/4, −5/4, 1/4)` the ground state `(0,2,1,4,2,0)` has gap `≥ 0.2635` (the exact
gap `5/2 − √5 ≈ 0.26393` follows from PvL Eqs. (48)–(49); not formalized). -/
theorem square_gap₁ : ∀ φ : Fin 6 → ℝ, ![0, 2, 1, 4, 2, 0] ⬝ᵥ φ = 0 →
    (qf (hamN H0sq occ4 ![5/4, -1/4, -5/4, 1/4]) ![0, 2, 1, 4, 2, 0] /
        (![0, 2, 1, 4, 2, 0] ⬝ᵥ ![0, 2, 1, 4, 2, 0]) + 527 / 2000) * (φ ⬝ᵥ φ) ≤
      qf (hamN H0sq occ4 ![5/4, -1/4, -5/4, 1/4]) φ := by
  intro φ h0
  have h0' : 2 * φ 1 + φ 2 + 4 * φ 3 + 2 * φ 4 = 0 := by
    have := h0; simp [dotProduct, Fin.sum_univ_succ] at this; linarith
  rw [qf_sq, qf_sq]
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [mul_self_eq_zero.mpr h0',
    mul_nonneg (by norm_num : (0:ℝ) ≤ (6473/2000))
      (sq_nonneg (1 * φ 0 + (-2000/6473) * φ 1 + (2000/6473) * φ 4)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (27025089/12946000))
      (sq_nonneg (1 * φ 1 + (-11910320/27025089) * φ 2 + (-8803280/27025089) * φ 3 +
        (6071360/27025089) * φ 4 + (12946000/27025089) * φ 5)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (182205508417/54050178000))
      (sq_nonneg (1 * φ 2 + (-7550006720/182205508417) * φ 3 + (-38554861360/182205508417) * φ 4 +
        (23820640000/182205508417) * φ 5)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (418783141664001/364411016834000))
      (sq_nonneg (1 * φ 3 + (-22544536105680/46531460184889) * φ 4 +
        (13928860320000/46531460184889) * φ 5)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (145314180034704177/93062920369778000))
      (sq_nonneg (1 * φ 4 + (-12946000/20953729) * φ 5)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (34571817/41907458000)) (sq_nonneg (1 * φ 5))]

/-- The gap at `v = (5/4, −1/4, −5/4, 1/4)` is below `0.264`: the vector `(191,309,0,0,−309,−500)`
is orthogonal to the ground state and has energy below `3/2 + 0.264`. With `square_gap₁` and
`square_energy₁`, the gap lies in `[0.2635, 0.264)` and rounds to `0.264`. -/
theorem square_gap₁_lt :
    ![0, 2, 1, 4, 2, 0] ⬝ᵥ ![191, 309, 0, 0, -309, -500] = 0 ∧
      qf (hamN H0sq occ4 ![5/4, -1/4, -5/4, 1/4]) ![191, 309, 0, 0, -309, -500] <
        (3 / 2 + 264 / 1000) *
          (![191, 309, 0, 0, -309, -500] ⬝ᵥ ![191, 309, 0, 0, -309, -500]) := by
  constructor
  · simp [dotProduct, Fin.sum_univ_succ]
  · rw [qf_sq]; simp [dotProduct, Fin.sum_univ_succ]; norm_num

/-- **The square counterexample of Penz and van Leeuwen, with non-degeneracy in the statement**
(stated by PvL, Sec. III C; formal proof here). Two fermions on
the square: the potentials `(3/4, −3/4, −3/4, 3/4)` and `(5/4, −1/4, −5/4, 1/4)`, which differ by
more than a constant, share the ground state `(0,2,1,4,2,0)`, and it is the only ground state of
each (up to scale). -/
theorem hk_fails_square_nondeg :
    IsGroundState (hamN H0sq occ4 ![3/4, -3/4, -3/4, 3/4]) ![0, 2, 1, 4, 2, 0] ∧
    IsGroundState (hamN H0sq occ4 ![5/4, -1/4, -5/4, 1/4]) ![0, 2, 1, 4, 2, 0] ∧
    (¬ ∃ k : ℝ, ∀ i, (![3/4, -3/4, -3/4, 3/4] : Fin 4 → ℝ) i -
        (![5/4, -1/4, -5/4, 1/4] : Fin 4 → ℝ) i = k) ∧
    (∀ φ, IsGroundState (hamN H0sq occ4 ![3/4, -3/4, -3/4, 3/4]) φ →
      ∃ a : ℝ, φ = a • ![0, 2, 1, 4, 2, 0]) ∧
    (∀ φ, IsGroundState (hamN H0sq occ4 ![5/4, -1/4, -5/4, 1/4]) φ →
      ∃ a : ℝ, φ = a • ![0, 2, 1, 4, 2, 0]) := by
  obtain ⟨h0, h1, hne⟩ := hk_fails_square
  exact ⟨h0, h1, hne,
    fun φ hφ => ⟨_, eq_smul_of_gap (hamN_isSymm H0sq_isSymm occ4 _) h0 (by norm_num)
      square_gap₀ hφ⟩,
    fun φ hφ => ⟨_, eq_smul_of_gap (hamN_isSymm H0sq_isSymm occ4 _) h1 (by norm_num)
      square_gap₁ hφ⟩⟩

/-! ### Two fermions on the triangle (Penz–van Leeuwen, Eqs. (42)–(43)) -/

/-- At `v = (0, −1, 0)` the ground state `(1,0,−1)` has gap `≥ 0.58` (the exact gap
`2 − √2` follows from PvL's `E_A`, `E_B`, text after their Eq. (44); not formalized). -/
theorem triangle_gap₁ : ∀ φ : Fin 3 → ℝ, ![1, 0, -1] ⬝ᵥ φ = 0 →
    (qf (hamN H0tri occ3 ![0, -1, 0]) ![1, 0, -1] / (![1, 0, -1] ⬝ᵥ ![1, 0, -1]) + 29 / 50) *
        (φ ⬝ᵥ φ) ≤ qf (hamN H0tri occ3 ![0, -1, 0]) φ := by
  intro φ h0
  have h0' : φ 0 - φ 2 = 0 := by
    have := h0; simp [dotProduct, Fin.sum_univ_succ] at this; linarith
  rw [qf_tri, qf_tri]
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [mul_self_eq_zero.mpr h0',
    mul_nonneg (by norm_num : (0:ℝ) ≤ (23/25))
      (sq_nonneg (1 * φ 0 + (-25/23) * φ 1 + (25/46) * φ 2)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (383/1150)) (sq_nonneg (1 * φ 1 + (-525/383) * φ 2)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (861/38300)) (sq_nonneg (1 * φ 2))]

/-- At `v = (0, −2, 0)` the ground state `(1,0,−1)` has gap `≥ 1` (the exact gap
`1` follows from PvL's `E_A`, `E_B`, text after their Eq. (44); not formalized). -/
theorem triangle_gap₂ : ∀ φ : Fin 3 → ℝ, ![1, 0, -1] ⬝ᵥ φ = 0 →
    (qf (hamN H0tri occ3 ![0, -2, 0]) ![1, 0, -1] / (![1, 0, -1] ⬝ᵥ ![1, 0, -1]) + 1) *
        (φ ⬝ᵥ φ) ≤ qf (hamN H0tri occ3 ![0, -2, 0]) φ := by
  intro φ h0
  have h0' : φ 0 - φ 2 = 0 := by
    have := h0; simp [dotProduct, Fin.sum_univ_succ] at this; linarith
  rw [qf_tri, qf_tri]
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [mul_self_eq_zero.mpr h0',
    mul_nonneg (by norm_num : (0:ℝ) ≤ (1/2)) (sq_nonneg (1 * φ 0 + (-2) * φ 1 + 1 * φ 2))]

/-- **The triangle counterexample of Penz and van Leeuwen, with non-degeneracy in the statement**
(stated by PvL, Sec. III C; formal proof here). Two fermions on
the triangle: the potentials `(0, −1, 0)` and `(0, −2, 0)` share the ground state `(1,0,−1)`, and it
is the only ground state of each (up to scale). -/
theorem hk_fails_triangle_nondeg :
    IsGroundState (hamN H0tri occ3 ![0, -1, 0]) ![1, 0, -1] ∧
    IsGroundState (hamN H0tri occ3 ![0, -2, 0]) ![1, 0, -1] ∧
    (¬ ∃ k : ℝ, ∀ i, (![0, -1, 0] : Fin 3 → ℝ) i - (![0, -2, 0] : Fin 3 → ℝ) i = k) ∧
    (∀ φ, IsGroundState (hamN H0tri occ3 ![0, -1, 0]) φ → ∃ a : ℝ, φ = a • ![1, 0, -1]) ∧
    (∀ φ, IsGroundState (hamN H0tri occ3 ![0, -2, 0]) φ → ∃ a : ℝ, φ = a • ![1, 0, -1]) := by
  obtain ⟨h0, h1, hne⟩ := hk_fails_triangle
  exact ⟨h0, h1, hne,
    fun φ hφ => ⟨_, eq_smul_of_gap (hamN_isSymm H0tri_isSymm occ3 _) h0 (by norm_num)
      triangle_gap₁ hφ⟩,
    fun φ hφ => ⟨_, eq_smul_of_gap (hamN_isSymm H0tri_isSymm occ3 _) h1 (by norm_num)
      triangle_gap₂ hφ⟩⟩

/-! ### One particle on the triangle with frustrated hopping (`t = −1`) -/

/-- `(1,−1,0)` is a ground state of the frustrated triangle at `v = (0,0,1)`. -/
lemma frustrated_ground₀ :
    IsGroundState (ham (⊤ : SimpleGraph (Fin 3)) (-1) ![0, 0, 1]) ![1, -1, 0] := by
  refine ⟨fun h => by simpa using congrFun h 0, fun φ => ?_⟩
  rw [qf_triangle, qf_triangle]
  simp [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (φ 0 + φ 1 + φ 2), sq_nonneg (φ 2)]

/-- `(1,−1,0)` is a ground state of the frustrated triangle at `v = (0,0,2)`. -/
lemma frustrated_ground₁ :
    IsGroundState (ham (⊤ : SimpleGraph (Fin 3)) (-1) ![0, 0, 2]) ![1, -1, 0] := by
  refine ⟨fun h => by simpa using congrFun h 0, fun φ => ?_⟩
  rw [qf_triangle, qf_triangle]
  simp [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (φ 0 + φ 1 + φ 2), sq_nonneg (φ 2)]

/-- At `v = (0,0,1)` the ground state `(1,−1,0)` has gap `≥ 0.58` (exact gap `2 − √2`, from the
exact spectrum computed in `scripts/gen_nondegenerate.py`; not formalized). -/
theorem frustrated_gap₀ : ∀ φ : Fin 3 → ℝ, ![1, -1, 0] ⬝ᵥ φ = 0 →
    (qf (ham (⊤ : SimpleGraph (Fin 3)) (-1) ![0, 0, 1]) ![1, -1, 0] / (![1, -1, 0] ⬝ᵥ ![1, -1, 0]) +
        29 / 50) * (φ ⬝ᵥ φ) ≤ qf (ham (⊤ : SimpleGraph (Fin 3)) (-1) ![0, 0, 1]) φ := by
  intro φ h0
  have h0' : φ 0 - φ 1 = 0 := by
    have := h0; simp [dotProduct, Fin.sum_univ_succ] at this; linarith
  rw [qf_triangle, qf_triangle]
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [mul_self_eq_zero.mpr h0',
    mul_nonneg (by norm_num : (0:ℝ) ≤ (23/25))
      (sq_nonneg (1 * φ 0 + (25/46) * φ 1 + (25/23) * φ 2)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (1491/2300)) (sq_nonneg (1 * φ 1 + (50/71) * φ 2)),
    mul_nonneg (by norm_num : (0:ℝ) ≤ (41/3550)) (sq_nonneg (1 * φ 2))]

/-- At `v = (0,0,2)` the ground state `(1,−1,0)` has gap `≥ 1` (exact gap `1`, from the exact
spectrum computed in `scripts/gen_nondegenerate.py`; not formalized). -/
theorem frustrated_gap₁ : ∀ φ : Fin 3 → ℝ, ![1, -1, 0] ⬝ᵥ φ = 0 →
    (qf (ham (⊤ : SimpleGraph (Fin 3)) (-1) ![0, 0, 2]) ![1, -1, 0] / (![1, -1, 0] ⬝ᵥ ![1, -1, 0]) +
        1) * (φ ⬝ᵥ φ) ≤ qf (ham (⊤ : SimpleGraph (Fin 3)) (-1) ![0, 0, 2]) φ := by
  intro φ h0
  have h0' : φ 0 - φ 1 = 0 := by
    have := h0; simp [dotProduct, Fin.sum_univ_succ] at this; linarith
  rw [qf_triangle, qf_triangle]
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [mul_self_eq_zero.mpr h0',
    mul_nonneg (by norm_num : (0:ℝ) ≤ (1/2)) (sq_nonneg (1 * φ 0 + 1 * φ 1 + 2 * φ 2))]

/-- **The frustrated-hopping counterexample, with non-degeneracy in the statement.** One particle
on the triangle
with `t = −1`: `v = (0,0,1)` and `v' = (0,0,2)` share the ground state `(1,−1,0)`, and it is the
only ground state of each (up to scale). -/
theorem hk_fails_frustrated_nondeg :
    IsGroundState (ham (⊤ : SimpleGraph (Fin 3)) (-1) ![0, 0, 1]) ![1, -1, 0] ∧
    IsGroundState (ham (⊤ : SimpleGraph (Fin 3)) (-1) ![0, 0, 2]) ![1, -1, 0] ∧
    (¬ ∃ k : ℝ, ∀ i, (![0, 0, 1] : Fin 3 → ℝ) i - (![0, 0, 2] : Fin 3 → ℝ) i = k) ∧
    (∀ φ, IsGroundState (ham (⊤ : SimpleGraph (Fin 3)) (-1) ![0, 0, 1]) φ →
      ∃ a : ℝ, φ = a • ![1, -1, 0]) ∧
    (∀ φ, IsGroundState (ham (⊤ : SimpleGraph (Fin 3)) (-1) ![0, 0, 2]) φ →
      ∃ a : ℝ, φ = a • ![1, -1, 0]) := by
  refine ⟨frustrated_ground₀, frustrated_ground₁, ?_,
    fun φ hφ => ⟨_, eq_smul_of_gap (ham_isSymm ⊤ (-1) _) frustrated_ground₀ (by norm_num)
      frustrated_gap₀ hφ⟩,
    fun φ hφ => ⟨_, eq_smul_of_gap (ham_isSymm ⊤ (-1) _) frustrated_ground₁ (by norm_num)
      frustrated_gap₁ hφ⟩⟩
  rintro ⟨k, hk⟩
  have h0 := hk 0; have h2 := hk 2
  simp at h0 h2
  linarith

end

end DFT
