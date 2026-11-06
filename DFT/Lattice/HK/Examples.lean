/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.HK.Basic

/-!
# Counterexamples to the Hohenberg–Kohn theorem on lattices

Two spinless fermions on a triangle (`hk_fails_triangle`) and on a square (`hk_fails_square`):
non-degenerate ground states with fractional densities that are shared by potentials differing by
more than a constant (cf. Penz & van Leeuwen, J. Chem. Phys. 155, 244111 (2021)).
-/

namespace DFT

section
open Matrix Finset

/-! ### Counterexample: two spinless fermions on a triangle (PvL Sect. III.3, Eq. 42)
Configurations (basis) c = {12, 13, 23}; n_i(c) = occupation of site i. H0 = 4·I +
[[0,−1,1],[−1,0,−1],[1,−1,0]]. With v = (0,−t,0), t > 0, the state (1,0,−1) is the ground state
(energy 3 − t): ⟨φ,Hφ⟩ − (3−t)|φ|² = (φ₀ − φ₁ + φ₂)² + t φ₁². It never puts particles on {1,3}, so
site 2 is always occupied and its potential is invisible. -/

/-- occupation n i c: rows = sites 1,2,3; columns = configurations {12},{13},{23} -/
def occ3 : Fin 3 → Fin 3 → ℝ := ![![1, 1, 0], ![1, 0, 1], ![0, 1, 1]]

def H0tri : Matrix (Fin 3) (Fin 3) ℝ := !![4, -1, 1; -1, 4, -1; 1, -1, 4]

lemma qf_tri (t : ℝ) (φ : Fin 3 → ℝ) :
    qf (hamN H0tri occ3 ![0, -t, 0]) φ =
      (4 - t) * φ 0 ^ 2 + 4 * φ 1 ^ 2 + (4 - t) * φ 2 ^ 2
        - 2 * φ 0 * φ 1 + 2 * φ 0 * φ 2 - 2 * φ 1 * φ 2 := by
  rw [qf_hamN]
  simp [qf, dens, H0tri, occ3, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

lemma ground_tri {t : ℝ} (ht : 0 < t) : IsGroundState
    (hamN H0tri occ3 ![0, -t, 0]) ![1, 0, -1] := by
  refine ⟨fun h => by simpa using congrFun h 0, fun φ => ?_⟩
  rw [qf_tri, qf_tri]
  simp [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (φ 0 - φ 1 + φ 2), sq_nonneg (φ 1), mul_nonneg ht.le (sq_nonneg (φ 1))]

/-- Strong HK fails: two non-equivalent potentials with the same (non-degenerate) ground state. -/
theorem hk_fails_triangle :
    IsGroundState (hamN H0tri occ3 ![0, -1, 0]) ![1, 0, -1] ∧
    IsGroundState (hamN H0tri occ3 ![0, -2, 0]) ![1, 0, -1] ∧
    ¬ ∃ k : ℝ, ∀ i, (![0, -1, 0] : Fin 3 → ℝ) i - (![0, -2, 0] : Fin 3 → ℝ) i = k := by
  refine ⟨ground_tri one_pos, ground_tri two_pos, ?_⟩
  rintro ⟨k, hk⟩
  have h0 := hk 0; have h1 := hk 1
  simp at h0 h1
  linarith

/-! ### Counterexample 2 (PvL Sect. III.3, Eqs. 45–51): two spinless fermions on a square.
Sites 0–1–2–3–0, hopping −1; basis {01, 02, 03, 12, 13, 23}. Potentials v(t) = (s+t, −s+t, −s−t,
s−t), s = 3/4. For |t| < s the ground state is Ψ_A ∝ (0, 2, 1, 4, 2, 0), energy 3/2, NON-DEGENERATE,
density (1,4,4,1)/5: no empty and no full site. Yet t = 0 and t = 1/2 give the same ground state: HK
fails non-trivially. Ground-state proofs via exact sum-of-squares (LDLᵀ) certificates of H − 3/2
(one zero pivot = the ground state). -/

def occ4 : Fin 4 → Fin 6 → ℝ :=
    ![![1, 1, 1, 0, 0, 0], ![1, 0, 0, 1, 1, 0], ![0, 1, 0, 1, 0, 1], ![0, 0, 1, 0, 1, 1]]

def H0sq : Matrix (Fin 6) (Fin 6) ℝ :=
    !![4, -1, 0, 0, 1, 0; -1, 4, -1, -1, 0, 1; 0, -1, 4, 0, -1, 0; 0, -1, 0, 4, -1, 0; 1, 0, -1, -1,
    4, -1; 0, 1, 0, 0, -1, 4]

lemma qf_sq (v : Fin 4 → ℝ) (φ : Fin 6 → ℝ) :
    qf (hamN H0sq occ4 v) φ =
        φ 0^2*v 0 + φ 0^2*v 1 + 4*φ 0^2 - 2*φ 0*φ 1 + 2*φ 0*φ 4 + φ 1^2*v 0 + φ 1^2*v 2 + 4*φ 1^2 -
        2*φ 1*φ 2 - 2*φ 1*φ 3 + 2*φ 1*φ 5 + φ 2^2*v 0 + φ 2^2*v 3 + 4*φ 2^2 - 2*φ 2*φ 4 +
        φ 3^2*v 1 + φ 3^2*v 2 + 4*φ 3^2 - 2*φ 3*φ 4 + φ 4^2*v 1 + φ 4^2*v 3 + 4*φ 4^2 - 2*φ 4*φ 5 +
        φ 5^2*v 2 + φ 5^2*v 3 + 4*φ 5^2 := by
  rw [qf_hamN]
  simp [qf, dens, H0sq, occ4, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

lemma ground_sq0 : IsGroundState (hamN H0sq occ4 ![3/4, -3/4, -3/4, 3/4]) ![0, 2, 1, 4, 2, 0] := by
  refine ⟨fun h => by simpa using congrFun h 1, fun φ => ?_⟩
  rw [qf_sq, qf_sq]
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (φ 0 - 2*φ 1/5 + 2*φ 4/5),
      sq_nonneg (φ 1 - 10*φ 2/21 - 10*φ 3/21 + 4*φ 4/21 + 10*φ 5/21),
      sq_nonneg (φ 2 - 5*φ 3/37 - 17*φ 4/74 + 5*φ 5/37), sq_nonneg (φ 3 - 2*φ 4 + 20*φ 5/17),
      sq_nonneg (φ 5)]

lemma ground_sq1 : IsGroundState (hamN H0sq occ4 ![5/4, -1/4, -5/4, 1/4]) ![0, 2, 1, 4, 2, 0] := by
  refine ⟨fun h => by simpa using congrFun h 1, fun φ => ?_⟩
  rw [qf_sq, qf_sq]
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (φ 0 - 2*φ 1/7 + 2*φ 4/7),
      sq_nonneg (φ 1 - 14*φ 2/31 - 14*φ 3/31 + 4*φ 4/31 + 14*φ 5/31),
      sq_nonneg (φ 2 - 7*φ 3/55 - 27*φ 4/110 + 7*φ 5/55), sq_nonneg (φ 3 - 2*φ 4 + 28*φ 5/27),
      sq_nonneg (φ 5)]

/-- Non-trivial failure of strong HK: non-degenerate ground state, density strictly between 0 and 1.
-/
theorem hk_fails_square :
    IsGroundState (hamN H0sq occ4 ![3/4, -3/4, -3/4, 3/4]) ![0, 2, 1, 4, 2, 0] ∧
    IsGroundState (hamN H0sq occ4 ![5/4, -1/4, -5/4, 1/4]) ![0, 2, 1, 4, 2, 0] ∧
    ¬ ∃ k : ℝ, ∀ i, (![3/4, -3/4, -3/4, 3/4] : Fin 4 → ℝ) i -
        (![5/4, -1/4, -5/4, 1/4] : Fin 4 → ℝ) i = k := by
  refine ⟨ground_sq0, ground_sq1, ?_⟩
  rintro ⟨k, hk⟩
  have h0 := hk 0; have h2 := hk 2
  simp at h0 h2
  norm_num at h0 h2
  linarith

end

end DFT
