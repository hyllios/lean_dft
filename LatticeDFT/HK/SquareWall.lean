import LatticeDFT.HK.Gap
import LatticeDFT.HK.Examples

/-!
# The Hohenberg–Kohn wall of the two-fermion square

`square_wall`: for every potential with `v₀ + v₂ = v₁ + v₃` and a gapped ground state, a non-constant potential
direction leaves the ground state unchanged. Mechanism: a hidden (non-lattice) involution `Qsq` commutes with
the Hamiltonian exactly on this plane.
-/

namespace LatticeDFT

section
open Matrix

/-! ### The wall of the 2-fermion square
Basis order (see `HK.Examples`): 0:01, 1:02, 2:03, 3:12, 4:13, 5:23.  The hidden involution
Q = swap(02 ↔ 13), +1 on {03, 12}, −1 on {01, 23}.  It is not a lattice symmetry. -/

def Qsq (φ : Fin 6 → ℝ) : Fin 6 → ℝ := ![-φ 0, φ 4, φ 2, φ 3, φ 1, -φ 5]

lemma H0sq_isSymm : H0sq.IsSymm := by
  unfold Matrix.IsSymm; ext i j; fin_cases i <;> fin_cases j <;> simp [H0sq]

lemma qf_Qsq {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3) (φ : Fin 6 → ℝ) :
    qf (hamN H0sq occ4 v) (Qsq φ) = qf (hamN H0sq occ4 v) φ := by
  rw [qf_sq, qf_sq]; simp [Qsq]; linear_combination (φ 4 ^ 2 - φ 1 ^ 2) * hv

lemma dot_Qsq (φ : Fin 6 → ℝ) : Qsq φ ⬝ᵥ Qsq φ = φ ⬝ᵥ φ := by
  simp [Qsq, dotProduct, Fin.sum_univ_succ]; ring

theorem square_wall {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3) {ψ : Fin 6 → ℝ}
    (hψ : IsGroundState (hamN H0sq occ4 v) ψ) (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf (hamN H0sq occ4 v) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (hamN H0sq occ4 v) χ) :
    ∃ w : Fin 4 → ℝ, w 0 ≠ w 2 ∧
      ∀ ε : ℝ, |ε| * 2 ≤ g → IsGroundState (hamN H0sq occ4 (v + ε • w)) ψ := by
  set H := hamN H0sq occ4 v
  have hS : H.IsSymm := hamN_isSymm H0sq_isSymm occ4 v
  -- Qψ is also a ground state, hence a multiple of ψ
  have hQ : IsGroundState H (Qsq ψ) := by
    refine ⟨fun h => hψ.1 ?_, fun φ => ?_⟩
    · have h' : Qsq ψ ⬝ᵥ Qsq ψ = 0 := by rw [h]; simp
      rw [dot_Qsq] at h'; exact dotProduct_self_eq_zero.mp h'
    · rw [qf_Qsq hv, dot_Qsq]; exact hψ.2 φ
  have hc := unique_of_gap hS hψ hN hg hgap hQ
  set c := ψ ⬝ᵥ Qsq ψ
  have e : ∀ i, Qsq ψ i = c * ψ i := fun i => by
    have := congrFun hc i; simpa using this
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5
  simp [Qsq] at e0 e1 e2 e3 e4 e5
  -- c² = 1
  have p0 : (c ^ 2 - 1) * ψ 0 = 0 := by linear_combination (-c + 1) * e0
  have p1 : (c ^ 2 - 1) * ψ 1 = 0 := by linear_combination -e4 - c * e1
  have p2 : (c ^ 2 - 1) * ψ 2 = 0 := by linear_combination (-c - 1) * e2
  have p3 : (c ^ 2 - 1) * ψ 3 = 0 := by linear_combination (-c - 1) * e3
  have p4 : (c ^ 2 - 1) * ψ 4 = 0 := by linear_combination -e1 - c * e4
  have p5 : (c ^ 2 - 1) * ψ 5 = 0 := by linear_combination (-c + 1) * e5
  have hc2 : ∀ i, (c ^ 2 - 1) * ψ i = 0 := by
    intro i; fin_cases i
    exacts [p0, p1, p2, p3, p4, p5]
  have hcc : c ^ 2 = 1 := by
    by_contra hne
    exact hψ.1 (funext fun i => by
      have := hc2 i; rcases mul_eq_zero.mp this with h | h
      · exact absurd (by linarith) hne
      · simpa using h)
  have hc' : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by linear_combination hcc
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hc' with h1 | h1
  · -- sector Q = +1: ψ(01) = ψ(23) = 0; invisible w = (1, 1, -1, -1)
    have z0 : ψ 0 = 0 := by rw [h1] at e0; linarith
    have z5 : ψ 5 = 0 := by rw [h1] at e5; linarith
    refine ⟨![1, 1, -1, -1], by norm_num, fun ε hε => ?_⟩
    refine persist_of_gap H0sq_isSymm hψ hN hgap (κ := 0) (m := 2) ?_ ?_ hε
    · intro c hc; fin_cases c
      · exact absurd z0 hc
      all_goals first | exact absurd z5 hc | simp [occ4, Fin.sum_univ_succ]
    · intro c; fin_cases c <;> norm_num [occ4, Fin.sum_univ_succ]
  · -- sector Q = -1: ψ(03) = ψ(12) = 0; invisible w = (1, -1, -1, 1)
    have z2 : ψ 2 = 0 := by rw [h1] at e2; linarith
    have z3 : ψ 3 = 0 := by rw [h1] at e3; linarith
    refine ⟨![1, -1, -1, 1], by norm_num, fun ε hε => ?_⟩
    refine persist_of_gap H0sq_isSymm hψ hN hgap (κ := 0) (m := 2) ?_ ?_ hε
    · intro c hc; fin_cases c
      all_goals first | exact absurd z2 hc | exact absurd z3 hc | simp [occ4, Fin.sum_univ_succ]
    · intro c; fin_cases c <;> norm_num [occ4, Fin.sum_univ_succ]

end

end LatticeDFT
