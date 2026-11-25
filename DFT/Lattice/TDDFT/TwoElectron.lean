/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import Mathlib.Combinatorics.SimpleGraph.Prod
import DFT.Lattice.Basic.SingleParticle
import DFT.Lattice.TDDFT.Frozen

/-!
# One up and one down electron: total-density HK for every potential

One up and one down electron on a graph `G` is one particle on the product graph `G □ G`: the
configuration `(i↑, j↓)` is the vertex `(i, j)`, a hop moves one of the two electrons (an edge of `G
□ G`), no fermion sign appears, and the total-density potential plus a configuration-diagonal
interaction is the diagonal `v_i + v_j + W(i, j)`. For hopping `t > 0`, `hk_single_particle` on `G □
G` gives total-density Hohenberg–Kohn for **every** potential, on any connected graph and for any
such interaction (not only outside a null set).

* `ham2`, `two_electron_hk`.
* `hubD_eq_ham_box`: the Hubbard dimer `hamN (hubD t U) occD v` is `ham2` on the dimer, entry by
  entry (basis `k = 2a + b ↦ (a, b)`).
-/

namespace DFT

open Matrix

section

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Adjacency in the box product `G □ G` is decidable when adjacency in `G` is. -/
instance boxProdDecRel : DecidableRel (G □ G).Adj :=
  fun _ _ => decidable_of_iff' _ SimpleGraph.boxProd_adj

/-- The two-electron Hamiltonian as a single particle on `G □ G`: hopping `t`, potential `v_i + v_j
+ W(i, j)`. -/
noncomputable def ham2 (t : ℝ) (W : V × V → ℝ) (v : V → ℝ) : Matrix (V × V) (V × V) ℝ :=
  ham (G □ G) t (fun p => v p.1 + v p.2 + W p)

/-- **Total-density HK for one up and one down electron, every potential.** For hopping `t > 0` on a
connected graph and any interaction `W`, a ground state shared by `v` and `v'` forces `v − v'`
constant. -/
theorem two_electron_hk (hG : G.Connected) {t : ℝ} (ht : 0 < t) (W : V × V → ℝ) {v v' : V → ℝ}
    {ψ : V × V → ℝ} (h : IsGroundState (ham2 G t W v) ψ) (h' : IsGroundState (ham2 G t W v') ψ) :
    ∃ c : ℝ, ∀ i, v i - v' i = c := by
  have hbox : (G □ G).Connected := hG.boxProd hG
  obtain ⟨c, hc⟩ := hk_single_particle (G □ G) hbox ht h h' (fun _ => rfl)
  refine ⟨c / 2, fun i => ?_⟩
  have := hc (i, i)
  simp only at this
  linarith

end

/-- The Hubbard dimer in a total-density potential `v`, `hamN (hubD t U) occD v`, is `ham2` on the
dimer with `W = U` on doubly occupied sites and the same `v`, in the basis `k = 2a + b ↦ (a, b)` of
`hubD` (up on `a`, down on `b`). -/
theorem hubD_eq_ham_box (t U : ℝ) (v : Fin 2 → ℝ) (k l : Fin 4) :
    hamN (hubD t U) occD v k l =
      ham2 (⊤ : SimpleGraph (Fin 2)) t (fun p => if p.1 = p.2 then U else 0) v
        (⟨k.val / 2, by omega⟩, ⟨k.val % 2, by omega⟩)
        (⟨l.val / 2, by omega⟩, ⟨l.val % 2, by omega⟩) := by
  fin_cases k <;> fin_cases l <;>
    simp [hamN, hubD, occD, ham2, ham, SimpleGraph.adjMatrix_apply,
      SimpleGraph.boxProd_adj, Fin.sum_univ_two] <;> ring

end DFT
