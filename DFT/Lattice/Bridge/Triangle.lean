/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.HK.Examples
import DFT.Lattice.Fermions.SecondQuantization

/-!
# Bridge: the hand-typed triangle is the general fermionic Hamiltonian

The two-fermion triangle of `HK.Examples` uses the hand-typed 3 × 3 matrix `H0tri` and occupations
`occ3`. In the basis `cfg` of two-fermion configurations (`01, 02, 12`), the general
second-quantized `H0F ⊤ 1 0` on the complete graph is `H0tri − 4·I` entry by entry (`H0F_triangle`),
and `occ3` is `occF` (`occ3_eq_occF`), so the triangle examples are statements about the physical
model.
-/

namespace DFT

open Matrix

namespace Bridge.Triangle

/-- The three configurations, in the order of `H0tri`. -/
def cfg : Fin 3 → Conf 3 2 := ![⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{1, 2}, by decide⟩]

lemma cfg_bijective : Function.Bijective cfg := by decide

def pos : Fin 3 → Fin 2 → Fin 3 := ![![0, 1], ![0, 2], ![1, 2]]

lemma pos_strictMono (i : Fin 3) : StrictMono (pos i) := by
  fin_cases i <;> (rw [Fin.strictMono_iff_lt_succ]; decide)

lemma τs_cfg (i : Fin 3) : τs (cfg i) = pos i := by
  unfold τs
  have h := Finset.orderEmbOfFin_unique (cfg i).2 (f := pos i)
    (by fin_cases i <;> decide) (pos_strictMono i)
  exact (congrArg (fun f : Fin 2 → Fin 3 => f) h).symm ▸ rfl

theorem H0F_triangle (i j : Fin 3) :
    H0F (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 0) (cfg i) (cfg j) =
      H0tri i j - 4 * (if i = j then 1 else 0) := by
  simp only [H0F, Matrix.add_apply, Matrix.diagonal_apply, Γ, amp, slater, τs_cfg]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, Matrix.det_fin_two, Function.update, Matrix.smul_apply,
      pos, cfg, H0tri]

/-- The hand-typed occupations are Lean's general occupations `occF` on the same configurations. -/
theorem occ3_eq_occF (i : Fin 3) (c : Fin 3) : occ3 i c = occF i (cfg c) := by
  fin_cases i <;> fin_cases c <;> simp [occ3, occF, cfg]

end Bridge.Triangle

end DFT
