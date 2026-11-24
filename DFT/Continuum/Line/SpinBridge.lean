/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.SpinStates

/-!
# Spin operators and linear maps

* `Sp_map`, `Sm_map`, `Sz_map`, `S2_map`, `Pc_map`: the spin operators commute with linear maps
  applied componentwise.
* `card_sector_pos`: every sector `S_z = c - N/2` with `c ≤ N` is nonempty.
* `ladder_Sp_gen`, `ladder_Sm_gen`: for a state of definite `S²` and `S_z` and any relabelling-
  invariant bilinear form `B`, `S₊` multiplies `B` by `λ - M(M+1)` and `S₋` by `λ - M(M-1)`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine Function

variable {n : ℕ}

/-! ### Linear maps -/

section maps

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

lemma Sp_map (L : V →ₗ[ℝ] W) (u : SpinC n → V) (s : SpinC n) :
    L (Sp u s) = Sp (fun t => L (u t)) s := by
  simp only [Sp_apply, map_sum]; exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma Sm_map (L : V →ₗ[ℝ] W) (u : SpinC n → V) (s : SpinC n) :
    L (Sm u s) = Sm (fun t => L (u t)) s := by
  simp only [Sm_apply, map_sum]; exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma Sz_map (L : V →ₗ[ℝ] W) (u : SpinC n → V) (s : SpinC n) :
    L (Sz u s) = Sz (fun t => L (u t)) s := by
  simp only [Sz_apply, map_smul]

lemma S2_map (L : V →ₗ[ℝ] W) (u : SpinC n → V) (s : SpinC n) :
    L (S2 u s) = S2 (fun t => L (u t)) s := by
  change L ((1 / 2 : ℝ) • (Sp (Sm u) s + Sm (Sp u) s) + Sz (Sz u) s) =
    (1 / 2 : ℝ) • (Sp (Sm fun t => L (u t)) s + Sm (Sp fun t => L (u t)) s) +
      Sz (Sz fun t => L (u t)) s
  rw [map_add, map_smul, map_add, Sp_map, Sm_map, Sz_map,
    show (fun t => L (Sm u t)) = Sm (fun t => L (u t)) from funext (Sm_map L u),
    show (fun t => L (Sp u t)) = Sp (fun t => L (u t)) from funext (Sp_map L u),
    show (fun t => L (Sz u t)) = Sz (fun t => L (u t)) from funext (Sz_map L u)]

lemma Pc_map (L : V →ₗ[ℝ] W) (c : ℕ) (u : SpinC n → V) (s : SpinC n) :
    L (Pc c u s) = Pc c (fun t => L (u t)) s := by
  simp only [Pc_apply]; split_ifs <;> simp

end maps

lemma card_sector_pos {c : ℕ} (hc : c ≤ n + 1) :
    0 < ((Finset.univ.filter fun s : SpinC n => nup s = c).card : ℝ) := by
  exact_mod_cast Finset.card_pos.2 ⟨sc n c, by simp [nup_sc hc]⟩

/-! ### The ladder -/

section ladderG

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  {u : SpinC n → V} {c : ℕ} (hc : Pc c u = u) {lam : ℝ}
  (hB2 : ∀ s, B (u s) (S2 u s) = lam * B (u s) (u s))

omit [AddCommGroup V] [Module ℝ V] in
lemma B_Sz_sector {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    {u : SpinC n → V} {c : ℕ} (hc : Pc c u = u) (s : SpinC n) (r : ℕ → ℝ) :
    B (u s) (r (nup s) • u s) = r c * B (u s) (u s) := by
  by_cases hs : nup s = c
  · rw [hs, map_smul, smul_eq_mul]
  · have : u s = 0 := by rw [← hc]; simp [Pc_apply, hs]
    simp [this]

include hc hB2

/-- **`S₊` along a multiplet**, for any bilinear form. -/
lemma ladder_Sp_gen :
    ∑ s, B (Sp u s) (Sp u s) =
      (lam - ((c : ℝ) - ((n : ℝ) + 1) / 2) ^ 2 - ((c : ℝ) - ((n : ℝ) + 1) / 2)) *
        ∑ s, B (u s) (u s) := by
  rw [adj_Sp B u (Sp u), Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hS2 := congrArg (fun T : Module.End ℝ (SpinC n → V) => T u s) (S2_eq (n := n) (V := V))
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply] at hS2
  have hSm : Sm (Sp u) s = S2 u s - Sz (Sz u) s - Sz u s := by rw [hS2]; abel
  rw [hSm, map_sub, map_sub, hB2]
  have h1 : Sz (Sz u) s = (fun k : ℕ => ((k : ℝ) - ((n : ℝ) + 1) / 2) ^ 2) (nup s) • u s := by
    simp only [Sz_apply, smul_smul, Mz]; congr 1; ring
  have h2 : Sz u s = (fun k : ℕ => (k : ℝ) - ((n : ℝ) + 1) / 2) (nup s) • u s := by
    simp only [Sz_apply, Mz]
  rw [h1, h2, B_Sz_sector B hc s (fun k : ℕ => ((k : ℝ) - ((n : ℝ) + 1) / 2) ^ 2),
    B_Sz_sector B hc s (fun k : ℕ => (k : ℝ) - ((n : ℝ) + 1) / 2)]
  ring

/-- **`S₋` along a multiplet**, for any symmetric bilinear form. -/
lemma ladder_Sm_gen (hBs : ∀ f g, B f g = B g f) :
    ∑ s, B (Sm u s) (Sm u s) =
      (lam - ((c : ℝ) - ((n : ℝ) + 1) / 2) ^ 2 + ((c : ℝ) - ((n : ℝ) + 1) / 2)) *
        ∑ s, B (u s) (u s) := by
  rw [← adj_Sp B (Sm u) u, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hBs]
  have hS2 := congrArg (fun T : Module.End ℝ (SpinC n → V) => T u s) (S2_eq (n := n) (V := V))
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply] at hS2
  have hc2 := congrFun (comm_Sp_Sm (n := n) (V := V) u) s
  simp only [Pi.sub_apply, Pi.smul_apply] at hc2
  have hSm' : Sm (Sp u) s = S2 u s - Sz (Sz u) s - Sz u s := by rw [hS2]; abel
  have hSp : Sp (Sm u) s = S2 u s - Sz (Sz u) s + Sz u s := by
    rw [sub_eq_iff_eq_add.1 hc2, hSm', two_smul]; abel
  rw [hSp, map_add, map_sub, hB2]
  have h1 : Sz (Sz u) s = (fun k : ℕ => ((k : ℝ) - ((n : ℝ) + 1) / 2) ^ 2) (nup s) • u s := by
    simp only [Sz_apply, smul_smul, Mz]; congr 1; ring
  have h2 : Sz u s = (fun k : ℕ => (k : ℝ) - ((n : ℝ) + 1) / 2) (nup s) • u s := by
    simp only [Sz_apply, Mz]
  rw [h1, h2, B_Sz_sector B hc s (fun k : ℕ => ((k : ℝ) - ((n : ℝ) + 1) / 2) ^ 2),
    B_Sz_sector B hc s (fun k : ℕ => (k : ℝ) - ((n : ℝ) + 1) / 2)]
  ring

end ladderG

end DFT.Continuum.Line
