/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.LinearAlgebra.TensorProduct.Map
import QM.AngularMomentum.SpinRep

/-!
# Coupling of two angular momenta

If `L` and `S` satisfy the su(2) relations and commute with each other, `J = L + S` satisfies them
too, and `J² = L² + S² + 2 L·S` with `L·S = ½ (L₊S₋ + L₋S₊) + L_z S_z` (`IsSU2.add`,
`IsSU2.add_S2`). This applies to `L ⊗ 1 + 1 ⊗ S` on a tensor product (`IsSU2.tensor`).

## Main results

* `IsSU2.add`, `IsSU2.add_S2`: coupling of commuting angular momenta.
* `IsSU2.rTensor`, `IsSU2.lTensor`, `IsSU2.tensor`, `IsSU2.tensor_S2`: the tensor product.
-/

namespace QM

open Module TensorProduct

variable {K : Type*} [Field K]

section Add

variable {V : Type*} [AddCommGroup V] [Module K V] {Lp Lm Lz Sp Sm Sz : End K V}

/-- `L` and `S` commute: every component of `L` commutes with every component of `S`. -/
structure Commutes (Lp Lm Lz Sp Sm Sz : End K V) : Prop where
  pp : Lp * Sp = Sp * Lp
  pm : Lp * Sm = Sm * Lp
  pz : Lp * Sz = Sz * Lp
  mp : Lm * Sp = Sp * Lm
  mm : Lm * Sm = Sm * Lm
  mz : Lm * Sz = Sz * Lm
  zp : Lz * Sp = Sp * Lz
  zm : Lz * Sm = Sm * Lz
  zz : Lz * Sz = Sz * Lz

/-- **Coupling**: `J = L + S` satisfies the su(2) relations. -/
theorem IsSU2.add (hL : IsSU2 Lp Lm Lz) (hS : IsSU2 Sp Sm Sz)
    (hc : Commutes Lp Lm Lz Sp Sm Sz) : IsSU2 (Lp + Sp) (Lm + Sm) (Lz + Sz) where
  comm_pm := by
    have e : (Lp + Sp) * (Lm + Sm) - (Lm + Sm) * (Lp + Sp) =
        (Lp * Lm - Lm * Lp) + (Sp * Sm - Sm * Sp) := by
      simp only [add_mul, mul_add, hc.pm, hc.mp]; abel
    rw [e, hL.comm_pm, hS.comm_pm, smul_add]
  comm_zp := by
    have e : (Lz + Sz) * (Lp + Sp) - (Lp + Sp) * (Lz + Sz) =
        (Lz * Lp - Lp * Lz) + (Sz * Sp - Sp * Sz) := by
      simp only [add_mul, mul_add, hc.zp, hc.pz]; abel
    rw [e, hL.comm_zp, hS.comm_zp]
  comm_zm := by
    have e : (Lz + Sz) * (Lm + Sm) - (Lm + Sm) * (Lz + Sz) =
        (Lz * Lm - Lm * Lz) + (Sz * Sm - Sm * Sz) := by
      simp only [add_mul, mul_add, hc.zm, hc.mz]; abel
    rw [e, hL.comm_zm, hS.comm_zm, neg_add]

/-- The spin–orbit operator `L·S = ½ (L₊S₋ + L₋S₊) + L_z S_z`. -/
def spinOrbit (Lp Lm Lz Sp Sm Sz : End K V) : End K V :=
  (1 / 2 : K) • (Lp * Sm + Lm * Sp) + Lz * Sz

/-- **`J² = L² + S² + 2 L·S`.** -/
theorem IsSU2.add_S2 [CharZero K] (hL : IsSU2 Lp Lm Lz) (hS : IsSU2 Sp Sm Sz)
    (hc : Commutes Lp Lm Lz Sp Sm Sz) :
    (hL.add hS hc).S2 = hL.S2 + hS.S2 + (2 : K) • spinOrbit Lp Lm Lz Sp Sm Sz := by
  simp only [IsSU2.S2, spinOrbit, smul_add, smul_smul]
  norm_num
  simp only [add_mul, mul_add, two_smul, ← hc.zz, hc.pm]
  abel

end Add

section Tensor

variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

lemma rTensor_sub' (f g : End K V) : (f - g).rTensor W = f.rTensor W - g.rTensor W := by
  rw [sub_eq_add_neg, LinearMap.rTensor_add, LinearMap.rTensor_neg, ← sub_eq_add_neg]

lemma lTensor_sub' (f g : End K W) : (f - g).lTensor V = f.lTensor V - g.lTensor V := by
  rw [sub_eq_add_neg, LinearMap.lTensor_add, LinearMap.lTensor_neg, ← sub_eq_add_neg]

/-- `L ⊗ 1` satisfies the su(2) relations. -/
theorem IsSU2.rTensor {Lp Lm Lz : End K V} (hL : IsSU2 Lp Lm Lz) :
    IsSU2 (Lp.rTensor W) (Lm.rTensor W) (Lz.rTensor W) where
  comm_pm := by
    rw [← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, ← rTensor_sub', hL.comm_pm,
      LinearMap.rTensor_smul]
  comm_zp := by
    rw [← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, ← rTensor_sub', hL.comm_zp]
  comm_zm := by
    rw [← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, ← rTensor_sub', hL.comm_zm,
      LinearMap.rTensor_neg]

/-- `1 ⊗ S` satisfies the su(2) relations. -/
theorem IsSU2.lTensor {Sp Sm Sz : End K W} (hS : IsSU2 Sp Sm Sz) :
    IsSU2 (Sp.lTensor V) (Sm.lTensor V) (Sz.lTensor V) where
  comm_pm := by
    rw [← LinearMap.lTensor_mul, ← LinearMap.lTensor_mul, ← lTensor_sub', hS.comm_pm,
      LinearMap.lTensor_smul]
  comm_zp := by
    rw [← LinearMap.lTensor_mul, ← LinearMap.lTensor_mul, ← lTensor_sub', hS.comm_zp]
  comm_zm := by
    rw [← LinearMap.lTensor_mul, ← LinearMap.lTensor_mul, ← lTensor_sub', hS.comm_zm,
      LinearMap.lTensor_neg]

lemma rTensor_mul_lTensor (f : End K V) (g : End K W) :
    f.rTensor W * g.lTensor V = g.lTensor V * f.rTensor W := by
  change f.rTensor W ∘ₗ g.lTensor V = g.lTensor V ∘ₗ f.rTensor W
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

lemma commutes_tensor (Lp Lm Lz : End K V) (Sp Sm Sz : End K W) :
    Commutes (Lp.rTensor W) (Lm.rTensor W) (Lz.rTensor W)
      (Sp.lTensor V) (Sm.lTensor V) (Sz.lTensor V) :=
  ⟨rTensor_mul_lTensor _ _, rTensor_mul_lTensor _ _, rTensor_mul_lTensor _ _,
    rTensor_mul_lTensor _ _, rTensor_mul_lTensor _ _, rTensor_mul_lTensor _ _,
    rTensor_mul_lTensor _ _, rTensor_mul_lTensor _ _, rTensor_mul_lTensor _ _⟩

/-- **Coupling on a tensor product**: `J = L ⊗ 1 + 1 ⊗ S` satisfies the su(2) relations. -/
theorem IsSU2.tensor {Lp Lm Lz : End K V} {Sp Sm Sz : End K W} (hL : IsSU2 Lp Lm Lz)
    (hS : IsSU2 Sp Sm Sz) :
    IsSU2 (Lp.rTensor W + Sp.lTensor V) (Lm.rTensor W + Sm.lTensor V)
      (Lz.rTensor W + Sz.lTensor V) :=
  hL.rTensor.add hS.lTensor (commutes_tensor _ _ _ _ _ _)

/-- **`J² = L² ⊗ 1 + 1 ⊗ S² + 2 L·S`** on a tensor product. -/
theorem IsSU2.tensor_S2 [CharZero K] {Lp Lm Lz : End K V} {Sp Sm Sz : End K W} (hL : IsSU2 Lp Lm Lz)
    (hS : IsSU2 Sp Sm Sz) :
    (hL.tensor hS).S2 = hL.S2.rTensor W + hS.S2.lTensor V +
      (2 : K) • spinOrbit (Lp.rTensor W) (Lm.rTensor W) (Lz.rTensor W)
        (Sp.lTensor V) (Sm.lTensor V) (Sz.lTensor V) := by
  have h := hL.rTensor.add_S2 hS.lTensor (commutes_tensor Lp Lm Lz Sp Sm Sz)
  have e1 : (hL.rTensor (W := W)).S2 = hL.S2.rTensor W := by
    simp only [IsSU2.S2, LinearMap.rTensor_add, LinearMap.rTensor_mul]
  have e2 : (hS.lTensor (V := V)).S2 = hS.S2.lTensor V := by
    simp only [IsSU2.S2, LinearMap.lTensor_add, LinearMap.lTensor_mul]
  rw [← e1, ← e2]
  exact h

end Tensor

end QM
