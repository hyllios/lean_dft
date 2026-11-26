/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import QM.Spin.SpinAlg

/-!
# The ladder theorem for su(2)

Let `S₊, S₋, S_z` be linear operators with `[S₊, S₋] = 2 S_z`, `[S_z, S₊] = S₊` and
`[S_z, S₋] = -S₋` (`IsSU2`), over a field of characteristic `0`, and `S² = S₋S₊ + S_z² + S_z`.
A highest-weight vector `v` (`S₊ v = 0`, `S_z v = m v`) generates the ladder `v_k = S₋^k v`, with
`S_z v_k = (m - k) v_k`, `S² v_k = m(m + 1) v_k` and `S₊ v_{k+1} = (k + 1)(2m - k) v_k`. If the
ladder stops, `v_K ≠ 0` and `v_{K+1} = 0`, then `2m = K`: the spin is a half-integer, and
`v_0, …, v_{2m}` span an invariant subspace of dimension `2m + 1`, the spin-`m` irreducible
representation. In finite dimension every ladder stops.

## Main definitions

* `IsSU2 Sp Sm Sz`: the commutation relations of su(2).
* `IsSU2.S2`, `IsSU2.ladder v k = S₋^k v`.

## Main results

* `IsSU2.Sz_ladder`, `IsSU2.Sp_ladder_succ`, `IsSU2.S2_ladder`: the action on the ladder.
* `IsSU2.two_m_eq` (**the spin is a half-integer**): `v_K ≠ 0`, `v_{K+1} = 0` imply `2m = K`.
* `IsSU2.ladder_linearIndependent`, `IsSU2.finrank_span_ladder`: the ladder is a basis of a
  subspace of dimension `2m + 1`, invariant under `S₊, S₋, S_z` (`IsSU2.span_ladder_invariant`).
* `IsSU2.exists_ladder_stop`: in finite dimension every ladder stops.
* `isSU2_spin`: the spin operators of `N` spin-½ particles (`QM/Spin/SpinAlg`) satisfy `IsSU2`.
-/

namespace QM

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The commutation relations of su(2): `[S₊, S₋] = 2 S_z`, `[S_z, S₊] = S₊`, `[S_z, S₋] = -S₋`. -/
structure IsSU2 (Sp Sm Sz : End K V) : Prop where
  comm_pm : Sp * Sm - Sm * Sp = (2 : K) • Sz
  comm_zp : Sz * Sp - Sp * Sz = Sp
  comm_zm : Sz * Sm - Sm * Sz = -Sm

namespace IsSU2

variable {Sp Sm Sz : End K V}

/-- The total spin `S² = S₋S₊ + S_z² + S_z`. -/
def S2 (_h : IsSU2 Sp Sm Sz) : End K V := Sm * Sp + Sz * Sz + Sz

/-- The ladder `v_k = S₋^k v`. -/
def ladder (_h : IsSU2 Sp Sm Sz) (v : V) (k : ℕ) : V := (Sm ^ k) v

variable (h : IsSU2 Sp Sm Sz) {v : V} {m : K}

lemma ladder_succ (k : ℕ) : h.ladder v (k + 1) = Sm (h.ladder v k) := by
  simp [ladder, pow_succ']

include h in
lemma Sz_Sm_apply (w : V) : Sz (Sm w) = Sm (Sz w) - Sm w := by
  have := congrArg (fun T : End K V => T w) h.comm_zm
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.neg_apply] at this
  rw [sub_eq_iff_eq_add] at this
  rw [this]; abel

include h in
lemma Sp_Sm_apply (w : V) : Sp (Sm w) = Sm (Sp w) + (2 : K) • Sz w := by
  have := congrArg (fun T : End K V => T w) h.comm_pm
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.smul_apply] at this
  rw [sub_eq_iff_eq_add] at this
  rw [this]; abel

/-- `S_z v_k = (m - k) v_k`. -/
theorem Sz_ladder (hz : Sz v = m • v) (k : ℕ) : Sz (h.ladder v k) = (m - k) • h.ladder v k := by
  induction k with
  | zero => simpa [ladder] using hz
  | succ k ih =>
    rw [ladder_succ, Sz_Sm_apply h, ih, map_smul]
    push_cast
    rw [sub_add_eq_sub_sub, sub_smul, sub_smul, sub_smul, one_smul]

/-- `S₊ v_{k+1} = (k + 1)(2m - k) v_k`. -/
theorem Sp_ladder_succ (hp : Sp v = 0) (hz : Sz v = m • v) (k : ℕ) :
    Sp (h.ladder v (k + 1)) = (((k : K) + 1) * (2 * m - k)) • h.ladder v k := by
  induction k with
  | zero =>
    rw [ladder_succ, Sp_Sm_apply h]
    simp [ladder, hp, hz, smul_smul]
  | succ k ih =>
    rw [ladder_succ, Sp_Sm_apply h, ih, map_smul, ← ladder_succ, Sz_ladder h hz, smul_smul,
      ← add_smul]
    congr 1
    push_cast; ring

/-- `S₊ v_0 = 0`. -/
lemma Sp_ladder_zero (hp : Sp v = 0) : Sp (h.ladder v 0) = 0 := by simpa [ladder] using hp

/-- `S² v_k = m(m + 1) v_k`. -/
theorem S2_ladder (hp : Sp v = 0) (hz : Sz v = m • v) (k : ℕ) :
    h.S2 (h.ladder v k) = (m * (m + 1)) • h.ladder v k := by
  have hzk := Sz_ladder h hz k
  rw [S2, LinearMap.add_apply, LinearMap.add_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    hzk, map_smul, hzk, smul_smul]
  cases k with
  | zero =>
    rw [Sp_ladder_zero h hp, map_zero, zero_add, ← add_smul]
    congr 1; push_cast; ring
  | succ k =>
    rw [Sp_ladder_succ h hp hz, map_smul, ← ladder_succ, ← add_smul, ← add_smul]
    congr 1; push_cast; ring

/-- **The spin is a half-integer**: if `v_K ≠ 0` and `v_{K+1} = 0`, then `2m = K`. -/
theorem two_m_eq [CharZero K] (hp : Sp v = 0) (hz : Sz v = m • v) {n : ℕ} (hn : h.ladder v n ≠ 0)
    (hn1 : h.ladder v (n + 1) = 0) : 2 * m = n := by
  have h1 := Sp_ladder_succ h hp hz n
  rw [hn1, map_zero] at h1
  have h2 := (smul_eq_zero.mp h1.symm).resolve_right hn
  have h3 : (n : K) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have := (mul_eq_zero.mp h2).resolve_left h3
  exact sub_eq_zero.mp this

lemma ladder_ne_zero_of_le {n : ℕ} (hn : h.ladder v n ≠ 0) {k : ℕ} (hk : k ≤ n) :
    h.ladder v k ≠ 0 := by
  intro h0
  apply hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp only [ladder] at h0 ⊢
  rw [add_comm, pow_add, mul_apply_eq_comp, h0, map_zero]

/-- **The ladder is linearly independent**: `v_0, …, v_n` are eigenvectors of `S_z` with the
distinct eigenvalues `m - k`. -/
theorem ladder_linearIndependent [CharZero K] (hz : Sz v = m • v) {n : ℕ} (hn : h.ladder v n ≠ 0) :
    LinearIndependent K fun k : Fin (n + 1) => h.ladder v k := by
  refine Module.End.eigenvectors_linearIndependent' Sz (fun k : Fin (n + 1) => m - k) ?_ _
    fun k => ?_
  · intro a b hab
    have : ((a : ℕ) : K) = (b : ℕ) := by simpa using hab
    exact Fin.ext (by exact_mod_cast this)
  · exact Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (Sz_ladder h hz k),
      ladder_ne_zero_of_le h hn (Nat.lt_succ_iff.mp k.2)⟩

/-- The span of the ladder `v_0, …, v_n`. -/
def ladderSpan (n : ℕ) : Submodule K V :=
  Submodule.span K (Set.range fun k : Fin (n + 1) => h.ladder v k)

/-- **The irreducible representation has dimension `2m + 1`**: the span of `v_0, …, v_K` has
dimension `K + 1 = 2m + 1`. -/
theorem finrank_span_ladder [CharZero K] (hz : Sz v = m • v) {n : ℕ} (hn : h.ladder v n ≠ 0) :
    Module.finrank K (h.ladderSpan (v := v) n) = n + 1 := by
  rw [ladderSpan, finrank_span_eq_card (ladder_linearIndependent h hz hn), Fintype.card_fin]

lemma ladder_mem (n : ℕ) {k : ℕ} (hk : k ≤ n) : h.ladder v k ∈ h.ladderSpan (v := v) n :=
  Submodule.subset_span ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩

/-- **The span of the ladder is invariant** under `S₊`, `S₋` and `S_z` when the ladder stops. -/
theorem span_ladder_invariant (hp : Sp v = 0) (hz : Sz v = m • v) {n : ℕ}
    (hn1 : h.ladder v (n + 1) = 0) {w : V} (hw : w ∈ h.ladderSpan (v := v) n) :
    Sp w ∈ h.ladderSpan (v := v) n ∧ Sm w ∈ h.ladderSpan (v := v) n ∧
      Sz w ∈ h.ladderSpan (v := v) n := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine ⟨?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (k : ℕ) with hk | hk
      · simp only [hk]; rw [Sp_ladder_zero h hp]; exact Submodule.zero_mem _
      · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hk
        simp only [hj, zero_add]
        rw [Sp_ladder_succ h hp hz]
        exact Submodule.smul_mem _ _ (ladder_mem h n (by omega))
    · rw [← ladder_succ]
      rcases Nat.lt_or_ge (k : ℕ) n with hk | hk
      · exact ladder_mem h n (by omega)
      · have : (k : ℕ) = n := by omega
        rw [this, hn1]; exact Submodule.zero_mem _
    · rw [Sz_ladder h hz]
      exact Submodule.smul_mem _ _ (ladder_mem h n (Nat.lt_succ_iff.mp k.2))
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add]
    exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2.1 hy.2.1,
      Submodule.add_mem _ hx.2.2 hy.2.2⟩
  | smul c x _ hx =>
    simp only [map_smul]
    exact ⟨Submodule.smul_mem _ _ hx.1, Submodule.smul_mem _ _ hx.2.1,
      Submodule.smul_mem _ _ hx.2.2⟩

/-- **In finite dimension every ladder stops**: if `v ≠ 0` there is `n` with `v_n ≠ 0` and
`v_{n+1} = 0`. -/
theorem exists_ladder_stop [CharZero K] [FiniteDimensional K V] (hz : Sz v = m • v) (hv : v ≠ 0) :
    ∃ n, h.ladder v n ≠ 0 ∧ h.ladder v (n + 1) = 0 := by
  have hex : ∃ k, h.ladder v k = 0 := by
    by_contra hc
    push Not at hc
    have hli := ladder_linearIndependent h hz (hc (Module.finrank K V))
    have := hli.fintype_card_le_finrank
    simp at this
  classical
  let k := Nat.find hex
  have hk : h.ladder v k = 0 := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0] at hk; exact hv (by simpa [ladder] using hk)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨n, fun h0 => ?_, by rw [show n + 1 = k from hn.symm]; exact hk⟩
  have := Nat.find_min' hex h0
  omega

end IsSU2

/-! ### Spin-½ particles -/

/-- **The spin operators of `N` spin-½ particles satisfy the su(2) relations.** -/
theorem isSU2_spin {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℝ W] :
    IsSU2 (DFT.Continuum.Line.Sp : End ℝ (DFT.Continuum.Line.SpinC n → W))
      DFT.Continuum.Line.Sm DFT.Continuum.Line.Sz where
  comm_pm := DFT.Continuum.Line.comm_Sp_Sm'
  comm_zp := DFT.Continuum.Line.comm_Sz_Sp'
  comm_zm := LinearMap.ext DFT.Continuum.Line.comm_Sz_Sm

/-- The total spin of `IsSU2` is the `S2` of `QM/Spin/SpinAlg`. -/
theorem isSU2_spin_S2 {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℝ W] :
    (isSU2_spin (n := n) (W := W)).S2 = DFT.Continuum.Line.S2 :=
  DFT.Continuum.Line.S2_eq.symm

end QM
