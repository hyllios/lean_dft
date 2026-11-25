/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.Generic.SquarePlane
import DFT.Lattice.GenericHK.DensityDim.Fermions
import DFT.Lattice.HK.Nondegenerate
import DFT.Lattice.TDDFT.Counterexample
import DFT.Lattice.TDDFT.Spin

/-!
# Bridge: the hand-typed square is the general fermionic Hamiltonian on the 4-cycle

The square examples of the library (`HK.Examples`, `HK.SquareWall`, `TDDFT.Counterexample`) use the
hand-typed 6 × 6 matrix `H0sq` and occupations `occ4`. The general theorems
(`generic_hk_lattice_fermions`, `dimH_nonUVDens_lattice_fermions`, `generic_ground_mem_omega`) are
stated for `H0F G t W` or `H0Fw G t W`, built from second quantization. This file shows that the two
agree: in the basis `cfg` of two-fermion configurations, `H0F sqG 1 0 = H0sq − 4·I` entry by entry
(`H0F_square`) and `occ4 = occF` (`occ4_eq_occF`), so ground states correspond
(`isGroundState_H0F_iff`). Transported to `H0F`, the square counterexample (`hk_fails_square`) shows
that the exceptional sets of the generic Hohenberg–Kohn theorem, of the density bound and of
`generic_ground_mem_omega` are not empty on the square, in the same statement as the theorem
(`generic_hk_square_nonvacuous`, `nonUVDens_square_nonvacuous`,
`ground_mem_omega_square_nonvacuous`): the general theorems are not vacuous there.
-/

namespace DFT

open Matrix

namespace Bridge.Square

/-! ### The square and its basis -/

/-- The 4-cycle `0 – 1 – 2 – 3 – 0`. -/
def sqG : SimpleGraph (Fin 4) where
  Adj a b := (a.val + 1) % 4 = b.val ∨ (b.val + 1) % 4 = a.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun a h => by rcases h with h | h <;> omega⟩

instance : DecidableRel sqG.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The two-fermion configurations in the order of `H0sq`: `01, 02, 03, 12, 13, 23`. -/
def cfg : Fin 6 → Conf 4 2 :=
  ![⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩,
    ⟨{1, 2}, by decide⟩, ⟨{1, 3}, by decide⟩, ⟨{2, 3}, by decide⟩]

lemma cfg_bijective : Function.Bijective cfg := by decide

/-- The occupied sites of `cfg i`, in increasing order. -/
def pos : Fin 6 → Fin 2 → Fin 4 :=
  ![![0, 1], ![0, 2], ![0, 3], ![1, 2], ![1, 3], ![2, 3]]

lemma pos_strictMono (i : Fin 6) : StrictMono (pos i) := by
  fin_cases i <;> (rw [Fin.strictMono_iff_lt_succ]; decide)

lemma τs_cfg (i : Fin 6) : τs (cfg i) = pos i := by
  unfold τs
  have h := Finset.orderEmbOfFin_unique (cfg i).2 (f := pos i)
    (by fin_cases i <;> decide) (pos_strictMono i)
  exact (congrArg (fun f : Fin 2 → Fin 4 => f) h).symm ▸ rfl

theorem H0F_square (i j : Fin 6) :
    H0F sqG 1 (fun _ => 0) (cfg i) (cfg j) = H0sq i j - 4 * (if i = j then 1 else 0) := by
  simp only [H0F, Matrix.add_apply, Matrix.diagonal_apply, Γ, amp, slater, τs_cfg]
  fin_cases i <;> fin_cases j <;>
    simp +decide [Fin.sum_univ_succ, Matrix.det_fin_two, Function.update, Matrix.smul_apply,
      pos, H0sq]

theorem occ4_eq_occF (i : Fin 4) (c : Fin 6) : occ4 i c = occF i (cfg c) := by
  fin_cases i <;> fin_cases c <;> simp [occ4, occF, cfg]

/-- The basis as an equivalence. -/
noncomputable def e : Fin 6 ≃ Conf 4 2 := Equiv.ofBijective cfg cfg_bijective

/-! ### Step 1: reindexing. -/

lemma qf_reindex {α β : Type*} [Fintype α] [Fintype β] (σ : α ≃ β) (M : Matrix β β ℝ) (φ : β → ℝ) :
    qf (M.submatrix σ σ) (φ ∘ σ) = qf M φ := by
  simp only [qf, dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Function.comp]
  rw [Equiv.sum_comp σ (fun x => φ x * ∑ j, M x (σ j) * φ (σ j))]
  exact Finset.sum_congr rfl fun x _ => by rw [Equiv.sum_comp σ (fun y => M x y * φ y)]

lemma dot_reindex {α β : Type*} [Fintype α] [Fintype β] (σ : α ≃ β) (φ : β → ℝ) :
    (φ ∘ σ) ⬝ᵥ (φ ∘ σ) = φ ⬝ᵥ φ := by
  simp only [dotProduct, Function.comp]
  exact Equiv.sum_comp σ (fun x => φ x * φ x)

lemma isGroundState_reindex {α β : Type*} [Fintype α] [Fintype β] (σ : α ≃ β) (M : Matrix β β ℝ)
    (ψ : β → ℝ) : IsGroundState (M.submatrix σ σ) (ψ ∘ σ) ↔ IsGroundState M ψ := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun h => h0 (by rw [h]; rfl), fun φ => ?_⟩
    have := h1 (φ ∘ σ)
    rwa [qf_reindex, qf_reindex, dot_reindex, dot_reindex] at this
  · rintro ⟨h0, h1⟩
    refine ⟨fun h => h0 (funext fun y => by simpa using congrFun h (σ.symm y)), fun φ => ?_⟩
    obtain ⟨φ', rfl⟩ : ∃ φ' : β → ℝ, φ = φ' ∘ σ := ⟨φ ∘ σ.symm, by funext x; simp⟩
    rw [qf_reindex, qf_reindex, dot_reindex, dot_reindex]
    exact h1 φ'

/-! ### Step 2: the two Hamiltonians (a constant shift: `isGroundState_add_smul_one`). -/

lemma hamN_reindex (v : Fin 4 → ℝ) :
    (hamN (H0F sqG 1 (fun _ : Conf 4 2 => 0)) occF v).submatrix e e =
      hamN H0sq occ4 v + (-4 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  ext i j
  have hinj : cfg i = cfg j ↔ i = j := cfg_bijective.1.eq_iff
  simp only [Matrix.submatrix_apply, e, Equiv.ofBijective_apply, hamN, Matrix.add_apply, H0F_square,
    Matrix.diagonal_apply, hinj, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, occ4_eq_occF]
  split_ifs <;> ring

/-! ### The bridge. -/

/-- `NonUV` for the general `H0F` on the square, at `v = (3/4, −3/4, −3/4, 3/4)`: the exceptional
set of `generic_hk_square_nonvacuous` is not empty. -/
theorem nonUV_H0F_square :
    NonUV (H0F sqG 1 (fun _ : Conf 4 2 => 0)) occF ![3/4, -3/4, -3/4, 3/4] := by
  obtain ⟨h1, h2, h3⟩ := hk_fails_square
  have transport : ∀ v : Fin 4 → ℝ, IsGroundState (hamN H0sq occ4 v) ![0, 2, 1, 4, 2, 0] →
      IsGroundState (hamN (H0F sqG 1 (fun _ : Conf 4 2 => 0)) occF v)
        (![0, 2, 1, 4, 2, 0] ∘ e.symm) := by
    intro v hv
    rw [← isGroundState_reindex e, hamN_reindex, isGroundState_add_smul_one]
    have : (![0, 2, 1, 4, 2, 0] ∘ e.symm) ∘ e = (![0, 2, 1, 4, 2, 0] : Fin 6 → ℝ) := by
      funext x; simp
    rw [this]; exact hv
  exact ⟨_, _, transport _ h1, transport _ h2, h3⟩

theorem exceptional_set_nonempty :
    {v | NonUV (H0F sqG 1 (fun _ : Conf 4 2 => 0)) occF v}.Nonempty :=
  ⟨_, nonUV_H0F_square⟩

lemma sqG_connected : sqG.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun b => ?_⟩
  have a01 : sqG.Adj 0 1 := by decide
  have a12 : sqG.Adj 1 2 := by decide
  have a03 : sqG.Adj 0 3 := by decide
  fin_cases b
  · exact SimpleGraph.Reachable.refl _
  · exact a01.reachable
  · exact a01.reachable.trans a12.reachable
  · exact a03.reachable

/-- The generic Hohenberg–Kohn theorem on the square, with its subject shown non-empty in the same
statement (one square graph throughout): the exceptional set lies in a closed, nowhere dense null
set Z, and it is not empty. -/
theorem generic_hk_square_nonvacuous : ∃ Z : Set (Fin 4 → ℝ), IsClosed Z ∧ interior Z = ∅ ∧
    MeasureTheory.volume Z = 0 ∧
    {v | NonUV (H0F sqG 1 (fun _ : Conf 4 2 => 0)) occF v} ⊆ Z ∧
    {v | NonUV (H0F sqG 1 (fun _ : Conf 4 2 => 0)) occF v}.Nonempty := by
  obtain ⟨Z, h1, h2, h3, h4⟩ :=
    generic_hk_lattice_fermions sqG_connected one_ne_zero (by norm_num) (by norm_num)
      (fun _ : Conf 4 2 => 0)
  exact ⟨Z, h1, h2, h3, h4, exceptional_set_nonempty⟩

/-! ### The density bound and `Ω` on the same `H0F`: their exceptional sets are not empty either

The density bound (`dimH_nonUVDens_lattice_fermions`) and `generic_ground_mem_omega` on the square
are an upper bound and a generic statement; an empty exceptional set would satisfy them. The
square's shared ground state is transported here, as for the generic Hohenberg–Kohn theorem: its
density lies in `NonUVDens` of `H0F` (with the non-degeneracy clause), and it is a ground state
outside `Ω`. -/

/-- Ground states of the two Hamiltonians correspond under the basis `e` (steps 1–2). -/
lemma isGroundState_H0F_iff (v : Fin 4 → ℝ) (ψ : Fin 6 → ℝ) :
    IsGroundState (hamN (H0F sqG 1 (fun _ : Conf 4 2 => 0)) occF v) (ψ ∘ e.symm) ↔
      IsGroundState (hamN H0sq occ4 v) ψ := by
  rw [← isGroundState_reindex e, hamN_reindex, isGroundState_add_smul_one]
  have : (ψ ∘ e.symm) ∘ e = ψ := by funext x; simp
  rw [this]

/-- The normalized ground state ψsq/5. -/
noncomputable def ψn : Fin 6 → ℝ := ![0, 2 / 5, 1 / 5, 4 / 5, 2 / 5, 0]

lemma ψn_eq : ψn = (1 / 5 : ℝ) • ![0, 2, 1, 4, 2, 0] := by
  funext k; fin_cases k <;> simp [ψn] <;> norm_num

lemma ψn_norm : ψn ⬝ᵥ ψn = 1 := by
  simp [ψn, dotProduct, Fin.sum_univ_succ]; norm_num

lemma dens_reindex (ψ : Fin 6 → ℝ) : dens occF (ψ ∘ e.symm) = dens occ4 ψ := by
  funext i
  simp only [dens]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [occ4_eq_occF]
  rfl

/-- **The non-uv density set is not empty for `H0F` on the square**: the density (1, 4, 4, 1)/5 lies
in `NonUVDens (H0F sqG 1 0) occF`, with every clause, the non-degeneracy included. -/
theorem square_density_mem_nonUVDens_H0F :
    (![1 / 5, 4 / 5, 4 / 5, 1 / 5] : Fin 4 → ℝ) ∈
      NonUVDens (H0F sqG 1 (fun _ : Conf 4 2 => 0)) occF := by
  obtain ⟨hψ, hψ', hnc⟩ := hk_fails_square
  refine ⟨![3/4, -3/4, -3/4, 3/4], ![5/4, -1/4, -5/4, 1/4], ψn ∘ e.symm, ?_, ?_, ?_, ?_, hnc, ?_⟩
  · rw [isGroundState_H0F_iff, ψn_eq]; exact isGroundState_smul hψ (by norm_num)
  · rw [dot_reindex]; exact ψn_norm
  · intro φ hφ
    have hφe : (φ ∘ e) ∘ e.symm = φ := by funext x; simp
    rw [← hφe, isGroundState_H0F_iff] at hφ
    obtain ⟨a, ha⟩ := hk_fails_square_nondeg.2.2.2.1 _ hφ
    refine ⟨5 * a, funext fun c => ?_⟩
    have hc := congrFun ha (e.symm c)
    rw [ψn_eq] at *
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul] at hc ⊢
    rw [hc]; ring
  · rw [isGroundState_H0F_iff, ψn_eq]; exact isGroundState_smul hψ' (by norm_num)
  · rw [dens_reindex]
    funext i; fin_cases i <;> simp [dens, occ4, ψn, Fin.sum_univ_succ] <;> norm_num

/-- The density bound `dimH_nonUVDens_lattice_fermions` on the square, with its subject shown
non-empty in the same statement. -/
theorem nonUVDens_square_nonvacuous :
    dimH (NonUVDens (H0F sqG 1 (fun _ : Conf 4 2 => 0)) (occF : Fin 4 → Conf 4 2 → ℝ)) ≤
      (4 : ENNReal) - 3 ∧
      (NonUVDens (H0F sqG 1 (fun _ : Conf 4 2 => 0)) (occF : Fin 4 → Conf 4 2 → ℝ)).Nonempty :=
  ⟨dimH_nonUVDens_lattice_fermions sqG_connected one_ne_zero (by norm_num) (by norm_num) _,
    ⟨_, square_density_mem_nonUVDens_H0F⟩⟩

lemma kMat_reindex (ψ : Fin 6 → ℝ) :
    kMat (H0F sqG 1 (fun _ : Conf 4 2 => 0)) occF (ψ ∘ e.symm) = kMat H0sq occ4 ψ := by
  ext i j
  simp only [kMat]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hinj : cfg a = cfg b ↔ a = b := cfg_bijective.1.eq_iff
  simp only [e, Equiv.ofBijective_apply, H0F_square, ← occ4_eq_occF]
  split_ifs with h
  · subst h; ring
  · ring

/-- **The exceptional set of `generic_ground_mem_omega` is not empty on the square**: the square
state is a ground state of the library's Hamiltonian at `v = (3/4, −3/4, −3/4, 3/4)`, and it lies
outside `Ω` (the zero mode w = (1, 1, −1, −1)). -/
theorem ground_not_mem_omega_H0Fw :
    IsGroundState
        (hamN (H0Fw sqG (fun _ _ => 1) (fun _ : Conf 4 2 => 0)) occF ![3/4, -3/4, -3/4, 3/4])
        (ψsq ∘ e.symm) ∧
      ((ψsq ∘ e.symm, 0) : (Conf 4 2 → ℝ) × (Conf 4 2 → ℝ)) ∉
        omega (H0Fw sqG (fun _ _ => 1) (fun _ : Conf 4 2 => 0)) occF := by
  rw [← H0F_eq_H0Fw]
  have hg : IsGroundState (hamN (H0F sqG 1 (fun _ : Conf 4 2 => 0)) occF ![3/4, -3/4, -3/4, 3/4])
      (ψsq ∘ e.symm) := (isGroundState_H0F_iff _ _).mpr hk_fails_square.1
  refine ⟨by convert hg using 2, fun h => h ?_⟩
  have hS := H0F_isSymm sqG 1 (fun _ : Conf 4 2 => 0)
  have hK : kfb (H0F sqG 1 (fun _ : Conf 4 2 => 0)) occF (ψsq ∘ e.symm, 0) *ᵥ wsq = 0 := by
    refine mulVec_eq_zero_of_psd (kfb_transpose hS occF _) (fun u => ?_) ?_
    · rw [kfb_quad_real hS]; linarith [kMat_nonpos hS hg u]
    · rw [kfb_quad_real hS, kMat_reindex, kMat_sq_w, dotProduct_zero, neg_zero]
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨wsq, fun h0 => by simpa [wsq] using congrFun h0 0, ?_⟩
  rw [kJ, add_mulVec, hK, onesM_mulVec, zero_add]
  funext i
  simp [wsq, Fin.sum_univ_four]

/-- `generic_ground_mem_omega` on the square, with its exceptional set shown non-empty in the same
statement. -/
theorem ground_mem_omega_square_nonvacuous : (∃ Z : Set (Fin 4 → ℝ), IsClosed Z ∧ interior Z = ∅ ∧
    MeasureTheory.volume Z = 0 ∧
    ∀ v0 ∉ Z, ∀ ψ0,
      IsGroundState (hamN (H0Fw sqG (fun _ _ => 1) (fun _ : Conf 4 2 => 0)) occF v0) ψ0 →
      ((ψ0, 0) : (Conf 4 2 → ℝ) × (Conf 4 2 → ℝ)) ∈
        omega (H0Fw sqG (fun _ _ => 1) (fun _ => 0)) occF) ∧
    ∃ v0 ψ0, IsGroundState (hamN (H0Fw sqG (fun _ _ => 1) (fun _ : Conf 4 2 => 0)) occF v0) ψ0 ∧
      ((ψ0, 0) : (Conf 4 2 → ℝ) × (Conf 4 2 → ℝ)) ∉
        omega (H0Fw sqG (fun _ _ => 1) (fun _ => 0)) occF :=
  ⟨generic_ground_mem_omega sqG_connected (fun _ _ => rfl) (s := 1) (fun _ _ _ => by norm_num)
    (by norm_num) (by norm_num) _, _, _, ground_not_mem_omega_H0Fw⟩

end Bridge.Square

end DFT
