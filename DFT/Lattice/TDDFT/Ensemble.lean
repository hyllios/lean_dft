/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.TDDFT.KohnSham
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Star.Real

/-!
# Ensembles in lattice TDDFT (purification)

A finite ensemble of states `b_k` (`k : κ`), all evolving under the same potential, is a single
state of an enlarged system on configurations `C × κ`: the Hamiltonian is block diagonal
(`liftM`), the occupations ignore `k` (`liftN`), and densities add up over `k`.

* `schr_slice`, `tdens_lift`, `tcur_lift`: the dynamics and observables of the enlarged system are
  those of the members.
* `form_lift`: its force-balance form is the sum of the members' forms, so `mem_omega_glue` puts a
  real ensemble in `Ω` as soon as one member has a definite form.
* `van_leeuwen_ens`: van Leeuwen's theorem with an ensemble as the reproducing system.
* `ens_purify`: a ground-state density matrix `Γ` is `Σ_k b_k b_kᵀ` with every `b_k` zero or a
  ground state (spectral theorem).
* `td_kohn_sham_ensemble`: time-dependent Kohn–Sham starting from any ground-state ensemble of a
  generic non-interacting Hamiltonian (no pure-state assumption, so it connects directly to
  `ks_potential_exists`).
-/

namespace DFT

open Matrix Set Filter Topology MeasureTheory

variable {C κ V : Type*} [Fintype C] [DecidableEq C] [Fintype κ] [DecidableEq κ] [Fintype V]
  [DecidableEq V]

variable (κ) in
/-- Block-diagonal copy of a matrix, one block per ensemble member. -/
def liftM (A : Matrix C C ℝ) : Matrix (C × κ) (C × κ) ℝ :=
  fun p q => if p.2 = q.2 then A p.1 q.1 else 0

variable (κ) in
/-- Occupations of the enlarged system. -/
def liftN (n : V → C → ℝ) : V → C × κ → ℝ := fun i p => n i p.1

/-- The state of member `k`. -/
def slice (Ψ : (C × κ → ℝ) × (C × κ → ℝ)) (k : κ) : (C → ℝ) × (C → ℝ) :=
  (fun c => Ψ.1 (c, k), fun c => Ψ.2 (c, k))

/-- The enlarged state of a family. -/
def glue (φ : κ → (C → ℝ) × (C → ℝ)) : (C × κ → ℝ) × (C × κ → ℝ) :=
  (fun p => (φ p.2).1 p.1, fun p => (φ p.2).2 p.1)

omit [Fintype C] [DecidableEq C] [Fintype κ] [DecidableEq κ] in
@[simp] lemma slice_glue (φ : κ → (C → ℝ) × (C → ℝ)) (k : κ) : slice (glue φ) k = φ k := rfl

omit [Fintype C] [DecidableEq C] [Fintype κ] [DecidableEq κ] in
@[simp] lemma glue_slice (Ψ : (C × κ → ℝ) × (C × κ → ℝ)) : glue (slice Ψ) = Ψ := rfl

section algebra

omit [Fintype C] [DecidableEq C] [Fintype κ] in
lemma liftM_isSymm {A : Matrix C C ℝ} (hA : A.IsSymm) : (liftM κ A).IsSymm := by
  ext p q
  simp only [transpose_apply, liftM, eq_comm (a := p.2)]
  split_ifs <;> simp [hA.apply]

omit [DecidableEq C] in
lemma liftM_mulVec (A : Matrix C C ℝ) (X : C × κ → ℝ) (c : C) (k : κ) :
    (liftM κ A *ᵥ X) (c, k) = (A *ᵥ fun c' => X (c', k)) c := by
  simp only [mulVec, dotProduct, liftM, Fintype.sum_prod_type, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit [DecidableEq C] [DecidableEq κ] in
lemma dot_lift (X Y : C × κ → ℝ) :
    X ⬝ᵥ Y = ∑ k, (fun c => X (c, k)) ⬝ᵥ (fun c => Y (c, k)) := by
  simp only [dotProduct, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [DecidableEq C] in
lemma liftM_mul (A B : Matrix C C ℝ) : liftM κ (A * B) = liftM κ A * liftM κ B := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp only [liftM, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  by_cases h : k = l <;> simp [h]

omit [Fintype C] [Fintype κ] in
lemma liftM_diagonal (d : C → ℝ) : liftM κ (diagonal d) = diagonal fun p : C × κ => d p.1 := by
  ext p q
  simp only [liftM, diagonal_apply, Prod.ext_iff]
  split_ifs <;> simp_all

omit [Fintype C] [Fintype κ] [Fintype V] [DecidableEq V] in
lemma Nmat_lift (n : V → C → ℝ) (i : V) : Nmat (liftN κ n) i = liftM κ (Nmat n i) := by
  rw [Nmat, Nmat, liftM_diagonal]; rfl

omit [Fintype C] [Fintype κ] [DecidableEq V] in
lemma hamN_lift (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) :
    hamN (liftM κ H0) (liftN κ n) v = liftM κ (hamN H0 n v) := by
  ext p q
  simp only [hamN, Matrix.add_apply, liftM, liftN, diagonal_apply, Prod.ext_iff]
  split_ifs <;> simp_all

omit [DecidableEq C] in
lemma Qf_lift (A : Matrix C C ℝ) (Ψ : (C × κ → ℝ) × (C × κ → ℝ)) :
    Qf (liftM κ A) Ψ = ∑ k, Qf A (slice Ψ k) := by
  simp only [Qf, dot_lift, liftM_mulVec, ← Finset.sum_add_distrib]
  rfl

omit [DecidableEq V] in
lemma schr_slice (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ)
    (Ψ : (C × κ → ℝ) × (C × κ → ℝ)) (k : κ) :
    slice (schr (liftM κ H0) (liftN κ n) v Ψ) k = schr H0 n v (slice Ψ k) := by
  simp only [schr, slice, hamN_lift, Pi.neg_apply, liftM_mulVec]
  rfl

omit [DecidableEq V] in
lemma schr_glue (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) (φ : κ → (C → ℝ) × (C → ℝ)) :
    schr (liftM κ H0) (liftN κ n) v (glue φ) = glue fun k => schr H0 n v (φ k) := by
  rw [← glue_slice (schr _ _ _ _)]
  congr 1; funext k; rw [schr_slice, slice_glue]

omit [Fintype V] [DecidableEq V] in
lemma tdens_lift (n : V → C → ℝ) (Ψ : (C × κ → ℝ) × (C × κ → ℝ)) (i : V) :
    tdens (liftN κ n) Ψ i = ∑ k, tdens n (slice Ψ k) i := by
  simp only [tdens, Nmat_lift, Qf_lift]

omit [Fintype V] [DecidableEq V] in
lemma tcur_lift (H0 : Matrix C C ℝ) (n : V → C → ℝ) (Ψ : (C × κ → ℝ) × (C × κ → ℝ)) (i : V) :
    tcur (liftM κ H0) (liftN κ n) Ψ i = ∑ k, tcur H0 n (slice Ψ k) i := by
  simp only [tcur, Nmat_lift, ← liftM_mul, dot_lift, liftM_mulVec, ← Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  rfl

end algebra

section calculus

variable (C κ) in
/-- Member `k` as a continuous linear map. -/
noncomputable def sliceL (k : κ) : ((C × κ → ℝ) × (C × κ → ℝ)) →L[ℝ] ((C → ℝ) × (C → ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Ψ => slice Ψ k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

variable (C κ) in
/-- Gluing as a continuous linear map. -/
noncomputable def glueL : (κ → (C → ℝ) × (C → ℝ)) →L[ℝ] ((C × κ → ℝ) × (C × κ → ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := glue, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [DecidableEq C] [DecidableEq κ] in
lemma slice_hasDerivAt {Φ : ℝ → (C × κ → ℝ) × (C × κ → ℝ)} {f : (C × κ → ℝ) × (C × κ → ℝ)}
    {t : ℝ} (h : HasDerivAt Φ f t) (k : κ) : HasDerivAt (fun s => slice (Φ s) k) (slice f k) t :=
  (sliceL C κ k).hasFDerivAt.comp_hasDerivAt t h

omit [DecidableEq C] [DecidableEq κ] in
lemma glue_hasDerivAt {φ : κ → ℝ → (C → ℝ) × (C → ℝ)} {f : κ → (C → ℝ) × (C → ℝ)} {t : ℝ}
    (h : ∀ k, HasDerivAt (φ k) (f k) t) : HasDerivAt (fun s => glue fun k => φ k s) (glue f) t :=
  (glueL C κ).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_pi.mpr h)

end calculus

section omega

omit [DecidableEq C] [DecidableEq V] in
/-- The force-balance form of a real ensemble is the sum of the members' forms. -/
lemma form_lift (H0 : Matrix C C ℝ) (n : V → C → ℝ) (b : κ → C → ℝ) (w : V → ℝ) :
    w ⬝ᵥ (kMat (liftM κ H0) (liftN κ n) (fun p => b p.2 p.1) *ᵥ w) =
      ∑ k, w ⬝ᵥ (kMat H0 n (b k) *ᵥ w) := by
  simp only [kMat_form]
  simp only [liftM, potW, liftN, Fintype.sum_prod_type, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]

/-- A real ensemble lies in `Ω` of the enlarged system if all members have negative semidefinite
forms and one of them has only constant zero modes. -/
lemma mem_omega_glue [Nonempty V] {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}
    {b : κ → C → ℝ} (hneg : ∀ k w, w ⬝ᵥ (kMat H0 n (b k) *ᵥ w) ≤ 0) (k0 : κ)
    (hdef : ∀ w, w ⬝ᵥ (kMat H0 n (b k0) *ᵥ w) = 0 → ∃ c, ∀ i, w i = c) :
    glue (fun k => (b k, 0)) ∈ omega (liftM κ H0) (liftN κ n) := by
  have hg : glue (fun k => (b k, (0 : C → ℝ))) = ((fun p => b p.2 p.1), 0) := rfl
  rw [hg]
  refine mem_omega_of_definite (liftM_isSymm hH0) (fun w => ?_) (fun w hw => hdef w ?_)
  · rw [form_lift]; exact Finset.sum_nonpos fun k _ => hneg k w
  · rw [form_lift] at hw
    exact (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hneg k w).mp hw k0 (Finset.mem_univ _)

end omega

section vanLeeuwen

variable {C₁ : Type*} [Fintype C₁] [DecidableEq C₁] {H1 : Matrix C₁ C₁ ℝ} {n1 : V → C₁ → ℝ}
  {N1 : ℝ} (hH1 : H1.IsSymm) (hN1 : ∀ c, ∑ i, n1 i c = N1) {ψ : ℝ → (C₁ → ℝ) × (C₁ → ℝ)}
  {v : ℝ → V → ℝ} (hψ : ∀ t, HasDerivAt ψ (schr H1 n1 (v t) (ψ t)) t) (hv : Continuous v)
  {H0 : Matrix C C ℝ} {n : V → C → ℝ} {Ntot : ℝ} (hH0 : H0.IsSymm) (hN : ∀ c, ∑ i, n i c = Ntot)
  [Nonempty V]
include hH1 hN1 hψ hv hH0 hN

/-- **Lattice van Leeuwen theorem for ensembles.** The density of a trajectory `ψ(t)` of any system
is reproduced, near `t₀`, by an ensemble `{φ_k(t)}` of states of a second system, all driven by
one common potential `v_s(t)` (gauge `Σ_i v_s,i = 0`): `Σ_k ρ[φ_k(t)] = ρ[ψ(t)]`. The ensemble
starts from `{b_k}`, with the initial density and current of `ψ(t₀)` and in `Ω` of the enlarged
system. The trajectories and the potential are unique. -/
theorem van_leeuwen_ens {t0 : ℝ} {b : κ → (C → ℝ) × (C → ℝ)}
    (hb : glue b ∈ omega (liftM κ H0) (liftN κ n))
    (hρ0 : ∀ i, ∑ k, tdens n (b k) i = tdens n1 (ψ t0) i)
    (hj0 : ∀ i, ∑ k, tcur H0 n (b k) i = tcur H1 n1 (ψ t0) i) :
    ∃ φ : κ → ℝ → (C → ℝ) × (C → ℝ), ∃ vs : ℝ → V → ℝ, (∀ k, φ k t0 = b k) ∧
      (∀ᶠ t in 𝓝 t0, (∀ k, HasDerivAt (φ k) (schr H0 n (vs t) (φ k t)) t) ∧
        ∑ i, vs t i = 0 ∧ ∀ i, ∑ k, tdens n (φ k t) i = tdens n1 (ψ t) i) ∧
      ∀ φ' : κ → ℝ → (C → ℝ) × (C → ℝ), ∀ vs' : ℝ → V → ℝ, (∀ k, φ' k t0 = b k) →
        (∀ᶠ t in 𝓝 t0, (∀ k, HasDerivAt (φ' k) (schr H0 n (vs' t) (φ' k t)) t) ∧
          ∑ i, vs' t i = 0 ∧ ∀ i, ∑ k, tdens n (φ' k t) i = tdens n1 (ψ t) i) →
        (∀ k, φ' k =ᶠ[𝓝 t0] φ k) ∧ vs' =ᶠ[𝓝 t0] vs := by
  obtain ⟨Φ, vs, h0, hev, huniq⟩ := van_leeuwen_unique' (t0 := t0) (n' := liftN κ n) hH1 hN1 hψ hv
    (liftM_isSymm hH0) (fun p => hN p.1) hb (fun i => by rw [tdens_lift]; simpa using hρ0 i)
    (fun i => by rw [tcur_lift]; simpa using hj0 i)
  refine ⟨fun k s => slice (Φ s) k, vs, fun k => by simp [h0], ?_, ?_⟩
  · filter_upwards [hev] with t ⟨hd, hs, hρ⟩
    refine ⟨fun k => ?_, hs, fun i => ?_⟩
    · have := slice_hasDerivAt hd k
      rwa [schr_slice] at this
    · rw [← hρ i, tdens_lift]
  · intro φ' vs' h0' h'
    have hg0 : (glue fun k => φ' k t0) = glue b := by simp only [h0']
    obtain ⟨hΦ, hv'⟩ := huniq (fun s => glue fun k => φ' k s) vs' hg0 (by
      filter_upwards [h'] with t ⟨hd, hs, hρ⟩
      refine ⟨?_, hs, fun i => ?_⟩
      · rw [schr_glue]; exact glue_hasDerivAt hd
      · rw [tdens_lift]; simpa using hρ i)
    refine ⟨fun k => ?_, hv'⟩
    filter_upwards [hΦ] with t ht
    simpa using congrArg (fun X => slice X k) ht

end vanLeeuwen

section purification

omit [DecidableEq C] in
/-- A symmetric positive semidefinite real matrix is `B Bᵀ` (spectral theorem). -/
lemma exists_eq_mul_transpose {Γ : Matrix C C ℝ} (hsym : Γᵀ = Γ)
    (hpos : ∀ x, 0 ≤ x ⬝ᵥ (Γ *ᵥ x)) : ∃ B : Matrix C C ℝ, Γ = B * Bᵀ := by
  classical
  have hH : Γ.IsHermitian := by
    change Γᴴ = Γ; rw [conjTranspose_eq_transpose_of_trivial, hsym]
  have hP : Γ.PosSemidef :=
    PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => by simpa using hpos x)
  refine ⟨(hH.eigenvectorUnitary : Matrix C C ℝ) * diagonal (fun i => √(hH.eigenvalues i)), ?_⟩
  conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [transpose_mul, diagonal_transpose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
  congr 2
  · congr 1; funext i; simp [Real.mul_self_sqrt (hP.eigenvalues_nonneg i)]

omit [DecidableEq C] in
lemma gsEnergy_mul_le [Nonempty C] {H : Matrix C C ℝ} (hS : H.IsSymm) (φ : C → ℝ) :
    gsEnergy H * (φ ⬝ᵥ φ) ≤ qf H φ := by
  obtain ⟨hg, hn⟩ := Classical.choose_spec (exists_groundState hS)
  have := hg.2 φ
  rw [hn, mul_one] at this
  simpa [gsEnergy, hS] using this

omit [DecidableEq C] in
/-- A nonzero eigenvector at the ground-state energy is a ground state. -/
lemma isGroundState_of_eigen_gs [Nonempty C] {H : Matrix C C ℝ} (hS : H.IsSymm) {b : C → ℝ}
    (hb : b ≠ 0) (he : H *ᵥ b = gsEnergy H • b) : IsGroundState H b := by
  refine ⟨hb, fun φ => ?_⟩
  have hq : qf H b = gsEnergy H * (b ⬝ᵥ b) := by simp [qf, he, dotProduct_smul]
  have hbb : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have := mul_le_mul_of_nonneg_right (gsEnergy_mul_le hS φ) hbb
  rw [hq]; linarith

omit [DecidableEq V] in
/-- **Purification of a ground-state ensemble.** `Γ = Σ_k b_k b_kᵀ`, every `b_k` is zero or an
eigenvector at the ground-state energy, not all vanish, and the densities add up to that of `Γ`. -/
lemma ens_purify [Nonempty C] {H0 : Matrix C C ℝ} {n : V → C → ℝ} {v : V → ℝ} {Γ : Matrix C C ℝ}
    (hΓ : Γ ∈ Ens H0 n v) :
    ∃ b : C → C → ℝ, Γ = ∑ k, vecMulVec (b k) (b k) ∧
      (∀ k, hamN H0 n v *ᵥ b k = Egs H0 n v • b k) ∧ (∃ k, b k ≠ 0) ∧
      ∀ i, ∑ k, tdens n (b k, 0) i = ensDens n Γ i := by
  obtain ⟨hsym, hpos, htr, heig⟩ := hΓ
  obtain ⟨B, hB⟩ := exists_eq_mul_transpose hsym hpos
  set h := hamN H0 n v
  set E := Egs H0 n v
  have hA : h * B = E • B := by
    have h1 : (h - E • 1) * Γ = 0 := by
      rw [Matrix.sub_mul, heig, Matrix.smul_mul, Matrix.one_mul, sub_self]
    have h2 : ((h - E • 1) * B) * ((h - E • 1) * B)ᴴ = 0 := by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, ← Matrix.mul_assoc,
        Matrix.mul_assoc _ B, ← hB, h1, Matrix.zero_mul]
    have h3 := self_mul_conjTranspose_eq_zero.mp h2
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at h3
    exact h3
  refine ⟨fun k c => B c k, ?_, fun k => ?_, ?_, fun i => ?_⟩
  · ext a c
    simp [hB, Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply]
  · ext c
    have := congrFun (congrFun hA c) k
    simpa [mulVec, dotProduct, Matrix.mul_apply] using this
  · by_contra hall
    push Not at hall
    have hB0 : B = 0 := by ext c k; exact congrFun (hall k) c
    rw [hB, hB0, Matrix.zero_mul, trace_zero] at htr
    exact zero_ne_one htr
  · simp only [tdens, Qf, Nmat, mulVec_diagonal, dotProduct, ensDens, hB, Matrix.mul_apply,
      transpose_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

end purification

universe u

variable {M N : ℕ}

/-- **Time-dependent Kohn–Sham from a ground-state ensemble.** Spinless lattice fermions on a
connected graph with symmetric hopping of a common sign. Outside a closed, nowhere dense,
Lebesgue-null set `Z` of static potentials: let `Γ` be any ground-state ensemble of the
non-interacting `H_s(v_s)`, `v_s ∉ Z` (as produced by `ks_potential_exists`), and let `ψ(t)` be
any trajectory on the same sites, driven by a continuous potential, real at `t₀` and with the
density of `Γ` there. Then `Γ = Σ_k b_k b_kᵀ`, and near `t₀` the Kohn–Sham ensemble `φ_k(t)`
(from `b_k`), all driven by one gauge-fixed potential `v_s(t)`, has exactly the density of
`ψ(t)`; the evolution and the potential are unique for this decomposition `b`. -/
theorem td_kohn_sham_ensemble [NeZero M] [Nonempty (Conf M N)] {G : SimpleGraph (Fin M)}
    [DecidableRel G.Adj] (hG : G.Connected) {t : Fin M → Fin M → ℝ}
    (htsym : ∀ a b, t a b = t b a) {s : ℝ} (hts : ∀ a b, G.Adj a b → 0 < s * t a b)
    (hN0 : 0 < N) (hNM : N < M) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      ∀ vs0 ∉ Z, ∀ Γ ∈ Ens (H0Fw G t (0 : Conf M N → ℝ)) occF vs0,
      ∀ {C : Type u} [Fintype C] [DecidableEq C] (H0 : Matrix C C ℝ) (n : Fin M → C → ℝ)
        (Ntot : ℝ), H0.IsSymm → (∀ c, ∑ i, n i c = Ntot) →
      ∀ (ψ : ℝ → (C → ℝ) × (C → ℝ)) (v : ℝ → Fin M → ℝ),
        (∀ t, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t) → Continuous v →
      ∀ t0, (ψ t0).2 = 0 → (∀ i, ensDens occF Γ i = tdens n (ψ t0) i) →
        ∃ b : Conf M N → Conf M N → ℝ, Γ = ∑ k, vecMulVec (b k) (b k) ∧
        ∃ φ : Conf M N → ℝ → (Conf M N → ℝ) × (Conf M N → ℝ), ∃ vs : ℝ → Fin M → ℝ,
          (∀ k, φ k t0 = (b k, 0)) ∧
          (∀ᶠ t' in 𝓝 t0, (∀ k, HasDerivAt (φ k) (schr (H0Fw G t 0) occF (vs t') (φ k t')) t') ∧
            ∑ i, vs t' i = 0 ∧ ∀ i, ∑ k, tdens occF (φ k t') i = tdens n (ψ t') i) ∧
          ∀ φ' : Conf M N → ℝ → (Conf M N → ℝ) × (Conf M N → ℝ), ∀ vs' : ℝ → Fin M → ℝ,
            (∀ k, φ' k t0 = (b k, 0)) →
            (∀ᶠ t' in 𝓝 t0,
              (∀ k, HasDerivAt (φ' k) (schr (H0Fw G t 0) occF (vs' t') (φ' k t')) t') ∧
              ∑ i, vs' t' i = 0 ∧ ∀ i, ∑ k, tdens occF (φ' k t') i = tdens n (ψ t') i) →
            (∀ k, φ' k =ᶠ[𝓝 t0] φ k) ∧ vs' =ᶠ[𝓝 t0] vs := by
  obtain ⟨Z, hcl, hint, hvol, hZ⟩ := generic_td_vrep hG htsym hts hN0 hNM 0
  refine ⟨Z, hcl, hint, hvol,
    fun vs0 hvs0 Γ hΓ C _ _ H0 n Ntot hH0 hN ψ v hψ hv t0 hreal hρ0 => ?_⟩
  have hHs := H0Fw_isSymm G htsym (0 : Conf M N → ℝ)
  obtain ⟨b, hΓb, heig, ⟨k0, hk0⟩, hdens⟩ := ens_purify hΓ
  have hgs : ∀ k, b k ≠ 0 → IsGroundState (hamN (H0Fw G t 0) occF vs0) (b k) := fun k hk =>
    isGroundState_of_eigen_gs (hamN_isSymm hHs occF vs0) hk (heig k)
  have hneg : ∀ k w, w ⬝ᵥ (kMat (H0Fw G t 0) occF (b k) *ᵥ w) ≤ 0 := by
    intro k w
    by_cases hk : b k = 0
    · simp [hk, kMat_form]
    · exact kMat_nonpos hHs (hgs k hk) w
  have hb := mem_omega_glue hHs hneg k0 (hZ vs0 hvs0 (b k0) (hgs k0 hk0))
  have hreal' : ψ t0 = ((ψ t0).1, 0) := Prod.ext rfl hreal
  refine ⟨b, hΓb, van_leeuwen_ens hH0 hN hψ hv hHs sum_occF hb
    (fun i => by rw [hdens, hρ0]) (fun i => ?_)⟩
  rw [hreal', tcur_real]
  simp [tcur_real]

end DFT
