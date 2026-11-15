/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.TDDFT.Ensemble

/-!
# Ground-state ensembles of a generic Hamiltonian are pure

Outside an exceptional set built like that of `td_kohn_sham_ensemble` (the zero set of the Krylov
determinants of the non-interacting Hamiltonian) the ensemble formulation of time-dependent
Kohn–Sham adds no case to the pure-state one: the ground level is simple, so the only ground-state
ensemble is the projector on the ground state, and the Kohn–Sham potential does not depend on how
that projector is written as a sum of rank-one terms.

* `eq_vecMulVec_of_simple`: a symmetric matrix of trace one whose columns lie in a
  one-dimensional eigenspace is the projector `ψ₀ ψ₀ᵀ` (positivity is not needed).
* `Ens_eq_singleton_of_simple`, `Ens_eq_singleton_of_hstar`: if the ground level of `H(v)` is
  simple, in particular if (H*) holds at `v`, then `Ens H0 n v = {ψ₀ ψ₀ᵀ}`.
* `generic_Ens_pure`: for spinless lattice fermions this holds outside a closed, nowhere dense,
  null set of potentials.
* `decomp_pure`: if `ψ₀ ψ₀ᵀ = Σ_k b_k b_kᵀ` then `b_k = α_k ψ₀` with `Σ_k α_k² = 1`.
* `schr_smul`, `tdens_smul`, `kMat_smul`: scaling of the dynamics, the density and the
  force-balance matrix.
* `van_leeuwen_ens_of_pure`: for a real target state at `t₀`, the members of any such
  decomposition evolve as `α_k φ(t)`, with `φ(t)` the pure trajectory, under the potential of the
  pure state; this is the only ensemble evolution from `{α_k ψ₀}` with the prescribed density and
  a gauge-fixed potential.
* `td_kohn_sham_ensemble_pure`: time-dependent Kohn–Sham for lattice fermions with one exceptional
  set `Z`: outside it the pure-state statement (`td_kohn_sham`) holds for every ground state, the
  ground-state ensemble is pure, and every decomposition of it has the same Kohn–Sham potential.
-/

namespace DFT

open Matrix Set Filter Topology MeasureTheory

section purity

variable {C V : Type*} [Fintype C]

/-- If `A Γ = E Γ`, every column of `Γ` is an eigenvector of `A` at `E` (or zero). -/
lemma mulVec_col_of_mul_eq {A Γ : Matrix C C ℝ} {E : ℝ} (heig : A * Γ = E • Γ) (c : C) :
    A *ᵥ (fun a => Γ a c) = E • fun a => Γ a c :=
  funext fun a => congrFun (congrFun heig a) c

/-- A symmetric matrix of trace one supported on a one-dimensional eigenspace is the projector on
it. Positivity is not needed. -/
lemma eq_vecMulVec_of_simple {A Γ : Matrix C C ℝ} {E : ℝ} {ψ0 : C → ℝ}
    (hsym : Γᵀ = Γ) (htr : Γ.trace = 1) (heig : A * Γ = E • Γ)
    (hn : ψ0 ⬝ᵥ ψ0 = 1) (hsimple : ∀ φ : C → ℝ, A *ᵥ φ = E • φ → ∃ a : ℝ, φ = a • ψ0) :
    Γ = vecMulVec ψ0 ψ0 := by
  choose β hβ using fun c => hsimple _ (mulVec_col_of_mul_eq heig c)
  have hΓ : ∀ a c, Γ a c = β c * ψ0 a := fun a c => congrFun (hβ c) a
  have hs : ∀ a c, Γ a c = Γ c a := fun a c => congrFun (congrFun hsym c) a
  have hn' : ∑ a, ψ0 a * ψ0 a = 1 := hn
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = ∑ a, β a * ψ0 a := ⟨_, rfl⟩
  have hβ' : ∀ c, β c = lam * ψ0 c := by
    intro c
    have h1 : ∀ a, β c * (ψ0 a * ψ0 a) = β a * ψ0 a * ψ0 c := by
      intro a
      have := hs a c
      rw [hΓ a c, hΓ c a] at this
      linear_combination ψ0 a * this
    calc β c = β c * ∑ a, ψ0 a * ψ0 a := by rw [hn', mul_one]
      _ = ∑ a, β a * ψ0 a * ψ0 c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => h1 a
      _ = lam * ψ0 c := by rw [hlam, Finset.sum_mul]
  have hlam1 : lam = 1 := by
    have htr' : ∑ a, Γ a a = 1 := htr
    have h2 : ∀ a, Γ a a = lam * (ψ0 a * ψ0 a) := fun a => by rw [hΓ, hβ']; ring
    simp only [h2] at htr'
    rw [← Finset.mul_sum, hn', mul_one] at htr'
    exact htr'
  ext a c
  rw [vecMulVec_apply, hΓ, hβ', hlam1]; ring

variable [DecidableEq C] [Fintype V] [Nonempty C]

/-- If the ground level of `H(v)` is simple, the only ground-state ensemble is the pure one. -/
theorem Ens_eq_singleton_of_simple {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ)
    {v : V → ℝ} {ψ0 : C → ℝ} (hψ0 : IsGroundState (hamN H0 n v) ψ0) (hn : ψ0 ⬝ᵥ ψ0 = 1)
    (hsimple : ∀ φ : C → ℝ, hamN H0 n v *ᵥ φ = Egs H0 n v • φ → ∃ a : ℝ, φ = a • ψ0) :
    Ens H0 n v = {vecMulVec ψ0 ψ0} := by
  rw [Set.eq_singleton_iff_unique_mem]
  exact ⟨pure_mem_Ens hH0 n hψ0 hn, fun Γ ⟨hsym, _, htr, heig⟩ =>
    eq_vecMulVec_of_simple hsym htr heig hn hsimple⟩

/-- If (H*) holds at `v` (every Krylov determinant nonzero), `H(v)` has exactly one ground-state
ensemble, and it is pure. -/
theorem Ens_eq_singleton_of_hstar {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ)
    {v : V → ℝ} {ord : C → ℕ} (hv : ∀ c, MvPolynomial.eval v (krylovPoly H0 n c ord) ≠ 0) :
    ∃ ψ0 : C → ℝ, IsGroundState (hamN H0 n v) ψ0 ∧ ψ0 ⬝ᵥ ψ0 = 1 ∧
      Ens H0 n v = {vecMulVec ψ0 ψ0} := by
  have hS := hamN_isSymm hH0 n v
  obtain ⟨ψ0, hψ0, hn⟩ := exists_groundState hS
  have heig0 : hamN H0 n v *ᵥ ψ0 = Egs H0 n v • ψ0 := by
    have := isGroundState_eigen hS hψ0
    rw [hn, div_one, qf_groundState_eq hS hψ0 hn] at this
    exact this
  have hv' : ∀ c, (kry (hamN H0 n v) c ord).det ≠ 0 := fun c => by
    rw [← eval_krylovPoly]; exact hv c
  exact ⟨ψ0, hψ0, hn, Ens_eq_singleton_of_simple hH0 n hψ0 hn fun φ hφ =>
    (eigen_unique_of_hstar hS hv' hψ0.1 heig0 hφ).2⟩

end purity

section decomposition

variable {C κ : Type*} [Fintype C] [Fintype κ]

/-- **Decompositions of a pure state are collinear.** If `ψ₀ ψ₀ᵀ = Σ_k b_k b_kᵀ` with `ψ₀`
normalised, then `b_k = (b_k · ψ₀) ψ₀` and the squared coefficients add up to one. -/
lemma decomp_pure {ψ0 : C → ℝ} (hn : ψ0 ⬝ᵥ ψ0 = 1) {b : κ → C → ℝ}
    (hb : vecMulVec ψ0 ψ0 = ∑ k, vecMulVec (b k) (b k)) :
    (∀ k, b k = (b k ⬝ᵥ ψ0) • ψ0) ∧ ∑ k, (b k ⬝ᵥ ψ0) ^ 2 = 1 := by
  have hn' : ∑ a, ψ0 a * ψ0 a = 1 := hn
  have hE : ∀ a c, ∑ k, b k a * b k c = ψ0 a * ψ0 c := by
    intro a c
    have := congrFun (congrFun hb a) c
    rw [Matrix.sum_apply] at this
    simpa only [vecMulVec_apply] using this.symm
  have h1 : ∀ c, ∑ k, (b k ⬝ᵥ ψ0) * b k c = ψ0 c := by
    intro c
    calc ∑ k, (b k ⬝ᵥ ψ0) * b k c = ∑ k, ∑ a, ψ0 a * (b k a * b k c) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [dotProduct, Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ a, ψ0 a * ∑ k, b k a * b k c := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ a, (ψ0 a * ψ0 a) * ψ0 c := Finset.sum_congr rfl fun a _ => by rw [hE]; ring
      _ = ψ0 c := by rw [← Finset.sum_mul, hn', one_mul]
  have h2 : ∑ k, (b k ⬝ᵥ ψ0) ^ 2 = 1 := by
    calc ∑ k, (b k ⬝ᵥ ψ0) ^ 2 = ∑ k, ∑ c, ψ0 c * ((b k ⬝ᵥ ψ0) * b k c) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have h : (b k ⬝ᵥ ψ0) ^ 2 = (b k ⬝ᵥ ψ0) * ∑ c, b k c * ψ0 c := sq _
          rw [h, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ = ∑ c, ψ0 c * ∑ k, (b k ⬝ᵥ ψ0) * b k c := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
      _ = 1 := by simp only [h1]; exact hn'
  refine ⟨fun k => funext fun a => ?_, h2⟩
  have h3 : ∑ k, (b k a - (b k ⬝ᵥ ψ0) * ψ0 a) ^ 2 = 0 := by
    have h : ∀ k, (b k a - (b k ⬝ᵥ ψ0) * ψ0 a) ^ 2 = b k a * b k a -
        2 * ψ0 a * ((b k ⬝ᵥ ψ0) * b k a) + ψ0 a ^ 2 * (b k ⬝ᵥ ψ0) ^ 2 := fun k => by ring
    simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hE, h1, h2]
    ring
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg _).mp h3 k (Finset.mem_univ k)
  have h5 := (pow_eq_zero_iff two_ne_zero).mp h4
  rw [Pi.smul_apply, smul_eq_mul]
  linarith

end decomposition

section scaling

variable {C V : Type*} [Fintype C] [Fintype V]

/-- The Schrödinger vector field is linear in the state. -/
lemma schr_smul [DecidableEq C] (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) (a : ℝ)
    (ψ : (C → ℝ) × (C → ℝ)) : schr H0 n v (a • ψ) = a • schr H0 n v ψ := by
  simp only [schr, Prod.smul_fst, Prod.smul_snd, mulVec_smul, Prod.smul_mk, smul_neg]

omit [Fintype V] in
/-- The density is quadratic in the state. -/
lemma tdens_smul [DecidableEq C] (n : V → C → ℝ) (a : ℝ) (ψ : (C → ℝ) × (C → ℝ)) (i : V) :
    tdens n (a • ψ) i = a ^ 2 * tdens n ψ i := by
  simp only [tdens, Qf, Prod.smul_fst, Prod.smul_snd, mulVec_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

omit [Fintype V] in
/-- The force-balance matrix is quadratic in the state. -/
lemma kMat_smul (H0 : Matrix C C ℝ) (n : V → C → ℝ) (a : ℝ) (ψ : C → ℝ) :
    kMat H0 n (a • ψ) = a ^ 2 • kMat H0 n ψ := by
  ext i j
  simp only [kMat, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => by ring

end scaling

section vanLeeuwen

variable {C κ V : Type*} [Fintype C] [DecidableEq C] [Fintype κ] [Fintype V]
  {C₁ : Type*} [Fintype C₁] [DecidableEq C₁] {H1 : Matrix C₁ C₁ ℝ} {n1 : V → C₁ → ℝ} {N1 : ℝ}
  (hH1 : H1.IsSymm) (hN1 : ∀ c, ∑ i, n1 i c = N1)
  {ψ : ℝ → (C₁ → ℝ) × (C₁ → ℝ)} {v : ℝ → V → ℝ}
  (hψ : ∀ t, HasDerivAt ψ (schr H1 n1 (v t) (ψ t)) t) (hv : Continuous v)
  {H0 : Matrix C C ℝ} {n : V → C → ℝ} {Ntot : ℝ} (hH0 : H0.IsSymm) (hN : ∀ c, ∑ i, n i c = Ntot)
  [Nonempty V]
include hH1 hN1 hψ hv hH0 hN

/-- **Every decomposition of a pure state has the pure Kohn–Sham potential.** Let `ψ(t)` be driven
by a continuous potential with `ψ(t₀)` real, and let `φ(t)`, driven by the gauge-fixed `v_s(t)`,
start from the real state `ψ₀` (force-balance form negative semidefinite with only
constant zero modes) and reproduce the density of `ψ(t)`. For any coefficients with
`Σ_k α_k² = 1`, the ensemble `{α_k φ(t)}` is driven by the same `v_s(t)` and has the density
of `ψ(t)`, and any ensemble evolution from `{α_k ψ₀}` with that density and a gauge-fixed
potential coincides with it near `t₀`, potential included. Both systems have
symmetric Hamiltonians and conserved particle numbers. -/
theorem van_leeuwen_ens_of_pure {t0 : ℝ} {ψ0 : C → ℝ}
    (hneg : ∀ w, w ⬝ᵥ (kMat H0 n ψ0 *ᵥ w) ≤ 0)
    (hdef : ∀ w, w ⬝ᵥ (kMat H0 n ψ0 *ᵥ w) = 0 → ∃ c, ∀ i, w i = c)
    (hreal : (ψ t0).2 = 0)
    {φ : ℝ → (C → ℝ) × (C → ℝ)} {vs : ℝ → V → ℝ} (hφ0 : φ t0 = (ψ0, 0))
    (hφ : ∀ᶠ t in 𝓝 t0, HasDerivAt φ (schr H0 n (vs t) (φ t)) t ∧ ∑ i, vs t i = 0 ∧
      ∀ i, tdens n (φ t) i = tdens n1 (ψ t) i)
    {α : κ → ℝ} (hα : ∑ k, α k ^ 2 = 1) :
    (∀ᶠ t in 𝓝 t0, (∀ k, HasDerivAt (fun τ => α k • φ τ) (schr H0 n (vs t) (α k • φ t)) t) ∧
        ∀ i, ∑ k, tdens n (α k • φ t) i = tdens n1 (ψ t) i) ∧
    ∀ φ' : κ → ℝ → (C → ℝ) × (C → ℝ), ∀ vs' : ℝ → V → ℝ, (∀ k, φ' k t0 = (α k • ψ0, 0)) →
      (∀ᶠ t in 𝓝 t0, (∀ k, HasDerivAt (φ' k) (schr H0 n (vs' t) (φ' k t)) t) ∧
        ∑ i, vs' t i = 0 ∧ ∀ i, ∑ k, tdens n (φ' k t) i = tdens n1 (ψ t) i) →
      (∀ k, φ' k =ᶠ[𝓝 t0] fun τ => α k • φ τ) ∧ vs' =ᶠ[𝓝 t0] vs := by
  classical
  have hex : ∀ᶠ t in 𝓝 t0,
      (∀ k, HasDerivAt (fun τ => α k • φ τ) (schr H0 n (vs t) (α k • φ t)) t) ∧
      ∑ i, vs t i = 0 ∧ ∀ i, ∑ k, tdens n (α k • φ t) i = tdens n1 (ψ t) i := by
    filter_upwards [hφ] with t ⟨hd, hs, hρ⟩
    refine ⟨fun k => ?_, hs, fun i => ?_⟩
    · rw [schr_smul]; exact hd.const_smul (α k)
    · simp only [tdens_smul]
      rw [← Finset.sum_mul, hα, one_mul, hρ i]
  refine ⟨hex.mono fun t h => ⟨h.1, h.2.2⟩, fun φ' vs' h0' h' => ?_⟩
  have hsm : ∀ k, (α k • ψ0, (0 : C → ℝ)) = α k • (ψ0, (0 : C → ℝ)) := fun k =>
    Prod.ext rfl (smul_zero (α k)).symm
  have hnegk : ∀ k w, w ⬝ᵥ (kMat H0 n (α k • ψ0) *ᵥ w) ≤ 0 := fun k w => by
    rw [kMat_smul, smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hneg w)
  obtain ⟨k0, hk0⟩ : ∃ k, α k ≠ 0 := by
    by_contra h
    push Not at h
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      zero_ne_one] at hα
  have hdefk0 : ∀ w, w ⬝ᵥ (kMat H0 n (α k0 • ψ0) *ᵥ w) = 0 → ∃ c, ∀ i, w i = c := fun w hw => by
    rw [kMat_smul, smul_mulVec, dotProduct_smul, smul_eq_mul] at hw
    exact hdef w ((mul_eq_zero.mp hw).resolve_left (pow_ne_zero 2 hk0))
  have hmem := mem_omega_glue hH0 hnegk k0 hdefk0
  have hρ0' : ∀ i, ∑ k, tdens n (α k • ψ0, (0 : C → ℝ)) i = tdens n1 (ψ t0) i := fun i => by
    have h := hφ.self_of_nhds.2.2 i
    rw [hφ0] at h
    simp only [hsm, tdens_smul]
    rw [← Finset.sum_mul, hα, one_mul, h]
  have hj0' : ∀ i, ∑ k, tcur H0 n (α k • ψ0, (0 : C → ℝ)) i = tcur H1 n1 (ψ t0) i := fun i => by
    have hreal' : ψ t0 = ((ψ t0).1, 0) := Prod.ext rfl hreal
    rw [hreal', tcur_real]
    simp only [tcur_real, Finset.sum_const_zero]
  obtain ⟨Φ, W, -, -, huniq⟩ := van_leeuwen_ens hH1 hN1 hψ hv hH0 hN hmem hρ0' hj0'
  have h8 := huniq (fun k τ => α k • φ τ) vs
    (fun k => by rw [hφ0]; exact (hsm k).symm) hex
  have h9 := huniq φ' vs' h0' h'
  exact ⟨fun k => (h9.1 k).trans (h8.1 k).symm, h9.2.trans h8.2.symm⟩

end vanLeeuwen

universe u w

variable {M N : ℕ}

/-- **Ground-state ensembles of lattice fermions are generically pure.** Spinless lattice fermions
on a connected graph, symmetric hopping of a common sign, any interaction: outside a closed,
nowhere dense, Lebesgue-null set of static potentials `v`, the only ground-state ensemble of `H(v)`
is the projector on its normalised ground state. -/
theorem generic_Ens_pure [Nonempty (Conf M N)] {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (Vint : Conf M N → ℝ) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      ∀ v ∉ Z, ∃ ψ0 : Conf M N → ℝ, IsGroundState (hamN (H0Fw G t Vint) occF v) ψ0 ∧
        ψ0 ⬝ᵥ ψ0 = 1 ∧ Ens (H0Fw G t Vint) occF v = {vecMulVec ψ0 ψ0} := by
  set ord : Conf M N → ℕ := fun j => (Fintype.equivFin (Conf M N) j : ℕ)
  set Q := ∏ c, krylovPoly (H0Fw G t Vint) occF c ord
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun c _ => hstar_lattice_fermions_w hG hts c Vint)
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hQ
  refine ⟨_, hcl, hint, volume_zeroSet hQ, fun v hv => ?_⟩
  have hv' : ∀ c, MvPolynomial.eval v (krylovPoly (H0Fw G t Vint) occF c ord) ≠ 0 := by
    intro c hc
    apply hv
    change MvPolynomial.eval v Q = 0
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) hc
  exact Ens_eq_singleton_of_hstar (H0Fw_isSymm G htsym Vint) occF hv'

/-- **Time-dependent Kohn–Sham from a ground-state ensemble: purity and independence of the
decomposition.** Spinless lattice fermions on a connected graph with symmetric hopping of a common
sign, `0 < N < M`. Outside a closed, nowhere dense, Lebesgue-null set `Z` of static potentials
(constructed as the zero set of the product of the Krylov determinants of the non-interacting
Hamiltonian), the conclusion of `td_kohn_sham` holds
for every ground state, so one `Z` serves the pure and the ensemble statements, and the
non-interacting `H_s(v_s)` has exactly one ground-state ensemble, the projector on its normalised
ground state `ψ₀`. Let `ψ(t)` be any trajectory on the same sites, driven by a continuous
potential, under a symmetric Hamiltonian with a conserved particle number, real at `t₀` and with
the density of `ψ₀` there. Then near `t₀` a Kohn–Sham trajectory
`φ(t)` from `ψ₀`, driven by a gauge-fixed potential `v_s(t)`, has the density of `ψ(t)`. Moreover,
for every decomposition `ψ₀ ψ₀ᵀ = Σ_k b_k b_kᵀ` (any finite index type), `b_k = α_k ψ₀` with
`Σ_k α_k² = 1`, the ensemble `{α_k φ(t)}` driven by the same `v_s(t)` has the density of `ψ(t)`,
and near `t₀` it is the only ensemble evolution from `{b_k}` with that density and a
gauge-fixed potential: the Kohn–Sham potential does not depend on the decomposition. -/
theorem td_kohn_sham_ensemble_pure [NeZero M] [Nonempty (Conf M N)] {G : SimpleGraph (Fin M)}
    [DecidableRel G.Adj] (hG : G.Connected) {t : Fin M → Fin M → ℝ}
    (htsym : ∀ a b, t a b = t b a) {s : ℝ} (hts : ∀ a b, G.Adj a b → 0 < s * t a b)
    (hN0 : 0 < N) (hNM : N < M) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      ∀ vs0 ∉ Z, (∀ φ0 : Conf M N → ℝ,
        IsGroundState (hamN (H0Fw G t (0 : Conf M N → ℝ)) occF vs0) φ0 →
        ∀ {C : Type u} [Fintype C] [DecidableEq C] (H0 : Matrix C C ℝ) (n : Fin M → C → ℝ)
          (Ntot : ℝ), H0.IsSymm → (∀ c, ∑ i, n i c = Ntot) →
        ∀ (ψ : ℝ → (C → ℝ) × (C → ℝ)) (v : ℝ → Fin M → ℝ),
          (∀ t, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t) → Continuous v →
        ∀ t0, (ψ t0).2 = 0 → (∀ i, tdens occF (φ0, 0) i = tdens n (ψ t0) i) →
          ∃ φ : ℝ → (Conf M N → ℝ) × (Conf M N → ℝ), ∃ vs : ℝ → Fin M → ℝ, φ t0 = (φ0, 0) ∧
            (∀ᶠ t' in 𝓝 t0, HasDerivAt φ (schr (H0Fw G t 0) occF (vs t') (φ t')) t' ∧
              ∑ i, vs t' i = 0 ∧ ∀ i, tdens occF (φ t') i = tdens n (ψ t') i) ∧
            ∀ φ' : ℝ → (Conf M N → ℝ) × (Conf M N → ℝ), ∀ vs' : ℝ → Fin M → ℝ,
              φ' t0 = (φ0, 0) →
              (∀ᶠ t' in 𝓝 t0, HasDerivAt φ' (schr (H0Fw G t 0) occF (vs' t') (φ' t')) t' ∧
                ∑ i, vs' t' i = 0 ∧ ∀ i, tdens occF (φ' t') i = tdens n (ψ t') i) →
              φ' =ᶠ[𝓝 t0] φ ∧ vs' =ᶠ[𝓝 t0] vs) ∧
      ∃ ψ0 : Conf M N → ℝ,
        IsGroundState (hamN (H0Fw G t (0 : Conf M N → ℝ)) occF vs0) ψ0 ∧ ψ0 ⬝ᵥ ψ0 = 1 ∧
        Ens (H0Fw G t (0 : Conf M N → ℝ)) occF vs0 = {vecMulVec ψ0 ψ0} ∧
      ∀ {C : Type u} [Fintype C] [DecidableEq C] (H0 : Matrix C C ℝ) (n : Fin M → C → ℝ)
        (Ntot : ℝ), H0.IsSymm → (∀ c, ∑ i, n i c = Ntot) →
      ∀ (ψ : ℝ → (C → ℝ) × (C → ℝ)) (v : ℝ → Fin M → ℝ),
        (∀ t, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t) → Continuous v →
      ∀ t0, (ψ t0).2 = 0 → (∀ i, tdens occF (ψ0, 0) i = tdens n (ψ t0) i) →
        ∃ φ : ℝ → (Conf M N → ℝ) × (Conf M N → ℝ), ∃ vs : ℝ → Fin M → ℝ, φ t0 = (ψ0, 0) ∧
          (∀ᶠ t' in 𝓝 t0, HasDerivAt φ (schr (H0Fw G t 0) occF (vs t') (φ t')) t' ∧
            ∑ i, vs t' i = 0 ∧ ∀ i, tdens occF (φ t') i = tdens n (ψ t') i) ∧
          ∀ {κ : Type w} [Fintype κ] (b : κ → Conf M N → ℝ),
            vecMulVec ψ0 ψ0 = ∑ k, vecMulVec (b k) (b k) →
            ∃ α : κ → ℝ, (∀ k, b k = α k • ψ0) ∧ ∑ k, α k ^ 2 = 1 ∧
              (∀ᶠ t' in 𝓝 t0,
                (∀ k, HasDerivAt (fun τ => α k • φ τ)
                  (schr (H0Fw G t 0) occF (vs t') (α k • φ t')) t') ∧
                ∀ i, ∑ k, tdens occF (α k • φ t') i = tdens n (ψ t') i) ∧
              ∀ φ' : κ → ℝ → (Conf M N → ℝ) × (Conf M N → ℝ), ∀ vs' : ℝ → Fin M → ℝ,
                (∀ k, φ' k t0 = (b k, 0)) →
                (∀ᶠ t' in 𝓝 t0,
                  (∀ k, HasDerivAt (φ' k) (schr (H0Fw G t 0) occF (vs' t') (φ' k t')) t') ∧
                  ∑ i, vs' t' i = 0 ∧ ∀ i, ∑ k, tdens occF (φ' k t') i = tdens n (ψ t') i) →
                (∀ k, φ' k =ᶠ[𝓝 t0] fun τ => α k • φ τ) ∧ vs' =ᶠ[𝓝 t0] vs := by
  set ord : Conf M N → ℕ := fun j => (Fintype.equivFin (Conf M N) j : ℕ)
  set Q := ∏ c, krylovPoly (H0Fw G t (0 : Conf M N → ℝ)) occF c ord
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun c _ => hstar_lattice_fermions_w hG hts c 0)
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hQ
  refine ⟨_, hcl, hint, volume_zeroSet hQ, fun vs0 hvs0 => ?_⟩
  have hv' : ∀ c,
      MvPolynomial.eval vs0 (krylovPoly (H0Fw G t (0 : Conf M N → ℝ)) occF c ord) ≠ 0 := by
    intro c hc
    apply hvs0
    change MvPolynomial.eval vs0 Q = 0
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) hc
  have hHs := H0Fw_isSymm G htsym (0 : Conf M N → ℝ)
  refine ⟨fun φ0 hφ0g {C} _ _ H0 n Ntot hH0 hN ψ v hψ hv t0 hreal hρ0 => ?_, ?_⟩
  · have hj0 : ∀ i, tcur (H0Fw G t 0) occF (φ0, 0) i = tcur H0 n (ψ t0) i := by
      intro i
      have : ψ t0 = ((ψ t0).1, 0) := Prod.ext rfl hreal
      rw [tcur_real, this, tcur_real]
    exact van_leeuwen_unique' hH0 hN hψ hv hHs sum_occF (mem_omega_of_definite hHs
      (kMat_nonpos hHs hφ0g) fun w hw => kMat_definite_of_hstar hHs (rigid_occF hN0 hNM) hv'
        hφ0g hw) hρ0 hj0
  obtain ⟨ψ0, hψ0, hn, hEns⟩ := Ens_eq_singleton_of_hstar hHs occF hv'
  refine ⟨ψ0, hψ0, hn, hEns, fun {C} _ _ H0 n Ntot hH0 hN ψ v hψ hv t0 hreal hρ0 => ?_⟩
  have hneg := kMat_nonpos hHs hψ0
  have hdef : ∀ w : Fin M → ℝ, w ⬝ᵥ (kMat (H0Fw G t 0) occF ψ0 *ᵥ w) = 0 → ∃ k, ∀ i, w i = k :=
    fun w hw => kMat_definite_of_hstar hHs (rigid_occF hN0 hNM) hv' hψ0 hw
  have hj0 : ∀ i, tcur (H0Fw G t 0) occF (ψ0, 0) i = tcur H0 n (ψ t0) i := by
    intro i
    have : ψ t0 = ((ψ t0).1, 0) := Prod.ext rfl hreal
    rw [tcur_real, this, tcur_real]
  obtain ⟨φ, vs, hφ0, hev, -⟩ := van_leeuwen_unique' hH0 hN hψ hv hHs sum_occF
    (mem_omega_of_definite hHs hneg hdef) hρ0 hj0
  refine ⟨φ, vs, hφ0, hev, fun {κ} _ b hb => ?_⟩
  obtain ⟨hbα, hα⟩ := decomp_pure hn hb
  obtain ⟨hexist, huniq⟩ := van_leeuwen_ens_of_pure hH0 hN hψ hv hHs sum_occF hneg hdef hreal
    hφ0 hev hα
  exact ⟨fun k => b k ⬝ᵥ ψ0, hbα, hα, hexist, fun φ' vs' h0' h' =>
    huniq φ' vs' (fun k => (h0' k).trans (congrArg (fun x => (x, (0 : Conf M N → ℝ))) (hbα k)))
      h'⟩

end DFT
