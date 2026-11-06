/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.TDDFT.GroundStart
import LatticeDFT.TDDFT.Global
import LatticeDFT.Spin.SpinField

/-!
# Spin-resolved lattice TDDFT

With two spin species the particle numbers `N↑` and `N↓` are conserved separately, so the
force-balance matrix of the spin densities `(n↑, n↓)` always has two zero modes (a constant on each
spin) and the one-constant gauge `K + 𝟙𝟙ᵀ` of the spinless theory is singular. We pass to `2(K+1) - 1`
reduced observables `occR` (`o_i = n_{i↑} - (Σ_{j≥1} n_{j↓})/(K+1)`, `o'_j = n_{j↓}` for `j ≥ 1`)
that carry the same information but only one conserved sum. All of the spinless machinery (local
existence and uniqueness, global continuation, van Leeuwen) then applies verbatim.

* `det_kry_add_smul_one`, `isGroundState_add_smul_one`: Krylov determinants and ground states do
  not see a constant energy shift.
* `rigid_occR`, `sum_occR`, `potW_occR`, `exists_spinPot_gauge`: the reduced observables are rigid
  modulo one constant; every spin-dependent potential `(v↑, v↓)` is `spinPot w` (with `Σ w = 0`) up
  to one constant per spin.
* `generic_ground_mem_omega_spin`: for almost every spin-dependent potential, every ground state
  lies in `Ω`.
* `td_spin_existence`, `td_spin_uniqueness`: spin-resolved TDDFT in spin language. The spin
  densities `(ρ↑, ρ↓)(t)` determine the spin-dependent potential up to one constant per spin.
-/

namespace LatticeDFT

open Matrix

section shift

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The binomial change of basis between the Krylov vectors of `H` and of `H + λ`. -/
noncomputable def binU (lam : ℝ) : Matrix C C ℝ := fun j' j =>
  if (Fintype.equivFin C j' : ℕ) ≤ Fintype.equivFin C j then
    (Nat.choose (Fintype.equivFin C j) (Fintype.equivFin C j') : ℝ) *
      lam ^ ((Fintype.equivFin C j : ℕ) - Fintype.equivFin C j')
  else 0

lemma det_binU (lam : ℝ) : (binU lam : Matrix C C ℝ).det = 1 := by
  set e := Fintype.equivFin C
  have h := det_reindex_self e (binU lam : Matrix C C ℝ)
  rw [← h, det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [binU, reindex_apply, submatrix_apply, e]
  · intro i j hij
    simp only [reindex_apply, submatrix_apply, binU, e, Equiv.apply_symm_apply]
    have : ¬ (i : ℕ) ≤ j := not_le.mpr hij
    simp only [this, ↓reduceIte]

lemma add_smul_one_pow_apply (H : Matrix C C ℝ) (lam : ℝ) (k : ℕ) (i c : C) :
    ((H + lam • (1 : Matrix C C ℝ)) ^ k) i c =
      ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * lam ^ (k - m) * (H ^ m) i c := by
  have hc : Commute H (lam • (1 : Matrix C C ℝ)) := (Commute.one_right H).smul_right lam
  rw [hc.add_pow, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro m _
  rw [smul_pow, one_pow, Matrix.mul_smul, Matrix.mul_one, ← Nat.cast_comm, ← nsmul_eq_mul,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Matrix.smul_apply, smul_eq_mul]

/-- **Krylov determinants are invariant under a constant energy shift.** -/
lemma det_kry_add_smul_one (H : Matrix C C ℝ) (lam : ℝ) (c : C) :
    (kry (H + lam • (1 : Matrix C C ℝ)) c (fun j => (Fintype.equivFin C j : ℕ))).det =
      (kry H c (fun j => (Fintype.equivFin C j : ℕ))).det := by
  set e := Fintype.equivFin C
  have hk : kry (H + lam • (1 : Matrix C C ℝ)) c (fun j => (e j : ℕ)) =
      kry H c (fun j => (e j : ℕ)) * binU lam := by
    ext i j
    rw [Matrix.mul_apply]
    change ((H + lam • (1 : Matrix C C ℝ)) ^ (e j : ℕ)) i c =
      ∑ j', (H ^ (e j' : ℕ)) i c * binU lam j' j
    rw [add_smul_one_pow_apply, ← e.symm.sum_comp]
    simp only [binU, e, Equiv.apply_symm_apply]
    rw [Fin.sum_univ_eq_sum_range (fun m => (H ^ m) i c * if m ≤ (Fintype.equivFin C j : ℕ) then
      ((Fintype.equivFin C j : ℕ).choose m : ℝ) * lam ^ ((Fintype.equivFin C j : ℕ) - m) else 0)]
    have hlt : (Fintype.equivFin C j : ℕ) + 1 ≤ Fintype.card C := (Fintype.equivFin C j).2
    symm
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hlt)]
    · apply Finset.sum_congr rfl
      intro m hm
      simp only [Nat.lt_succ_iff.mp (Finset.mem_range.mp hm), ↓reduceIte]
      ring
    · intro m _ hm
      have : ¬ m ≤ (Fintype.equivFin C j : ℕ) :=
        fun h => hm (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      simp only [this, ↓reduceIte, mul_zero]
  rw [hk, det_mul, det_binU, mul_one]

lemma isGroundState_add_smul_one {M : Matrix C C ℝ} {ψ : C → ℝ} (lam : ℝ) :
    IsGroundState (M + lam • (1 : Matrix C C ℝ)) ψ ↔ IsGroundState M ψ := by
  have hq : ∀ φ : C → ℝ, qf (M + lam • (1 : Matrix C C ℝ)) φ = qf M φ + lam * (φ ⬝ᵥ φ) := by
    intro φ
    simp only [qf, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
  unfold IsGroundState
  simp only [hq]
  constructor
  · rintro ⟨h0, h⟩; exact ⟨h0, fun φ => by have := h φ; nlinarith⟩
  · rintro ⟨h0, h⟩; exact ⟨h0, fun φ => by have := h φ; nlinarith⟩

end shift

section linear

variable {C V V' : Type*} [Fintype C] [DecidableEq C] [Fintype V]

omit [Fintype V] in
lemma tdens_eq_sum (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) (i : V) :
    tdens n ψ i = ∑ c, n i c * (ψ.1 c ^ 2 + ψ.2 c ^ 2) := by
  simp only [tdens, Qf, Nmat, dotProduct, mulVec, diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro c _; ring

omit [Fintype V] in
lemma tcur_eq_sum (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) (i : V) :
    tcur H0 n ψ i = 2 * ∑ a, ∑ c, H0 a c * n i c * (ψ.2 a * ψ.1 c - ψ.1 a * ψ.2 c) := by
  simp only [tcur, Nmat, dotProduct, mulVec, mul_diagonal, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro c _
  ring

lemma tdens_lin {n : V → C → ℝ} {n' : V' → C → ℝ} {L : V' → V → ℝ}
    (h : ∀ k c, n' k c = ∑ i, L k i * n i c) (ψ : (C → ℝ) × (C → ℝ)) (k : V') :
    tdens n' ψ k = ∑ i, L k i * tdens n ψ i := by
  simp only [tdens_eq_sum, h, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro c _
  ring

lemma tcur_lin (H0 : Matrix C C ℝ) {n : V → C → ℝ} {n' : V' → C → ℝ} {L : V' → V → ℝ}
    (h : ∀ k c, n' k c = ∑ i, L k i * n i c) (ψ : (C → ℝ) × (C → ℝ)) (k : V') :
    tcur H0 n' ψ k = ∑ i, L k i * tcur H0 n ψ i := by
  simp only [tcur_eq_sum, h, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun c _ => ?_
  ring

end linear

section spin

open MeasureTheory MvPolynomial

variable {K Nu Nd : ℕ}

/-- Index set of the reduced spin observables: all sites for the first family, sites `1, …, K` for
the second. -/
abbrev SpinIdx (K : ℕ) := Fin (K + 1) ⊕ Fin K

/-- Two-species configurations on `K + 1` sites. -/
abbrev SConf (K Nu Nd : ℕ) := Conf (K + 1) Nu × Conf (K + 1) Nd

/-- The reduced spin observables: `o_i = n_{i↑} - (Σ_{j≥1} n_{j↓})/(K+1)` for every site and
`o'_j = n_{j↓}` for `j ≥ 1`. They span the spin-resolved densities modulo the two conserved particle
numbers, and only their total sum is conserved, so the one-constant TDDFT framework applies. -/
noncomputable def occR : SpinIdx K → SConf K Nu Nd → ℝ :=
  Sum.elim (fun i x => occF i x.1 - (∑ j : Fin K, occF j.succ x.2) / (K + 1))
    (fun j x => occF j.succ x.2)

/-- The spin-dependent potential `(v↑, v↓)` coupled by the reduced potential `w`:
`v↑_i = w_i`, `v↓_0 = 0`, `v↓_j = w'_j - mean(w)` for `j ≥ 1`. -/
noncomputable def spinPot (w : SpinIdx K → ℝ) : Fin (K + 1) ⊕ Fin (K + 1) → ℝ :=
  Sum.elim (fun i => w (Sum.inl i))
    (fun j => Fin.cases 0 (fun j' => w (Sum.inr j') - (∑ i, w (Sum.inl i)) / (K + 1)) j)

lemma potW_occR (w : SpinIdx K → ℝ) (x : SConf K Nu Nd) :
    ∑ k, w k * occR k x = ∑ σi, spinPot w σi * occS σi x := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [occR, spinPot, occS, Sum.elim_inl, Sum.elim_inr]
  rw [Fin.sum_univ_succ (fun j => (Fin.cases (0 : ℝ) (fun j' => w (Sum.inr j') -
    (∑ i, w (Sum.inl i)) / (K + 1)) j : ℝ) * occF j x.2)]
  simp only [Fin.cases_zero, Fin.cases_succ, zero_mul, zero_add, mul_sub, sub_mul,
    Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

lemma sum_occR (x : SConf K Nu Nd) : ∑ k, occR k x = (Nu : ℝ) := by
  rw [Fintype.sum_sum_type]
  simp only [occR, Sum.elim_inl, Sum.elim_inr, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sum_occF' x.1]
  have hK : ((K : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Rigidity of the reduced spin observables**: modulo one overall constant. -/
theorem rigid_occR (hNu0 : 0 < Nu) (hNuM : Nu < K + 1) (hNd0 : 0 < Nd) (hNdM : Nd < K + 1) :
    Rigid (occR : SpinIdx K → SConf K Nu Nd → ℝ) := by
  intro w κ h
  have h' : ∀ x, ∑ σi, spinPot w σi * occS σi x = κ := fun x => (potW_occR w x) ▸ h x
  obtain ⟨a, b, hab⟩ := rigid_occS hNu0 hNuM hNd0 hNdM (spinPot w) κ h'
  have hb : b = 0 := by have := (hab 0).2; simp [spinPot] at this; linarith
  have hW : ∑ i, w (Sum.inl i) = (K + 1) * a := by
    simp only [show ∀ i, w (Sum.inl i) = a from fun i => by simpa [spinPot] using (hab i).1,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  refine ⟨a, ?_⟩
  rintro (i | j)
  · simpa [spinPot] using (hab i).1
  · have := (hab j.succ).2
    simp only [spinPot, Sum.elim_inr, Fin.cases_succ, hW, hb] at this
    have hK : ((K : ℝ) + 1) ≠ 0 := by positivity
    field_simp at this
    linarith

lemma hamN_occR (H0 : Matrix (SConf K Nu Nd) (SConf K Nu Nd) ℝ)
    (w : SpinIdx K → ℝ) : hamN H0 occR w = hamN H0 occS (spinPot w) := by
  unfold hamN
  congr 2
  funext x
  exact potW_occR w x

/-- Every spin-dependent potential is a reduced one, up to a constant on the down spins. -/
lemma exists_spinPot (V : Fin (K + 1) ⊕ Fin (K + 1) → ℝ) :
    ∃ (w : SpinIdx K → ℝ) (b : ℝ),
      ∀ σi, V σi = spinPot w σi + Sum.elim (fun _ => 0) (fun _ => b) σi := by
  set W := ∑ i, V (Sum.inl i)
  refine ⟨Sum.elim (fun i => V (Sum.inl i))
    (fun j => V (Sum.inr j.succ) - V (Sum.inr 0) + W / (K + 1)),
    V (Sum.inr 0), ?_⟩
  rintro (i | j)
  · simp [spinPot]
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp [spinPot]
    · simp [spinPot, W]

lemma hamN_occS_shift
    (H0 : Matrix (SConf K Nu Nd) (SConf K Nu Nd) ℝ)
    {V : Fin (K + 1) ⊕ Fin (K + 1) → ℝ} {w : SpinIdx K → ℝ} {b : ℝ}
    (h : ∀ σi, V σi = spinPot w σi + Sum.elim (fun _ => 0) (fun _ => b) σi) :
    hamN H0 occS V = hamN H0 occR w + (b * Nd) • (1 : Matrix _ _ ℝ) := by
  rw [hamN_occR]
  ext x y
  simp only [hamN]
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, diagonal_apply, diagonal_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs with hxy
  · subst hxy
    simp only [h, add_mul, Finset.sum_add_distrib, Fintype.sum_sum_type, occS, Sum.elim_inl,
      Sum.elim_inr, zero_mul, Finset.sum_const_zero, ← Finset.mul_sum, sum_occF' x.2]
    ring
  · ring

/-- **Spin-resolved TDDFT from the ground state, for almost every potential.** `Nu` up and `Nd`
down electrons (`0 < Nσ < K + 1`) on a connected graph, spin-conserving hopping of a common sign,
any diagonal interaction: outside a closed, nowhere dense, Lebesgue-null set of spin-dependent
potentials `(v↑, v↓)`, every ground state lies in the v-representability set `Ω` of the reduced
spin observables. `td_existence`, `td_uniqueness` and `td_global` then apply. -/
theorem generic_ground_mem_omega_spin {G : SimpleGraph (Fin (K + 1))} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin (K + 1) → Fin (K + 1) → ℝ} (htsym : ∀ a b, t a b = t b a)
    {s : ℝ} (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hNu0 : 0 < Nu) (hNuM : Nu < K + 1)
    (hNd0 : 0 < Nd) (hNdM : Nd < K + 1) (Vint : SConf K Nu Nd → ℝ) :
    ∃ Z : Set (Fin (K + 1) ⊕ Fin (K + 1) → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      ∀ V ∉ Z, ∀ ψ, IsGroundState (hamN (H0S G t Vint) occS V) ψ →
        ((ψ, 0) : (SConf K Nu Nd → ℝ) × (SConf K Nu Nd → ℝ))
          ∈ omega (H0S G t Vint) occR := by
  set ord : SConf K Nu Nd → ℕ :=
    fun j => (Fintype.equivFin (SConf K Nu Nd) j : ℕ)
  set Q := ∏ c, krylovPoly (H0S G t Vint) occS c ord
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hstar_spin hG hts c Vint
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hQ
  refine ⟨_, hcl, hint, volume_zeroSet hQ, fun V hV ψ hψ => ?_⟩
  obtain ⟨w, b, hwb⟩ := exists_spinPot V
  have hH := hamN_occS_shift (H0S G t Vint) hwb
  have hS := H0S_isSymm G htsym Vint
  have hψ' : IsGroundState (hamN (H0S G t Vint) occR w) ψ := by
    rw [hH] at hψ; exact (isGroundState_add_smul_one _).1 hψ
  have hv : ∀ c, eval w (krylovPoly (H0S G t Vint) occR c ord) ≠ 0 := by
    intro c hc
    apply hV
    change eval V Q = 0
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
    rw [eval_krylovPoly, hH, det_kry_add_smul_one, ← eval_krylovPoly]
    exact hc
  exact mem_omega_of_definite hS (kMat_nonpos hS hψ')
    (fun u hu => kMat_definite_of_hstar hS (rigid_occR hNu0 hNuM hNd0 hNdM) hv hψ' hu)

/-- The linear map from spin-resolved densities to the reduced observables. -/
noncomputable def Lr : SpinIdx K → Fin (K + 1) ⊕ Fin (K + 1) → ℝ :=
  Sum.elim (fun i => Sum.elim (fun i' => if i' = i then 1 else 0)
      (fun j' => Fin.cases 0 (fun _ => -1 / ((K : ℝ) + 1)) j'))
    (fun j => Sum.elim (fun _ => 0) (fun j' => if j' = j.succ then 1 else 0))

/-- Reduced densities `L ρ` of spin-resolved densities `ρ = (ρ↑, ρ↓)`. -/
noncomputable def redDens (ρ : Fin (K + 1) ⊕ Fin (K + 1) → ℝ) (k : SpinIdx K) : ℝ :=
  ∑ σi, Lr k σi * ρ σi

lemma redDens_inl (ρ : Fin (K + 1) ⊕ Fin (K + 1) → ℝ) (i : Fin (K + 1)) :
    redDens ρ (Sum.inl i) = ρ (Sum.inl i) - (∑ j : Fin K, ρ (Sum.inr j.succ)) / (K + 1) := by
  simp only [redDens, Lr, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, zero_add, Finset.sum_div]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro j _
  ring

lemma redDens_inr (ρ : Fin (K + 1) ⊕ Fin (K + 1) → ℝ) (j : Fin K) :
    redDens ρ (Sum.inr j) = ρ (Sum.inr j.succ) := by
  simp [redDens, Lr, Fintype.sum_sum_type]

lemma occR_eq (k : SpinIdx K) (x : SConf K Nu Nd) :
    occR k x = ∑ σi, Lr k σi * occS σi x := by
  change occR k x = redDens (fun σi => occS σi x) k
  rcases k with i | j
  · rw [redDens_inl]; rfl
  · rw [redDens_inr]; rfl

lemma tdens_occR (ψ : (SConf K Nu Nd → ℝ) × (SConf K Nu Nd → ℝ))
    (k : SpinIdx K) : tdens occR ψ k = redDens (fun σi => tdens occS ψ σi) k :=
  tdens_lin occR_eq ψ k

lemma tcur_occR (H0 : Matrix (SConf K Nu Nd) (SConf K Nu Nd) ℝ)
    (ψ : (SConf K Nu Nd → ℝ) × (SConf K Nu Nd → ℝ))
    (k : SpinIdx K) : tcur H0 occR ψ k = redDens (fun σi => tcur H0 occS ψ σi) k :=
  tcur_lin H0 occR_eq ψ k

lemma sum_redDens (ρ : Fin (K + 1) ⊕ Fin (K + 1) → ℝ) :
    ∑ k, redDens ρ k = ∑ i, ρ (Sum.inl i) := by
  rw [Fintype.sum_sum_type]
  simp only [redDens_inl, redDens_inr, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hK : ((K : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma hasDerivAt_redDens {ρ : ℝ → Fin (K + 1) ⊕ Fin (K + 1) → ℝ}
    {ρ' : Fin (K + 1) ⊕ Fin (K + 1) → ℝ}
    {t : ℝ} (h : HasDerivAt ρ ρ' t) :
    HasDerivAt (fun s => redDens (ρ s)) (redDens ρ') t := by
  refine hasDerivAt_pi.2 fun k => ?_
  exact HasDerivAt.fun_sum fun σi _ => (hasDerivAt_pi.1 h σi).const_mul (Lr k σi)

lemma continuous_redDens {ρ : ℝ → Fin (K + 1) ⊕ Fin (K + 1) → ℝ} (h : Continuous ρ) :
    Continuous (fun s => redDens (ρ s)) :=
  continuous_pi fun _ => continuous_finsetSum _ fun σi _ =>
    continuous_const.mul ((continuous_apply σi).comp h)

lemma schr_occR (H0 : Matrix (SConf K Nu Nd) (SConf K Nu Nd) ℝ)
    (w : SpinIdx K → ℝ)
    (ψ : (SConf K Nu Nd → ℝ) × (SConf K Nu Nd → ℝ)) :
    schr H0 occR w ψ = schr H0 occS (spinPot w) ψ := by
  simp only [schr, hamN_occR]

lemma sum_tdens_dn (ψ : (SConf K Nu Nd → ℝ) × (SConf K Nu Nd → ℝ)) :
    ∑ i, tdens occS ψ (Sum.inr i) = Nd * Qf 1 ψ := by
  have h1 : Qf 1 ψ = ∑ c, (ψ.1 c ^ 2 + ψ.2 c ^ 2) := by
    simp only [Qf, one_mulVec, dotProduct, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro c _; ring
  simp only [tdens_eq_sum, occS, Sum.elim_inr]
  rw [Finset.sum_comm, h1, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  rw [← Finset.sum_mul, sum_occF' c.2]

/-- Spin densities from the reduced ones, given the number of down electrons. -/
lemma spin_of_red {a b : Fin (K + 1) ⊕ Fin (K + 1) → ℝ} (h : ∀ k, redDens a k = redDens b k)
    (hdn : ∑ i, a (Sum.inr i) = ∑ i, b (Sum.inr i)) : a = b := by
  have hs : ∀ j : Fin K, a (Sum.inr j.succ) = b (Sum.inr j.succ) := fun j => by
    simpa [redDens_inr] using h (Sum.inr j)
  have hS : ∑ j : Fin K, a (Sum.inr j.succ) = ∑ j : Fin K, b (Sum.inr j.succ) :=
    Finset.sum_congr rfl fun j _ => hs j
  funext σi
  rcases σi with i | j
  · have := h (Sum.inl i); rw [redDens_inl, redDens_inl, hS] at this; linarith
  · refine Fin.cases ?_ (fun j' => hs j') j
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hS] at hdn
    linarith

/-- **Every spin-dependent potential is gauge-equivalent to a reduced one**: `(v↑, v↓)` equals
`spinPot w` with `Σ w = 0` up to a constant on each spin (which only shifts the energy). -/
lemma exists_spinPot_gauge (V : Fin (K + 1) ⊕ Fin (K + 1) → ℝ) :
    ∃ (w : SpinIdx K → ℝ) (a b : ℝ), ∑ k, w k = 0 ∧
      ∀ σi, V σi = spinPot w σi + Sum.elim (fun _ => a) (fun _ => b) σi := by
  obtain ⟨w, b, h⟩ := exists_spinPot V
  set c := (∑ k, w k) / (2 * K + 1)
  refine ⟨fun k => w k - c, c, b, ?_, ?_⟩
  · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    have hK : (2 * (K : ℝ) + 1) ≠ 0 := by positivity
    simp only [c]; push_cast; field_simp; ring
  · rintro (i | j)
    · rw [h]; simp [spinPot]
    · rw [h]
      refine Fin.cases ?_ (fun j' => ?_) j
      · simp [spinPot]
      · simp only [spinPot, Sum.elim_inr, Fin.cases_succ, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hK : ((K : ℝ) + 1) ≠ 0 := by positivity
        push_cast; field_simp; ring

section td

open Filter Topology Set

variable {H0 : Matrix (SConf K Nu Nd) (SConf K Nu Nd) ℝ}
  (hH0 : H0.IsSymm) {ρ ρ' ρ'' : ℝ → Fin (K + 1) ⊕ Fin (K + 1) → ℝ}
  (hρ : ∀ t, HasDerivAt ρ (ρ' t) t) (hρ' : ∀ t, HasDerivAt ρ' (ρ'' t) t) (hc : Continuous ρ'')
include hH0 hρ hρ' hc

/-- **Spin-resolved lattice TDDFT, existence.** Let the target spin densities `ρ(t) = (ρ↑, ρ↓)`
have a continuous second derivative, with `Σ_i ρ̈↑_i = 0` and `Σ_i ρ↓_i` constant, and let the
initial state `ψ0 ∈ Ω` reproduce `ρ(t₀)` and `ρ̇(t₀)`. Then near `t₀` there is a solution of the
Schrödinger equation driven by a spin-dependent potential `(v↑, v↓)(t) = spinPot w(t)` (gauge
`Σ w = 0`) whose spin densities are `ρ(t)`. -/
theorem td_spin_existence (hup : ∀ t, ∑ i, ρ'' t (Sum.inl i) = 0) {t0 : ℝ}
    (hdn : ∀ t, ∑ i, ρ t (Sum.inr i) = ∑ i, ρ t0 (Sum.inr i))
    {ψ0 : (SConf K Nu Nd → ℝ) × (SConf K Nu Nd → ℝ)}
    (hψ0 : ψ0 ∈ omega H0 occR) (hρ0 : ∀ σi, tdens occS ψ0 σi = ρ t0 σi)
    (hj0 : ∀ σi, tcur H0 occS ψ0 σi = ρ' t0 σi) :
    ∃ ε > 0, ∃ ψ : ℝ → (SConf K Nu Nd → ℝ) × (SConf K Nu Nd → ℝ),
      ∃ w : ℝ → SpinIdx K → ℝ, ψ t0 = ψ0 ∧ ∀ t ∈ Ioo (t0 - ε) (t0 + ε),
        HasDerivAt ψ (schr H0 occS (spinPot (w t)) (ψ t)) t ∧ ∑ k, w t k = 0 ∧
          ∀ σi, tdens occS (ψ t) σi = ρ t σi := by
  obtain ⟨ε, hε, ψ, h0, h⟩ := td_existence (nn := fun t => redDens (ρ t))
    (nd := fun t => redDens (ρ' t)) (ndd := fun t => redDens (ρ'' t)) hH0 sum_occR
    (fun t => hasDerivAt_redDens (hρ t)) (fun t => hasDerivAt_redDens (hρ' t))
    (continuous_redDens hc) (fun t => by rw [sum_redDens]; exact hup t) hψ0
    (fun k => by rw [tdens_occR]; exact congrArg (redDens · k) (funext hρ0))
    (fun k => by rw [tcur_occR]; exact congrArg (redDens · k) (funext hj0))
  refine ⟨ε, hε, ψ, fun t => vfb H0 occR (ψ t) (redDens (ρ'' t)), h0, fun t ht => ?_⟩
  obtain ⟨hd, hs, hden⟩ := h t ht
  refine ⟨by rw [← schr_occR]; exact hd, hs, ?_⟩
  -- the norm is conserved, hence so is the number of down electrons
  have hQ : ∀ s ∈ Ioo (t0 - ε) (t0 + ε), HasDerivAt (fun r => Qf 1 (ψ r)) 0 s := by
    intro s hs'
    have := Qf_hasDerivAt hH0 (h s hs').1 1
    simpa [Wf] using this
  have ht0 : t0 ∈ Ioo (t0 - ε) (t0 + ε) := ⟨by linarith, by linarith⟩
  have hQt := const_of_hasDerivAt_zero hQ ht ht0
  have hdn' : ∑ i, tdens occS (ψ t) (Sum.inr i) = ∑ i, ρ t (Sum.inr i) := by
    rw [sum_tdens_dn, hQt, h0, ← sum_tdens_dn, hdn t]
    exact Finset.sum_congr rfl fun i _ => hρ0 _
  have := spin_of_red (a := fun σi => tdens occS (ψ t) σi) (b := ρ t)
    (fun k => by rw [← tdens_occR]; exact hden k) hdn'
  exact fun σi => congrFun this σi

omit hρ' hc in
/-- **Spin-resolved lattice TDDFT, uniqueness.** Two trajectories from the same `ψ0 ∈ Ω`, both
driven by gauge-fixed spin-dependent potentials `spinPot w(t)` (`Σ w = 0`) and both reproducing the
spin densities `ρ(t)`, coincide near `t₀`, and so do their potentials. By `exists_spinPot_gauge`,
any spin potential is of this form up to one constant per spin. -/
theorem td_spin_uniqueness (hρ' : ∀ t, HasDerivAt ρ' (ρ'' t) t) (hc : Continuous ρ'') {t0 : ℝ}
    {ψ0 : (SConf K Nu Nd → ℝ) × (SConf K Nu Nd → ℝ)}
    (hψ0 : ψ0 ∈ omega H0 occR)
    {ψ1 ψ2 : ℝ → (SConf K Nu Nd → ℝ) × (SConf K Nu Nd → ℝ)}
    {w1 w2 : ℝ → SpinIdx K → ℝ}
    (h1 : ∀ᶠ t in 𝓝 t0, HasDerivAt ψ1 (schr H0 occS (spinPot (w1 t)) (ψ1 t)) t ∧
      ∑ k, w1 t k = 0 ∧ ∀ σi, tdens occS (ψ1 t) σi = ρ t σi)
    (h2 : ∀ᶠ t in 𝓝 t0, HasDerivAt ψ2 (schr H0 occS (spinPot (w2 t)) (ψ2 t)) t ∧
      ∑ k, w2 t k = 0 ∧ ∀ σi, tdens occS (ψ2 t) σi = ρ t σi)
    (h10 : ψ1 t0 = ψ0) (h20 : ψ2 t0 = ψ0) :
    ψ1 =ᶠ[𝓝 t0] ψ2 ∧ w1 =ᶠ[𝓝 t0] w2 := by
  have conv : ∀ {ψ : ℝ → _} {w : ℝ → SpinIdx K → ℝ},
      (∀ᶠ t in 𝓝 t0, HasDerivAt ψ (schr H0 occS (spinPot (w t)) (ψ t)) t ∧
        ∑ k, w t k = 0 ∧ ∀ σi, tdens occS (ψ t) σi = ρ t σi) →
      ∀ᶠ t in 𝓝 t0, HasDerivAt ψ (schr H0 occR (w t) (ψ t)) t ∧ ∑ k, w t k = 0 ∧
        ∀ k, tdens occR (ψ t) k = redDens (ρ t) k := by
    intro ψ w h
    filter_upwards [h] with t ht
    refine ⟨by rw [schr_occR]; exact ht.1, ht.2.1, fun k => ?_⟩
    rw [tdens_occR]
    exact congrArg (redDens · k) (funext ht.2.2)
  exact td_uniqueness (nn := fun t => redDens (ρ t)) (nd := fun t => redDens (ρ' t))
    (ndd := fun t => redDens (ρ'' t)) hH0 (fun t => hasDerivAt_redDens (hρ t))
    (fun t => hasDerivAt_redDens (hρ' t)) (continuous_redDens hc) hψ0 (conv h1) (conv h2) h10 h20

end td

end spin

end LatticeDFT
