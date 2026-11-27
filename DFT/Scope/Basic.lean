/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.EReal.Lemmas
import ForMathlib.Analysis.Matrix.Spectrum

/-!
# Scopes: the common structure of finite-dimensional functional theories

After C.-C. Wang, J. Liebert, M. Penz, C. Schilling, arXiv:2606.06676. A **scope** on `𝕜^d`
(`𝕜 = ℝ` or `ℂ`) is a Hermitian `H₀` and Hermitian observables `B_1, …, B_m`; the Hamiltonians
are `H(v) = H₀ + Σ_i v_i B_i` for `v ∈ ℝ^m`. The paper's abstract potential space `V` with a
linear map `ι : V → Herm(d)` is written here in a basis: `ι v = Σ_i v_i B_i` (`pot`). Lattice
DFT (`B_i` the site occupations), RDMFT (`B_i` all one-body operators) and spin DFT are scopes.

## Definitions

* `expv A ψ = Re⟨ψ, A ψ⟩`, `trv A Γ = Re tr(Γ A)`; `unitVecs`, `densMats` (pure and mixed states).
* `densPure ψ`, `dens Γ : ℝ^m`: the "densities" `ρ_i = ⟨B_i⟩`.
* `Bp`, `Be`: the pure and the ensemble ranges.
* `E v = min_ψ ⟨ψ, H(v) ψ⟩`; `Fp ρ`, `Fe ρ : EReal`: constrained searches of `⟨H₀⟩` over pure and
  mixed states with density `ρ` (`⊤` off the ranges).
* `IsGS`, `IsEnsGS`: pure and ensemble ground states.
* `IsCritical ψ`: `ψ` is an eigenvector of some `ι v ∉ ℝ·1`; `Bc`, `Br = Bp \ Bc`.
* `IsAbelian`, `NoRedundancy` (`ι` injective and `1 ∉ range ι`).

## Basic results

* `expv_ham`, `trv_ham`: `⟨H(v)⟩ = ⟨H₀⟩ + ρ·v`.
* `exists_decomp`: every density matrix is a convex combination of pure states (its spectral
  decomposition), `tr(Γ A) = Σ_k p_k ⟨u_k, A u_k⟩`.
* `isCompact_unitVecs`, `isCompact_densMats`.
* `E_le`, `E_le_trv`, `exists_isGS`: the ground-state energy is a minimum over pure states and a
  lower bound over mixed states.
-/

namespace DFT

open Matrix RCLike Set
open scoped ComplexOrder

/-- A **scope**: a Hermitian `H₀` and Hermitian observables `B_i`; `H(v) = H₀ + Σ_i v_i B_i`. -/
structure Scope (𝕜 : Type*) [RCLike 𝕜] (d m : Type*) where
  /-- The fixed part of the Hamiltonian. -/
  H0 : Matrix d d 𝕜
  /-- The observables coupled to the potentials. -/
  B : m → Matrix d d 𝕜
  isHermitian_H0 : H0.IsHermitian
  isHermitian_B : ∀ i, (B i).IsHermitian

namespace Scope

variable {𝕜 d m : Type*} [RCLike 𝕜] [Fintype d] [Fintype m]

/-- `Re⟨ψ, A ψ⟩`. -/
def expv (A : Matrix d d 𝕜) (ψ : d → 𝕜) : ℝ := re (star ψ ⬝ᵥ (A *ᵥ ψ))

/-- `Re tr(Γ A)`. -/
def trv (A Γ : Matrix d d 𝕜) : ℝ := re (Γ * A).trace

/-- Unit vectors (pure states). -/
def unitVecs : Set (d → 𝕜) := {ψ | star ψ ⬝ᵥ ψ = 1}

/-- Density matrices (mixed states). -/
def densMats : Set (Matrix d d 𝕜) := {Γ | Γ.PosSemidef ∧ Γ.trace = 1}

variable (S : Scope 𝕜 d m)

/-- The potential term `ι v = Σ_i v_i B_i`. -/
def pot (v : m → ℝ) : Matrix d d 𝕜 := ∑ i, v i • S.B i

/-- The Hamiltonian `H(v) = H₀ + ι v`. -/
def ham (v : m → ℝ) : Matrix d d 𝕜 := S.H0 + S.pot v

/-- The density of a pure state, `ρ_i = ⟨ψ, B_i ψ⟩`. -/
def densPure (ψ : d → 𝕜) : m → ℝ := fun i => expv (S.B i) ψ

/-- The density of a mixed state, `ρ_i = tr(Γ B_i)`. -/
def dens (Γ : Matrix d d 𝕜) : m → ℝ := fun i => trv (S.B i) Γ

/-- The pure-state range. -/
def Bp : Set (m → ℝ) := S.densPure '' unitVecs

/-- The ensemble range. -/
def Be : Set (m → ℝ) := S.dens '' densMats

/-- The ground-state energy `E(v) = min_ψ ⟨ψ, H(v) ψ⟩`. -/
noncomputable def E (v : m → ℝ) : ℝ := sInf (expv (S.ham v) '' unitVecs)

/-- The pure-state constrained-search functional (`⊤` off `Bp`). -/
noncomputable def Fp (ρ : m → ℝ) : EReal :=
  ⨅ ψ ∈ {ψ ∈ unitVecs | S.densPure ψ = ρ}, (expv S.H0 ψ : EReal)

/-- The ensemble constrained-search functional (`⊤` off `Be`). -/
noncomputable def Fe (ρ : m → ℝ) : EReal :=
  ⨅ Γ ∈ {Γ ∈ densMats | S.dens Γ = ρ}, (trv S.H0 Γ : EReal)

/-- `ψ` is a (pure) ground state of `H(v)`. -/
def IsGS (v : m → ℝ) (ψ : d → 𝕜) : Prop := ψ ∈ unitVecs ∧ expv (S.ham v) ψ = S.E v

/-- `Γ` is an ensemble ground state of `H(v)`. -/
def IsEnsGS (v : m → ℝ) (Γ : Matrix d d 𝕜) : Prop := Γ ∈ densMats ∧ trv (S.ham v) Γ = S.E v

/-- `ψ` is **critical**: an eigenvector of some `ι v` that is not a multiple of the identity. -/
def IsCritical [DecidableEq d] (ψ : d → 𝕜) : Prop :=
  ∃ v : m → ℝ, (∀ c : ℝ, S.pot v ≠ (c : 𝕜) • 1) ∧ ∃ μ : 𝕜, S.pot v *ᵥ ψ = μ • ψ

/-- The critical values: densities of critical pure states. -/
def Bc [DecidableEq d] : Set (m → ℝ) := S.densPure '' {ψ ∈ unitVecs | S.IsCritical ψ}

/-- The regular values. -/
def Br [DecidableEq d] : Set (m → ℝ) := S.Bp \ S.Bc

/-- The observables commute. -/
def IsAbelian : Prop := ∀ i j, Commute (S.B i) (S.B j)

/-- `ι` is injective and the identity is not a potential term. -/
def NoRedundancy [DecidableEq d] : Prop := Function.Injective S.pot ∧ ∀ v, S.pot v ≠ 1

/-! ### Linearity -/

lemma expv_add (A B : Matrix d d 𝕜) (ψ : d → 𝕜) : expv (A + B) ψ = expv A ψ + expv B ψ := by
  simp [expv, add_mulVec, dotProduct_add]

lemma expv_smul (r : ℝ) (A : Matrix d d 𝕜) (ψ : d → 𝕜) : expv (r • A) ψ = r * expv A ψ := by
  simp [expv, smul_mulVec, dotProduct_smul, RCLike.smul_re]

lemma expv_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix d d 𝕜) (ψ : d → 𝕜) :
    expv (∑ i ∈ s, A i) ψ = ∑ i ∈ s, expv (A i) ψ := by
  simp [expv, sum_mulVec, dotProduct_sum]

lemma trv_add (A B Γ : Matrix d d 𝕜) : trv (A + B) Γ = trv A Γ + trv B Γ := by
  simp [trv, Matrix.mul_add, trace_add]

lemma trv_smul (r : ℝ) (A Γ : Matrix d d 𝕜) : trv (r • A) Γ = r * trv A Γ := by
  simp [trv, Matrix.mul_smul, trace_smul, RCLike.smul_re]

lemma trv_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix d d 𝕜) (Γ : Matrix d d 𝕜) :
    trv (∑ i ∈ s, A i) Γ = ∑ i ∈ s, trv (A i) Γ := by
  simp [trv, Matrix.mul_sum, trace_sum]

lemma trv_add_right (A Γ₁ Γ₂ : Matrix d d 𝕜) : trv A (Γ₁ + Γ₂) = trv A Γ₁ + trv A Γ₂ := by
  simp [trv, Matrix.add_mul, trace_add]

lemma trv_smul_right (r : ℝ) (A Γ : Matrix d d 𝕜) : trv A (r • Γ) = r * trv A Γ := by
  simp [trv, Matrix.smul_mul, trace_smul, RCLike.smul_re]

lemma trv_pure (A : Matrix d d 𝕜) (ψ : d → 𝕜) : trv A (vecMulVec ψ (star ψ)) = expv A ψ := by
  rw [trv, trace_vecMulVec_star_mul, expv]

lemma expv_ham (v : m → ℝ) (ψ : d → 𝕜) :
    expv (S.ham v) ψ = expv S.H0 ψ + S.densPure ψ ⬝ᵥ v := by
  simp only [ham, pot, expv_add, expv_sum, expv_smul, densPure, dotProduct]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma trv_ham (v : m → ℝ) (Γ : Matrix d d 𝕜) : trv (S.ham v) Γ = trv S.H0 Γ + S.dens Γ ⬝ᵥ v := by
  simp only [ham, pot, trv_add, trv_sum, trv_smul, dens, dotProduct]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [Fintype m] in
lemma dens_add (Γ₁ Γ₂ : Matrix d d 𝕜) : S.dens (Γ₁ + Γ₂) = S.dens Γ₁ + S.dens Γ₂ := by
  funext i; simp [dens, trv_add_right]

omit [Fintype m] in
lemma dens_smul (r : ℝ) (Γ : Matrix d d 𝕜) : S.dens (r • Γ) = r • S.dens Γ := by
  funext i; simp [dens, trv_smul_right]

omit [Fintype m] in
lemma dens_pure (ψ : d → 𝕜) : S.dens (vecMulVec ψ (star ψ)) = S.densPure ψ := by
  funext i; simp [dens, densPure, trv_pure]

lemma expv_pot (a : m → ℝ) (x : d → 𝕜) : expv (S.pot a) x = S.densPure x ⬝ᵥ a := by
  have h := S.expv_ham a x
  rw [ham, expv_add] at h
  linarith

lemma trv_pot (a : m → ℝ) (Γ : Matrix d d 𝕜) : trv (S.pot a) Γ = S.dens Γ ⬝ᵥ a := by
  have h := S.trv_ham a Γ
  rw [ham, trv_add] at h
  linarith

omit [Fintype d] in
lemma pot_add (v w : m → ℝ) : S.pot (v + w) = S.pot v + S.pot w := by
  simp [pot, add_smul, Finset.sum_add_distrib]

omit [Fintype d] in
lemma pot_smul (r : ℝ) (v : m → ℝ) : S.pot (r • v) = r • S.pot v := by
  simp [pot, Finset.smul_sum, smul_smul]

omit [Fintype d] in
lemma pot_sub (v w : m → ℝ) : S.pot (v - w) = S.pot v - S.pot w := by
  simp [pot, sub_smul, Finset.sum_sub_distrib]

omit [Fintype d] in
lemma pot_sum {ι : Type*} (s : Finset ι) (v : ι → m → ℝ) :
    S.pot (∑ j ∈ s, v j) = ∑ j ∈ s, S.pot (v j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pot]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, pot_add, ih]

omit [Fintype d] in
@[simp] lemma pot_zero : S.pot 0 = 0 := by simp [pot]

omit [Fintype d] in
lemma isHermitian_pot (v : m → ℝ) : (S.pot v).IsHermitian := by
  unfold pot
  rw [IsHermitian, conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [conjTranspose_smul, star_trivial, (S.isHermitian_B i).eq]

omit [Fintype d] in
lemma isHermitian_ham (v : m → ℝ) : (S.ham v).IsHermitian :=
  S.isHermitian_H0.add (S.isHermitian_pot v)

lemma pot_mulVec (v : m → ℝ) (ψ : d → 𝕜) : S.pot v *ᵥ ψ = ∑ i, v i • (S.B i *ᵥ ψ) := by
  simp [pot, sum_mulVec, smul_mulVec]

/-! ### Pure and mixed states -/

lemma sum_norm_sq_eq_one {ψ : d → 𝕜} (hψ : ψ ∈ unitVecs) : ∑ i, ‖ψ i‖ ^ 2 = 1 := by
  have h : star ψ ⬝ᵥ ψ = 1 := hψ
  rw [star_dotProduct_self_eq] at h
  exact_mod_cast h

lemma norm_le_one {ψ : d → 𝕜} (hψ : ψ ∈ unitVecs) (i : d) : ‖ψ i‖ ≤ 1 := by
  have h1 := sum_norm_sq_eq_one hψ
  have : ‖ψ i‖ ^ 2 ≤ 1 := h1 ▸ Finset.single_le_sum (fun j _ => sq_nonneg ‖ψ j‖)
    (Finset.mem_univ i)
  nlinarith [norm_nonneg (ψ i)]

lemma pure_mem_densMats {ψ : d → 𝕜} (hψ : ψ ∈ unitVecs) : vecMulVec ψ (star ψ) ∈ densMats := by
  refine ⟨posSemidef_vecMulVec_self_star ψ, ?_⟩
  rw [trace_vecMulVec, dotProduct_comm]
  exact hψ

lemma single_mem_unitVecs [DecidableEq d] (k : d) : (Pi.single k 1 : d → 𝕜) ∈ unitVecs := by
  simp [unitVecs]

/-- **Spectral decomposition of a density matrix**: `Γ = Σ_k p_k |u_k⟩⟨u_k|` with `p` a
probability vector and `u_k` unit vectors, so `tr(Γ A) = Σ_k p_k ⟨u_k, A u_k⟩`. -/
lemma exists_decomp {Γ : Matrix d d 𝕜} (hΓ : Γ ∈ densMats) :
    ∃ (p : d → ℝ) (u : d → d → 𝕜), (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 ∧ (∀ k, u k ∈ unitVecs) ∧
      Γ = ∑ k, (p k : 𝕜) • vecMulVec (u k) (star (u k)) ∧
      ∀ A : Matrix d d 𝕜, trv A Γ = ∑ k, p k * expv A (u k) := by
  classical
  have hH := hΓ.1.isHermitian
  refine ⟨hH.eigenvalues, fun k => ⇑(hH.eigenvectorBasis k), hΓ.1.eigenvalues_nonneg, ?_,
    fun k => hH.star_dotProduct_eigenvectorBasis k, hH.eq_sum_vecMulVec, fun A => ?_⟩
  · have h := hH.trace_eq_sum_eigenvalues
    rw [hΓ.2] at h
    have := congrArg re h
    simpa using this.symm
  · rw [trv, hH.trace_mul_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [re_ofReal_mul]; rfl

/-! ### Compactness and the ground-state energy -/

lemma continuous_expv (A : Matrix d d 𝕜) : Continuous (expv A) := by
  unfold expv; fun_prop

lemma continuous_trv (A : Matrix d d 𝕜) : Continuous (trv A) := by
  unfold trv; fun_prop

omit [Fintype m] in
lemma continuous_densPure : Continuous S.densPure :=
  continuous_pi fun i => continuous_expv (S.B i)

omit [Fintype m] in
lemma continuous_dens : Continuous S.dens :=
  continuous_pi fun i => continuous_trv (S.B i)

lemma isCompact_unitVecs : IsCompact (unitVecs : Set (d → 𝕜)) := by
  refine (isCompact_univ_pi fun _ => isCompact_closedBall (0 : 𝕜) 1).of_isClosed_subset
    (isClosed_eq (by fun_prop) continuous_const) fun ψ hψ => ?_
  simpa using fun i => norm_le_one hψ i

lemma norm_apply_le_one {Γ : Matrix d d 𝕜} (hΓ : Γ ∈ densMats) (i j : d) : ‖Γ i j‖ ≤ 1 := by
  classical
  obtain ⟨p, u, hp, hp1, hu, hΓe, -⟩ := exists_decomp hΓ
  rw [hΓe, Matrix.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  rw [← hp1]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, norm_mul, norm_mul, Pi.star_apply,
    norm_star, norm_ofReal, abs_of_nonneg (hp k)]
  have h1 := norm_le_one (hu k) i
  have h2 := norm_le_one (hu k) j
  have := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
  nlinarith [hp k, norm_nonneg (u k i), norm_nonneg (u k j)]

lemma isCompact_densMats : IsCompact (densMats : Set (Matrix d d 𝕜)) := by
  classical
  have hK : IsCompact
      (Set.pi univ fun _ : d => Set.pi univ fun _ : d => Metric.closedBall (0 : 𝕜) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset (isClosed_setOfPred_posSemidef.inter
    (isClosed_eq (by fun_prop) continuous_const)) fun Γ hΓ => ?_
  simpa using fun i j => norm_apply_le_one hΓ i j

lemma bddBelow_expv (A : Matrix d d 𝕜) : BddBelow (expv A '' unitVecs) :=
  (isCompact_unitVecs.image (continuous_expv A)).bddBelow

lemma E_le (v : m → ℝ) {ψ : d → 𝕜} (hψ : ψ ∈ unitVecs) : S.E v ≤ expv (S.ham v) ψ :=
  csInf_le (bddBelow_expv _) ⟨ψ, hψ, rfl⟩

lemma exists_isGS [Nonempty d] (v : m → ℝ) : ∃ ψ, S.IsGS v ψ := by
  classical
  obtain ⟨ψ, hψ, he⟩ := (isCompact_unitVecs.image (continuous_expv (S.ham v))).sInf_mem
    ⟨_, Pi.single (Classical.arbitrary d) 1, single_mem_unitVecs _, rfl⟩
  exact ⟨ψ, hψ, he⟩

/-- Mixed states do not go below the ground-state energy. -/
lemma E_le_trv (v : m → ℝ) {Γ : Matrix d d 𝕜} (hΓ : Γ ∈ densMats) : S.E v ≤ trv (S.ham v) Γ := by
  classical
  obtain ⟨p, u, hp, hp1, hu, -, htr⟩ := exists_decomp hΓ
  rw [htr, ← one_mul (S.E v), ← hp1, Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (S.E_le v (hu k)) (hp k)

lemma isGS_iff_isEnsGS_pure (v : m → ℝ) {ψ : d → 𝕜} (hψ : ψ ∈ unitVecs) :
    S.IsGS v ψ ↔ S.IsEnsGS v (vecMulVec ψ (star ψ)) := by
  simp [IsGS, IsEnsGS, hψ, pure_mem_densMats hψ, trv_pure]

end Scope

end DFT
