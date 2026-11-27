/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.ManyBody.QuasiFree
import DFT.Lattice.RDMFT.Coleman
import DFT.Lattice.RDMFT.FockRDM
import DFT.Scope.Ranges

/-!
# RDMFT as a scope

`N` spinless fermions on `M` modes: the Hilbert space is spanned by the configurations `Conf M N`,
`H₀` is any Hermitian matrix (kinetic energy plus interaction), and the observables are a real basis
of all one-body operators, `X_ij = ½(c_i†c_j + c_j†c_i)` and `Y_ij = -(i/2)(c_i†c_j - c_j†c_i)`
(restricted to the `N`-particle sector). Their expectation values are `Re γ_ij` and `Im γ_ij`, so a
density of the scope is the one-body reduced density matrix `γ` in real coordinates (`coords`).

* `rdmftScope_densPure`: the density of `ψ` is `coords (γ(Ψ))`, with `Ψ` the state extended by zero
  to the Fock space (`extF`).
* `rdmftScope_Be`: **the ensemble range is `{γ : γ = γ†, 0 ≤ γ ≤ 1, tr γ = N}`** (Coleman's
  theorem).
-/

namespace DFT.Lattice.RDMFT

open Matrix QM.ManyBody RCLike Set
open scoped ComplexOrder

variable {M N : ℕ}

/-- The one-body operator `c_i† c_j`. -/
noncomputable def oneE (i j : Fin M) : FockOp M := cre i * ann j

lemma oneE_conjTranspose (i j : Fin M) : (oneE i j)ᴴ = oneE j i := by
  simp [oneE, conjTranspose_mul, ann]

/-- The real basis of one-body operators: `X_ij` (`b = false`) and `Y_ij` (`b = true`). -/
noncomputable def oneObs (a : Fin M × Fin M × Bool) : FockOp M :=
  if a.2.2 then (-Complex.I / 2) • (oneE a.1 a.2.1 - oneE a.2.1 a.1)
  else (1 / 2 : ℂ) • (oneE a.1 a.2.1 + oneE a.2.1 a.1)

lemma isHermitian_oneObs (a : Fin M × Fin M × Bool) : (oneObs a).IsHermitian := by
  unfold oneObs IsHermitian
  split_ifs
  · rw [conjTranspose_smul, conjTranspose_sub, oneE_conjTranspose, oneE_conjTranspose]
    ext x y
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, star_div₀, star_neg,
      Complex.star_def, Complex.conj_I, map_ofNat]
    ring
  · rw [conjTranspose_smul, conjTranspose_add, oneE_conjTranspose, oneE_conjTranspose, add_comm]
    congr 1
    simp

/-- **RDMFT as a scope.** -/
noncomputable def rdmftScope (H0 : Matrix (Conf M N) (Conf M N) ℂ) (hH0 : H0.IsHermitian) :
    Scope ℂ (Conf M N) (Fin M × Fin M × Bool) where
  H0 := H0
  B a := (oneObs a).submatrix Subtype.val Subtype.val
  isHermitian_H0 := hH0
  isHermitian_B a := (isHermitian_oneObs a).submatrix _

/-- Real coordinates of a one-body matrix: `Re γ_ij` and `Im γ_ij`. -/
def coords (γ : Matrix (Fin M) (Fin M) ℂ) (a : Fin M × Fin M × Bool) : ℝ :=
  if a.2.2 then (γ a.1 a.2.1).im else (γ a.1 a.2.1).re

/-- An `N`-particle state extended by zero to the Fock space. -/
noncomputable def extF (ψ : Conf M N → ℂ) : Fock M :=
  WithLp.toLp 2 fun s => if h : s.card = N then ψ ⟨s, h⟩ else 0

lemma extF_conf (ψ : Conf M N → ℂ) (c : Conf M N) : (extF ψ).ofLp c.1 = ψ c := by
  simp [extF, c.2]

lemma extF_of_ne (ψ : Conf M N → ℂ) {s : Finset (Fin M)} (hs : s.card ≠ N) :
    (extF ψ).ofLp s = 0 := by
  simp [extF, hs]

/-- Expectation values in the `N`-particle sector are Fock-space expectation values. -/
lemma dotProduct_submatrix (X : FockOp M) (ψ : Conf M N → ℂ) :
    star ψ ⬝ᵥ (X.submatrix Subtype.val Subtype.val *ᵥ ψ) =
      star (extF ψ).ofLp ⬝ᵥ (X *ᵥ (extF ψ).ofLp) := by
  symm
  simp only [dotProduct, mulVec, Pi.star_apply]
  rw [sum_eq_sum_conf (N := N) _ fun s hs => by simp [extF_of_ne ψ hs]]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_eq_sum_conf (N := N) _ fun t ht => by simp [extF_of_ne ψ ht]]
  simp [extF_conf, submatrix_apply]

lemma rdm1_eq_dotProduct (Ψ : Fock M) (i j : Fin M) :
    rdm1 Ψ i j = star Ψ.ofLp ⬝ᵥ (oneE i j *ᵥ Ψ.ofLp) := by
  rw [rdm1, ← inner_toFockCLM, oneE, map_mul]
  rfl

/-- The density of a state is its one-body matrix in real coordinates. -/
theorem rdmftScope_densPure {H0 : Matrix (Conf M N) (Conf M N) ℂ} (hH0 : H0.IsHermitian)
    (ψ : Conf M N → ℂ) : (rdmftScope H0 hH0).densPure ψ = coords (rdm1 (extF ψ)) := by
  funext a
  obtain ⟨i, j, b⟩ := a
  have hji : rdm1 (extF ψ) j i = star (rdm1 (extF ψ) i j) := by
    have := congrFun (congrFun (rdm1_isHermitian (extF ψ)) i) j
    rw [conjTranspose_apply] at this
    rw [← this, star_star]
  simp only [Scope.densPure, Scope.expv, rdmftScope, dotProduct_submatrix, coords, oneObs]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, smul_mulVec, add_mulVec, dotProduct_smul,
      dotProduct_add, ← rdm1_eq_dotProduct, hji, smul_eq_mul, Complex.star_def]
    simp
    ring
  · simp only [↓reduceIte, smul_mulVec, sub_mulVec, dotProduct_smul,
      dotProduct_sub, ← rdm1_eq_dotProduct, hji, smul_eq_mul, Complex.star_def]
    simp
    ring

/-- `extF` of a unit vector is an `N`-particle state. -/
lemma extF_isNState {ψ : Conf M N → ℂ} (hψ : ψ ∈ Scope.unitVecs) : IsNState N (extF ψ) := by
  refine ⟨?_, ?_⟩
  · have h1 := Scope.sum_norm_sq_eq_one hψ
    have h : ‖extF ψ‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq, sum_eq_sum_conf (N := N) _ fun u hu => by
        simp [extF_of_ne ψ hu]]
      simpa [extF_conf] using h1
    nlinarith [norm_nonneg (extF ψ)]
  · unfold numTotOp extF
    rw [toEuclideanCLM_toLp]
    ext u
    simp only [PiLp.smul_apply, smul_eq_mul, numTot_mulVec]
    by_cases hu : u.card = N
    · rw [show (u.card : ℂ) = N by exact_mod_cast hu]
    · simp [hu]

/-- An `N`-particle state is supported on `N`-particle configurations. -/
lemma eq_zero_of_isNState {Ψ : Fock M} (hΨ : IsNState N Ψ) {u : Finset (Fin M)}
    (hu : u.card ≠ N) : Ψ.ofLp u = 0 := by
  have h := congrArg (fun Φ : Fock M => Φ.ofLp u) hΨ.2
  simp only [numTotOp] at h
  rw [show (toFockCLM numTot Ψ).ofLp = numTot *ᵥ Ψ.ofLp from rfl, numTot_mulVec,
    PiLp.smul_apply, smul_eq_mul] at h
  have hne : (u.card : ℂ) - N ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hu)
  have : ((u.card : ℂ) - N) * Ψ.ofLp u = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.1 this).resolve_left hne

/-- The restriction of an `N`-particle state to `N`-particle configurations. -/
def restrF (Ψ : Fock M) : Conf M N → ℂ := fun c => Ψ.ofLp c.1

lemma extF_restrF {Ψ : Fock M} (hΨ : IsNState N Ψ) : extF (restrF (N := N) Ψ) = Ψ := by
  ext u
  by_cases hu : u.card = N
  · exact extF_conf _ ⟨u, hu⟩
  · rw [extF_of_ne _ hu, eq_zero_of_isNState hΨ hu]

lemma restrF_mem_unitVecs {Ψ : Fock M} (hΨ : IsNState N Ψ) :
    restrF (N := N) Ψ ∈ Scope.unitVecs := by
  change star (restrF Ψ) ⬝ᵥ restrF Ψ = 1
  rw [star_dotProduct_self_eq]
  have h := hΨ.1
  have h2 : ‖Ψ‖ ^ 2 = 1 := by rw [h, one_pow]
  rw [EuclideanSpace.norm_sq_eq, sum_eq_sum_conf (N := N) _ fun u hu => by
    simp [eq_zero_of_isNState hΨ hu]] at h2
  simp [restrF, h2]

lemma coords_sum {ι : Type*} [Fintype ι] (w : ι → ℝ) (γ : ι → Matrix (Fin M) (Fin M) ℂ) :
    coords (∑ k, (w k : ℂ) • γ k) = ∑ k, w k • coords (γ k) := by
  funext a
  simp only [coords, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_apply,
    Pi.smul_apply]
  split_ifs <;> simp [Complex.re_sum, Complex.im_sum]

/-- **The ensemble range of RDMFT** is the set of one-body matrices with `0 ≤ γ ≤ 1` and
`tr γ = N` (Coleman's theorem), in real coordinates. -/
theorem rdmftScope_Be {H0 : Matrix (Conf M N) (Conf M N) ℂ} (hH0 : H0.IsHermitian) :
    (rdmftScope H0 hH0).Be = coords '' {γ | γ.IsHermitian ∧ γ.PosSemidef ∧ (1 - γ).PosSemidef ∧
      γ.trace = N} := by
  ext ρ
  constructor
  · rintro ⟨Γ, hΓ, rfl⟩
    obtain ⟨p, u, hp, hp1, hu, -, htr⟩ := Scope.exists_decomp hΓ
    set e := (Fintype.equivFin (Conf M N)).symm
    refine ⟨rdm1Ens (fun k => p (e k)) fun k => extF (u (e k)), (coleman _).1 ⟨_, _, _,
      ⟨fun k => hp _, by rw [Equiv.sum_comp e p, hp1], fun k => extF_isNState (hu _)⟩, rfl⟩, ?_⟩
    rw [rdm1Ens, coords_sum, (rdmftScope H0 hH0).dens_eq_sum htr]
    rw [Equiv.sum_comp e (fun k => p k • coords (rdm1 (extF (u k))))]
    exact Finset.sum_congr rfl fun k _ => by rw [rdmftScope_densPure]
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨k, w, Ψ, hE, hγE⟩ := (coleman γ).2 hγ
    set ψ : Fin k → Conf M N → ℂ := fun l => restrF (Ψ l)
    have hψ : ∀ l, ψ l ∈ Scope.unitVecs := fun l => restrF_mem_unitVecs (hE.2.2 l)
    set Γ := ∑ l, w l • vecMulVec (ψ l) (star (ψ l))
    have hΓ : Γ ∈ Scope.densMats :=
      Scope.convex_densMats.sum_mem (fun l _ => hE.1 l) hE.2.1
        fun l _ => Scope.pure_mem_densMats (hψ l)
    refine ⟨Γ, hΓ, ?_⟩
    have hdens : (rdmftScope H0 hH0).dens Γ = ∑ l, w l • (rdmftScope H0 hH0).densPure (ψ l) := by
      funext a
      simp only [Γ, Scope.dens, Scope.trv, Finset.sum_mul, trace_sum, map_sum, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Matrix.smul_mul, trace_smul, RCLike.smul_re]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      exact Scope.trv_pure _ _
    rw [hdens, ← hγE, rdm1Ens, coords_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [rdmftScope_densPure, extF_restrF (hE.2.2 l)]

end DFT.Lattice.RDMFT
