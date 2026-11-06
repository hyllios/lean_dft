import LatticeDFT.Fermions.CauchyBinet
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The aufbau principle for non-interacting lattice fermions

For a symmetric single-particle Hamiltonian `h` with an orthonormal eigenbasis `φ_a` (energies `ε_a`):
* `slaterSub_eigen`: the Slater determinant of any `N` orbitals `S` is a many-body eigenvector of `Γ h`
  with energy `E_S = Σ_{a ∈ S} ε_a`;
* `qf_gamma_ge`: `⟨Ψ, Γ h Ψ⟩ ≥ min_S E_S · ‖Ψ‖²` for every many-body state (the Slater determinants form
  an orthonormal basis);
* `aufbau`: the non-interacting ground-state energy is the smallest sum of `N` orbital energies, and the
  Slater determinant of a minimising set of orbitals is a ground state.
-/

namespace LatticeDFT

open Matrix

variable {M N : ℕ}

/-- Total energy of the orbitals selected by `S`. -/
def orbEnergy (ε : Fin M → ℝ) (S : Conf M N) : ℝ := ∑ j, ε (τs S j)

theorem slaterSub_eigen (h : Matrix (Fin M) (Fin M) ℝ) {φ : Fin M → Fin M → ℝ} {ε : Fin M → ℝ}
    (hφ : ∀ a, h *ᵥ φ a = ε a • φ a) (S : Conf M N) :
    (Γ h : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ slaterSub φ S = orbEnergy ε S • slaterSub φ S :=
  gamma_slater h (fun j => φ (τs S j)) (fun j => ε (τs S j)) (fun j => hφ _)

section
variable (φ : Fin M → Fin M → ℝ)

/-- Matrix whose columns are the Slater determinants of all orbital subsets. -/
def slaterMat : Matrix (Conf M N) (Conf M N) ℝ := fun s S => slaterSub φ S s

variable {φ}

lemma slaterMat_orth (hON : ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0) :
    (slaterMat (N := N) φ)ᵀ * slaterMat φ = 1 := by
  ext S T
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [transpose_apply, slaterMat]
  exact slater_orthonormal hON S T

lemma dot_slaterMat (hON : ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0)
    (x y : Conf M N → ℝ) : (slaterMat φ *ᵥ x) ⬝ᵥ (slaterMat φ *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, slaterMat_orth hON, vecMul_one]

end

/-- **Variational lower bound by the smallest orbital-sum energy.** -/
theorem qf_gamma_ge (h : Matrix (Fin M) (Fin M) ℝ) {φ : Fin M → Fin M → ℝ} {ε : Fin M → ℝ}
    (hφ : ∀ a, h *ᵥ φ a = ε a • φ a) (hON : ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0)
    {E : ℝ} (hE : ∀ S : Conf M N, E ≤ orbEnergy ε S) (v : Conf M N → ℝ) :
    E * (v ⬝ᵥ v) ≤ qf (Γ h) v := by
  set P := slaterMat (N := N) φ
  have hPP : P * Pᵀ = 1 := mul_eq_one_comm.mp (slaterMat_orth hON)
  obtain ⟨c, rfl⟩ : ∃ c, v = P *ᵥ c := ⟨Pᵀ *ᵥ v, by rw [mulVec_mulVec, hPP, one_mulVec]⟩
  have hGP : (Γ h : Matrix (Conf M N) (Conf M N) ℝ) * P = P * diagonal (orbEnergy ε) := by
    ext s S
    have := congrFun (slaterSub_eigen h hφ S) s
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [P, slaterMat, diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [this, mul_comm]
  have hq : qf (Γ h) (P *ᵥ c) = c ⬝ᵥ (diagonal (orbEnergy ε) *ᵥ c) := by
    unfold qf
    rw [mulVec_mulVec, hGP, ← mulVec_mulVec, dot_slaterMat hON]
  rw [hq, dot_slaterMat hON]
  simp only [dotProduct, mulVec, diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.mul_sum]
  apply Finset.sum_le_sum; intro S _
  nlinarith [hE S, mul_self_nonneg (c S)]

/-- Orthonormal eigenvectors of a symmetric real matrix (spectral theorem). -/
theorem exists_eigenbasis (h : Matrix (Fin M) (Fin M) ℝ) (hS : h.IsSymm) :
    ∃ (ε : Fin M → ℝ) (φ : Fin M → Fin M → ℝ), (∀ a, h *ᵥ φ a = ε a • φ a) ∧
      ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0 := by
  have hH : h.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]; exact hS
  refine ⟨hH.eigenvalues, fun a => ⇑(hH.eigenvectorBasis a), fun a => hH.mulVec_eigenvectorBasis a, ?_⟩
  intro a b
  have h1 := (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) a b
  rw [← h1, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

lemma conf_nonempty (hN : N ≤ M) : Nonempty (Conf M N) := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin M))) (n := N)
    (by simpa using hN)
  exact ⟨⟨t, ht⟩⟩

/-- **Aufbau theorem.** The ground-state energy of `N` non-interacting fermions with single-particle
Hamiltonian `h` is the smallest sum of `N` orbital energies, attained by the Slater determinant of the
corresponding orbitals, which is a many-body ground state. -/
theorem aufbau (h : Matrix (Fin M) (Fin M) ℝ) (hS : h.IsSymm) (hN : N ≤ M) :
    ∃ (ε : Fin M → ℝ) (φ : Fin M → Fin M → ℝ) (S0 : Conf M N),
      (∀ a, h *ᵥ φ a = ε a • φ a) ∧
      (∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0) ∧
      (∀ S : Conf M N, orbEnergy ε S0 ≤ orbEnergy ε S) ∧
      IsGroundState (Γ h) (slaterSub φ S0) ∧
      ∀ v : Conf M N → ℝ, orbEnergy ε S0 * (v ⬝ᵥ v) ≤ qf (Γ h) v := by
  obtain ⟨ε, φ, hφ, hON⟩ := exists_eigenbasis h hS
  have := conf_nonempty hN
  obtain ⟨S0, -, hmin⟩ := Finset.exists_min_image Finset.univ (orbEnergy (N := N) ε) Finset.univ_nonempty
  have hmin' : ∀ S, orbEnergy ε S0 ≤ orbEnergy ε S := fun S => hmin S (Finset.mem_univ S)
  have hlow := qf_gamma_ge h hφ hON hmin'
  have hnorm : slaterSub φ S0 ⬝ᵥ slaterSub φ S0 = 1 := by
    have := slater_orthonormal hON S0 S0
    simpa [dotProduct] using this
  refine ⟨ε, φ, S0, hφ, hON, hmin', ⟨?_, fun w => ?_⟩, hlow⟩
  · intro h0; rw [h0] at hnorm; simp at hnorm
  · have hq : qf (Γ h) (slaterSub φ S0) = orbEnergy ε S0 := by
      unfold qf; rw [slaterSub_eigen h hφ S0, dotProduct_smul, hnorm, smul_eq_mul, mul_one]
    rw [hq, hnorm, mul_one]
    exact hlow w

end LatticeDFT
