import LatticeDFT.Basic.GroundState

/-!
# Single-particle Hohenberg–Kohn theorem on a graph

Setting: finite vertex set `V`, simple graph `G`, hopping `t`, potential `v`, `H(v) = diag v − t A_G`.
* `hk_single_particle`: for `t > 0` on a connected graph, two potentials with ground states of equal density
  differ by a constant (Perron–Frobenius-free proof: `|ψ|` is a ground state, nonnegative ground states are
  strictly positive, a common positive eigenvector fixes `v − v'`).
* `hk_fails_frustrated`: for frustrated hopping (`t < 0` on a triangle) the theorem fails.
-/

namespace LatticeDFT

section
open Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- single-particle lattice Hamiltonian H(v) = diag(v) − t A_G -/
noncomputable def ham (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (v : V → ℝ) : Matrix V V ℝ :=
  Matrix.diagonal v - t • G.adjMatrix ℝ

variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma adj_nonneg (i j : V) : 0 ≤ G.adjMatrix ℝ i j := by
  rw [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num

lemma ham_mulVec_apply (t : ℝ) (v ψ : V → ℝ) (i : V) :
    (ham G t v *ᵥ ψ) i = v i * ψ i - t * ∑ j, G.adjMatrix ℝ i j * ψ j := by
  rw [ham, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal, Matrix.smul_mulVec,
    Pi.smul_apply, smul_eq_mul]
  rfl

lemma ham_isSymm (t : ℝ) (v : V → ℝ) : (ham G t v).IsSymm := by
  unfold ham
  exact (Matrix.isSymm_diagonal v).sub ((G.isSymm_adjMatrix).smul t)

lemma qf_ham (t : ℝ) (v φ : V → ℝ) :
    qf (ham G t v) φ = ∑ i, v i * φ i ^ 2 - t * ∑ i, ∑ j, G.adjMatrix ℝ i j * φ i * φ j := by
  simp only [qf, dotProduct, ham_mulVec_apply, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; ring
  · apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma qf_ham_abs_le {t : ℝ} (ht : 0 ≤ t) (v φ : V → ℝ) :
    qf (ham G t v) (fun i => |φ i|) ≤ qf (ham G t v) φ := by
  rw [qf_ham, qf_ham]
  have h1 : ∑ i, v i * |φ i| ^ 2 = ∑ i, v i * φ i ^ 2 := by simp [sq_abs]
  have h2 : ∑ i, ∑ j, G.adjMatrix ℝ i j * φ i * φ j ≤
      ∑ i, ∑ j, G.adjMatrix ℝ i j * |φ i| * |φ j| := by
    apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
    rw [mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (adj_nonneg G i j)
    rw [← abs_mul]; exact le_abs_self _
  rw [h1]
  nlinarith [mul_le_mul_of_nonneg_left h2 ht]

/-- For `t > 0`, `|ψ|` is a ground state whenever `ψ` is (the hopping term can only decrease). -/
theorem abs_isGroundState {t : ℝ} (ht : 0 < t) {v ψ : V → ℝ}
    (h : IsGroundState (ham G t v) ψ) : IsGroundState (ham G t v) (fun i => |ψ i|) := by
  obtain ⟨hne, hmin⟩ := h
  refine ⟨?_, fun φ => ?_⟩
  · intro h0; apply hne; funext i; have := congrFun h0 i; simpa using this
  · have hdot : (fun i => |ψ i|) ⬝ᵥ (fun i => |ψ i|) = ψ ⬝ᵥ ψ := by
      simp [dotProduct, abs_mul_abs_self]
    have hφ : 0 ≤ φ ⬝ᵥ φ := by
      simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    rw [hdot]
    calc qf (ham G t v) (fun i => |ψ i|) * (φ ⬝ᵥ φ) ≤ qf (ham G t v) ψ * (φ ⬝ᵥ φ) :=
          mul_le_mul_of_nonneg_right (qf_ham_abs_le G ht.le v ψ) hφ
      _ ≤ qf (ham G t v) φ * (ψ ⬝ᵥ ψ) := hmin φ


/-- On a connected graph with `t > 0`, a nonnegative ground state is strictly positive. -/
theorem pos_of_nonneg (hG : G.Connected) {t : ℝ} (ht : 0 < t) {v ψ : V → ℝ}
    (h : IsGroundState (ham G t v) ψ) (hnn : ∀ i, 0 ≤ ψ i) : ∀ i, 0 < ψ i := by
  have heig := isGroundState_eigen (ham_isSymm G t v) h
  have hprop : ∀ i j, G.Adj i j → ψ i = 0 → ψ j = 0 := by
    intro i j hij hi
    have hi_eq := congrFun heig i
    rw [ham_mulVec_apply, Pi.smul_apply, smul_eq_mul, hi] at hi_eq
    simp only [mul_zero, zero_sub, neg_eq_zero] at hi_eq
    have hsum : ∑ k, G.adjMatrix ℝ i k * ψ k = 0 := by
      rcases mul_eq_zero.mp hi_eq with h0 | h0
      · exact absurd h0 ht.ne'
      · exact h0
    have hnonneg : ∀ k ∈ (Finset.univ : Finset V), 0 ≤ G.adjMatrix ℝ i k * ψ k :=
      fun k _ => mul_nonneg (adj_nonneg G i k) (hnn k)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum j (Finset.mem_univ j)
    rw [SimpleGraph.adjMatrix_apply, if_pos hij, one_mul] at this
    exact this
  have hreach : ∀ i j, G.Reachable i j → ψ i = 0 → ψ j = 0 := by
    intro i j ⟨p⟩
    induction p with
    | nil => exact id
    | cons hadj p ih => exact fun h0 => ih (hprop _ _ hadj h0)
  intro i
  rcases (hnn i).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply h.1
    funext j
    exact hreach i j (hG.preconnected i j) heq.symm

/-- **Single-particle Hohenberg–Kohn theorem** on a connected graph with `t > 0`. -/
theorem hk_single_particle (hG : G.Connected) {t : ℝ} (ht : 0 < t) {v v' ψ ψ' : V → ℝ}
    (hψ : IsGroundState (ham G t v) ψ) (hψ' : IsGroundState (ham G t v') ψ')
    (hn : ∀ i, ψ i ^ 2 = ψ' i ^ 2) : ∃ c : ℝ, ∀ i, v i - v' i = c := by
  have hφ' : (fun i => |ψ' i|) = (fun i => |ψ i|) := by
    funext i; exact ((sq_eq_sq_iff_abs_eq_abs _ _).mp (hn i)).symm
  have g1 : IsGroundState (ham G t v) (fun i => |ψ i|) := abs_isGroundState G ht hψ
  have g2 : IsGroundState (ham G t v') (fun i => |ψ i|) := by
    rw [← hφ']; exact abs_isGroundState G ht hψ'
  have pos := pos_of_nonneg G hG ht g1 (fun i => abs_nonneg _)
  have e1 := isGroundState_eigen (ham_isSymm G t v) g1
  have e2 := isGroundState_eigen (ham_isSymm G t v') g2
  set φ : V → ℝ := fun i => |ψ i| with hφdef
  refine ⟨qf (ham G t v) φ / (φ ⬝ᵥ φ) - qf (ham G t v') φ / (φ ⬝ᵥ φ), fun i => ?_⟩
  have h1 := congrFun e1 i
  have h2 := congrFun e2 i
  rw [ham_mulVec_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  have hpi := (pos i).ne'
  have hkey : (v i - v' i) * φ i =
      (qf (ham G t v) φ / (φ ⬝ᵥ φ) - qf (ham G t v') φ / (φ ⬝ᵥ φ)) * φ i := by
    linear_combination h1 - h2
  exact mul_right_cancel₀ hpi hkey

/-! ### The sign of the hopping matters: a frustrated counterexample

On the triangle (complete graph on 3 vertices) with t = −1 (frustrated hopping), the vector
ψ = (1, −1, 0) is a ground state for both v = (0,0,1) and v' = (0,0,2), so the densities agree,
yet v − v' is not constant: the single-particle HK theorem fails without `0 < t`.
Mechanism: the ground state has a node on site 2, and the potential there is invisible. -/

lemma qf_triangle (v φ : Fin 3 → ℝ) :
    qf (ham (⊤ : SimpleGraph (Fin 3)) (-1) v) φ =
      v 0 * φ 0 ^ 2 + v 1 * φ 1 ^ 2 + v 2 * φ 2 ^ 2 + 2 * (φ 0 * φ 1 + φ 0 * φ 2 + φ 1 * φ 2) := by
  rw [qf_ham]
  simp [Fin.sum_univ_three, SimpleGraph.adjMatrix_apply]
  ring

theorem hk_fails_frustrated :
    ∃ v v' ψ : Fin 3 → ℝ,
      IsGroundState (ham (⊤ : SimpleGraph (Fin 3)) (-1) v) ψ ∧
      IsGroundState (ham (⊤ : SimpleGraph (Fin 3)) (-1) v') ψ ∧
      ¬ ∃ c : ℝ, ∀ i, v i - v' i = c := by
  refine ⟨![0, 0, 1], ![0, 0, 2], ![1, -1, 0], ?_, ?_, ?_⟩
  · refine ⟨fun h => by simpa using congrFun h 0, fun φ => ?_⟩
    rw [qf_triangle, qf_triangle]
    simp [dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (φ 0 + φ 1 + φ 2), sq_nonneg (φ 2)]
  · refine ⟨fun h => by simpa using congrFun h 0, fun φ => ?_⟩
    rw [qf_triangle, qf_triangle]
    simp [dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (φ 0 + φ 1 + φ 2), sq_nonneg (φ 2)]
  · rintro ⟨c, hc⟩
    have h0 := hc 0; have h2 := hc 2
    simp at h0 h2
    linarith

end

end LatticeDFT
