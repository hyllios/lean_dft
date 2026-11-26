/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.ManyBody.QuasiFreeMixed
import QM.ManyBody.RDM2
import QM.ManyBody.OneBody
import ForMathlib.Topology.Instances.UnitaryGroup

/-!
# Hartree–Fock theory and Lieb's variational principle

The Hamiltonian `H = Σ_ij h_ij c_i† c_j + ½ Σ V_{ij,kl} c_i† c_j† c_l c_k` has expectation
`Σ h_ij γ_ij + ½ Σ V_{ij,kl} D_{ij,kl}` in terms of the reduced density matrices. On a Slater state
`D_{ij,kl} = γ_ik γ_jl - γ_il γ_jk` (Wick), so the energy is the Hartree–Fock functional
`E_HF(γ) = Re (Σ h_ij γ_ij + ½ Σ V_{ij,kl} (γ_ik γ_jl - γ_il γ_jk))` of its one-body matrix.

**Lieb's variational principle**: if the interaction is repulsive, `V ⪰ 0` on the pair space, then
for every `0 ≤ γ ≤ 1` with `tr γ = N` there is a projection `P` of rank `N` with
`E_HF(P) ≤ E_HF(γ)`; hence some `N`-particle (Slater) state has energy at most `E_HF(γ)`.
Write `γ = Σ_k n_k φ_k φ_k†`. If some `n_a` is fractional, so is another `n_b` (the trace is an
integer). Moving occupation between `a` and `b`, `E_HF` is a quadratic in the shift whose leading
coefficient is `-½ ⟨w, V w⟩ ≤ 0` with `w = φ_a ∧ φ_b`, so it is concave, and one of the two
endpoints (where `n_a` or `n_b` becomes `0` or `1`) does not raise the energy (`exists_vertex_le`).

## Main definitions

* `twoBody V`, `ham h V`: the second-quantized Hamiltonian.
* `pairForm V A B`, `hfEnergy h V γ`: the Hartree–Fock functional.

## Main results

* `energy_eq_rdm`, `energy_slater`: `⟨H⟩` in terms of `γ, D`; on Slater states it is `E_HF(γ)`.
* `exists_vertex_le`: a function on `{0 ≤ n ≤ 1, Σ n = N}` that is concave along every `e_a - e_b`
  takes a value at most `F n` at some `0/1` vector.
* `lieb_variational` (**Lieb's variational principle**), `exists_state_le_hf`, `ground_le_hf`.
* `exists_hf_minimizer`: a Slater state minimizes `E_HF` over all admissible `γ`.
-/

namespace QM.ManyBody

open Matrix Finset
open scoped ComplexOrder

variable {M : ℕ}

/-! ### The Hamiltonian and the Hartree–Fock functional -/

/-- The two-body operator `½ Σ V_{ij,kl} c_i† c_j† c_l c_k`. -/
noncomputable def twoBody (V : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ) : FockOp M :=
  (2⁻¹ : ℂ) • ∑ i, ∑ j, ∑ k, ∑ l, V (i, j) (k, l) • (cre i * cre j * ann l * ann k)

/-- The Hamiltonian `Σ h_ij c_i† c_j + ½ Σ V_{ij,kl} c_i† c_j† c_l c_k`. -/
noncomputable def ham (h : Matrix (Fin M) (Fin M) ℂ)
    (V : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ) :
    FockOp M :=
  oneBody h + twoBody V

/-- The bilinear form `½ Σ V_{ij,kl} (A_ik B_jl - A_il B_jk)`. -/
noncomputable def pairForm (V : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ)
    (A B : Matrix (Fin M) (Fin M) ℂ) : ℂ :=
  2⁻¹ * ∑ i, ∑ j, ∑ k, ∑ l, V (i, j) (k, l) * (A i k * B j l - A i l * B j k)

/-- **The Hartree–Fock functional** `Re (Σ h_ij γ_ij + ½ Σ V_{ij,kl} (γ_ik γ_jl - γ_il γ_jk))`. -/
noncomputable def hfEnergy (h : Matrix (Fin M) (Fin M) ℂ)
    (V : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ) (γ : Matrix (Fin M) (Fin M) ℂ) : ℝ :=
  (∑ i, ∑ j, h i j * γ i j + pairForm V γ γ).re

variable (h : Matrix (Fin M) (Fin M) ℂ) (V : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ)

/-- `⟨Ψ, H Ψ⟩ = Σ h_ij γ_ij + ½ Σ V_{ij,kl} D_{ij,kl}`. -/
theorem energy_eq_rdm (Ψ : Fock M) :
    inner ℂ Ψ (toFockCLM (ham h V) Ψ) =
      ∑ i, ∑ j, h i j * rdm1 Ψ i j +
        2⁻¹ * ∑ i, ∑ j, ∑ k, ∑ l, V (i, j) (k, l) * rdm2 Ψ (i, j) (k, l) := by
  simp only [ham, oneBody, twoBody, map_add, map_sum, map_smul, add_apply,
    sum_apply, smul_apply, inner_add_right, inner_sum,
    inner_smul_right, Finset.mul_sum, map_mul, mul_apply_eq_comp, rdm1, rdm2]
  rfl

/-- **On a Slater state the energy is the Hartree–Fock functional of its one-body matrix.** -/
theorem energy_slater {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (s : Finset (Fin M)) :
    (inner ℂ (slaterState u s) (toFockCLM (ham h V) (slaterState u s))).re =
      hfEnergy h V (rdm1 (slaterState u s)) := by
  rw [energy_eq_rdm, hfEnergy, pairForm]
  simp only [rdm2_slater hu]

/-! ### Quadratic expansion -/

lemma pairForm_add_smul (A Δ : Matrix (Fin M) (Fin M) ℂ) (t : ℂ) :
    pairForm V (A + t • Δ) (A + t • Δ) =
      pairForm V A A + t * (pairForm V A Δ + pairForm V Δ A) + t ^ 2 * pairForm V Δ Δ := by
  simp only [pairForm, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `E_HF(A + tΔ)` is a quadratic polynomial in `t` with leading coefficient `Re pairForm Δ Δ`. -/
lemma hfEnergy_add_smul (A Δ : Matrix (Fin M) (Fin M) ℂ) (t : ℝ) :
    hfEnergy h V (A + (t : ℂ) • Δ) = hfEnergy h V A +
      (∑ i, ∑ j, h i j * Δ i j + pairForm V A Δ + pairForm V Δ A).re * t +
        (pairForm V Δ Δ).re * t ^ 2 := by
  rw [hfEnergy, hfEnergy, pairForm_add_smul]
  have hlin : ∑ i, ∑ j, h i j * (A + (t : ℂ) • Δ) i j =
      ∑ i, ∑ j, h i j * A i j + (t : ℂ) * ∑ i, ∑ j, h i j * Δ i j := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    ring
  rw [hlin]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two,
    Complex.mul_im, zero_mul, sub_zero, mul_zero, add_zero]
  ring

/-! ### The abstract lemma: concave along `e_a - e_b` ⇒ a `0/1` vertex is lower -/

/-- If `n_a` is fractional and `Σ n` is an integer, then some other `n_b` is fractional. -/
lemma exists_other_frac {N : ℕ} {n : Fin M → ℝ} (h01 : ∀ k, 0 ≤ n k ∧ n k ≤ 1)
    (hsum : ∑ k, n k = N) {a : Fin M} (ha : 0 < n a ∧ n a < 1) :
    ∃ b, b ≠ a ∧ 0 < n b ∧ n b < 1 := by
  by_contra hcon
  push Not at hcon
  have hk : ∀ k ∈ Finset.univ.erase a, n k = if n k = 1 then 1 else 0 := by
    intro k hk
    have hka := Finset.ne_of_mem_erase hk
    split_ifs with h1
    · exact h1
    · rcases (h01 k).1.lt_or_eq with h | h
      · have := hcon k hka h
        exact absurd (le_antisymm (h01 k).2 this) h1
      · exact h.symm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), Finset.sum_congr rfl hk,
    Finset.sum_boole] at hsum
  set c := ((Finset.univ.erase a).filter fun k => n k = 1).card
  have hz : n a = ((N - c : ℤ) : ℝ) := by push_cast; linarith
  rw [hz] at ha
  obtain ⟨h1, h2⟩ := ha
  have h1' : (0 : ℤ) < N - c := by exact_mod_cast h1
  have h2' : (N - c : ℤ) < 1 := by exact_mod_cast h2
  omega

/-- The fractional coordinates. -/
noncomputable def fracSet (n : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter fun k => 0 < n k ∧ n k < 1

lemma shift_apply (n : Fin M → ℝ) (a b : Fin M) (t : ℝ) (k : Fin M) :
    ((n + t • (Pi.single a (1 : ℝ) - Pi.single b (1 : ℝ)) : Fin M → ℝ)) k =
      n k + t * ((if k = a then 1 else 0) - (if k = b then 1 else 0)) := by
  simp [Pi.single_apply]

/-- One step: shifting by `t` between two fractional coordinates `a, b` so that one of them hits
`0` or `1` keeps the box and the sum, and removes a fractional coordinate. -/
lemma shift_step {n : Fin M → ℝ} (h01 : ∀ k, 0 ≤ n k ∧ n k ≤ 1) {a b : Fin M} (hab : a ≠ b)
    (ha : 0 < n a ∧ n a < 1) (hb : 0 < n b ∧ n b < 1) {t : ℝ}
    (hta : 0 ≤ n a + t ∧ n a + t ≤ 1) (htb : 0 ≤ n b - t ∧ n b - t ≤ 1)
    (hend : (n a + t = 0 ∨ n a + t = 1) ∨ (n b - t = 0 ∨ n b - t = 1)) :
    let n' := n + t • (Pi.single a 1 - Pi.single b 1)
    (∀ k, 0 ≤ n' k ∧ n' k ≤ 1) ∧ ∑ k, n' k = ∑ k, n k ∧ (fracSet n').card < (fracSet n).card := by
  intro n'
  have hn' : ∀ k, n' k = if k = a then n a + t else if k = b then n b - t else n k := by
    intro k
    simp only [n', shift_apply]
    by_cases hka : k = a
    · subst hka; simp [hab]
    · by_cases hkb : k = b
      · subst hkb; simp [hka, sub_eq_add_neg]
      · simp [hka, hkb]
  refine ⟨fun k => ?_, ?_, ?_⟩
  · rw [hn']; split_ifs
    · exact hta
    · exact htb
    · exact h01 k
  · simp only [n', Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ, ite_true,
      sub_self, mul_zero, add_zero]
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · rcases hend with h | h
      · refine ⟨a, ?_, ?_⟩
        · simp [fracSet, ha]
        · simp only [fracSet, Finset.mem_filter, Finset.mem_univ, true_and, hn']
          rcases h with h | h <;> rw [h] <;> norm_num
      · refine ⟨b, ?_, ?_⟩
        · simp [fracSet, hb]
        · simp only [fracSet, Finset.mem_filter, Finset.mem_univ, true_and, hn',
            ite_eq_right hab.symm]
          rcases h with h | h <;> rw [h] <;> norm_num
    · intro k hk
      simp only [fracSet, Finset.mem_filter, Finset.mem_univ, true_and, hn'] at hk ⊢
      split_ifs at hk with h1 h2
      · subst h1; exact ha
      · subst h2; exact hb
      · exact hk

/-- **A function concave along every `e_a - e_b` takes a lower value at a `0/1` vector** with the
same sum. -/
theorem exists_vertex_le {N : ℕ} (F : (Fin M → ℝ) → ℝ)
    (hF : ∀ n (a b : Fin M), a ≠ b → ∃ l c : ℝ, c ≤ 0 ∧ ∀ t : ℝ,
      F (n + t • (Pi.single a 1 - Pi.single b 1)) = F n + l * t + c * t ^ 2)
    (n : Fin M → ℝ) (h01 : ∀ k, 0 ≤ n k ∧ n k ≤ 1) (hsum : ∑ k, n k = N) :
    ∃ m : Fin M → ℝ, (∀ k, m k = 0 ∨ m k = 1) ∧ ∑ k, m k = N ∧ F m ≤ F n := by
  induction hc : (fracSet n).card using Nat.strong_induction_on generalizing n with
  | _ c ih =>
  by_cases hfr : fracSet n = ∅
  · refine ⟨n, fun k => ?_, hsum, le_rfl⟩
    have hk : k ∉ fracSet n := by rw [hfr]; simp
    simp only [fracSet, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hk
    rcases (h01 k).1.lt_or_eq with h | h
    · exact Or.inr (le_antisymm (h01 k).2 (hk h))
    · exact Or.inl h.symm
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hfr
  simp only [fracSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨b, hba, hb⟩ := exists_other_frac h01 hsum ha
  have hab : a ≠ b := hba.symm
  obtain ⟨l, cq, hcq, hq⟩ := hF n a b hab
  set tp := min (1 - n a) (n b)
  set tm := min (n a) (1 - n b)
  have htp : 0 < tp := lt_min (by linarith [ha.2]) hb.1
  have htm : 0 < tm := lt_min ha.1 (by linarith [hb.2])
  -- one endpoint is not higher
  have hend : F (n + tp • (Pi.single a 1 - Pi.single b 1)) ≤ F n ∨
      F (n + (-tm) • (Pi.single a 1 - Pi.single b 1)) ≤ F n := by
    rw [hq, hq]
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have c1 := mul_nonpos_of_nonpos_of_nonneg hcq (sq_nonneg tp)
    have c2 := mul_nonpos_of_nonpos_of_nonneg hcq (sq_nonneg (-tm))
    have e1 : 0 < l * tp := by linarith
    have e2 : 0 < l * (-tm) := by linarith
    have hl : 0 < l := (pos_iff_pos_of_mul_pos e1).mpr htp
    nlinarith [mul_pos hl htm]
  rcases hend with hle | hle
  · obtain ⟨hbox, hs, hlt⟩ := shift_step h01 hab ha hb (t := tp)
      ⟨by linarith [htp.le], by linarith [min_le_left (1 - n a) (n b)]⟩
      ⟨by linarith [min_le_right (1 - n a) (n b)], by linarith [hb.2, htp.le]⟩
      (by
        rcases min_choice (1 - n a) (n b) with h | h
        · left; right; rw [show tp = 1 - n a from h]; ring
        · right; left; rw [show tp = n b from h]; ring)
    obtain ⟨m, hm, hms, hFm⟩ := ih _ (hc ▸ hlt) _ hbox (hs.trans hsum) rfl
    exact ⟨m, hm, hms, hFm.trans hle⟩
  · obtain ⟨hbox, hs, hlt⟩ := shift_step h01 hab ha hb (t := -tm)
      ⟨by linarith [min_le_left (n a) (1 - n b)], by linarith [ha.2, htm.le]⟩
      ⟨by linarith [htm.le, hb.1], by linarith [min_le_right (n a) (1 - n b)]⟩
      (by
        rcases min_choice (n a) (1 - n b) with h | h
        · left; left; rw [show tm = n a from h]; ring
        · right; right; rw [show tm = 1 - n b from h]; ring)
    obtain ⟨m, hm, hms, hFm⟩ := ih _ (hc ▸ hlt) _ hbox (hs.trans hsum) rfl
    exact ⟨m, hm, hms, hFm.trans hle⟩

/-! ### Natural-orbital form -/

/-- `v̄ diag(d) vᵀ`. -/
noncomputable def natMat (v : Matrix (Fin M) (Fin M) ℂ) (d : Fin M → ℂ) :
    Matrix (Fin M) (Fin M) ℂ :=
  v.map star * diagonal d * vᵀ

lemma natMat_apply (v : Matrix (Fin M) (Fin M) ℂ) (d : Fin M → ℂ) (i j : Fin M) :
    natMat v d i j = ∑ m, star (v i m) * d m * v j m := by
  simp only [natMat]
  rw [Matrix.mul_apply]
  simp [Matrix.mul_diagonal]

lemma natMat_add_smul (v : Matrix (Fin M) (Fin M) ℂ) (n d : Fin M → ℝ) (t : ℝ) :
    natMat v (fun k => ((n + t • d) k : ℂ)) =
      natMat v (fun k => (n k : ℂ)) + (t : ℂ) • natMat v (fun k => (d k : ℂ)) := by
  ext i j
  simp only [natMat_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast; ring

/-- **The leading coefficient is `-½ ⟨w, V w⟩ ≤ 0`** for a shift between two natural orbitals. -/
lemma pairForm_shift_re_nonpos (hV : V.PosSemidef) (v : Matrix (Fin M) (Fin M) ℂ) (a b : Fin M) :
    (pairForm V (natMat v fun k => (((Pi.single a 1 - Pi.single b 1 : Fin M → ℝ) k : ℝ) : ℂ))
      (natMat v fun k => (((Pi.single a 1 - Pi.single b 1 : Fin M → ℝ) k : ℝ) : ℂ))).re ≤ 0 := by
  set Δ := natMat v fun k => (((Pi.single a 1 - Pi.single b 1 : Fin M → ℝ) k : ℝ) : ℂ)
  have hΔ : ∀ i j, Δ i j = star (v i a) * v j a - star (v i b) * v j b := by
    intro i j
    have hc : ∀ x, (((Pi.single a 1 - Pi.single b 1 : Fin M → ℝ) x : ℝ) : ℂ) =
        (if x = a then 1 else 0) - (if x = b then 1 else 0) := by
      intro x; simp only [Pi.sub_apply, Pi.single_apply]; split_ifs <;> simp
    simp only [Δ, natMat_apply, hc, mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul,
      mul_one, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  set w : Fin M × Fin M → ℂ := fun p => v p.1 a * v p.2 b - v p.1 b * v p.2 a
  have hform : pairForm V Δ Δ = -(2⁻¹ * (star w ⬝ᵥ (V *ᵥ w))) := by
    simp only [pairForm, hΔ, dotProduct, mulVec, Fintype.sum_prod_type, Finset.mul_sum,
      Pi.star_apply, w, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [star_sub, star_mul']
    ring
  rw [hform]
  have h0 := hV.dotProduct_mulVec_nonneg w
  have hre : 0 ≤ (star w ⬝ᵥ (V *ᵥ w)).re := (Complex.nonneg_iff.mp h0).1
  simp only [Complex.neg_re, Complex.mul_re]
  norm_num
  linarith

/-! ### Lieb's variational principle -/

/-- **Lieb's variational principle.** For a repulsive interaction (`V ⪰ 0` on the pair space) and
any `0 ≤ γ ≤ 1` with `tr γ = N`, some Hermitian projection `P` with `tr P = N` has
`E_HF(P) ≤ E_HF(γ)`. -/
theorem lieb_variational {N : ℕ} (hV : V.PosSemidef) {γ : Matrix (Fin M) (Fin M) ℂ}
    (h0 : γ.PosSemidef) (h1 : (1 - γ).PosSemidef) (htr : γ.trace = N) :
    ∃ P : Matrix (Fin M) (Fin M) ℂ, Pᴴ = P ∧ P * P = P ∧ P.trace = N ∧
      hfEnergy h V P ≤ hfEnergy h V γ := by
  have hγ := gamma_eq_qfU h0.1
  have hv := qfU_mem h0.1
  set v := qfU h0.1
  set ev : Fin M → ℝ := fun k => h0.1.eigenvalues k
  have hvv : vᵀ * v.map star = 1 := by
    have h := (mem_unitaryGroup_iff').mp hv
    have := congrArg transpose h
    rwa [transpose_mul, transpose_one, star_eq_conjTranspose, conjTranspose, transpose_map,
      transpose_transpose] at this
  -- the occupations are in `[0, 1]` and sum to `N`
  have hb : ∀ k, 0 ≤ ev k ∧ ev k ≤ 1 := by
    intro k
    refine ⟨h0.eigenvalues_nonneg k, ?_⟩
    have hconj : (vᵀ)ᴴ = v.map star := by ext a b; simp
    have hD1 : 1 - diagonal (fun k => (ev k : ℂ)) = vᵀ * (1 - γ) * (vᵀ)ᴴ := by
      have hD : diagonal (fun k => (ev k : ℂ)) = vᵀ * γ * (vᵀ)ᴴ := by
        rw [hconj, hγ]
        calc diagonal (fun k => (ev k : ℂ)) = (vᵀ * v.map star) * diagonal (fun k => (ev k : ℂ)) *
              (vᵀ * v.map star) := by rw [hvv, one_mul, mul_one]
          _ = _ := by simp only [mul_assoc]; rfl
      rw [mul_sub, sub_mul, mul_one, ← hD, hconj, hvv]
    have h := (h1.mul_mul_conjTranspose_same vᵀ).diag_nonneg (i := k)
    rw [← hD1, Matrix.sub_apply, Matrix.one_apply_eq, diagonal_apply_eq] at h
    have h' := (Complex.nonneg_iff.mp h).1
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at h'
    linarith
  have hsum : ∑ k, ev k = N := by
    have := h0.1.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h4 := congrArg Complex.re this
    simp only [Complex.natCast_re] at h4
    rw [h4]
    simp [ev]
  -- apply the abstract lemma to `F n = E_HF(v̄ diag(n) vᵀ)`
  set F : (Fin M → ℝ) → ℝ := fun n => hfEnergy h V (natMat v fun k => (n k : ℂ))
  have hF : ∀ n (a b : Fin M), a ≠ b → ∃ l c : ℝ, c ≤ 0 ∧ ∀ t : ℝ,
      F (n + t • (Pi.single a 1 - Pi.single b 1)) = F n + l * t + c * t ^ 2 := by
    intro n a b _
    refine ⟨(∑ i, ∑ j, h i j * (natMat v fun k =>
        (((Pi.single a 1 - Pi.single b 1 : Fin M → ℝ) k : ℝ) : ℂ)) i j +
      pairForm V (natMat v fun k => (n k : ℂ))
        (natMat v fun k => (((Pi.single a 1 - Pi.single b 1 : Fin M → ℝ) k : ℝ) : ℂ)) +
      pairForm V (natMat v fun k => (((Pi.single a 1 - Pi.single b 1 : Fin M → ℝ) k : ℝ) : ℂ))
        (natMat v fun k => (n k : ℂ))).re, _, pairForm_shift_re_nonpos V hV v a b, fun t => ?_⟩
    simp only [F]
    rw [natMat_add_smul, hfEnergy_add_smul]
  obtain ⟨m, hm, hms, hFm⟩ := exists_vertex_le F hF ev hb hsum
  have hFγ : F ev = hfEnergy h V γ := congrArg (hfEnergy h V) hγ.symm
  refine ⟨natMat v fun k => (m k : ℂ), ?_, ?_, ?_, hFm.trans_eq hFγ⟩
  · ext i j
    simp only [conjTranspose_apply, natMat_apply, star_sum, star_mul',
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · have hD : (diagonal fun k => (m k : ℂ)) * diagonal (fun k => (m k : ℂ)) =
        diagonal fun k => (m k : ℂ) := by
      rw [diagonal_mul_diagonal]; congr 1; funext k; rcases hm k with h | h <;> simp [h]
    simp only [natMat]
    calc v.map star * diagonal (fun k => (m k : ℂ)) * vᵀ *
          (v.map star * diagonal (fun k => (m k : ℂ)) * vᵀ)
        = v.map star * diagonal (fun k => (m k : ℂ)) * (vᵀ * v.map star) *
            diagonal (fun k => (m k : ℂ)) * vᵀ := by simp only [mul_assoc]
      _ = _ := by rw [hvv, mul_one, mul_assoc (v.map star), hD]
  · rw [natMat, trace_mul_comm, ← mul_assoc, hvv, one_mul, trace_diagonal]
    exact_mod_cast hms

/-- **Some `N`-particle state has energy at most `E_HF(γ)`** (a Slater state), for every
`0 ≤ γ ≤ 1` with `tr γ = N`. -/
theorem exists_state_le_hf {N : ℕ} (hV : V.PosSemidef) {γ : Matrix (Fin M) (Fin M) ℂ}
    (h0 : γ.PosSemidef) (h1 : (1 - γ).PosSemidef) (htr : γ.trace = N) :
    ∃ Ψ : Fock M, IsNState N Ψ ∧ (inner ℂ Ψ (toFockCLM (ham h V) Ψ)).re ≤ hfEnergy h V γ := by
  obtain ⟨P, hPh, hPP, hPtr, hPE⟩ := lieb_variational h V hV h0 h1 htr
  obtain ⟨u, hu, s, hs, hP⟩ := exists_slater_of_proj hPh hPP hPtr
  refine ⟨slaterState u s, hs ▸ slaterState_isNState hu s, ?_⟩
  rw [energy_slater h V hu, hP]
  exact hPE

/-- **The ground-state energy is at most the Hartree–Fock energy of every admissible `γ`.** -/
theorem ground_le_hf {N : ℕ} (hV : V.PosSemidef) {Φ : Fock M}
    (hΦ : ∀ Ψ : Fock M, IsNState N Ψ →
      (inner ℂ Φ (toFockCLM (ham h V) Φ)).re ≤ (inner ℂ Ψ (toFockCLM (ham h V) Ψ)).re)
    {γ : Matrix (Fin M) (Fin M) ℂ} (h0 : γ.PosSemidef) (h1 : (1 - γ).PosSemidef)
    (htr : γ.trace = N) :
    (inner ℂ Φ (toFockCLM (ham h V) Φ)).re ≤ hfEnergy h V γ := by
  obtain ⟨Ψ, hΨ, hE⟩ := exists_state_le_hf h V hV h0 h1 htr
  exact (hΦ Ψ hΨ).trans hE

/-! ### Existence of a Hartree–Fock minimizer -/

lemma continuous_hfEnergy : Continuous (hfEnergy h V) := by
  unfold hfEnergy pairForm
  fun_prop

/-- **A Slater state minimizes the Hartree–Fock functional** over all `0 ≤ γ ≤ 1` with
`tr γ = N`. -/
theorem exists_hf_minimizer {N : ℕ} (hN : N ≤ M) (hV : V.PosSemidef) :
    ∃ u ∈ unitaryGroup (Fin M) ℂ, ∃ s : Finset (Fin M), s.card = N ∧
      ∀ γ : Matrix (Fin M) (Fin M) ℂ, γ.PosSemidef → (1 - γ).PosSemidef → γ.trace = N →
        hfEnergy h V (rdm1 (slaterState u s)) ≤ hfEnergy h V γ := by
  set G : Finset (Fin M) → Matrix (Fin M) (Fin M) ℂ → ℝ := fun s u =>
    hfEnergy h V (natMat u fun i => if i ∈ s then 1 else 0)
  have hG : ∀ s, Continuous (G s) := fun s =>
    (continuous_hfEnergy h V).comp
      (((continuous_id.matrix_map continuous_star).matrix_mul continuous_const).matrix_mul
        continuous_id.matrix_transpose)
  have hmin : ∀ s, ∃ u ∈ unitaryGroup (Fin M) ℂ, ∀ w ∈ unitaryGroup (Fin M) ℂ, G s u ≤ G s w :=
    fun s => (Matrix.isCompact_unitaryGroup.exists_isMinOn ⟨1, one_mem _⟩
      (hG s).continuousOn).imp fun u hu => ⟨hu.1, fun w hw => hu.2 hw⟩
  choose U hU hUmin using hmin
  obtain ⟨s₀, hs₀⟩ : (Finset.univ.filter fun s : Finset (Fin M) => s.card = N).Nonempty := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin M)))
      (by simpa using hN)
    exact ⟨s, by simpa using hs⟩
  obtain ⟨s, hsT, hsmin⟩ := Finset.exists_min_image _ (fun s => G s (U s)) ⟨s₀, hs₀⟩
  have hscard : s.card = N := (Finset.mem_filter.mp hsT).2
  refine ⟨U s, hU s, s, hscard, fun γ h0 h1 htr => ?_⟩
  obtain ⟨P, hPh, hPP, hPtr, hPE⟩ := lieb_variational h V hV h0 h1 htr
  obtain ⟨v, hv, t, ht, hP⟩ := exists_slater_of_proj hPh hPP hPtr
  have e1 : hfEnergy h V (rdm1 (slaterState (U s) s)) = G s (U s) := by
    simp only [G, rdm1_slaterState_eq (hU s)]; rfl
  have e2 : hfEnergy h V P = G t v := by
    simp only [G, ← hP, rdm1_slaterState_eq hv]; rfl
  rw [e1]
  calc G s (U s) ≤ G t (U t) := hsmin t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
    _ ≤ G t v := hUmin t v hv
    _ = hfEnergy h V P := e2.symm
    _ ≤ hfEnergy h V γ := hPE

end QM.ManyBody
