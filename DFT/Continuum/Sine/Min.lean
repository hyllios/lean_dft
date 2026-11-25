/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Form

/-!
# A minimiser in coefficient space

The energy of a coefficient sequence is `F(c) = Σ_m λ_m c_m² + Σ_m c_m (Kc)_m`, `λ_m = π² |k|²`.
Among sequences of the exchange symmetry `τ` with `Σ c² = 1` and finite kinetic energy, `F` attains
its infimum `E₀` (direct method). A minimising sequence has bounded kinetic energy, so its tails
`Σ_{m ∉ T_K} c_m²` are uniformly small; a subsequence converges coordinatewise (the cube `[-1, 1]^I`
is compact and first countable), hence in `ℓ²`, the potential energy converges, and the kinetic
energy is lower semicontinuous.

* `lam`, `Adm`, `Fn`, `E0`.
* `box`, `tail_le`, `tendsto_l2`: tails outside `T_K = {m | m_j < K}` are at most `M / (K + 1)`, so
  coordinatewise convergence with bounded kinetic energy is `ℓ²` convergence.
* `exists_min`: **the minimiser**.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real
open scoped ENNReal

variable {n : ℕ}

/-- `λ_m = π² |k|²`. -/
noncomputable def lam (m : Fin (n + 1) → ℕ) : ℝ := π ^ 2 * ksq m

lemma lam_nonneg (m : Fin (n + 1) → ℕ) : 0 ≤ lam m := by unfold lam; positivity

/-- Admissible sequences: square summable, finite kinetic energy, exchange symmetry `τ`. -/
structure Dir (τ : SymT n) (c : (Fin (n + 1) → ℕ) → ℝ) : Prop where
  sq : Summable fun m => c m ^ 2
  kin : Summable fun m => lam m * c m ^ 2
  sym : InS τ c

/-- Normalised admissible sequences. -/
structure Adm (τ : SymT n) (c : (Fin (n + 1) → ℕ) → ℝ) : Prop extends Dir τ c where
  norm : ∑' m, c m ^ 2 = 1

/-- The energy of a coefficient sequence. -/
noncomputable def Fn (V : Cfg n → ℝ) (c : (Fin (n + 1) → ℕ) → ℝ) : ℝ :=
  ∑' m, lam m * c m ^ 2 + Bf V c c

/-- The ground-state energy in coefficient space. -/
noncomputable def E0 (V : Cfg n → ℝ) (τ : SymT n) : ℝ := sInf (Fn V '' {c | Adm τ c})

lemma InS_smul {τ : SymT n} {c : (Fin (n + 1) → ℕ) → ℝ} (hc : InS τ c) (a : ℝ) :
    InS τ fun m => a * c m := fun σ hσ m => by
  change a * c (pmI σ m) = τ.χ σ * (a * c m)
  rw [hc σ hσ m]; ring

lemma Dir_smul {τ : SymT n} {c : (Fin (n + 1) → ℕ) → ℝ} (hc : Dir τ c) (a : ℝ) :
    Dir τ fun m => a * c m :=
  ⟨by simpa [mul_pow] using hc.sq.mul_left (a ^ 2),
    by simpa [mul_pow, mul_left_comm] using hc.kin.mul_left (a ^ 2), InS_smul hc.sym a⟩

namespace KBd

section energy

variable {V : Cfg n → ℝ} {C : ℝ} (hK : KBd V C)
include hK

lemma abs_Bf_le {c : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2) :
    |Bf V c c| ≤ √C * ∑' m, c m ^ 2 := by
  have h := hK.Bf_sq_le hc hc
  have h0 : 0 ≤ ∑' m, c m ^ 2 := tsum_nonneg fun m => sq_nonneg _
  rw [← Real.sqrt_sq (abs_nonneg _), sq_abs, ← Real.sqrt_sq h0, ← Real.sqrt_mul (hK.nonneg)]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- The energy is bounded below on normalised sequences. -/
lemma Fn_ge_neg {τ : SymT n} {c : (Fin (n + 1) → ℕ) → ℝ} (hc : Adm τ c) : -√C ≤ Fn V c := by
  have h1 := abs_Bf_le hK hc.sq
  rw [hc.norm, mul_one] at h1
  have h2 : 0 ≤ ∑' m, lam m * c m ^ 2 :=
    tsum_nonneg fun m => mul_nonneg (lam_nonneg m) (sq_nonneg _)
  rw [Fn]
  linarith [neg_abs_le (Bf V c c)]

lemma bddBelow_Fn (τ : SymT n) : BddBelow (Fn V '' {c | Adm τ c}) :=
  ⟨-√C, by rintro _ ⟨c, hc, rfl⟩; exact Fn_ge_neg hK hc⟩

end energy

end KBd

/-- The box `T_K = {m | m_j < K for all j}`. -/
def box (K : ℕ) : Finset (Fin (n + 1) → ℕ) := Fintype.piFinset fun _ => Finset.range K

/-- Outside the box `T_K`, `λ_m ≥ K + 1`. -/
lemma lam_ge {K : ℕ} {m : Fin (n + 1) → ℕ} (hm : m ∉ box K) : (K : ℝ) + 1 ≤ lam m := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_range, not_forall, not_lt] at hm
  obtain ⟨i, hi⟩ := hm
  have h1 : K + 1 ≤ ksq m :=
    le_trans (by nlinarith) (Finset.single_le_sum (f := fun j => (m j + 1) ^ 2)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
  have h2 : ((K : ℝ) + 1) ≤ ksq m := by exact_mod_cast h1
  have h3 : (1 : ℝ) ≤ π ^ 2 := by nlinarith [pi_gt_three]
  unfold lam
  nlinarith [(ksq m).cast_nonneg (α := ℝ)]

/-- The complement of the box. -/
def out (K : ℕ) : Set (Fin (n + 1) → ℕ) := {m | m ∉ box K}

/-- **Tail bound**: `Σ_{m ∉ T_K} c_m² ≤ (Σ λ c²) / (K + 1)`. -/
lemma tail_le {c : (Fin (n + 1) → ℕ) → ℝ} (hs : Summable fun m => c m ^ 2)
    (hk : Summable fun m => lam m * c m ^ 2) (K : ℕ) :
    ∑' m : out (n := n) K, c m ^ 2 ≤ (∑' m, lam m * c m ^ 2) / ((K : ℝ) + 1) := by
  have h1 : Summable fun m : out (n := n) K => c m ^ 2 * ((K : ℝ) + 1) :=
    (hs.comp_injective Subtype.val_injective).mul_right _
  have h2 : Summable fun m : out (n := n) K => lam (n := n) m * c m ^ 2 :=
    hk.comp_injective Subtype.val_injective
  have h3 : ∀ m : out (n := n) K, c m ^ 2 * ((K : ℝ) + 1) ≤ lam (n := n) m * c m ^ 2 := fun m => by
    have := lam_ge (n := n) (K := K) (m := m) m.2
    nlinarith [sq_nonneg (c m)]
  have h0 : ∀ m, 0 ≤ lam m * c m ^ 2 := fun m => mul_nonneg (lam_nonneg m) (sq_nonneg (c m))
  rw [le_div_iff₀ (by positivity), ← tsum_mul_right]
  exact (Summable.tsum_le_tsum h3 h1 h2).trans (hk.tsum_subtype_le _ _ h0)

lemma exists_div_lt {M ε : ℝ} (hε : 0 < ε) : ∃ K : ℕ, M / ((K : ℝ) + 1) < ε := by
  obtain ⟨K, hK⟩ := exists_nat_gt (M / ε)
  refine ⟨K, ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hK
  nlinarith

/-- Weighted sums are lower semicontinuous under coordinatewise convergence. -/
lemma lim_sum_le {d : ℕ → (Fin (n + 1) → ℕ) → ℝ} {a : (Fin (n + 1) → ℕ) → ℝ}
    (hlim : ∀ m, Tendsto (fun j => d j m) atTop (𝓝 (a m))) {w : (Fin (n + 1) → ℕ) → ℝ}
    (hw : ∀ m, 0 ≤ w m) {B : ℝ} (hd : ∀ j, Summable fun m => w m * d j m ^ 2)
    (hB : ∀ j, ∑' m, w m * d j m ^ 2 ≤ B) :
    Summable (fun m => w m * a m ^ 2) ∧ ∑' m, w m * a m ^ 2 ≤ B := by
  have hT : ∀ T : Finset (Fin (n + 1) → ℕ), ∑ m ∈ T, w m * a m ^ 2 ≤ B := fun T => by
    refine le_of_tendsto' (tendsto_finsetSum T fun m _ => ((hlim m).pow 2).const_mul (w m))
      fun j => ?_
    exact ((hd j).sum_le_tsum T fun m _ => mul_nonneg (hw m) (sq_nonneg _)).trans (hB j)
  have h0 : 0 ≤ fun m => w m * a m ^ 2 := fun m => mul_nonneg (hw m) (sq_nonneg _)
  exact ⟨summable_of_sum_le h0 hT, Real.tsum_le_of_sum_le h0 hT⟩

lemma summable_sub_sq {c d : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hd : Summable fun m => d m ^ 2) : Summable fun m => (c m - d m) ^ 2 :=
  Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => by nlinarith [sq_nonneg (c m + d m)])
    ((hc.add hd).mul_left 2)

/-- `Σ_{T_K} c² ≥ Σ c² − M / (K + 1)` when the kinetic energy is at most `M`. -/
lemma sum_box_ge {c : (Fin (n + 1) → ℕ) → ℝ} (hs : Summable fun m => c m ^ 2)
    (hk : Summable fun m => lam m * c m ^ 2) {M : ℝ} (hM : ∑' m, lam m * c m ^ 2 ≤ M) (K : ℕ) :
    ∑' m, c m ^ 2 - M / ((K : ℝ) + 1) ≤ ∑ m ∈ box K, c m ^ 2 := by
  have h := hs.sum_add_tsum_compl (s := box (n := n) K)
  change ∑ m ∈ box K, c m ^ 2 + ∑' m : out (n := n) K, c m ^ 2 = _ at h
  have ht := tail_le hs hk K
  have : (∑' m, lam m * c m ^ 2) / ((K : ℝ) + 1) ≤ M / ((K : ℝ) + 1) :=
    div_le_div_of_nonneg_right hM (by positivity)
  linarith

/-- **`ℓ²` convergence**: coordinatewise convergence with a uniform kinetic bound. -/
lemma tendsto_l2 {d : ℕ → (Fin (n + 1) → ℕ) → ℝ} {a : (Fin (n + 1) → ℕ) → ℝ}
    (hlim : ∀ m, Tendsto (fun j => d j m) atTop (𝓝 (a m))) {M : ℝ}
    (hds : ∀ j, Summable fun m => d j m ^ 2) (hdk : ∀ j, Summable fun m => lam m * d j m ^ 2)
    (hdM : ∀ j, ∑' m, lam m * d j m ^ 2 ≤ M)
    (has : Summable fun m => a m ^ 2) (hak : Summable fun m => lam m * a m ^ 2)
    (haM : ∑' m, lam m * a m ^ 2 ≤ M) :
    Tendsto (fun j => ∑' m, (d j m - a m) ^ 2) atTop (𝓝 0) := by
  have hsum : ∀ j, Summable fun m => (d j m - a m) ^ 2 := fun j => summable_sub_sq (hds j) has
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_div_lt (M := 4 * M) (half_pos hε)
  have hfin : Tendsto (fun j => ∑ m ∈ box (n := n) K, (d j m - a m) ^ 2) atTop (𝓝 0) := by
    have := tendsto_finsetSum (box (n := n) K) fun m _ =>
      ((hlim m).sub (tendsto_const_nhds (x := a m))).pow 2
    simpa using this
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hfin) (ε / 2) (half_pos hε)
  refine ⟨N, fun j hj => ?_⟩
  have h1 := hN j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _)] at h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun m => sq_nonneg _)]
  have hsplit := (hsum j).sum_add_tsum_compl (s := box (n := n) K)
  change _ + ∑' m : out (n := n) K, (d j m - a m) ^ 2 = _ at hsplit
  have sd : Summable fun m : out (n := n) K => d j m ^ 2 :=
    (hds j).comp_injective Subtype.val_injective
  have sa : Summable fun m : out (n := n) K => a m ^ 2 := has.comp_injective Subtype.val_injective
  have htail : ∑' m : out (n := n) K, (d j m - a m) ^ 2 ≤
      2 * ∑' m : out (n := n) K, d j m ^ 2 + 2 * ∑' m : out (n := n) K, a m ^ 2 := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (sd.mul_left 2).tsum_add (sa.mul_left 2)]
    exact Summable.tsum_le_tsum (fun m => by nlinarith [sq_nonneg (d j m + a m)])
      ((hsum j).comp_injective Subtype.val_injective) ((sd.mul_left 2).add (sa.mul_left 2))
  have t1 := (tail_le (hds j) (hdk j) K).trans (div_le_div_of_nonneg_right (hdM j) (by positivity))
  have t2 := (tail_le has hak K).trans (div_le_div_of_nonneg_right haM (by positivity))
  have e : 4 * M / ((K : ℝ) + 1) = 4 * (M / ((K : ℝ) + 1)) := mul_div_assoc _ _ _
  linarith


lemma lam_pm (σ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) : lam (pmI σ m) = lam m := by
  simp only [lam, ksq_pm]

lemma mem_box_pm {K : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) :
    pmI σ m ∈ box K ↔ m ∈ box K := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_range, pmI]
  exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h _⟩

lemma mem_box_sup (m : Fin (n + 1) → ℕ) : m ∈ box (Finset.univ.sup m + 1) := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_range]
  exact fun i => Nat.lt_succ_of_le (Finset.le_sup (f := m) (Finset.mem_univ i))

/-! ### The direct method -/

namespace KBd

section minimiser

variable {V : Cfg n → ℝ} {C : ℝ} (hK : KBd V C)
include hK

lemma abs_Bf_le' {c d : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hd : Summable fun m => d m ^ 2) :
    |Bf V c d| ≤ √(C * (∑' m, c m ^ 2) * ∑' m, d m ^ 2) :=
  Real.abs_le_sqrt (hK.Bf_sq_le hc hd)

/-- Continuity of the potential energy in `ℓ²`. -/
lemma abs_Bf_sub_le {c d : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hd : Summable fun m => d m ^ 2) :
    |Bf V c c - Bf V d d| ≤ √(C * (∑' m, (c m - d m) ^ 2) * ∑' m, c m ^ 2) +
      √(C * (∑' m, d m ^ 2) * ∑' m, (c m - d m) ^ 2) := by
  have hcd := summable_sub_sq hc hd
  have e : Bf V c c - Bf V d d = Bf V (fun m => c m - d m) c + Bf V d (fun m => c m - d m) := by
    rw [← hK.Bf_sub_left hc hd hc, ← hK.Bf_sub_right hd hc hd]; ring
  rw [e]
  exact (abs_add_le _ _).trans
    (add_le_add (abs_Bf_le' hK hcd hc) (abs_Bf_le' hK hd hcd))

/-- **The minimiser** (direct method): if some normalised admissible sequence exists, the energy
attains its infimum `E₀`. -/
theorem exists_min {τ : SymT n} (hne : ∃ c : (Fin (n + 1) → ℕ) → ℝ, Adm τ c) :
    ∃ c, Adm τ c ∧ Fn V c = E0 V τ := by
  have hbdd := bddBelow_Fn hK (V := V) τ
  obtain ⟨c0, hc0⟩ := hne
  have hSne : (Fn V '' {c | Adm τ c}).Nonempty := ⟨_, c0, hc0, rfl⟩
  have hseq : ∀ j : ℕ, ∃ c, Adm τ c ∧ Fn V c < E0 V τ + 1 / ((j : ℝ) + 1) := fun j => by
    have hp : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    obtain ⟨_, ⟨c, hc, rfl⟩, h⟩ := exists_lt_of_csInf_lt hSne
      (show sInf (Fn V '' {c | Adm τ c}) < E0 V τ + 1 / ((j : ℝ) + 1) by unfold E0; linarith)
    exact ⟨c, hc, h⟩
  choose c hc hcE using hseq
  have hcE' : ∀ j, E0 V τ ≤ Fn V (c j) := fun j => csInf_le hbdd ⟨_, hc j, rfl⟩
  set M := E0 V τ + 1 + √C with hM
  have hkin : ∀ j, ∑' m, lam m * c j m ^ 2 ≤ M := fun j => by
    have h1 := abs_Bf_le hK (hc j).sq
    rw [(hc j).norm, mul_one] at h1
    have h2 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    have h3 := hcE j
    unfold Fn at h3
    linarith [neg_abs_le (Bf V (c j) (c j))]
  have hbox : ∀ j, c j ∈ Set.univ.pi fun _ : Fin (n + 1) → ℕ => Set.Icc (-1 : ℝ) 1 := fun j =>
    Set.mem_univ_pi.2 fun m => by
      have h : c j m ^ 2 ≤ 1 :=
        (hc j).norm ▸ (hc j).sq.le_tsum m (fun m' _ => sq_nonneg (c j m'))
      exact abs_le.1 ((sq_le_one_iff_abs_le_one _).1 h)
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ : Fin (n + 1) → ℕ => isCompact_Icc).tendsto_subseq hbox
  rw [tendsto_pi_nhds] at hlim
  set d := fun j => c (φ j) with hd_def
  have hd : ∀ j, Adm τ (d j) := fun j => hc (φ j)
  have hdM : ∀ j, ∑' m, lam m * d j m ^ 2 ≤ M := fun j => hkin (φ j)
  have hlim' : ∀ m, Tendsto (fun j => d j m) atTop (𝓝 (a m)) := hlim
  -- the limit: norm, kinetic energy, symmetry
  have hak := lim_sum_le hlim' (fun m => lam_nonneg m) (fun j => (hd j).kin) hdM
  have has := lim_sum_le hlim' (w := fun _ => 1) (B := 1) (fun _ => zero_le_one)
    (fun j => by simpa using (hd j).sq) (fun j => by simpa using (hd j).norm.le)
  simp only [one_mul] at has
  have hsym : InS τ a := fun σ hσ m =>
    tendsto_nhds_unique (hlim' (pmI σ m))
      (by simpa only [(hd _).sym σ hσ m] using (hlim' m).const_mul (τ.χ σ))
  have hM0 : 0 ≤ M := (tsum_nonneg fun m => mul_nonneg (lam_nonneg m) (sq_nonneg (a m))).trans hak.2
  have hnorm : ∑' m, a m ^ 2 = 1 := by
    refine le_antisymm has.2 (le_of_forall_pos_lt_add fun ε hε => ?_)
    obtain ⟨K, hK⟩ := exists_div_lt (M := M) hε
    have hT : 1 - M / ((K : ℝ) + 1) ≤ ∑ m ∈ box K, a m ^ 2 := by
      refine ge_of_tendsto' (tendsto_finsetSum (box (n := n) K) fun m _ => (hlim' m).pow 2)
        fun j => ?_
      have := sum_box_ge (hd j).sq (hd j).kin (hdM j) K
      rwa [(hd j).norm] at this
    have := has.1.sum_le_tsum (box K) fun m _ => sq_nonneg (a m)
    linarith
  have ha : Adm τ a := ⟨⟨has.1, hak.1, hsym⟩, hnorm⟩
  -- convergence of the energies
  have hl2 := tendsto_l2 hlim' (fun j => (hd j).sq) (fun j => (hd j).kin) hdM has.1 hak.1 hak.2
  have hB : Tendsto (fun j => Bf V (d j) (d j)) atTop (𝓝 (Bf V a a)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun j => √(C * (∑' m, (d j m - a m) ^ 2) * 1) +
        √(C * 1 * ∑' m, (d j m - a m) ^ 2)) atTop (𝓝 0) := by
      have h1 := ((tendsto_const_nhds (x := C)).mul hl2).mul_const 1
      have h2 := (tendsto_const_nhds (x := C * 1)).mul hl2
      simpa using h1.sqrt.add h2.sqrt
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hb
    have := abs_Bf_sub_le hK (hd j).sq ha.sq
    rwa [(hd j).norm, hnorm] at this
  have hF : Tendsto (fun j => Fn V (d j)) atTop (𝓝 (E0 V τ)) := by
    have hup : Tendsto (fun j : ℕ => E0 V τ + 1 / ((j : ℝ) + 1)) atTop (𝓝 (E0 V τ)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (E0 V τ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun j => hcE' (φ j)) fun j => (hcE (φ j)).le.trans ?_
    have : ((j : ℝ) + 1) ≤ (φ j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right (hφ.id_le j) 1
    gcongr
  -- lower semicontinuity of the kinetic energy
  have hle : ∀ T : Finset (Fin (n + 1) → ℕ), ∑ m ∈ T, lam m * a m ^ 2 ≤ E0 V τ - Bf V a a :=
    fun T => by
      have h := le_of_tendsto_of_tendsto'
        ((tendsto_finsetSum T fun m _ => ((hlim' m).pow 2).const_mul (lam m)).add hB) hF
        fun j => by
          unfold Fn
          exact add_le_add ((hd j).kin.sum_le_tsum T fun m _ =>
            mul_nonneg (lam_nonneg m) (sq_nonneg _)) le_rfl
      linarith
  have hkin_a := Real.tsum_le_of_sum_le (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg (a m))) hle
  refine ⟨a, ha, le_antisymm ?_ (csInf_le hbdd ⟨a, ha, rfl⟩)⟩
  unfold Fn
  linarith

end minimiser

end KBd

end DFT.Continuum.Sine
