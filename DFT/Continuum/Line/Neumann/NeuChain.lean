/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Neumann.NeuDens

/-!
# The chain rule with Neumann walls

For `Φ ∈ H¹` of the cube (no boundary condition) the cosine truncations `P_M = truncC M Φ` are `C²`
with `∂ₖ P_M ⇀ ∂ₖ Φ` weakly in `L²` (**`tendsto_truncC_dk`**). As in `Line/Chain` this gives the
chain rule `∂ₖ (G ∘ Φ) = G'(Φ) ∂ₖ Φ` for `G ∈ C¹` with bounded derivative (**`isWDN_comp`**). The
weak convergence is tested on the sine basis: sines vanish on all faces, so they are admissible
Neumann test functions.

* `IsWDN.mul_C1`: the product rule with a `C¹` function.
* **`isWDN_abs`**, `abs_mem_DomN`, `kinN_abs_le` (Kato's inequality with Neumann walls).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology Sine

variable {n : ℕ} {τ : Stat}

/-! ### Weak convergence of the derivatives of the cosine truncations -/

lemma testN_smd (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) : TestN k (smd m) :=
  ⟨(contDiff_smd m).of_le (by norm_num), fun x hx => smd_face m x k hx⟩

/-- `⟨s_m, ∂ₖ Ψ⟩ = -π(m_k+1) ⟨c^k_m, Ψ⟩` for Neumann weak derivatives. -/
lemma integral_smd_dkN (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) {Ψ G : Cfg n → ℝ}
    (hG : IsWDN k Ψ G) :
    ∫ x, smd m x * G x ∂μN n = -(π * (m k + 1)) * ∫ x, Ψ x * cmd k m x ∂μN n := by
  have h := hG.2 (smd m) (testN_smd k m)
  have e1 : ∫ x, Ψ x * dk k (smd m) x ∂μN n = π * (m k + 1) * ∫ x, Ψ x * cmd k m x ∂μN n := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [dk_smd]; ring)
  have e2 : ∫ x, smd m x * G x ∂μN n = ∫ x, G x * smd m x ∂μN n :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  rw [e2]
  linarith

section truncC

variable {s : Sine.SymT n} {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomNS s)
include hΦ

/-- The cosine truncations have kinetic energy at most that of `Φ`, in each direction. -/
lemma norm_dk_truncC_sq_le (k : Fin (n + 1)) (M : ℕ) :
    ∫ x, dk k (truncC M Φ) x ^ 2 ∂μN n ≤ kinN Φ := by
  have hc : ∀ k, Continuous (dk k (truncC M Φ)) := fun k =>
    continuous_dk_of_C1 ((contDiff_truncC M Φ).of_le (by norm_num)) k
  have h := kin_truncC_le hΦ M
  rw [integral_finsetSum (f := fun k x => dk k (truncC M Φ) x * dk k (truncC M Φ) x) _
    fun k _ => integrableN ((hc k).mul (hc k))] at h
  refine le_trans ?_ h
  have := Finset.single_le_sum
    (f := fun k => ∫ x, dk k (truncC M Φ) x * dk k (truncC M Φ) x ∂μN n)
    (fun k _ => integral_nonneg fun x => mul_self_nonneg _) (Finset.mem_univ k)
  refine le_trans (le_of_eq ?_) this
  exact integral_congr_ae (ae_of_all _ fun x => sq _)

/-- **Weak convergence of the derivatives of the cosine truncations.** -/
theorem tendsto_truncC_dk (k : Fin (n + 1)) {g : Cfg n → ℝ} (hg : MemLp g 2 (μN n)) :
    Tendsto (fun M => ∫ x, g x * dk k (truncC M Φ) x ∂μN n) atTop
      (𝓝 (∫ x, g x * dWN k Φ x ∂μN n)) := by
  have hPm : ∀ M, MemLp (dk k (truncC M Φ)) 2 (μN n) := fun M =>
    memLp_cont (continuous_dk_of_C1 ((contDiff_truncC M Φ).of_le (by norm_num)) k)
  have hW := dWN_spec (hΦ.2.1 k)
  set x : ℕ → HN n := fun M => (hPm M).toLp _
  set x0 : HN n := hW.1.toLp _
  have hC : ∀ M, ‖x M‖ ≤ √(kinN Φ) := fun M => by
    refine Real.le_sqrt_of_sq_le ?_
    rw [norm_sq_toLp]
    exact norm_dk_truncC_sq_le hΦ k M
  have hb : ∀ m, Tendsto (fun M => inner ℝ (bN m) (x M)) atTop (𝓝 (inner ℝ (bN m) x0)) := by
    intro m
    simp only [bN_apply, x, x0, eN, inner_toLp_toLp]
    rw [integral_smd_dkN k m hW]
    simp only [fun M => integral_smd_dkN k m
      (isWDN_of_C1 ((contDiff_truncC M Φ).of_le (by norm_num)) k)]
    refine Tendsto.const_mul _ ?_
    exact tendsto_integral_mul_of_L2 (fun M => memLp_cont (continuous_truncC M Φ)) hΦ.1
      (memLp_cont (contDiff_cmd k m).continuous) (tendsto_truncC hΦ.1)
  have h := tendsto_inner_of_basis bN hC hb (hg.toLp g)
  simp only [x, x0, inner_toLp_toLp] at h
  exact h

/-- **The chain rule with Neumann walls**: `∂ₖ (G ∘ Φ) = G'(Φ) ∂ₖ Φ` for `G ∈ C¹`, `|G'| ≤ L`,
`G(0) = 0`. -/
theorem isWDN_comp {G G' : ℝ → ℝ}
    (hG : ∀ t, HasDerivAt G (G' t) t) (hG'c : Continuous G') {L : ℝ} (hL : ∀ t, |G' t| ≤ L)
    (hG0 : G 0 = 0) (k : Fin (n + 1)) :
    IsWDN k (fun x => G (Φ x)) (fun x => G' (Φ x) * dWN k Φ x) := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hGd : Differentiable ℝ G := fun t => (hG t).differentiableAt
  have hderiv : deriv G = G' := funext fun t => (hG t).deriv
  have hGC1 : ContDiff ℝ 1 G := contDiff_one_iff_deriv.2 ⟨hGd, hderiv ▸ hG'c⟩
  have hLip : ∀ a b, |G a - G b| ≤ L * |a - b| := by
    have hl := lipschitzWith_of_nnnorm_deriv_le (C := L.toNNReal) hGd (fun x => by
      rw [hderiv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hL0]
      exact hL x)
    intro a b
    have h := hl.dist_le_mul a b
    rwa [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0] at h
  have hGb : ∀ t, |G t| ≤ L * |t| := fun t => by simpa [hG0] using hLip t 0
  have hW := dWN_spec (hΦ.2.1 k)
  have hΦm := hΦ.1.aestronglyMeasurable
  have hGΦ : MemLp (fun x => G (Φ x)) 2 (μN n) :=
    hΦ.1.of_le_mul (c := L) (hGC1.continuous.comp_aestronglyMeasurable hΦm)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hGb _)
  have hG'Φm : AEStronglyMeasurable (fun x => G' (Φ x)) (μN n) :=
    hG'c.comp_aestronglyMeasurable hΦm
  have hG'Φ : MemLp (fun x => G' (Φ x)) 2 (μN n) :=
    MemLp.of_bound hG'Φm L (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hL _)
  refine ⟨hW.1.of_le_mul (c := L) (hG'Φm.mul hW.1.aestronglyMeasurable) (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hL _) (abs_nonneg _)), fun φ hφ => ?_⟩
  set P : ℕ → Cfg n → ℝ := fun M => truncC M Φ with hPdef
  have hP2 : ∀ M, ContDiff ℝ 2 (P M) := fun M => contDiff_truncC M Φ
  have hPc : ∀ M, Continuous (P M) := fun M => continuous_truncC M Φ
  -- the classical identity for the truncations
  have hM : ∀ M, ∫ x, G (P M x) * dk k φ x ∂μN n =
      -∫ x, G' (P M x) * dk k (P M) x * φ x ∂μN n := fun M => by
    have hC1 : ContDiff ℝ 1 (fun x => G (P M x)) := hGC1.comp ((hP2 M).of_le (by norm_num))
    have h := (isWDN_of_C1 hC1 k).2 φ hφ
    have hdk : ∀ x, dk k (fun x => G (P M x)) x = G' (P M x) * dk k (P M) x := fun x => by
      have hf := (((hP2 M).differentiable (by norm_num)) x).hasFDerivAt
      have h2 := ((hG (P M x)).comp_hasFDerivAt x hf).fderiv
      simp only [dk]
      rw [show (fun x => G (P M x)) = G ∘ P M from rfl, h2]
      simp
    simp only [hdk] at h
    exact h
  -- a subsequence converging a.e.
  have hL2 := tendsto_truncC hΦ.1
  obtain ⟨ns, hns, hae⟩ := exists_ae_subseq (fun M => memLp_cont (hPc M)) hΦ.1 hL2
  have hL2s : Tendsto (fun j => ∫ x, (Φ x - P (ns j) x) ^ 2 ∂μN n) atTop (𝓝 0) :=
    hL2.comp hns.tendsto_atTop
  have hdφ := continuous_dk_of_C1 hφ.1 k
  -- the left side
  have hlhs : Tendsto (fun j => ∫ x, G (P (ns j) x) * dk k φ x ∂μN n) atTop
      (𝓝 (∫ x, G (Φ x) * dk k φ x ∂μN n)) := by
    refine tendsto_integral_mul_of_L2 (f := fun j x => G (P (ns j) x))
      (fun j => memLp_cont (hGC1.continuous.comp (hPc _))) hGΦ (memLp_cont hdφ) ?_
    refine squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg _) (fun j => ?_)
      (by simpa using hL2s.const_mul (L ^ 2))
    rw [← integral_const_mul]
    have hint : Integrable (fun x => L ^ 2 * (Φ x - P (ns j) x) ^ 2) (μN n) := by
      have := ((hΦ.1.sub (memLp_cont (hPc (ns j)))).integrable_sq).const_mul (L ^ 2)
      simpa only [Pi.sub_apply] using this
    refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hint
      (ae_of_all _ fun x => ?_)
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (hLip (Φ x) (P (ns j) x)) 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    exact h2
  -- the right side, split in two
  obtain ⟨B, hB⟩ := ae_bound_cont hφ.1.continuous
  set g2 : Cfg n → ℝ := fun x => G' (Φ x) * φ x
  have hg2 : MemLp g2 2 (μN n) := by
    have := memLp_mul_cont hφ.1.continuous hG'Φ
    simpa only [g2, mul_comm] using this
  set D : ℕ → Cfg n → ℝ := fun j x => (G' (P (ns j) x) - G' (Φ x)) * φ x
  have hDm : ∀ j, MemLp (D j) 2 (μN n) := fun j => by
    have h1 : MemLp (fun x => G' (P (ns j) x) - G' (Φ x)) 2 (μN n) :=
      (memLp_cont (hG'c.comp (hPc _))).sub hG'Φ
    simpa only [D, mul_comm] using memLp_mul_cont hφ.1.continuous h1
  have hdP : ∀ j, MemLp (dk k (P (ns j))) 2 (μN n) := fun j =>
    memLp_cont (continuous_dk_of_C1 ((hP2 _).of_le (by norm_num)) k)
  have hsplit : ∀ j, ∫ x, G' (P (ns j) x) * dk k (P (ns j)) x * φ x ∂μN n =
      ∫ x, D j x * dk k (P (ns j)) x ∂μN n + ∫ x, g2 x * dk k (P (ns j)) x ∂μN n := fun j => by
    rw [← integral_add (int_mul_L2 (hDm j) (hdP j)) (int_mul_L2 hg2 (hdP j))]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [D, g2]; ring)
  have hDlim : Tendsto (fun j => ∫ x, D j x ^ 2 ∂μN n) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ x, (0 : ℝ) ∂μN n := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 * L * B) ^ 2)
      (fun j => ((hDm j).aestronglyMeasurable.pow 2)) (integrable_const _) (fun j => ?_) ?_
    · filter_upwards [hB] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 : |G' (P (ns j) x) - G' (Φ x)| ≤ 2 * L := by
        have := abs_sub (G' (P (ns j) x)) (G' (Φ x)); linarith [hL (P (ns j) x), hL (Φ x)]
      have h2 : |D j x| ≤ 2 * L * B := by
        simp only [D, abs_mul]
        rw [Real.norm_eq_abs] at hx
        exact mul_le_mul h1 hx (abs_nonneg _) (by positivity)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    · filter_upwards [hae] with x hx
      have h1 := ((hG'c.tendsto (Φ x)).comp hx).sub_const (G' (Φ x))
      have h2 := (h1.mul_const (φ x)).pow 2
      simpa [D] using h2
  have hT1 : Tendsto (fun j => ∫ x, D j x * dk k (P (ns j)) x ∂μN n) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero, Real.norm_eq_abs]
    refine squeeze_zero (fun j => abs_nonneg _) (fun j => ?_)
      (by simpa using (hDlim.sqrt).mul_const √(kinN Φ))
    refine (abs_integral_mul_le (hDm j) (hdP j)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
    exact norm_dk_truncC_sq_le hΦ k (ns j)
  have hT2 : Tendsto (fun j => ∫ x, g2 x * dk k (P (ns j)) x ∂μN n) atTop
      (𝓝 (∫ x, g2 x * dWN k Φ x ∂μN n)) :=
    (tendsto_truncC_dk hΦ k hg2).comp hns.tendsto_atTop
  have hrhs := hT1.add hT2
  rw [zero_add] at hrhs
  have heq : (fun j => ∫ x, G (P (ns j) x) * dk k φ x ∂μN n) =
      fun j => -(∫ x, D j x * dk k (P (ns j)) x ∂μN n +
        ∫ x, g2 x * dk k (P (ns j)) x ∂μN n) := funext fun j => by rw [hM, hsplit]
  rw [heq] at hlhs
  have := tendsto_nhds_unique hlhs hrhs.neg
  rw [this]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => by simp only [g2]; ring)

/-- **`|Φ|` has Neumann weak derivatives `rsgn(Φ) ∂ₖΦ`.** -/
theorem isWDN_abs (k : Fin (n + 1)) :
    IsWDN k (fun x => |Φ x|) (fun x => rsgn (Φ x) * dWN k Φ x) := by
  set ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε : ∀ j, 0 < ε j := fun j => by positivity
  have hW := dWN_spec (hΦ.2.1 k)
  have hcomp : ∀ j, IsWDN k (fun x => Geps (ε j) (Φ x))
      (fun x => Geps' (ε j) (Φ x) * dWN k Φ x) :=
    fun j => isWDN_comp hΦ (hasDerivAt_Geps (hε j)) (continuous_Geps' (hε j))
      (abs_Geps'_le (hε j)) (Geps_zero (hε j)) k
  have hlimD : ∀ x, Tendsto (fun j => Geps' (ε j) (Φ x) * dWN k Φ x) atTop
      (𝓝 (rsgn (Φ x) * dWN k Φ x)) := fun x => (tendsto_Geps' (Φ x)).mul_const _
  have hmeas : AEStronglyMeasurable (fun x => rsgn (Φ x) * dWN k Φ x) (μN n) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hcomp j).1.aestronglyMeasurable)
      (ae_of_all _ hlimD)
  refine ⟨hW.1.of_le_mul (c := 1) hmeas (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_rsgn_le _) (abs_nonneg _)), fun φ hφ => ?_⟩
  have hdφ := continuous_dk_of_C1 hφ.1 k
  have hlhs : Tendsto (fun j => ∫ x, Geps (ε j) (Φ x) * dk k φ x ∂μN n) atTop
      (𝓝 (∫ x, |Φ x| * dk k φ x ∂μN n)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |Φ x| * |dk k φ x|)
      (fun j => (((continuous_iff_continuousAt.2 fun t =>
        (hasDerivAt_Geps (hε j) t).continuousAt).comp_aestronglyMeasurable
        hΦ.1.aestronglyMeasurable).mul hdφ.aestronglyMeasurable)) ?_
      (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => (tendsto_Geps (Φ x)).mul_const _)
    · have := (int_mul_cont hΦ.1 hdφ).norm
      simpa [Real.norm_eq_abs, abs_mul] using this
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_Geps_le (hε j) _) (abs_nonneg _)
  have hrhs : Tendsto (fun j => ∫ x, Geps' (ε j) (Φ x) * dWN k Φ x * φ x ∂μN n) atTop
      (𝓝 (∫ x, rsgn (Φ x) * dWN k Φ x * φ x ∂μN n)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |dWN k Φ x| * |φ x|)
      (fun j => ((hcomp j).1.aestronglyMeasurable.mul hφ.1.continuous.aestronglyMeasurable)) ?_
      (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => (hlimD x).mul_const _)
    · have := (int_mul_cont hW.1 hφ.1.continuous).norm
      simpa [Real.norm_eq_abs, abs_mul] using this
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (abs_nonneg _) (abs_Geps'_le (hε j) _)) (abs_nonneg _)
  have heq : (fun j => ∫ x, Geps (ε j) (Φ x) * dk k φ x ∂μN n) =
      fun j => -∫ x, Geps' (ε j) (Φ x) * dWN k Φ x * φ x ∂μN n :=
    funext fun j => (hcomp j).2 φ hφ
  rw [heq] at hlhs
  exact tendsto_nhds_unique hlhs hrhs.neg

end truncC

/-- `|Φ|` is a bosonic Neumann state, for either statistics of `Φ`. -/
theorem abs_mem_DomN {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) : (fun x => |Φ x|) ∈ DomN .bos n :=
  ⟨hΦ.1.abs, fun k => ⟨_, isWDN_abs hΦ k⟩, fun σ _ => by
    filter_upwards [hΦ.2.2 σ trivial] with x hx
    rw [hx, abs_mul, abs_ch, ch_bos]⟩

/-- **Kato's inequality with Neumann walls**: `T(|Φ|) ≤ T(Φ)`. -/
theorem kinN_abs_le {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) : kinN (fun x => |Φ x|) ≤ kinN Φ := by
  refine Finset.sum_le_sum fun k _ => ?_
  have hd := dWN_ae_eq (isWDN_abs hΦ k)
  have hm := memLp_dWN (h1NW_of_mem hΦ) k
  have e : ∫ x, dWN k (fun x => |Φ x|) x * dWN k (fun x => |Φ x|) x ∂μN n =
      ∫ x, (rsgn (Φ x) * dWN k Φ x) * (rsgn (Φ x) * dWN k Φ x) ∂μN n :=
    integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx])
  rw [e]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => mul_self_nonneg _) (int_mul_L2 hm hm)
    (ae_of_all _ fun x => ?_)
  have h1 : rsgn (Φ x) * rsgn (Φ x) ≤ 1 := by
    have := abs_rsgn_le (Φ x)
    nlinarith [abs_mul_abs_self (rsgn (Φ x)), abs_nonneg (rsgn (Φ x))]
  have h2 := mul_self_nonneg (dWN k Φ x)
  calc rsgn (Φ x) * dWN k Φ x * (rsgn (Φ x) * dWN k Φ x) =
      (rsgn (Φ x) * rsgn (Φ x)) * (dWN k Φ x * dWN k Φ x) := by ring
    _ ≤ 1 * (dWN k Φ x * dWN k Φ x) := mul_le_mul_of_nonneg_right h1 h2
    _ = _ := one_mul _


/-- The trivial symmetry type: no constraint. -/
def symT1 (n : ℕ) : Sine.SymT n := ⟨fun σ => σ = 1, fun _ => 1⟩

/-- Every Neumann `H¹` function is a state of the trivial symmetry type. -/
lemma mem_symT1 {Φ : Cfg n → ℝ} (h : H1NW Φ) : Φ ∈ DomNS (symT1 n) :=
  ⟨h.1, h.2, fun σ hσ => by
    subst hσ
    exact ae_of_all _ fun x => by
      change Φ (pm 1 x) = 1 * Φ x
      rw [one_mul]; rfl⟩

/-- **The product rule** with a `C¹` function, Neumann walls. -/
lemma IsWDN.mul_C1 {k : Fin (n + 1)} {f G : Cfg n → ℝ} (h : IsWDN k f G)
    (hf : MemLp f 2 (μN n)) {ζ : Cfg n → ℝ} (hζ : ContDiff ℝ 1 ζ) :
    IsWDN k (fun x => ζ x * f x) (fun x => ζ x * G x + dk k ζ x * f x) := by
  have hdζ := continuous_dk_of_C1 hζ k
  refine ⟨(memLp_mul_cont hζ.continuous h.1).add (memLp_mul_cont hdζ hf), fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ.1 k
  have hζφ : TestN k (fun x => ζ x * φ x) :=
    ⟨hζ.mul hφ.1, fun x hx => by simp [hφ.2 x hx]⟩
  have h1 := h.2 _ hζφ
  have hprod : ∀ x, dk k (fun y => ζ y * φ y) x = ζ x * dk k φ x + dk k ζ x * φ x :=
    dk_mul (hζ.differentiable one_ne_zero) (hφ.1.differentiable one_ne_zero) k
  simp only [hprod] at h1
  have i1 : Integrable (fun x => f x * (ζ x * dk k φ x)) (μN n) :=
    int_mul_cont hf (hζ.continuous.mul hd)
  have i2 : Integrable (fun x => f x * (dk k ζ x * φ x)) (μN n) :=
    int_mul_cont hf (hdζ.mul hφ.1.continuous)
  have i3 : Integrable (fun x => G x * (ζ x * φ x)) (μN n) :=
    int_mul_cont h.1 hζφ.1.continuous
  have e1 : ∫ x, f x * (ζ x * dk k φ x + dk k ζ x * φ x) ∂μN n =
      ∫ x, f x * (ζ x * dk k φ x) ∂μN n + ∫ x, f x * (dk k ζ x * φ x) ∂μN n := by
    rw [← integral_add i1 i2]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e1] at h1
  have e2 : ∫ x, ζ x * f x * dk k φ x ∂μN n = ∫ x, f x * (ζ x * dk k φ x) ∂μN n :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  have e3 : ∫ x, (ζ x * G x + dk k ζ x * f x) * φ x ∂μN n =
      ∫ x, G x * (ζ x * φ x) ∂μN n + ∫ x, f x * (dk k ζ x * φ x) ∂μN n := by
    rw [← integral_add i3 i2]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e2, e3]
  linarith

/-- A Neumann `H¹` function times a `C¹` cutoff vanishing on the whole boundary is in `H¹₀`. -/
lemma IsWDN.mul_cutoff {k : Fin (n + 1)} {f G : Cfg n → ℝ} (h : IsWDN k f G)
    (hf : MemLp f 2 (μN n)) {ζ : Cfg n → ℝ} (hζ : ContDiff ℝ 1 ζ)
    (hζw : ∀ x j, (x j = 0 ∨ x j = 1) → ζ x = 0) :
    IsWD k (fun x => ζ x * f x) (fun x => ζ x * G x + dk k ζ x * f x) := by
  have hdζ := continuous_dk_of_C1 hζ k
  refine ⟨(memLp_mul_cont hζ.continuous h.1).add (memLp_mul_cont hdζ hf), fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ k
  have hζφ : TestN k (fun x => ζ x * φ x) :=
    ⟨hζ.mul hφ, fun x hx => by simp [hζw x k hx]⟩
  have h1 := h.2 _ hζφ
  have hprod : ∀ x, dk k (fun y => ζ y * φ y) x = ζ x * dk k φ x + dk k ζ x * φ x :=
    dk_mul (hζ.differentiable one_ne_zero) (hφ.differentiable one_ne_zero) k
  simp only [hprod] at h1
  have i1 : Integrable (fun x => f x * (ζ x * dk k φ x)) (μN n) :=
    int_mul_cont hf (hζ.continuous.mul hd)
  have i2 : Integrable (fun x => f x * (dk k ζ x * φ x)) (μN n) :=
    int_mul_cont hf (hdζ.mul hφ.continuous)
  have i3 : Integrable (fun x => G x * (ζ x * φ x)) (μN n) :=
    int_mul_cont h.1 hζφ.1.continuous
  have e1 : ∫ x, f x * (ζ x * dk k φ x + dk k ζ x * φ x) ∂μN n =
      ∫ x, f x * (ζ x * dk k φ x) ∂μN n + ∫ x, f x * (dk k ζ x * φ x) ∂μN n := by
    rw [← integral_add i1 i2]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e1] at h1
  have e2 : ∫ x, ζ x * f x * dk k φ x ∂μN n = ∫ x, f x * (ζ x * dk k φ x) ∂μN n :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  have e3 : ∫ x, (ζ x * G x + dk k ζ x * f x) * φ x ∂μN n =
      ∫ x, G x * (ζ x * φ x) ∂μN n + ∫ x, f x * (dk k ζ x * φ x) ∂μN n := by
    rw [← integral_add i3 i2]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e2, e3]
  linarith

end DFT.Continuum.Line
