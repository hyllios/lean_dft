/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.GroundState.WeakHK

/-!
# The `N`-particle state space with Neumann walls

`G` is the weak `k`-th derivative of `Φ` with Neumann walls (`IsWDN k Φ G`) if `G ∈ L²` and
`∫ Φ ∂ₖφ = -∫ G φ` for every `C¹` function `φ` vanishing on the faces `x_k ∈ {0, 1}` (`TestN k φ`).
This class of test functions contains `C_c^∞` of the open cube, and integration by parts in `x_k`
against it produces no boundary term, so `IsWDN` describes exactly `H¹` of the cube, with no
boundary condition. Compare `IsWD` (`Line/Weak`), which tests against all `C¹` functions and so
builds in the Dirichlet condition.

* `TestN`, `IsWDN`, `IsWDN.add`, `IsWDN.const_mul`, `IsWDN.sum`, `IsWDN.unique`.
* `IsWD.toN`: Dirichlet weak derivatives are Neumann weak derivatives.
* `isWDN_of_C1`: every `C¹` function has its classical derivatives as weak derivatives.
* `dWN`, `H1NW`, `DomNS s`, `DomN τ n`: the state space of symmetry type `s`; `kinN`, `h0NW`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ} {τ : Stat}

/-- Test functions for the `k`-th weak derivative with Neumann walls: `C¹`, vanishing on the faces
`x_k ∈ {0, 1}`. -/
def TestN (k : Fin (n + 1)) (φ : Cfg n → ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧ ∀ x : Cfg n, (x k = 0 ∨ x k = 1) → φ x = 0

/-- `G` is the weak `k`-th partial derivative of `Φ` on the cube (no boundary condition). -/
def IsWDN (k : Fin (n + 1)) (Φ G : Cfg n → ℝ) : Prop :=
  MemLp G 2 (μN n) ∧ ∀ φ : Cfg n → ℝ, TestN k φ →
    ∫ x, Φ x * dk k φ x ∂μN n = -∫ x, G x * φ x ∂μN n

/-- Dirichlet weak derivatives are Neumann weak derivatives. -/
lemma IsWD.toN {k : Fin (n + 1)} {Φ G : Cfg n → ℝ} (h : IsWD k Φ G) : IsWDN k Φ G :=
  ⟨h.1, fun φ hφ => h.2 φ hφ.1⟩

namespace IsWDN

variable {k : Fin (n + 1)} {Φ Ψ G H : Cfg n → ℝ}

lemma zero (k : Fin (n + 1)) : IsWDN k (0 : Cfg n → ℝ) 0 :=
  ⟨MemLp.zero, fun φ _ => by simp⟩

lemma add (hΦ : MemLp Φ 2 (μN n)) (hΨ : MemLp Ψ 2 (μN n)) (hG : IsWDN k Φ G)
    (hH : IsWDN k Ψ H) : IsWDN k (fun x => Φ x + Ψ x) (fun x => G x + H x) := by
  refine ⟨hG.1.add hH.1, fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ.1 k
  have e1 : ∫ x, (Φ x + Ψ x) * dk k φ x ∂μN n =
      ∫ x, Φ x * dk k φ x ∂μN n + ∫ x, Ψ x * dk k φ x ∂μN n := by
    rw [← integral_add (int_mul_cont hΦ hd) (int_mul_cont hΨ hd)]
    congr 1; funext x; ring
  have e2 : ∫ x, (G x + H x) * φ x ∂μN n = ∫ x, G x * φ x ∂μN n + ∫ x, H x * φ x ∂μN n := by
    rw [← integral_add (int_mul_cont hG.1 hφ.1.continuous) (int_mul_cont hH.1 hφ.1.continuous)]
    congr 1; funext x; ring
  rw [e1, e2, hG.2 φ hφ, hH.2 φ hφ]; ring

lemma const_mul (c : ℝ) (hG : IsWDN k Φ G) :
    IsWDN k (fun x => c * Φ x) (fun x => c * G x) := by
  refine ⟨hG.1.const_mul c, fun φ hφ => ?_⟩
  have e1 : ∫ x, c * Φ x * dk k φ x ∂μN n = c * ∫ x, Φ x * dk k φ x ∂μN n := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have e2 : ∫ x, c * G x * φ x ∂μN n = c * ∫ x, G x * φ x ∂μN n := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [e1, e2, hG.2 φ hφ]; ring

lemma sum {ι : Type*} (s : Finset ι) {Φs Gs : ι → Cfg n → ℝ}
    (hΦ : ∀ i ∈ s, MemLp (Φs i) 2 (μN n)) (hG : ∀ i ∈ s, IsWDN k (Φs i) (Gs i)) :
    MemLp (fun x => ∑ i ∈ s, Φs i x) 2 (μN n) ∧
      IsWDN k (fun x => ∑ i ∈ s, Φs i x) (fun x => ∑ i ∈ s, Gs i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨by exact MemLp.zero, by exact MemLp.zero, fun φ _ => by simp⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have ih' := ih (fun i hi => hΦ i (Finset.mem_insert_of_mem hi))
      (fun i hi => hG i (Finset.mem_insert_of_mem hi))
    have h1 := hΦ a (Finset.mem_insert_self a s)
    exact ⟨by exact h1.add ih'.1, add h1 ih'.1 (hG a (Finset.mem_insert_self a s)) ih'.2⟩

/-- Compactly supported test functions in the open cube are admissible. -/
lemma testN_of_tsupport {g : Cfg n → ℝ} (hg : ContDiff ℝ 1 g) (hs : tsupport g ⊆ Cube n)
    (k : Fin (n + 1)) : TestN k g := by
  refine ⟨hg, fun x hx => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := (hs h) k (mem_univ k)
  rcases hx with h0 | h1
  · rw [h0] at this; exact lt_irrefl _ this.1
  · rw [h1] at this; exact lt_irrefl _ this.2

/-- **Uniqueness of weak derivatives** (a.e. on the cube). -/
lemma unique (hG : IsWDN k Φ G) (hH : IsWDN k Φ H) : G =ᵐ[μN n] H := by
  have hint : Integrable (fun x => G x - H x) (μN n) :=
    (hG.1.integrable one_le_two).sub (hH.1.integrable one_le_two)
  have h0 : ∀ φ : Cfg n → ℝ, TestN k φ → ∫ x, φ x * (G x - H x) ∂μN n = 0 := by
    intro φ hφ
    have a := hG.2 φ hφ
    have b := hH.2 φ hφ
    have e : ∫ x, φ x * (G x - H x) ∂μN n = ∫ x, G x * φ x ∂μN n - ∫ x, H x * φ x ∂μN n := by
      rw [← integral_sub (int_mul_cont hG.1 hφ.1.continuous) (int_mul_cont hH.1 hφ.1.continuous)]
      congr 1; funext x; ring
    rw [e]; linarith
  have h := isOpen_cube.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (f := fun x => G x - H x)
    ((show IntegrableOn (fun x => G x - H x) (Cube n) volume from hint).locallyIntegrableOn)
    (fun g hg _ hsupp => by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Cube n) fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h), zero_smul]]
      exact h0 g (testN_of_tsupport (hg.of_le (by exact_mod_cast le_top)) hsupp k))
  filter_upwards [(ae_restrict_iff' measurableSet_cube).2 h] with x hx
  exact sub_eq_zero.1 hx

end IsWDN

/-- Integration by parts: every `C¹` function has its classical derivatives as Neumann weak
derivatives. -/
lemma isWDN_of_C1 {Φ : Cfg n → ℝ} (hC1 : ContDiff ℝ 1 Φ) (k : Fin (n + 1)) :
    IsWDN k Φ (dk k Φ) := by
  have hdc : Continuous (dk k Φ) := continuous_dk_of_C1 hC1 k
  refine ⟨memLp_cont hdc, fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ.1 k
  have hφd : Differentiable ℝ φ := hφ.1.differentiable one_ne_zero
  rw [integral_cube_ins (F := fun x => Φ x * dk k φ x) k (integrableN (hC1.continuous.mul hd)),
    integral_cube_ins (F := fun x => dk k Φ x * φ x) k (integrableN (hdc.mul hφ.1.continuous)),
    ← integral_neg]
  refine setIntegral_congr_fun measurableSet_cube' fun y _ => ?_
  simp only [integral_Ioo_eq_interval]
  have hc : ∀ {g : Cfg n → ℝ}, Continuous g →
      IntervalIntegrable (fun t => g (Fin.insertNth k t y)) volume 0 1 := fun hg =>
    (hg.comp (continuous_ins k y)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t => Φ (Fin.insertNth k t y)) (v := fun t => φ (Fin.insertNth k t y))
    (fun t _ => hasDerivAt_ins (hC1.differentiable one_ne_zero) k y t)
    (fun t _ => hasDerivAt_ins hφd k y t) (hc hdc) (hc hd)]
  have w0 : φ (Fin.insertNth k 0 y) = 0 := hφ.2 _ (Or.inl (by simp))
  have w1 : φ (Fin.insertNth k 1 y) = 0 := hφ.2 _ (Or.inr (by simp))
  rw [w0, w1]; ring

/-- The Neumann weak derivative (a chosen representative; `0` if there is none). -/
noncomputable def dWN (k : Fin (n + 1)) (Φ : Cfg n → ℝ) : Cfg n → ℝ :=
  open Classical in if h : ∃ G, IsWDN k Φ G then h.choose else 0

lemma dWN_spec {k : Fin (n + 1)} {Φ : Cfg n → ℝ} (h : ∃ G, IsWDN k Φ G) :
    IsWDN k Φ (dWN k Φ) := by
  unfold dWN
  split_ifs
  exact h.choose_spec

lemma dWN_ae_eq {k : Fin (n + 1)} {Φ G : Cfg n → ℝ} (h : IsWDN k Φ G) : dWN k Φ =ᵐ[μN n] G :=
  (dWN_spec ⟨G, h⟩).unique h

/-- `H¹` of the cube: `L²` functions with all weak first derivatives. -/
def H1NW (Φ : Cfg n → ℝ) : Prop := MemLp Φ 2 (μN n) ∧ ∀ k, ∃ G, IsWDN k Φ G

/-- `H¹` states of symmetry type `s` with Neumann walls. -/
def DomNS (s : Sine.SymT n) : Submodule ℝ (Cfg n → ℝ) where
  carrier := {Φ | MemLp Φ 2 (μN n) ∧ (∀ k, ∃ G, IsWDN k Φ G) ∧
    ∀ σ, s.G σ → ∀ᵐ x ∂μN n, Φ (pm σ x) = s.χ σ * Φ x}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun k => by
      obtain ⟨G, hG⟩ := ha.2.1 k
      obtain ⟨H, hH⟩ := hb.2.1 k
      exact ⟨_, IsWDN.add ha.1 hb.1 hG hH⟩,
    fun σ hσ => by
      filter_upwards [ha.2.2 σ hσ, hb.2.2 σ hσ] with x h1 h2
      simp only [Pi.add_apply, h1, h2]; ring⟩
  zero_mem' := ⟨MemLp.zero, fun k => ⟨0, IsWDN.zero k⟩, fun σ _ => ae_of_all _ fun x => by simp⟩
  smul_mem' c a ha := ⟨ha.1.const_smul c, fun k => by
      obtain ⟨G, hG⟩ := ha.2.1 k
      exact ⟨_, IsWDN.const_mul c hG⟩,
    fun σ hσ => by
      filter_upwards [ha.2.2 σ hσ] with x h1
      simp only [Pi.smul_apply, smul_eq_mul, h1]; ring⟩

/-- `H¹` states of exchange symmetry `τ` with Neumann walls. -/
noncomputable abbrev DomN (τ : Stat) (n : ℕ) : Submodule ℝ (Cfg n → ℝ) := DomNS (n := n) τ.toSym

lemma h1NW_of_mem {s : Sine.SymT n} {Φ : Cfg n → ℝ} (h : Φ ∈ DomNS s) : H1NW Φ := ⟨h.1, h.2.1⟩

/-- Dirichlet states are Neumann states. -/
lemma DomWS_le_DomNS (s : Sine.SymT n) : DomWS s ≤ DomNS s := fun _ h =>
  ⟨h.1, fun k => by obtain ⟨G, hG⟩ := h.2.1 k; exact ⟨G, hG.toN⟩, h.2.2⟩

lemma memLp_dWN {Φ : Cfg n → ℝ} (hΦ : H1NW Φ) (k : Fin (n + 1)) : MemLp (dWN k Φ) 2 (μN n) :=
  (dWN_spec (hΦ.2 k)).1

/-- The kinetic energy `Σ_k ∫ |∂ₖΦ|²` with Neumann walls. -/
noncomputable def kinN (Φ : Cfg n → ℝ) : ℝ := ∑ k, ∫ x, dWN k Φ x * dWN k Φ x ∂μN n

lemma kinN_nonneg (Φ : Cfg n → ℝ) : 0 ≤ kinN Φ :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => mul_self_nonneg _

/-- On Dirichlet states the two kinetic energies agree. -/
lemma kinN_eq_kinW {s : Sine.SymT n} {Φ : Cfg n → ℝ} (h : Φ ∈ DomWS s) : kinN Φ = kinW Φ := by
  simp only [kinN, kinW]
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  filter_upwards [dWN_ae_eq (dW_spec (h.2.1 k)).toN] with x hx
  rw [hx]

end DFT.Continuum.Line
