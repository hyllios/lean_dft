/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Exists

/-!
# Concrete potentials and interactions in the cosine class

`CosClass V`: on the closed cube, `V = Σ_l β_l Π_j cos(π l_j x_j)` with
`Σ_l |β_l| (1 + |l|)^s < ∞` for every `s` (the hypothesis of `Sine/Exists`). The class is closed
under sums and contains:

* one-body terms `v(x_k)` with `v(t) = Σ_l a_l cos(π l t)` on `[0, 1]`, `Σ |a_l| (1 + l)^s < ∞`;
* mirror-image pair terms `u(x_i - x_j) + u(x_i + x_j)` with `u(d) = Σ_l b_l cos(π l d)`,
  `Σ |b_l| (1 + l)^s < ∞` (the interaction of particle `i` with particle `j` and with its mirror
  images in the walls).

* `CosClass.of_family`: a family `Σ_i γ_i cosM (L i)` indexed by any type is in the class.
* `pairW`: the mirror-image interaction `Σ_{i<j} [u(x_i - x_j) + u(x_i + x_j)]`.
* `hk_line_mirror`, `lieb_line_mirror`: **unconditional Hohenberg–Kohn and Lieb** for `n + 1`
  bosons or fermions on `[0, 1]` with such `v` and `u`.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real
open scoped ENNReal

variable {n : ℕ}

/-- The cosine class: rapidly converging cosine series on the closed cube. -/
def CosClass (V : Cfg n → ℝ) : Prop :=
  ∃ β : (Fin (n + 1) → ℕ) → ℝ, (∀ s : ℕ, Summable fun l => |β l| * (1 + (sz l : ℝ)) ^ s) ∧
    ∀ x ∈ CubeC n, V x = ∑' l, β l * cosM l x

lemma summable_cos_mul {β : (Fin (n + 1) → ℕ) → ℝ}
    (hβ : ∀ s : ℕ, Summable fun l => |β l| * (1 + (sz l : ℝ)) ^ s) (x : Cfg n) :
    Summable fun l => β l * cosM l x :=
  Summable.of_norm_bounded (by simpa using hβ 0) fun l => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cosM_le l x)

lemma CosClass.zero : CosClass (fun _ : Cfg n => (0 : ℝ)) :=
  ⟨fun _ => 0, fun s => by simp [summable_zero], fun x _ => by simp⟩

lemma CosClass.add {V V' : Cfg n → ℝ} (h : CosClass V) (h' : CosClass V') :
    CosClass fun x => V x + V' x := by
  obtain ⟨β, hβ, hV⟩ := h
  obtain ⟨β', hβ', hV'⟩ := h'
  refine ⟨fun l => β l + β' l, fun s => ?_, fun x hx => ?_⟩
  · refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) ((hβ s).add (hβ' s))
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)
  · simp only
    rw [hV x hx, hV' x hx, ← (summable_cos_mul hβ x).tsum_add (summable_cos_mul hβ' x)]
    exact tsum_congr fun l => by ring

lemma CosClass.sum {ι : Type*} (s : Finset ι) {V : ι → Cfg n → ℝ} (h : ∀ i ∈ s, CosClass (V i)) :
    CosClass fun x => ∑ i ∈ s, V i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CosClass.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma CosClass.smul {V : Cfg n → ℝ} (h : CosClass V) (c : ℝ) : CosClass fun x => c * V x := by
  obtain ⟨β, hβ, hV⟩ := h
  refine ⟨fun l => c * β l, fun s => ?_, fun x hx => ?_⟩
  · simpa [abs_mul, mul_assoc] using (hβ s).mul_left |c|
  · simp only
    rw [hV x hx, ← tsum_mul_left]; exact tsum_congr fun l => by ring

/-- **A family `Σ_i γ_i cosM (L i)` over any index type is in the class** (group the terms by
their multi-index). -/
theorem CosClass.of_family {ι : Type*} (γ : ι → ℝ) (L : ι → Fin (n + 1) → ℕ)
    (hγ : ∀ s : ℕ, Summable fun i => |γ i| * (1 + (sz (L i) : ℝ)) ^ s) {V : Cfg n → ℝ}
    (hV : ∀ x ∈ CubeC n, V x = ∑' i, γ i * cosM (L i) x) : CosClass V := by
  refine ⟨fun l => ∑' i : L ⁻¹' {l}, γ i, fun s => ?_, fun x hx => ?_⟩
  · have hF := ((hγ s).hasSum).tsum_fiberwise L
    refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) hF.summable
    have hsub : Summable fun i : L ⁻¹' {l} => |γ i| :=
      (by simpa using hγ 0 : Summable fun i => |γ i|).comp_injective Subtype.val_injective
    calc |∑' i : L ⁻¹' {l}, γ i| * (1 + (sz l : ℝ)) ^ s
        ≤ (∑' i : L ⁻¹' {l}, |γ i|) * (1 + (sz l : ℝ)) ^ s := by
          gcongr
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun i : L ⁻¹' {l} => γ i)
            (by simpa [Real.norm_eq_abs] using hsub)
      _ = ∑' i : L ⁻¹' {l}, |γ ↑i| * (1 + (sz (L i) : ℝ)) ^ s := by
          rw [← tsum_mul_right]
          refine tsum_congr fun i => ?_
          rw [show L i = l from i.2]
  · have hs : Summable fun i => γ i * cosM (L i) x :=
      Summable.of_norm_bounded (by simpa using hγ 0) fun i => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_cosM_le _ x)
    have hF := hs.hasSum.tsum_fiberwise L
    rw [hV x hx, ← hF.tsum_eq]
    refine tsum_congr fun l => ?_
    rw [← tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [show L i = l from i.2]

/-! ### One-body terms and mirror-image pairs -/

lemma sz_single (k : Fin (n + 1)) (l : ℕ) : sz (Pi.single k l : Fin (n + 1) → ℕ) = l := by
  classical
  simp [sz, Finset.sum_pi_single']

lemma cosM_single (k : Fin (n + 1)) (l : ℕ) (x : Cfg n) :
    cosM (Pi.single k l : Fin (n + 1) → ℕ) x = Real.cos (π * l * x k) := by
  classical
  rw [cosM, Finset.prod_eq_single k (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_univ k) h)]
  simp

lemma sz_pair (i j : Fin (n + 1)) (l : ℕ) :
    sz (Pi.single i l + Pi.single j l : Fin (n + 1) → ℕ) = 2 * l := by
  classical
  simp only [sz, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true]
  ring

lemma cosM_pair {i j : Fin (n + 1)} (hij : i ≠ j) (l : ℕ) (x : Cfg n) :
    cosM (Pi.single i l + Pi.single j l : Fin (n + 1) → ℕ) x =
      Real.cos (π * l * x i) * Real.cos (π * l * x j) := by
  classical
  rw [cosM, Finset.prod_eq_mul i j hij
    (fun c _ hc => by simp [hc.1, hc.2])
    (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)]
  simp [hij, hij.symm]

/-- A one-body term `v(x_k)` with a rapidly converging cosine series. -/
lemma CosClass.one_body {a : ℕ → ℝ} (ha : ∀ s : ℕ, Summable fun l => |a l| * (1 + (l : ℝ)) ^ s)
    {v : Pot} (hv : ∀ t : Icc (0 : ℝ) 1, v t = ∑' l, a l * Real.cos (π * l * t))
    (k : Fin (n + 1)) : CosClass fun x : Cfg n => Box.ext v (x k) := by
  refine CosClass.of_family a (fun l => Pi.single k l) (fun s => by simpa [sz_single] using ha s)
    fun x hx => ?_
  have hk : x k ∈ Icc (0 : ℝ) 1 := hx k (Set.mem_univ k)
  rw [Box.ext, Set.projIcc_of_mem _ hk, hv]
  exact tsum_congr fun l => by rw [cosM_single]

/-- The one-body potential `Σ_k v(x_k)`. -/
lemma CosClass.LN {a : ℕ → ℝ} (ha : ∀ s : ℕ, Summable fun l => |a l| * (1 + (l : ℝ)) ^ s)
    {v : Pot} (hv : ∀ t : Icc (0 : ℝ) 1, v t = ∑' l, a l * Real.cos (π * l * t)) :
    CosClass fun x : Cfg n => LN n v x :=
  CosClass.sum Finset.univ fun k _ => CosClass.one_body ha hv k

/-- A mirror-image pair term `u(x_i - x_j) + u(x_i + x_j)`, `i ≠ j`. -/
lemma CosClass.pair {b : ℕ → ℝ} (hb : ∀ s : ℕ, Summable fun l => |b l| * (1 + (l : ℝ)) ^ s)
    {u : ℝ → ℝ} (hu : ∀ d, u d = ∑' l, b l * Real.cos (π * l * d)) {i j : Fin (n + 1)}
    (hij : i ≠ j) : CosClass fun x : Cfg n => u (x i - x j) + u (x i + x j) := by
  refine CosClass.of_family (fun l => 2 * b l) (fun l => Pi.single i l + Pi.single j l)
    (fun s => ?_) fun x _ => ?_
  · refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_)
      ((hb s).mul_left (2 * 2 ^ s))
    rw [sz_pair, abs_mul, abs_two]
    have h1 : (1 + ((2 * l : ℕ) : ℝ)) ^ s ≤ 2 ^ s * (1 + (l : ℝ)) ^ s := by
      rw [← mul_pow]; gcongr; push_cast; linarith
    calc 2 * |b l| * (1 + ((2 * l : ℕ) : ℝ)) ^ s ≤ 2 * |b l| * (2 ^ s * (1 + (l : ℝ)) ^ s) := by
          gcongr
      _ = _ := by ring
  · have hs : ∀ d, Summable fun l => b l * Real.cos (π * l * d) := fun d =>
      Summable.of_norm_bounded (by simpa using hb 0) fun l => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
    rw [hu, hu, ← (hs _).tsum_add (hs _)]
    refine tsum_congr fun l => ?_
    rw [cosM_pair hij]
    have e1 : π * l * (x i - x j) = π * l * x i - π * l * x j := by ring
    have e2 : π * l * (x i + x j) = π * l * x i + π * l * x j := by ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]; ring

/-- **The mirror-image interaction** `W(x) = ½ Σ_{i ≠ j} [u(x_i - x_j) + u(x_i + x_j)]`:
particle `i` interacts with particle `j` and with the mirror images of `j` in the walls. For even
`u` it is `Σ_{i<j} [u(x_i - x_j) + u(x_i + x_j)]`. -/
noncomputable def pairW (u : ℝ → ℝ) (x : Cfg n) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else 1 / 2 * (u (x i - x j) + u (x i + x j))

lemma CosClass.pairW {b : ℕ → ℝ} (hb : ∀ s : ℕ, Summable fun l => |b l| * (1 + (l : ℝ)) ^ s)
    {u : ℝ → ℝ} (hu : ∀ d, u d = ∑' l, b l * Real.cos (π * l * d)) :
    CosClass (pairW (n := n) u) :=
  CosClass.sum Finset.univ fun i _ => CosClass.sum Finset.univ fun j _ => by
    split_ifs with hij
    · exact CosClass.zero
    · exact (CosClass.pair hb hu hij).smul _

lemma continuous_of_cos {b : ℕ → ℝ} (hb : ∀ s : ℕ, Summable fun l => |b l| * (1 + (l : ℝ)) ^ s)
    {u : ℝ → ℝ} (hu : ∀ d, u d = ∑' l, b l * Real.cos (π * l * d)) : Continuous u := by
  rw [show u = fun d => ∑' l, b l * Real.cos (π * l * d) from funext hu]
  refine continuous_tsum (fun l => by fun_prop) (by simpa using hb 0) fun l d => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

lemma continuous_pairW {u : ℝ → ℝ} (hu : Continuous u) : Continuous (pairW (n := n) u) := by
  unfold pairW
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · exact continuous_const
  · fun_prop

lemma pairW_pm (u : ℝ → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    pairW u (pm σ x) = pairW u x := by
  set H : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => if i = j then 0 else 1 / 2 * (u (x i - x j) + u (x i + x j))
  calc pairW u (pm σ x) = ∑ i, ∑ j, H (σ i) (σ j) := by
        simp only [pairW, pm, H, σ.injective.eq_iff]
    _ = ∑ i, ∑ j, H (σ i) j := Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (H (σ i))
    _ = pairW u x := Equiv.sum_comp σ fun i => ∑ j, H i j

/-! ### Unconditional theorems -/

section mirror

variable {a b : ℕ → ℝ} (ha : ∀ s : ℕ, Summable fun l => |a l| * (1 + (l : ℝ)) ^ s)
  {v : Pot} (hv : ∀ t : Icc (0 : ℝ) 1, v t = ∑' l, a l * Real.cos (π * l * t))
  (hb : ∀ s : ℕ, Summable fun l => |b l| * (1 + (l : ℝ)) ^ s)
  {u : ℝ → ℝ} (hu : ∀ d, u d = ∑' l, b l * Real.cos (π * l * d))
include ha hv hb hu

/-- **Hohenberg–Kohn for `N` interacting bosons or fermions on `[0, 1]` with a mirror-image pair
interaction, unconditional.** `v(t) = Σ_l a_l cos(π l t)` and `u(d) = Σ_l b_l cos(π l d)` with
rapidly decaying coefficients. The ground state of `v` exists, and ground states of `v` and of any
continuous `v'` with the same one-body density force `v - v'` to be constant. -/
theorem hk_line_mirror {τ : Stat} (v' : Pot) :
    (∃ Φ, IsGS (setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))) v Φ) ∧
      ∀ Φ Φ', IsGS (setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))) v Φ →
        IsGS (setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))) v' Φ' →
        (∀ t ∈ Ioo (0 : ℝ) 1, ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 =
          ∫ y in Cube' n, Φ' (Fin.cons t y) ^ 2) → ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨β, hβ, hV⟩ := (CosClass.LN (n := n) ha hv).add (CosClass.pairW hb hu)
  exact hk_line_sine (pairW_pm u) hβ hV v'

/-- **The Lieb functional for `N` interacting bosons or fermions on `[0, 1]` with a mirror-image
pair interaction, unconditional**: a normalised ground state `ψ` of `v` exists; at its density the
Lieb functional equals `⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient, and every other subgradient `-v'`
has `v - v'` constant. -/
theorem lieb_line_mirror {τ : Stat} :
    ∃ ψ, IsNGS (setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))) v ψ ∧
      liebF (setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu)))
          (dens (setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))) ψ) =
        (((setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))).h0 ψ ψ : ℝ) :
          EReal) ∧
      (∀ ρ : Pot → ℝ,
        (((setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))).h0 ψ ψ +
          dens (setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))) ψ v -
            ρ v : ℝ) : EReal) ≤
          liebF (setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ,
        (((setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))).h0 ψ ψ +
          dens (setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))) ψ v' -
            ρ v' : ℝ) : EReal) ≤
          liebF (setting τ n (pairW u) (continuous_pairW (continuous_of_cos hb hu))) ρ) →
        ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨β, hβ, hV⟩ := (CosClass.LN (n := n) ha hv).add (CosClass.pairW hb hu)
  exact lieb_line_sine (pairW_pm u) hβ hV

end mirror

end DFT.Continuum.Sine
