/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.MeasureHKgen
import DFT.Continuum.Line.Neumann.NeuEL

/-!
# Estimates for the Hohenberg–Kohn theorem with Neumann walls

* `tendsto_kinN_sub_truncC`: the cosine truncations converge in `H¹`.
* `kinN_mul_le`: the kinetic energy of a product with a `C¹` function.
* `SHN X = N ∫ X² + T(X)`; `norm_rhoE_le`: `‖ρ_X‖_{H¹} ≤ 4 SHN(X)`;
  **`norm_rhoE2_le`**: `‖ρ(A, B)‖_{H¹} ≤ 8 √(SHN(A) SHN(B))`, from bilinearity of the mixed
  density (`rhoE2_add_left`, `rhoE2_smul_left`, ...).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology Sine

variable {n : ℕ} {τ : Stat}

/-! ### Convergence of the cosine truncations in `H¹` -/

lemma kinN_congr {Φ Ψ : Cfg n → ℝ} (hΦ : H1NW Φ) (h : Φ =ᵐ[μN n] Ψ) : kinN Φ = kinN Ψ := by
  simp only [kinN]
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  have h1 := dWN_spec (hΦ.2 k)
  have h2 := dWN_ae_eq (h1.congr_ae h)
  filter_upwards [h2] with x hx; rw [hx]

lemma truncC_memN {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) (M : ℕ) : truncC M Φ ∈ DomN τ n :=
  ⟨memLp_cont (continuous_truncC M Φ),
    fun k => ⟨_, isWDN_of_C1 ((contDiff_truncC M Φ).of_le (by norm_num)) k⟩,
    fun σ _ => ae_of_all _ fun x => (truncC_mem hΦ M).2 σ x⟩

theorem kinN_eq_tsum {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) :
    kinN Φ = ∑' m, lamC m * cC m Φ ^ 2 := by
  have hD := dirN_cC hΦ
  have hae : Φ =ᵐ[μN n] serN fun m => cC m Φ :=
    ae_eq_of_cC_eq hΦ.1 memLp_serN fun m => (cC_serN hD.sq m).symm
  rw [kinN_congr (h1NW_of_mem hΦ) hae, kinN_serN hD]

/-- **The cosine truncations converge in `H¹`.** -/
theorem tendsto_kinN_sub_truncC {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) :
    Tendsto (fun M => kinN (Φ - truncC M Φ)) atTop (𝓝 0) := by
  have hD : ∀ M, Φ - truncC M Φ ∈ DomN τ n := fun M => sub_mem hΦ (truncC_memN hΦ M)
  have hc : ∀ M m, cC m (Φ - truncC M Φ) = if m ∈ boxI n M then 0 else cC m Φ := fun M m => by
    rw [cC_sub hΦ.1 (truncC_memN hΦ M).1, cC_truncC]
    split_ifs <;> ring
  have hk := (dirN_cC hΦ).kin
  have e : ∀ M, kinN (Φ - truncC M Φ) =
      ∑' m, lamC m * cC m Φ ^ 2 - ∑ m ∈ boxI n M, lamC m * cC m Φ ^ 2 := fun M => by
    rw [kinN_eq_tsum (hD M)]
    simp only [hc]
    have hfin : Summable fun m => if m ∈ boxI n M then lamC m * cC m Φ ^ 2 else 0 :=
      summable_of_ne_finset_zero (s := boxI n M) fun m hm => by simp [hm]
    have htsum : ∑' m, (if m ∈ boxI n M then lamC m * cC m Φ ^ 2 else 0) =
        ∑ m ∈ boxI n M, lamC m * cC m Φ ^ 2 := by
      rw [tsum_eq_sum (s := boxI n M) fun m hm => by simp [hm]]
      exact Finset.sum_congr rfl fun m hm => by simp [hm]
    have h1 : (fun m => lamC m * (if m ∈ boxI n M then 0 else cC m Φ) ^ 2) =
        fun m => lamC m * cC m Φ ^ 2 - if m ∈ boxI n M then lamC m * cC m Φ ^ 2 else 0 := by
      funext m; split_ifs <;> simp
    rw [h1, hk.tsum_sub hfin, htsum]
  simp only [e]
  have h := hk.hasSum.comp tendsto_boxI
  have := (tendsto_const_nhds (x := ∑' m, lamC m * cC m Φ ^ 2)).sub h
  rwa [sub_self] at this

theorem tendsto_sq_sub_truncC {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) :
    Tendsto (fun M => ∫ x, (Φ - truncC M Φ) x ^ 2 ∂μN n) atTop (𝓝 0) :=
  tendsto_truncC hΦ.1

/-! ### Products with `C¹` functions -/

/-- The kinetic energy of a product with a `C¹` function. -/
theorem kinN_mul_le {Y : Cfg n → ℝ} (hY : H1NW Y) {ζ : Cfg n → ℝ} (hζ : ContDiff ℝ 1 ζ)
    {Z Z' : ℝ} (hZ : ∀ x, |ζ x| ≤ Z) (hZ' : ∀ k x, |dk k ζ x| ≤ Z') :
    kinN (fun x => ζ x * Y x) ≤ 2 * Z ^ 2 * kinN Y + 2 * (n + 1) * Z' ^ 2 * ∫ x, Y x ^ 2 ∂μN n := by
  have hk : ∀ k, ∫ x, dWN k (fun x => ζ x * Y x) x * dWN k (fun x => ζ x * Y x) x ∂μN n ≤
      2 * Z ^ 2 * ∫ x, dWN k Y x * dWN k Y x ∂μN n + 2 * Z' ^ 2 * ∫ x, Y x ^ 2 ∂μN n :=
    fun k => by
    have hW := (dWN_spec (hY.2 k)).mul_C1 hY.1 hζ
    have hd := dWN_ae_eq hW
    have hmG := (dWN_spec (hY.2 k)).1
    have i1 : Integrable (fun x => dWN k Y x * dWN k Y x) (μN n) := int_mul_L2 hmG hmG
    have i2 : Integrable (fun x => Y x ^ 2) (μN n) := int_sq hY.1
    have i0 : Integrable (fun x => (ζ x * dWN k Y x + dk k ζ x * Y x) *
        (ζ x * dWN k Y x + dk k ζ x * Y x)) (μN n) := int_mul_L2 hW.1 hW.1
    rw [integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx]),
      ← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _) (i2.const_mul _)]
    refine integral_mono i0 ((i1.const_mul _).add (i2.const_mul _)) fun x => ?_
    have h1 : (ζ x) ^ 2 ≤ Z ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hZ x) 2
    have h2 : (dk k ζ x) ^ 2 ≤ Z' ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hZ' k x) 2
    nlinarith [sq_nonneg (ζ x * dWN k Y x - dk k ζ x * Y x), mul_le_mul_of_nonneg_right h1
      (mul_self_nonneg (dWN k Y x)), mul_le_mul_of_nonneg_right h2 (sq_nonneg (Y x))]
  calc kinN (fun x => ζ x * Y x)
      ≤ ∑ k : Fin (n + 1), (2 * Z ^ 2 * ∫ x, dWN k Y x * dWN k Y x ∂μN n +
          2 * Z' ^ 2 * ∫ x, Y x ^ 2 ∂μN n) := Finset.sum_le_sum fun k _ => hk k
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, kinN]
        push_cast; ring

/-! ### The `H¹` size of states and the size of densities -/

/-- `SHN X = N ∫ X² + T(X)`. -/
noncomputable def SHN (X : Cfg n → ℝ) : ℝ := (n + 1) * ∫ x, X x ^ 2 ∂μN n + kinN X

lemma SHN_nonneg (X : Cfg n → ℝ) : 0 ≤ SHN X := by
  unfold SHN
  have := kinN_nonneg X
  have : 0 ≤ ∫ x, X x ^ 2 ∂μN n := integral_nonneg fun _ => sq_nonneg _
  positivity

lemma SHN_smul {X : Cfg n → ℝ} (hX : H1NW X) (c : ℝ) : SHN (c • X) = c ^ 2 * SHN X := by
  simp only [SHN, Pi.smul_apply, smul_eq_mul, mul_pow, integral_const_mul]
  rw [kinN_smul hX]; ring

lemma kinN_add_le {X Y : Cfg n → ℝ} (hX : H1NW X) (hY : H1NW Y) :
    kinN (X + Y) ≤ 2 * kinN X + 2 * kinN Y := by
  have h1 := kinN_expand hX hY 1
  have h2 := kinN_expand hX hY (-1)
  have h3 := kinN_nonneg (X + (-1 : ℝ) • Y)
  rw [one_smul] at h1
  rw [h1]
  nlinarith

lemma sq_int_add_le {X Y : Cfg n → ℝ} (hX : MemLp X 2 (μN n)) (hY : MemLp Y 2 (μN n)) :
    ∫ x, (X + Y) x ^ 2 ∂μN n ≤ 2 * ∫ x, X x ^ 2 ∂μN n + 2 * ∫ x, Y x ^ 2 ∂μN n := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((int_sq hX).const_mul _)
    ((int_sq hY).const_mul _)]
  exact integral_mono (int_sq (hX.add hY)) (((int_sq hX).const_mul _).add ((int_sq hY).const_mul _))
    fun x => by simp only [Pi.add_apply]; nlinarith [sq_nonneg (X x - Y x)]

lemma SHN_add_le {X Y : Cfg n → ℝ} (hX : H1NW X) (hY : H1NW Y) :
    SHN (X + Y) ≤ 2 * SHN X + 2 * SHN Y := by
  unfold SHN
  have h1 := kinN_add_le hX hY
  have h2 := sq_int_add_le hX.1 hY.1
  have hN : (0 : ℝ) ≤ n + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hN]

/-- `‖ρ_X‖_{H¹} ≤ 4 SHN(X)`. -/
theorem norm_rhoE_le {X : Cfg n → ℝ} (hX : X ∈ DomN τ n) : ‖rhoE τ X‖ ≤ 4 * SHN X := by
  set g := gNH τ X
  have hg := h1N_gNH (τ := τ) X
  have hint := integral_gNH_sq hX
  have hk := kinM_gNH_le hX
  set S := SHN X
  have hS0 := SHN_nonneg X
  have hM : ∀ t ∈ Icc (0 : ℝ) 1, g t ^ 2 ≤ 2 * S := fun t ht => by
    have h1 := sq_le_H1N hg one_pos ht
    simp only [S, SHN]
    have : (0 : ℝ) ≤ kinN X := kinN_nonneg X
    have h0 : 0 ≤ ∫ x, X x ^ 2 ∂μN n := integral_nonneg fun _ => sq_nonneg _
    rw [hint] at h1
    nlinarith
  have h2 := norm_sqE_sq_le hg hM
  have hkg : kinM g ≤ S := by
    simp only [S, SHN]
    have h0 : 0 ≤ ∫ x, X x ^ 2 ∂μN n := integral_nonneg fun _ => sq_nonneg _
    have : (0 : ℝ) ≤ (n + 1) * ∫ x, X x ^ 2 ∂μN n := by positivity
    linarith
  have h3 : ‖rhoE τ X‖ ^ 2 ≤ (4 * S) ^ 2 := by
    change ‖sqE hg‖ ^ 2 ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hkg (by positivity : (0 : ℝ) ≤ 4 * (2 * S))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

/-! ### Bilinearity of the mixed density -/

lemma pfN_add_left (u : C01) {A A' B : Cfg n → ℝ} (hA : MemLp A 2 (μN n))
    (hA' : MemLp A' 2 (μN n)) (hB : MemLp B 2 (μN n)) :
    pfN u (A + A') B = pfN u A B + pfN u A' B := by
  unfold pfN
  rw [← integral_add (integrable_pfN u hA hB) (integrable_pfN u hA' hB)]
  congr 1; funext x; simp only [Pi.add_apply]; ring

lemma pfN_smul_left (u : C01) (c : ℝ) (A B : Cfg n → ℝ) :
    pfN u (c • A) B = c * pfN u A B := by
  unfold pfN
  rw [← integral_const_mul]; congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma pfN_comm (u : C01) (A B : Cfg n → ℝ) : pfN u A B = pfN u B A := by
  unfold pfN; congr 1; funext x; ring

lemma rhoE2_add_left {A A' B : Cfg n → ℝ} (hA : A ∈ DomN τ n) (hA' : A' ∈ DomN τ n)
    (hB : B ∈ DomN τ n) : rhoE2 τ (A + A') B = rhoE2 τ A B + rhoE2 τ A' B :=
  eq_of_int fun u => by
    rw [int_rhoE2 (add_mem hA hA') hB, show rhoE2 τ A B + rhoE2 τ A' B =
      (1 : ℝ) • rhoE2 τ A B + (1 : ℝ) • rhoE2 τ A' B by simp, int_ext_evE_add_smul,
      int_rhoE2 hA hB, int_rhoE2 hA' hB, pfN_add_left u hA.1 hA'.1 hB.1]
    ring

lemma rhoE2_smul_left {A B : Cfg n → ℝ} (hA : A ∈ DomN τ n) (hB : B ∈ DomN τ n) (c : ℝ) :
    rhoE2 τ (c • A) B = c • rhoE2 τ A B :=
  eq_of_int fun u => by
    rw [int_rhoE2 (Submodule.smul_mem _ c hA) hB, show c • rhoE2 τ A B =
      c • rhoE2 τ A B + (0 : ℝ) • rhoE2 τ A B by simp, int_ext_evE_add_smul, int_rhoE2 hA hB,
      pfN_smul_left]
    ring

lemma rhoE2_comm {A B : Cfg n → ℝ} (hA : A ∈ DomN τ n) (hB : B ∈ DomN τ n) :
    rhoE2 τ A B = rhoE2 τ B A :=
  eq_of_int fun u => by rw [int_rhoE2 hA hB, int_rhoE2 hB hA, pfN_comm]

lemma rhoE2_self {A : Cfg n → ℝ} (hA : A ∈ DomN τ n) : rhoE2 τ A A = rhoE τ A :=
  eq_of_int fun u => by rw [int_rhoE2 hA hA, int_rhoE hA]

/-- `‖ρ(A, B)‖_{H¹} ≤ 4 (SHN A + SHN B)`. -/
lemma norm_rhoE2_le_add {A B : Cfg n → ℝ} (hA : A ∈ DomN τ n) (hB : B ∈ DomN τ n) :
    ‖rhoE2 τ A B‖ ≤ 4 * (SHN A + SHN B) := by
  have h1 := norm_rhoE_le (add_mem hA hB)
  have h2 := norm_rhoE_le (sub_mem hA hB)
  have h3 := SHN_add_le (h1NW_of_mem hA) (h1NW_of_mem hB)
  have h4 := SHN_add_le (h1NW_of_mem hA) (h1NW_of_mem (neg_mem hB))
  have hneg : SHN (-B) = SHN B := by
    have := SHN_smul (h1NW_of_mem hB) (-1)
    rwa [neg_one_smul, neg_one_sq, one_mul] at this
  rw [← sub_eq_add_neg, hneg] at h4
  calc ‖rhoE2 τ A B‖ = ‖(1 / 4 : ℝ) • (rhoE τ (A + B) - rhoE τ (A - B))‖ := rfl
    _ ≤ 1 / 4 * (‖rhoE τ (A + B)‖ + ‖rhoE τ (A - B)‖) := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ 4 * (SHN A + SHN B) := by nlinarith

/-- **`‖ρ(A, B)‖_{H¹} ≤ 8 √(SHN A · SHN B)`.** -/
theorem norm_rhoE2_le {A B : Cfg n → ℝ} (hA : A ∈ DomN τ n) (hB : B ∈ DomN τ n) :
    ‖rhoE2 τ A B‖ ≤ 8 * √(SHN A * SHN B) := by
  have h := le_two_sqrt_of_forall (K := ‖rhoE2 τ A B‖ / 4) (SHN_nonneg A) (SHN_nonneg B)
    fun ε hε => by
      have hs : 0 < √ε := Real.sqrt_pos.2 hε
      have e : rhoE2 τ A B = rhoE2 τ (√ε • A) ((1 / √ε) • B) := by
        rw [rhoE2_smul_left hA (Submodule.smul_mem _ _ hB), rhoE2_comm hA
          (Submodule.smul_mem _ _ hB), rhoE2_smul_left hB hA, rhoE2_comm hB hA, smul_smul]
        field_simp; simp
      have := norm_rhoE2_le_add (Submodule.smul_mem _ (√ε) hA)
        (Submodule.smul_mem _ (1 / √ε) hB) (τ := τ)
      rw [← e, SHN_smul (h1NW_of_mem hA), SHN_smul (h1NW_of_mem hB), Real.sq_sqrt hε.le,
        div_pow, one_pow, Real.sq_sqrt hε.le] at this
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
      calc ‖rhoE2 τ A B‖ ≤ 4 * (ε * SHN A + 1 / ε * SHN B) := this
        _ = (ε * SHN A + SHN B / ε) * 4 := by ring
  linarith

end DFT.Continuum.Line
