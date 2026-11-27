/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.HK.UcpY
import DFT.Continuum.Line.HK.YoungL2

/-!
# `H²` regularity of fermionic ground states, in sine coefficients

For `N` fermions on `H¹₀` with continuous `v` and a continuous, relabelling-invariant `w`, the sine
coefficients `c_m = ⟨s_m, Ψ⟩` of a ground state satisfy

  `λ_m c_m + ⟨s_m, V Ψ⟩ = E c_m`,  `V = Σ_k v(x_k) + w`,

(the weak equation tested against the single mode `s_m`, `el_all`), hence `Σ_m λ_m² c_m² < ∞`:
the ground state is in `H²` with Dirichlet conditions, with no smoothness of `v` or `w`.

* `int_dW_smd`: `∫ ∂ₖΨ ∂ₖs_m = π²(m_k+1)² c_m` for `Ψ ∈ H¹`.
* `h0W_smd`: `h₀(Ψ, s_m) = λ_m c_m + ⟨s_m, w Ψ⟩`.
* **`coef_EL`**: the coefficient equation.
* **`summable_lam_sq`**: `Σ_m λ_m² c_m² < ∞`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology Sine

variable {n : ℕ}

/-- `∫ ∂ₖΨ ∂ₖs_m = π²(m_k + 1)² c_m`. -/
lemma int_dW_smd {Ψ : Cfg n → ℝ} (hΨ : H1W Ψ) (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) :
    ∫ x, dW k Ψ x * dW k (smd m) x ∂μN n = (π * (m k + 1)) ^ 2 * cN m Ψ := by
  have h1 : dW k (smd m) =ᵐ[μN n] fun x => π * (m k + 1) * cmd k m x := dW_ae_eq (isWD_smd k m)
  have h2 := (dW_spec (hΨ.2 k)).2 (cmd k m) (contDiff_cmd k m)
  simp only [dk_cmd] at h2
  rw [integral_congr_ae (show (fun x => dW k Ψ x * dW k (smd m) x) =ᵐ[μN n]
    fun x => dW k Ψ x * (π * (m k + 1) * cmd k m x) from h1.mono fun x hx => by
      simp only [hx])]
  have e1 : ∫ x, dW k Ψ x * (π * (m k + 1) * cmd k m x) ∂μN n =
      π * (m k + 1) * ∫ x, dW k Ψ x * cmd k m x ∂μN n := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have e2 : ∫ x, Ψ x * (-(π * (m k + 1)) * smd m x) ∂μN n = -(π * (m k + 1)) * cN m Ψ := by
    rw [cN_eq, ← integral_const_mul]; congr 1; funext x; ring
  rw [e2] at h2
  have h3 : ∫ x, dW k Ψ x * cmd k m x ∂μN n = π * (m k + 1) * cN m Ψ := by linarith
  rw [e1, h3]; ring

lemma h0W_smd {w : Cfg n → ℝ} {Ψ : Cfg n → ℝ} (hΨ : H1W Ψ) (m : Fin (n + 1) → ℕ) :
    h0W n w Ψ (smd m) = lam m * cN m Ψ + ∫ x, w x * (Ψ x * smd m x) ∂μN n := by
  simp only [h0W, int_dW_smd hΨ]
  congr 1
  rw [← Finset.sum_mul, lam, ksq]
  push_cast
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

lemma h1W_smd (m : Fin (n + 1) → ℕ) : H1W (smd (d := n + 1) m) :=
  ⟨memLp_cont (continuous_smd m), fun k => ⟨_, isWD_smd k m⟩⟩

variable {w : Cfg n → ℝ} {hw : Continuous w}

/-- **The coefficient equation** `λ_m c_m + ⟨s_m, VΨ⟩ = E c_m` for a fermionic ground state. -/
theorem coef_EL (hws : ∀ σ x, w (pm σ x) = w x) {v : C01} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW .fer n w hw) v Ψ) (m : Fin (n + 1) → ℕ) :
    lam m * cN m Ψ + cN m (fun x => (LN n v x + w x) * Ψ x) =
      Q (settingW .fer n w hw) v Ψ / ip (μ := μN n) Ψ Ψ * cN m Ψ := by
  have hY := isGS_fer_Y hΨ
  have hel := el_all hw hws hY (h1W_smd m)
  have hQ : Q (settingWS (ymix (n + 1)) w hw) v Ψ = Q (settingW .fer n w hw) v Ψ := rfl
  rw [hQ, h0W_smd (h1W_of_mem hY.1)] at hel
  have hii : Integrable (fun x => Ψ x * smd m x) (μN n) :=
    int_mul_L2 hΨ.1.1 (memLp_cont (continuous_smd m))
  have hiw : Integrable (fun x => w x * (Ψ x * smd m x)) (μN n) := by
    obtain ⟨C, hC⟩ := ae_bound_cont hw
    exact hii.bdd_mul hw.aestronglyMeasurable hC
  have hiv : Integrable (fun x => LN n v x * (Ψ x * smd m x)) (μN n) := by
    obtain ⟨C, hC⟩ := ae_bound_cont (continuous_LN (n := n) v)
    exact hii.bdd_mul (continuous_LN v).aestronglyMeasurable hC
  have hc1 : cN m (fun x => (LN n v x + w x) * Ψ x) =
      ∫ x, w x * (Ψ x * smd m x) ∂μN n + ∫ x, LN n v x * (Ψ x * smd m x) ∂μN n := by
    rw [cN_eq, ← integral_add hiw hiv]
    congr 1; funext x; ring
  have hc2 : cN m Ψ = ∫ x, Ψ x * smd m x ∂μN n := by
    rw [cN_eq]; congr 1; funext x; ring
  rw [hc1, hc2]
  rw [← hc2] at hel ⊢
  linarith

/-- **`H²` regularity**: `Σ_m λ_m² c_m² < ∞` for a fermionic ground state. -/
theorem summable_lam_sq (hws : ∀ σ x, w (pm σ x) = w x) {v : C01} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW .fer n w hw) v Ψ) :
    Summable fun m => lam m ^ 2 * cN m Ψ ^ 2 := by
  set E := Q (settingW .fer n w hw) v Ψ / ip (μ := μN n) Ψ Ψ
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hV : Continuous V := (continuous_LN v).add hw
  have hs1 := (parsevalW hΨ.1.1).summable
  have hs2 := (parsevalW (memLp_mul_cont hV hΨ.1.1)).summable
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((hs1.mul_left (2 * E ^ 2)).add (hs2.mul_left 2))
  have h := coef_EL hws hΨ m
  have e : lam m ^ 2 * cN m Ψ ^ 2 = (E * cN m Ψ - cN m (fun x => V x * Ψ x)) ^ 2 := by
    rw [← h]; ring
  rw [e]
  nlinarith [sq_nonneg (E * cN m Ψ + cN m (fun x => V x * Ψ x))]

end DFT.Continuum.Line
