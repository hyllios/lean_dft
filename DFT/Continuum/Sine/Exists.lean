/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Regular
import DFT.Continuum.Line.FreeFermions

/-!
# Interacting ground states on a line exist

`n + 1` bosons or fermions on `[0, 1]` with a one-body potential `v` and an interaction `w`
invariant under relabelling. Assume the total potential `V(x) = Σ_k v(x_k) + w(x)` is, on the
closed cube, a cosine series `Σ_l β_l Π_j cos(π l_j x_j)` with `Σ_l |β_l| (1 + |l|)^s < ∞` for every
`s` (for example, the even 2-periodic extension of `V` is smooth). Then:

* `Q_eq_Fn`, `ip_eq_tsum`: for `φ ∈ Dom`, the energy and the norm are the coefficient-space
  energy `Fn V` and `Σ cN²` of the sine coefficients.
* `exists_isGS_line`: **a normalised ground state exists** (the series of the minimiser of
  `Sine/Min`, which is in the domain by `Sine/Regular`).
* `hk_line_sine`, `lieb_line_sine`: **unconditional Hohenberg–Kohn and Lieb** in this class.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real
open scoped ENNReal

variable {n : ℕ}

/-- Parseval: `⟨φ, φ⟩ = Σ_m cN_m(φ)²`. -/
lemma hasSum_ip {φ : Cfg n → ℝ} (hφ : Continuous φ) :
    HasSum (fun m => cN m φ ^ 2) (ip (μ := μN n) φ φ) := by
  rw [ip, muN_eq]; exact hasSum_sq_cube hφ

lemma ip_eq_tsum {φ : Cfg n → ℝ} (hφ : Continuous φ) :
    ip (μ := μN n) φ φ = ∑' m, cN m φ ^ 2 := (hasSum_ip hφ).tsum_eq.symm

/-- The sine coefficients of a state in the domain are admissible. -/
lemma Dir_cN {τ : Stat} {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) : Dir τ fun m => cN m φ :=
  ⟨(hasSum_ip hφ.1.continuous).summable, by simpa [lam] using (hasSum_kin hφ).summable,
    cN_InS hφ⟩

/-- **The energy in the sine basis**: `⟨φ, H φ⟩ = Σ λ_m c_m² + Σ c_m (K c)_m`. -/
lemma Q_eq_Fn {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) (v : Pot) {φ : Cfg n → ℝ}
    (hφ : φ ∈ Dom τ n) :
    Q (setting τ n w hw) v φ = Fn (fun x => LN n v x + w x) fun m => cN m φ := by
  have hc := hφ.1.continuous
  have hVc : Continuous fun x => LN n v x + w x := (continuous_LN v).add hw
  rw [Fn, Bf_cN hVc hc]
  have hk : ∑' m, lam m * cN m φ ^ 2 = ∫ x, ∑ k, dk k φ x * dk k φ x ∂μN n := by
    simpa [lam] using (hasSum_kin hφ).tsum_eq
  rw [hk]
  have hsplit : ∫ x, (LN n v x + w x) * (φ x * φ x) ∂μN n =
      ∫ x, LN n v x * (φ x * φ x) ∂μN n + ∫ x, w x * (φ x * φ x) ∂μN n := by
    rw [← integral_add (f := fun x => LN n v x * (φ x * φ x)) (g := fun x => w x * (φ x * φ x))
      (integrableN ((continuous_LN v).mul (hc.mul hc)))
      (integrableN (hw.mul (hc.mul hc)))]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [hsplit]
  change ∫ x, ∑ k, dk k φ x * dk k φ x ∂μN n + ∫ x, w x * (φ x * φ x) ∂μN n +
    ∫ x, LN n v x * (φ x * φ x) ∂μN n = _
  ring

/-- A nonzero state of either statistics. -/
lemma exists_dom_pos (τ : Stat) : ∃ Ψ ∈ Dom τ n, 0 < ip (μ := μN n) Ψ Ψ := by
  cases τ
  · obtain ⟨Ψ, hΨ, -⟩ := prodS_isGS (n := n) 0
    exact ⟨Ψ, hΨ.1, hΨ.2.1⟩
  · obtain ⟨Ψ, -, hΨ, -⟩ := slater_isGS (n := n) 0
    exact ⟨Ψ, hΨ.1, hΨ.2.1⟩

/-- Normalised admissible sequences exist. -/
lemma exists_adm (τ : Stat) : ∃ c : (Fin (n + 1) → ℕ) → ℝ, Adm τ c := by
  obtain ⟨Ψ, hΨ, hpos⟩ := exists_dom_pos (n := n) τ
  set a := (√(ip (μ := μN n) Ψ Ψ))⁻¹
  refine ⟨fun m => a * cN m Ψ, Dir_smul (Dir_cN hΨ) a, ?_⟩
  simp only [mul_pow]
  rw [tsum_mul_left, ← ip_eq_tsum hΨ.1.continuous, inv_pow, Real.sq_sqrt hpos.le,
    inv_mul_cancel₀ hpos.ne']

section existence

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {β : (Fin (n + 1) → ℕ) → ℝ}

/-- **Interacting ground states on a line exist** when `Σ_k v(x_k) + w(x)` is a rapidly
converging cosine series on the closed cube. -/
theorem exists_isGS_line {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x)
    (hβ : ∀ s : ℕ, Summable fun l => |β l| * (1 + (sz l : ℝ)) ^ s)
    (hV : ∀ x ∈ CubeC n, LN n v x + w x = ∑' l, β l * cosM l x) :
    ∃ Φ, IsGS (setting τ n w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 := by
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hVs : ∀ σ x, V (pm σ x) = V x := fun σ x => by simp only [V, LN_pm, hws]
  obtain ⟨a, ha, hmin⟩ := exists_min hβ hV (exists_adm τ)
  obtain ⟨hΦ, hcoef⟩ := ser_min hβ hV hVs ha hmin
  have hcoef' : (fun m => cN m (ser a)) = a := funext hcoef
  have hip : ip (μ := μN n) (ser a) (ser a) = 1 := by
    rw [ip_eq_tsum hΦ.1.continuous]; simp only [hcoef]; exact ha.norm
  have hQ : Q (setting τ n w hw) v (ser a) = E0 V τ := by
    rw [Q_eq_Fn hw v hΦ, hcoef', hmin]
  refine ⟨ser a, ⟨hΦ, hip ▸ one_pos, fun φ hφ => ?_⟩, hip⟩
  rw [hQ, hip, mul_one, Q_eq_Fn hw v hφ, ip_eq_tsum hφ.1.continuous]
  exact Fn_ge hβ hV (Dir_cN hφ)

/-- A normalised ground state as an `IsNGS`. -/
theorem exists_isNGS_line {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x)
    (hβ : ∀ s : ℕ, Summable fun l => |β l| * (1 + (sz l : ℝ)) ^ s)
    (hV : ∀ x ∈ CubeC n, LN n v x + w x = ∑' l, β l * cosM l x) :
    ∃ ψ, IsNGS (setting τ n w hw) v ψ := by
  obtain ⟨Φ, hΦ, hip⟩ := exists_isGS_line (τ := τ) (hw := hw) hws hβ hV
  refine ⟨Φ, ⟨hΦ.1, hip⟩, fun φ hφ => ?_⟩
  have := hΦ.2.2 φ hφ.1
  rwa [hφ.2, hip, mul_one, mul_one] at this

/-- **Hohenberg–Kohn for `N` interacting bosons or fermions on a line, unconditional** in the
cosine-series class: the ground state of `v` exists, and ground states of `v` and `v'` with the
same one-body density force `v - v'` to be constant. -/
theorem hk_line_sine {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x)
    (hβ : ∀ s : ℕ, Summable fun l => |β l| * (1 + (sz l : ℝ)) ^ s)
    (hV : ∀ x ∈ CubeC n, LN n v x + w x = ∑' l, β l * cosM l x) (v' : Pot) :
    (∃ Φ, IsGS (setting τ n w hw) v Φ) ∧ ∀ Φ Φ', IsGS (setting τ n w hw) v Φ →
      IsGS (setting τ n w hw) v' Φ' →
      (∀ t ∈ Ioo (0 : ℝ) 1, ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 =
        ∫ y in Cube' n, Φ' (Fin.cons t y) ^ 2) → ∃ k : ℝ, v - v' = k • one :=
  ⟨(exists_isGS_line hws hβ hV).imp fun _ h => h.1, fun _ _ h h' hρ =>
    hk_line_of_ucp h h' hρ (ucp_line_stat hws h)⟩

/-- **The Lieb functional for `N` interacting bosons or fermions on a line, unconditional** in the
cosine-series class: a normalised ground state `ψ` exists; at its density the Lieb functional
equals `⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient, and every other subgradient `-v'` has `v - v'`
constant. -/
theorem lieb_line_sine {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x)
    (hβ : ∀ s : ℕ, Summable fun l => |β l| * (1 + (sz l : ℝ)) ^ s)
    (hV : ∀ x ∈ CubeC n, LN n v x + w x = ∑' l, β l * cosM l x) :
    ∃ ψ, IsNGS (setting τ n w hw) v ψ ∧
      liebF (setting τ n w hw) (dens (setting τ n w hw) ψ) =
        (((setting τ n w hw).h0 ψ ψ : ℝ) : EReal) ∧
      (∀ ρ : Pot → ℝ, (((setting τ n w hw).h0 ψ ψ + dens (setting τ n w hw) ψ v - ρ v : ℝ) :
        EReal) ≤ liebF (setting τ n w hw) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ,
        (((setting τ n w hw).h0 ψ ψ + dens (setting τ n w hw) ψ v' - ρ v' : ℝ) : EReal) ≤
          liebF (setting τ n w hw) ρ) → ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨ψ, hψ⟩ := exists_isNGS_line (τ := τ) (hw := hw) hws hβ hV
  exact ⟨ψ, hψ, lieb_line hws hψ⟩

end existence

end DFT.Continuum.Sine
