/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Neumann.Cpt
import DFT.Continuum.Line.Neumann.HKa

/-!
# The Lieb and Levy–Lieb functionals with Neumann walls

For `ρ ∈ H¹(0, 1)`, with Neumann walls, `H⁻¹` potentials and a continuous interaction `w`:

* `liebNH τ w ρ = sup_v (E(v) - v(ρ))`, the Lieb functional, in `(-∞, +∞]`;
* `levyNH τ w ρ = inf {T(Φ) + ∫ w Φ² : Φ normalised, ρ_Φ = ρ}`, the Levy–Lieb constrained search
  (`+∞` if no state has density `ρ`).

## Main results

* `liebNH_le_levyNH`: `F ≤ F_LL` everywhere.
* `gsEH_sub_rhoE_eq`, `gsEH_sub_le_of_isGSNH`: if `Ψ` is a ground state of `v` with density `ρ`,
  then `E(v) - v(ρ) = T(Ψ) + ∫ w Ψ²`, and `v` maximises `v' ↦ E(v') - v'(ρ)`.
* **`liebNH_eq_of_isGSNH`, `levyNH_eq_of_isGSNH`**: on `v`-representable densities both functionals
  equal `T(Ψ) + ∫ w Ψ²`.
* **`levyNH_attained_iff`**: a normalised state with density `ρ` attains the constrained search iff
  it is `±Ψ` almost everywhere.
* **`exists_levy_min`**, `levyNH_eq_of_min`: whenever some normalised state has density `ρ`, the
  constrained search has a minimiser (compactness, `compact_states`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ}

/-- The internal energy `T(Φ) + ∫ w Φ²` of a Neumann state. -/
noncomputable def intEN (w : Cfg n → ℝ) (Φ : Cfg n → ℝ) : ℝ :=
  kinN Φ + ∫ x, w x * (Φ x * Φ x) ∂μN n

/-- **The Lieb functional** `F(ρ) = sup_v (E(v) - v(ρ))` with Neumann walls. -/
noncomputable def liebNH (τ : Stat) (w : Cfg n → ℝ) (ρ : H1E) : EReal :=
  ⨆ v : PotH, ((gsEH τ w v - v ρ : ℝ) : EReal)

/-- **The Levy–Lieb functional** `F_LL(ρ) = inf {T(Φ) + ∫ w Φ² : ρ_Φ = ρ}` with Neumann walls. -/
noncomputable def levyNH (τ : Stat) (w : Cfg n → ℝ) (ρ : H1E) : EReal :=
  ⨅ (Φ : Cfg n → ℝ) (_ : Φ ∈ DomN τ n ∧ ∫ x, Φ x ^ 2 ∂μN n = 1 ∧ rhoE τ Φ = ρ),
    ((intEN w Φ : ℝ) : EReal)

lemma QNH_eq_intEN (v : PotH) (Φ : Cfg n → ℝ) : QNH τ w v Φ = intEN w Φ + v (rhoE τ Φ) := rfl

/-- `E(v) - v(ρ_Φ) ≤ T(Φ) + ∫ w Φ²` for every normalised state. -/
lemma gsEH_sub_le_intEN (hw : Continuous w) (v : PotH) {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n)
    (hn : ∫ x, Φ x ^ 2 ∂μN n = 1) : gsEH τ w v - v (rhoE τ Φ) ≤ intEN w Φ := by
  have := gsEH_le (v := v) hw hΦ hn
  rw [QNH_eq_intEN] at this
  linarith

/-- **Lieb below Levy–Lieb.** -/
theorem liebNH_le_levyNH (hw : Continuous w) (ρ : H1E) : liebNH τ w ρ ≤ levyNH τ w ρ :=
  iSup_le fun v => le_iInf₂ fun Φ ⟨hΦ, hn, hρ⟩ => by
    rw [← hρ]; exact EReal.coe_le_coe_iff.2 (gsEH_sub_le_intEN hw v hΦ hn)

/-- At a ground state, `E(v) - v(ρ_Ψ) = T(Ψ) + ∫ w Ψ²`. -/
lemma gsEH_sub_rhoE_eq (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ} (hΨ : IsGSNH τ w v Ψ) :
    gsEH τ w v - v (rhoE τ Ψ) = intEN w Ψ := by
  rw [gsEH_of_isGSNH hw hΨ, QNH_eq_intEN]; ring

/-- **A ground-state density is a supergradient of `E`**: `v` maximises `v' ↦ E(v') - v'(ρ_Ψ)`. -/
lemma gsEH_sub_le_of_isGSNH (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH τ w v Ψ) (v' : PotH) :
    gsEH τ w v' - v' (rhoE τ Ψ) ≤ gsEH τ w v - v (rhoE τ Ψ) := by
  rw [gsEH_sub_rhoE_eq hw hΨ]; exact gsEH_sub_le_intEN hw v' hΨ.1 hΨ.2.1

/-- **The Lieb functional at a `v`-representable density.** -/
theorem liebNH_eq_of_isGSNH (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH τ w v Ψ) : liebNH τ w (rhoE τ Ψ) = (intEN w Ψ : EReal) := by
  rw [← gsEH_sub_rhoE_eq hw hΨ]
  exact le_antisymm (iSup_le fun v' => EReal.coe_le_coe_iff.2 (gsEH_sub_le_of_isGSNH hw hΨ v'))
    (le_iSup (fun v' : PotH => ((gsEH τ w v' - v' (rhoE τ Ψ) : ℝ) : EReal)) v)

/-- **The Levy–Lieb functional at a `v`-representable density.** -/
theorem levyNH_eq_of_isGSNH (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH τ w v Ψ) : levyNH τ w (rhoE τ Ψ) = (intEN w Ψ : EReal) := by
  refine le_antisymm (iInf₂_le Ψ ⟨hΨ.1, hΨ.2.1, rfl⟩) ?_
  rw [← liebNH_eq_of_isGSNH hw hΨ]
  exact liebNH_le_levyNH hw _

/-- **The minimisers of the constrained search** at a `v`-representable density `ρ_Ψ` are `±Ψ`. -/
theorem levyNH_attained_iff (hw : Continuous w) {v : PotH} {Ψ Φ : Cfg n → ℝ}
    (hΨ : IsGSNH τ w v Ψ) (hΦ : Φ ∈ DomN τ n) (hn : ∫ x, Φ x ^ 2 ∂μN n = 1)
    (hρ : rhoE τ Φ = rhoE τ Ψ) :
    intEN w Φ = intEN w Ψ ↔ Φ =ᵐ[μN n] Ψ ∨ Φ =ᵐ[μN n] (-1 : ℝ) • Ψ := by
  constructor
  · intro h
    have hGS : IsGSNH τ w v Φ := isGSNH_of_le hw hΦ hn (by
      rw [gsEH_of_isGSNH hw hΨ, QNH_eq_intEN, QNH_eq_intEN, h, hρ])
    exact gsNH_unique hw hΨ hGS
  · have hint : ∀ {A B : Cfg n → ℝ}, A =ᵐ[μN n] B →
        ∫ x, w x * (A x * A x) ∂μN n = ∫ x, w x * (B x * B x) ∂μN n := fun h =>
      integral_congr_ae (h.mono fun x hx => by simp only [hx])
    rintro (h | h)
    · simp only [intEN, kinN_congr (h1NW_of_mem hΦ) h, hint h]
    · rw [intEN, intEN, kinN_congr (h1NW_of_mem hΦ) h, kinN_smul (h1NW_of_mem hΨ.1), hint h]
      simp

/-! ### The constrained search is attained -/

lemma rhoE_eq_of_forall_pot {ρ ρ' : H1E} (h : ∀ u : PotH, u ρ = u ρ') : ρ = ρ' := by
  have h1 := h (InnerProductSpace.toDual ℝ H1E (ρ - ρ'))
  rw [InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDual_apply_apply] at h1
  have h2 : inner ℝ (ρ - ρ') (ρ - ρ') = (0 : ℝ) := by rw [inner_sub_right, h1, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h2)

/-- **The constrained search is attained**: if some normalised Neumann state has density `ρ`, one
of them minimises `T + ∫ w Φ²` among them. -/
theorem exists_levy_min (hw : Continuous w) {ρ : H1E} {Φ₀ : Cfg n → ℝ} (hΦ₀ : Φ₀ ∈ DomN τ n)
    (hn₀ : ∫ x, Φ₀ x ^ 2 ∂μN n = 1) (hρ₀ : rhoE τ Φ₀ = ρ) :
    ∃ Ψ ∈ DomN τ n, ∫ x, Ψ x ^ 2 ∂μN n = 1 ∧ rhoE τ Ψ = ρ ∧
      ∀ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 → rhoE τ Φ = ρ → intEN w Ψ ≤ intEN w Φ := by
  set S : Set ℝ := {e | ∃ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 ∧ rhoE τ Φ = ρ ∧ intEN w Φ = e}
  have hne : S.Nonempty := ⟨_, Φ₀, hΦ₀, hn₀, hρ₀, rfl⟩
  have hbdd : BddBelow S := ⟨gsEH τ w 0, fun e ⟨Φ, hΦ, hn, _, he⟩ => by
    rw [← he]; have := gsEH_sub_le_intEN hw (0 : PotH) hΦ hn
    simpa using this⟩
  set m := sInf S
  have hseq : ∀ j : ℕ, ∃ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 ∧ rhoE τ Φ = ρ ∧
      intEN w Φ < m + 1 / ((j : ℝ) + 1) := fun j => by
    obtain ⟨_, ⟨Φ, hΦ, hn, hρ, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne
      (lt_add_of_pos_right m (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1)))
    exact ⟨Φ, hΦ, hn, hρ, hlt⟩
  choose Φ hΦ hn hρ hlt using hseq
  have hge : ∀ j, m ≤ intEN w (Φ j) := fun j => csInf_le hbdd ⟨Φ j, hΦ j, hn j, hρ j, rfl⟩
  have hlim : Tendsto (fun j => intEN w (Φ j)) atTop (𝓝 m) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hge fun j => (hlt j).le
    simpa using (tendsto_const_nhds (x := m)).add tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨B, hB⟩ := ae_bound_cont (n := n) hw
  have hW : ∀ j, |∫ x, w x * (Φ j x * Φ j x) ∂μN n| ≤ B := fun j => abs_int_w_le hB (hΦ j).1 (hn j)
  have hkin : ∀ j, kinN (Φ j) ≤ m + 1 + B := fun j => by
    have h1 := hlt j
    have h2 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    simp only [intEN] at h1
    linarith [(abs_le.1 (hW j)).1]
  obtain ⟨Ψ, χ, hχ, hΨ, hnΨ, hlsc, hWt, hu⟩ := compact_states hw hΦ hn hkin
  -- the density is preserved
  have hρΨ : rhoE τ Ψ = ρ := rhoE_eq_of_forall_pot fun u => by
    have h := hu u
    simp only [hρ] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  refine ⟨Ψ, hΨ, hnΨ, hρΨ, fun Φ' hΦ' hn' hρ' => ?_⟩
  have hmΦ : m ≤ intEN w Φ' := csInf_le hbdd ⟨Φ', hΦ', hn', hρ', rfl⟩
  -- lower semicontinuity: `T(Ψ) ≤ m - W(Ψ)`
  set WΨ := ∫ x, w x * (Ψ x * Ψ x) ∂μN n
  have hT : kinN Ψ ≤ m - WΨ := hlsc _ fun ε hε => by
    have h1 := (hlim.comp hχ.tendsto_atTop).sub hWt
    have h2 : ∀ᶠ k in atTop, intEN w (Φ (χ k)) - ∫ x, w x * (Φ (χ k) x * Φ (χ k) x) ∂μN n <
        m - WΨ + ε := (tendsto_order.1 h1).2 _ (by linarith)
    filter_upwards [h2] with k hk
    simp only [intEN] at hk
    linarith
  simp only [intEN] at hmΦ ⊢
  linarith

/-- At a minimiser, the Levy–Lieb functional takes its value. -/
lemma levyNH_eq_of_min {ρ : H1E} {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomN τ n)
    (hn : ∫ x, Ψ x ^ 2 ∂μN n = 1) (hρ : rhoE τ Ψ = ρ)
    (hmin : ∀ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 → rhoE τ Φ = ρ → intEN w Ψ ≤ intEN w Φ) :
    levyNH τ w ρ = (intEN w Ψ : EReal) :=
  le_antisymm (iInf₂_le Ψ ⟨hΨ, hn, hρ⟩)
    (le_iInf₂ fun Φ ⟨hΦ, hnΦ, hρΦ⟩ => EReal.coe_le_coe_iff.2 (hmin Φ hΦ hnΦ hρΦ))

end DFT.Continuum.Line
