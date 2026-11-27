/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Neumann.NeuHKc
import DFT.Continuum.Line.NeumannKS.Lieb

/-!
# Continuity of the inverse map `ρ ↦ v_ρ` with Neumann walls

Let `ρ_k → ρ` in `H¹(0, 1)`, all of them ground-state densities, of potentials `v_k` and `v`.
Then `v_k(δ) → v(δ)` for every `δ` of mass zero: the potentials converge weakly-`*` modulo
constants (**`tendsto_vrepNH`**).

Shift `v_k` by constants so that `v_k(ρ) = 0`. Local `N`-representability around `ρ` (radius `r`,
energy bound `M`) covers the ball of radius `r/2` around `ρ_k` once `‖ρ_k - ρ‖ ≤ r/2`; with the
lower bound `E(0) ≤ E(v_k) - v_k(ρ_k)` this bounds `v_k` in `H⁻¹` (`norm_le_of_lower`). A weak
limit `v*` of a subsequence makes `ρ` a supergradient of `E` (`le_gsEH_of_tendsto`), so `ρ` is its
ground-state density (`rhoE_eq_of_supergrad`) and `v* = v + c` (`hkNH`). The limit does not
depend on the subsequence.

* `exists_subseq_tendsto_vrepNH`: the subsequence statement.
* **`tendsto_vrepNH`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ}

/-- Shifting the potential by a constant does not change `E(v) - v(ρ)` on densities of mass `N`. -/
lemma gsEH_sub_shift (hw : Continuous w) (v : PotH) (c : ℝ) {ρ : H1E} (hρ : ellE ρ = n + 1) :
    gsEH τ w (v + c • ellE) - (v + c • ellE) ρ = gsEH τ w v - v ρ := by
  rw [gsEH_shift hw, add_apply, smul_apply, hρ,
    smul_eq_mul]
  ring

/-- **Subsequences of inverse potentials converge** (weakly, modulo constants). -/
lemma exists_subseq_tendsto_vrepNH (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH τ w v Ψ) {vk : ℕ → PotH} {Ψk : ℕ → Cfg n → ℝ}
    (hΨk : ∀ k, IsGSNH τ w (vk k) (Ψk k))
    (hk : Tendsto (fun k => rhoE τ (Ψk k)) atTop (𝓝 (rhoE τ Ψ))) {δ : H1E} (hδ : ellE δ = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun j => vk (φ j) δ) atTop (𝓝 (v δ)) := by
  set ρ := rhoE τ Ψ
  set ρk := fun k => rhoE τ (Ψk k)
  have hNp : (0 : ℝ) < n + 1 := by positivity
  obtain ⟨hpos, hN⟩ := vrepNH_nec hw ⟨v, Ψ, hΨ, rfl⟩
  have hellρ : ellE ρ = n + 1 := ellE_rhoE hΨ.1 hΨ.2.1
  have hellk : ∀ k, ellE (ρk k) = n + 1 := fun k => ellE_rhoE (hΨk k).1 (hΨk k).2.1
  obtain ⟨r, hr, M, hM⟩ := locRepNH_of_pos (τ := τ) hw hpos hN
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hk (r / 2) (by positivity)
  -- the shifted potentials, `u j (ρ) = 0`, along `k = j + K`
  set u : ℕ → PotH := fun j => vk (j + K) + (-(vk (j + K) ρ) / (n + 1)) • ellE
  have huρ : ∀ j, u j ρ = 0 := fun j => by
    simp only [u, add_apply, smul_apply, smul_eq_mul,
      hellρ]
    field_simp; ring
  have huδ : ∀ j, u j δ = vk (j + K) δ := fun j => by
    simp [u, hδ]
  -- `ρ_k` is a supergradient of `E` at `u j`
  have hsup : ∀ j (v' : PotH),
      gsEH τ w v' - v' (ρk (j + K)) ≤ gsEH τ w (u j) - u j (ρk (j + K)) := fun j v' => by
    rw [gsEH_sub_shift hw _ _ (hellk _)]
    exact gsEH_sub_le_of_isGSNH hw (hΨk (j + K)) v'
  -- the bound
  set L := gsEH τ w 0
  have hlow : ∀ j (h : H1E), ellE h = 0 → ‖h‖ ≤ r / 2 → -(M - L) ≤ u j h := by
    intro j h hh hhr
    have hd : ‖ρk (j + K) - ρ‖ ≤ r / 2 := by
      have := hK (j + K) (Nat.le_add_left K j)
      rw [dist_eq_norm] at this; exact this.le
    obtain ⟨Φ, hΦ, hn, hρΦ, hE⟩ := hM (ρk (j + K) - ρ + h)
      (by rw [map_add, map_sub, hellk, hellρ, hh]; ring)
      ((norm_add_le _ _).trans (by linarith))
    have h1 := gsEH_sub_le_of_rep hw hΦ hn (ρ0 := ρk (j + K)) (h := h)
      (by rw [hρΦ]; abel) hE (u j)
    have h2 := hsup j 0
    simp only [zero_apply, sub_zero] at h2
    linarith
  have hbound : ∀ j, ‖u j‖ ≤ (M - L) / (r / 2) * (1 + ‖ellE‖ * ‖ρ‖ / (n + 1)) := fun j =>
    norm_le_of_lower hNp (by positivity) hellρ (huρ j) (hlow j)
  obtain ⟨vs, φ, hφ, hlim⟩ := exists_weak_subseq_PotH hbound
  set R := (M - L) / (r / 2) * (1 + ‖ellE‖ * ‖ρ‖ / (n + 1))
  -- `ρ` is a supergradient of `E` at `vs`
  have hρsub : Tendsto (fun j => ρk (φ j + K)) atTop (𝓝 ρ) :=
    hk.comp (tendsto_atTop_mono (fun j => Nat.le_add_right (φ j) K) hφ.tendsto_atTop)
  have hvsρ : vs ρ = 0 := by
    have := hlim ρ; simp only [huρ] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have huk : Tendsto (fun j => u (φ j) (ρk (φ j + K))) atTop (𝓝 0) := by
    have hsmall : Tendsto (fun j => ‖ρk (φ j + K) - ρ‖) atTop (𝓝 0) := by
      simpa using (hρsub.sub_const ρ).norm
    refine squeeze_zero_norm (fun j => ?_) (by simpa using hsmall.const_mul R)
    have e : u (φ j) (ρk (φ j + K)) = u (φ j) (ρk (φ j + K) - ρ) := by
      rw [map_sub, huρ, sub_zero]
    rw [e]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _))
  have hsupv : ∀ v' : PotH, gsEH τ w v' ≤ gsEH τ w vs + (v' - vs) ρ := fun v' => by
    have := le_gsEH_of_tendsto hw hlim
      (a := fun j => gsEH τ w v' - v' (ρk (φ j + K)) + u (φ j) (ρk (φ j + K)))
      (((tendsto_const_nhds.sub ((v'.continuous.tendsto ρ).comp hρsub)).add huk))
      fun j => by linarith [hsup (φ j) v']
    rw [sub_apply, hvsρ]
    linarith
  obtain ⟨Ψs, hΨs⟩ := exists_isGSNH τ hw vs
  have hρs : rhoE τ Ψs = ρ := rhoE_eq_of_supergrad hw hsupv hΨs
  obtain ⟨c, hc⟩ := hkNH hw hΨ hΨs hρs.symm
  have hvδ : v δ = vs δ := by
    have := congrArg (fun f : PotH => f δ) hc
    simp only [sub_apply, smul_apply, hδ,
      smul_zero] at this
    linarith
  refine ⟨fun j => φ j + K, fun a b hab => by simpa using hφ hab, ?_⟩
  rw [hvδ]
  simpa only [huδ] using hlim δ

/-- **Continuity of the inverse map** (Neumann walls, `H⁻¹` potentials): if the ground-state
densities of `v_k` converge in `H¹` to the ground-state density of `v`, then `v_k(δ) → v(δ)` for
every `δ` of mass zero. -/
theorem tendsto_vrepNH (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH τ w v Ψ) {vk : ℕ → PotH} {Ψk : ℕ → Cfg n → ℝ}
    (hΨk : ∀ k, IsGSNH τ w (vk k) (Ψk k))
    (hk : Tendsto (fun k => rhoE τ (Ψk k)) atTop (𝓝 (rhoE τ Ψ))) {δ : H1E} (hδ : ellE δ = 0) :
    Tendsto (fun k => vk k δ) atTop (𝓝 (v δ)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φ, -, hφ⟩ := exists_subseq_tendsto_vrepNH hw hΨ (fun k => hΨk (ns k))
    (hk.comp hns) hδ
  exact ⟨φ, hφ⟩

end DFT.Continuum.Line
