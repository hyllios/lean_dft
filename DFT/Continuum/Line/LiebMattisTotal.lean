/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.SpinBridge

/-!
# The Lieb–Mattis theorem for the total spin of spin-orbital states

For `N = n + 1` spin-½ fermions on `[0, 1]` with a spin-independent Hamiltonian
`-Δ + Σ_k v(x_k) + w(x)` (`w` invariant under relabelling, `Σ v + w` smooth on the closed cube),
consider fermionic spin-orbital states `Ψ(s, x)` (`FermD`) with `C²` components vanishing on the
walls. The total spin is the operator `S² = ½ (S₊S₋ + S₋S₊) + S_z²` on the spin variables. Let

`E(S) = inf { ⟨Ψ, HΨ⟩ / ⟨Ψ, Ψ⟩ : S² Ψ = S(S+1) Ψ }` (`EspinT`, with `S = a - N/2`).

* `lower_bound`: every state of total spin `S' = a - N/2 ≥ 0` has energy at least the ground-state
  energy of the spatial sector `(a, N - a)`: split `Ψ` into `S_z` sectors; sectors above `S'` are
  empty, and `S₊` carries each lower sector up the multiplet to the top sector `S_z = S'`,
  multiplying energy and norm by the same positive factor; the top sector is a spatial state of
  mixed symmetry `(a, N - a)`.
* `upper_bound`: the ground state `Φ` of the spatial sector `(a, b)`, `a ≥ b ≥ 1`, lifts to a
  fermionic spin-orbital state of total spin exactly `(a - b)/2`. Its image under `S₊` lies in the
  sector `(a + 1, b - 1)` with the same energy per norm, so it vanishes by `lieb_mattis`.
* `Espin_total_eq`: **`E(S)` is the ground-state energy of the spatial sector `S_z = S`.**
* `lieb_mattis_total`: **`E(S) < E(S + 1)`** for `S ≥ 0`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine Function

variable {n : ℕ} {a : ℕ}

/-- `S(S+1)` with `S = a - N/2`. -/
noncomputable def lamS (n a : ℕ) : ℝ :=
  ((a : ℝ) - ((n : ℝ) + 1) / 2) * ((a : ℝ) - ((n : ℝ) + 1) / 2 + 1)

/-- Fermionic spin-orbital states of total spin `S = a - N/2`. -/
def SpinClass (a : ℕ) (u : SpinC n → D0 n) : Prop :=
  FermD u ∧ 0 < ipS u ∧ EigC (lamS n a) u

/-- **`E(S)`**: the lowest energy of a state of total spin `S = a - N/2`. -/
noncomputable def EspinT (w : Cfg n → ℝ) (hw : Continuous w) (v : Pot) (a : ℕ) : EReal :=
  ⨅ (u : SpinC n → D0 n) (_ : SpinClass a u), ((QS w hw v u / ipS u : ℝ) : EReal)

section main

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} (hws : ∀ σ x, w (pm σ x) = w x)

/-! ### Sectors -/

lemma sum_sectors (B : D0 n →ₗ[ℝ] D0 n →ₗ[ℝ] ℝ) (u : SpinC n → D0 n) :
    ∑ s, B (u s) (u s) = ∑ c ∈ Finset.range (n + 2), ∑ s, B (Pc c u s) (Pc c u s) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pc_apply]
  have : ∀ c, B (if nup s = c then u s else 0) (if nup s = c then u s else 0) =
      if nup s = c then B (u s) (u s) else 0 := fun c => by split_ifs <;> simp
  simp only [this]
  have hs : nup s ∈ Finset.range (n + 2) := Finset.mem_range.2 (by have := nup_le s; omega)
  simp only [Finset.sum_ite_eq, hs, ite_true]

include hws in
/-- **The lower bound** along a multiplet of total spin `S' = a' - N/2 ≥ 0`. -/
theorem lower_bound {a' : ℕ} (ha' : ((n : ℝ) + 1) / 2 ≤ a') (ha'N : a' ≤ n + 1) {E' : ℝ}
    (hE' : ∀ f ∈ DomY a' n, E' * ip (μ := μN n) f f ≤ Q (settingS (ymix a') w hw) v f)
    {u : SpinC n → D0 n} (hF : FermD u) (heig : EigC (lamS n a') u) :
    E' * ipS u ≤ QS w hw v u := by
  set S' : ℝ := (a' : ℝ) - ((n : ℝ) + 1) / 2
  have hS' : 0 ≤ S' := by simp only [S']; linarith
  have hlam : lamS n a' = S' * (S' + 1) := rfl
  -- the two forms satisfy the hypotheses of the ladder
  have hBQc := BQ_congr w hw v
  have hBic := Bip_congr (n := n)
  have hBQs := BQ_symm w hw v
  have hBis := Bip_symm (n := n)
  -- sectors at and below the top
  have key : ∀ k c (φ : SpinC n → D0 n), c + k = a' → FermD φ → Pc c φ = φ →
      EigC (lamS n a') φ → E' * ipS φ ≤ QS w hw v φ := by
    intro k
    induction k with
    | zero =>
      intro c φ hck hφ hc _
      simp only [add_zero] at hck
      subst hck
      rw [QS, ipS, sector_reduce (BQ w hw v) (fun f σ => BQ_pm hws f σ) hφ hc,
        sector_reduce Bip (fun f σ => Bip_pm f σ) hφ hc]
      have h := hE' _ (mem_DomY_sc hφ c)
      have hK := (card_sector_pos (n := n) (c := c) (by omega)).le
      change E' * (_ * ip (μ := μN n) _ _) ≤ _ * Q (settingS (ymix c) w hw) v _
      nlinarith
    | succ k ih =>
      intro c φ hck hφ hc heigφ
      rcases (ipS_nonneg φ).eq_or_lt with h0 | hpos
      · rw [← h0, QS_eq_zero_of_ipS h0.symm, mul_zero]
      set M : ℝ := (c : ℝ) - ((n : ℝ) + 1) / 2
      have hSM : S' - M = k + 1 := by
        simp only [S', M]; have : (c : ℝ) + (k + 1 : ℕ) = a' := by exact_mod_cast hck
        push_cast at this; linarith
      have hm := ladder_Sm Bip hBis hBic hc heigφ
      have hp := ladder_Sp Bip hBic hc heigφ
      have hq := ladder_Sp (BQ w hw v) hBQc hc heigφ
      change ipS (Sm φ) = _ * ipS φ at hm
      change ipS (Sp φ) = _ * ipS φ at hp
      change QS w hw v (Sp φ) = _ * QS w hw v φ at hq
      have hcm : 0 ≤ lamS n a' - M ^ 2 + M := by
        have := ipS_nonneg (Sm φ)
        rw [hm] at this
        exact nonneg_of_mul_nonneg_left this hpos
      have hcp : 0 < lamS n a' - M ^ 2 - M := by
        rw [hlam] at hcm ⊢
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      have hIH := ih (c + 1) (Sp φ) (by omega) (FermD_Sp hφ) (by rw [← Sp_Pc, hc])
        (EigC_Sp heigφ)
      rw [hp, hq, ← mul_assoc, mul_comm E', mul_assoc] at hIH
      exact le_of_mul_le_mul_left hIH hcp
  -- sectors above the top are empty
  have above : ∀ c, a' < c → ipS (Pc c u) = 0 := by
    intro c hc
    have hφ := FermD_Pc hF c
    have hPc : Pc c (Pc c u) = Pc c u := Pc_Pc c u
    have hp := ladder_Sp Bip hBic hPc (EigC_Pc heig c)
    change ipS (Sp (Pc c u)) = _ * ipS (Pc c u) at hp
    set M : ℝ := (c : ℝ) - ((n : ℝ) + 1) / 2
    have hMS : S' < M := by
      simp only [S', M]; have : (a' : ℝ) < c := by exact_mod_cast hc
      linarith
    have hneg : lamS n a' - M ^ 2 - M < 0 := by rw [hlam]; nlinarith
    have hnn := ipS_nonneg (Sp (Pc c u))
    rw [hp] at hnn
    exact le_antisymm (nonpos_of_mul_nonneg_right hnn hneg) (ipS_nonneg _)
  -- sum over sectors
  have hsec : ∀ c ∈ Finset.range (n + 2), E' * ipS (Pc c u) ≤ QS w hw v (Pc c u) := by
    intro c _
    by_cases hc : c ≤ a'
    · exact key (a' - c) c (Pc c u) (by omega) (FermD_Pc hF c) (Pc_Pc c u) (EigC_Pc heig c)
    · have h0 := above c (by omega)
      rw [h0, QS_eq_zero_of_ipS h0, mul_zero]
  rw [QS, ipS, sum_sectors (BQ w hw v), sum_sectors Bip, Finset.mul_sum]
  exact Finset.sum_le_sum hsec

/-! ### The upper bound -/

omit hws in
lemma Strong_Sp {E : ℝ} {u : SpinC n → D0 n} (hu : ∀ s, Strong w v E (u s)) (s : SpinC n) :
    Strong w v E ((Sp u s : D0 n) : Cfg n → ℝ) := by
  have h : Sp u s = ∑ i, if s i = true then u (update s i false) else 0 := Sp_apply u s
  rw [h]
  exact Strong.sum w v E Finset.univ fun i _ => Strong.ite w v E (hu _)

variable {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
  (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x)
include hws hF hVF

/-- **The sector ground state has total spin exactly `(a - b)/2`**, as a spin-orbital state. -/
theorem upper_bound {b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a)
    {Φ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a) w hw) v Φ) :
    ∃ u, SpinClass a u ∧
      QS w hw v u / ipS u = Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ := by
  classical
  have ha : a ≤ n + 1 := by omega
  set E := Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ
  have hΦD : Φ ∈ D0 n := DomY_le_D0 hΦ.1
  set u := lift a hΦD
  have hFu : FermD u := FermD_lift hΦD
  have hPu : Pc a u = u := Pc_lift hΦD ha
  -- the components solve the Schrödinger equation
  have hΦs : Strong w v E Φ := fun x hx => by
    have := strong_eq_Y hws hΦ x hx; linarith
  have hus : ∀ s, Strong w v E (u s) := fun s => by
    refine Strong.sum w v E _ fun σ _ => Strong.ite w v E ?_
    exact Strong.smul w v E (Strong.pm w v E hws hΦ.1.1 hΦs σ) _
  have hSus : ∀ s, Strong w v E ((Sp u s : D0 n) : Cfg n → ℝ) := Strong_Sp hus
  -- `S₊ u` vanishes on the cube
  set R := Sp u (sc n (a + 1))
  have hRY : (R : Cfg n → ℝ) ∈ DomY (a + 1) n := mem_DomY_sc (FermD_Sp hFu) (a + 1)
  have hR0 : ∀ x ∈ Cube n, (R : Cfg n → ℝ) x = 0 := by
    rcases (Bip_self_nonneg R).eq_or_lt with h0 | hpos
    · exact eq_zero_of_Bip h0.symm
    · exfalso
      obtain ⟨Ψ, hΨ, -⟩ := exists_isGS_smoothS (a + 1) hws hF hVF (hw := hw)
      have hlm := lieb_mattis hws hF hVF hab hb1 hba hΦ hΨ
      have hle := le_Q_of_isGS hΨ hRY
      have hQR := BQ_of_strong w hw v E (hSus (sc n (a + 1)))
      change Q (settingS (ymix (a + 1)) w hw) v R = E * ip (μ := μN n) R R at hQR
      rw [hQR] at hle
      have := (mul_le_mul_iff_of_pos_right (show 0 < ip (μ := μN n) (R : Cfg n → ℝ) R from hpos)).1
        hle
      linarith
  have hSu0 : ∀ s, ∀ x ∈ Cube n, ((Sp u s : D0 n) : Cfg n → ℝ) x = 0 := by
    intro s x hx
    by_cases hs : nup s = a + 1
    · obtain ⟨τ, hτ⟩ := exists_rel_sc hs
      rw [← hτ, Ferm_comp (FermD_Sp hFu) τ (sc n (a + 1)) x, hR0 _ (pm_mem_cube.2 hx), mul_zero]
    · have : Sp u = Pc (a + 1) (Sp u) := by rw [← Sp_Pc, hPu]
      rw [this]; simp [Pc_apply, hs]
  -- so `u` has total spin `a - N/2`
  have heig : EigC (lamS n a) u := by
    intro s x hx
    have hS2 := congrArg (fun T : Module.End ℝ (SpinC n → D0 n) => T u s)
      (S2_eq (n := n) (V := D0 n))
    simp only [Module.End.mul_apply, LinearMap.add_apply] at hS2
    rw [hS2, Pi.add_apply, Pi.add_apply, map_add, map_add, Sm_map, Sz_map, Sz_map]
    have hz : (fun t => ev x (Sp u t)) = 0 := funext fun t => hSu0 t x hx
    rw [hz, map_zero]
    simp only [Pi.zero_apply, Sz_apply, smul_eq_mul, zero_add, ev_apply, Submodule.coe_smul,
      Pi.smul_apply]
    by_cases hs : nup s = a
    · simp only [Mz, hs, lamS]; ring
    · have : u s = 0 := by rw [← hPu]; simp [Pc_apply, hs]
      simp [this]
  -- energy and norm
  set K := ((Finset.univ.filter fun s : SpinC n => nup s = a).card : ℝ)
  set Y := ((Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => YG a σ).card : ℝ)
  have hK : 0 < K := card_sector_pos ha
  have hY : 0 < Y := by
    simp only [Y, Nat.cast_pos]
    exact Finset.card_pos.2 ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, YG_one a⟩⟩
  have hsc := lift_sc hΦ.1
  have hQ : QS w hw v u = K * (Y * Y * Q (settingS (ymix a) w hw) v Φ) := by
    rw [QS, sector_reduce (BQ w hw v) (fun f σ => BQ_pm hws f σ) hFu hPu]
    change K * BQ w hw v (lift a hΦD (sc n a)) (lift a hΦD (sc n a)) = _
    rw [hsc, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc Y]
    rfl
  have hI : ipS u = K * (Y * Y * ip (μ := μN n) Φ Φ) := by
    rw [ipS, sector_reduce Bip (fun f σ => Bip_pm f σ) hFu hPu]
    change K * Bip (lift a hΦD (sc n a)) (lift a hΦD (sc n a)) = _
    rw [hsc, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc Y]
    rfl
  have hipΦ := hΦ.2.1
  refine ⟨u, ⟨hFu, by rw [hI]; positivity, heig⟩, ?_⟩
  rw [hQ, hI, mul_div_mul_left _ _ hK.ne', mul_div_mul_left _ _ (by positivity)]

/-! ### The theorem -/

/-- **`E(S)` is the ground-state energy of the spatial sector `S_z = S`** (`a ≥ b ≥ 1`). -/
theorem Espin_total_eq {b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a)
    {Φ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a) w hw) v Φ) :
    EspinT w hw v a = ((Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ : ℝ) : EReal) := by
  refine le_antisymm ?_ (le_iInf₂ fun u hu => ?_)
  · obtain ⟨u, hu, he⟩ := upper_bound hws hF hVF hab hb1 hba hΦ
    rw [← he]; exact iInf₂_le u hu
  · refine EReal.coe_le_coe_iff.2 ?_
    have hlb := lower_bound hws (a' := a) (by
      have : (b : ℝ) ≤ a := by exact_mod_cast hba
      have : (a : ℝ) + b = n + 1 := by exact_mod_cast hab
      linarith) (by omega) (E' := Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ)
      (fun f hf => le_Q_of_isGS hΦ hf) hu.1 hu.2.2
    rw [le_div_iff₀ hu.2.1]; linarith

/-- **The Lieb–Mattis theorem**: for `N` spin-½ fermions on a line with a spin-independent
Hamiltonian, the lowest energy with total spin `S` is strictly below the lowest energy with total
spin `S + 1`, for `S ≥ 0` (`S = a - N/2` with `a ≥ N - a ≥ 1`). -/
theorem lieb_mattis_total {b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a) :
    EspinT w hw v a < EspinT w hw v (a + 1) := by
  obtain ⟨Φ, hΦ, -⟩ := exists_isGS_smoothS a hws hF hVF (hw := hw)
  obtain ⟨Ψ, hΨ, -⟩ := exists_isGS_smoothS (a + 1) hws hF hVF (hw := hw)
  have hlm := lieb_mattis hws hF hVF hab hb1 hba hΦ hΨ
  rw [Espin_total_eq hws hF hVF hab hb1 hba hΦ]
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hlm) (le_iInf₂ fun u hu => ?_)
  refine EReal.coe_le_coe_iff.2 ?_
  have hlb := lower_bound hws (a' := a + 1) (by
    have : (b : ℝ) ≤ a := by exact_mod_cast hba
    have : (a : ℝ) + b = n + 1 := by exact_mod_cast hab
    push_cast; linarith) (by omega)
    (E' := Q (settingS (ymix (a + 1)) w hw) v Ψ / ip (μ := μN n) Ψ Ψ)
    (fun f hf => le_Q_of_isGS hΨ hf) hu.1 hu.2.2
  rw [le_div_iff₀ hu.2.1]; linarith

end main

end DFT.Continuum.Line
