/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Applications.OneBody

/-!
# Kohn–Sham theory on the line (`H¹₀`, continuous potentials)

The Kohn–Sham system is the same `N` particles with no interaction (`ksS τ n`). A density is
Kohn–Sham `v`-representable (`KSRep`) if it is the density of a ground state of some continuous
`v_s`; ensembles add nothing (`ensVRep_iff_W_cont`).

* `pureDens_hk`, **`ks_unique`**: the Kohn–Sham potential of a density is unique up to a constant;
  **`hxc_unique`**: so is the Hxc potential `v_s - v`.
* **`ksDens_fer`**: the Kohn–Sham equations. For every `v_s` there are orthonormal `C²` orbitals
  `φ_j'' = (v_s - λ_j) φ_j` such that the Kohn–Sham densities of `v_s` are exactly `Σ_j φ_j²`.
* `prodS_isGS_of`: the product of a box ground state is a ground state of free bosons;
  **`ksDens_bos`**: the Kohn–Sham density of `N` bosons is `N φ₀²`, `φ₀` the box ground state.
* **`ksRep_bos_iff`**: `ρ` is bosonic Kohn–Sham `v`-representable iff `ρ = N g²` with `g` as in
  `Box.BoxRep` (`C²`, positive inside, `g''/g` continuous on `[0, 1]`).
* `Ts`, `EHxc`, **`ks_decomposition`**: if `ρ` is an interacting ground-state density and Kohn–Sham
  `v`-representable, then `T_s(ρ)` and `E_Hxc(ρ) = F(ρ) - T_s(ρ)` are finite and
  `E = T_s + ∫ v ρ + E_Hxc`.
* **`ks_exists_one`**: for one particle every interacting ground-state density is Kohn–Sham
  `v`-representable, with `v_s = v + w`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box

variable {n : ℕ} {τ : Stat}

/-- The Kohn–Sham setting: `N` non-interacting particles on `H¹₀`. -/
noncomputable abbrev ksS (τ : Stat) (n : ℕ) : Setting (μN n) Pot :=
  settingW τ n (fun _ => 0) continuous_const

/-- Kohn–Sham `v`-representability. -/
def KSRep (τ : Stat) (n : ℕ) (ρ : Pot → ℝ) : Prop := PureVRep (ksS τ n) ρ

/-! ### Uniqueness of the Kohn–Sham and Hxc potentials -/

/-- Hohenberg–Kohn in terms of densities. -/
theorem pureDens_hk {w : Cfg n → ℝ} {hw : Continuous w} {v v' : Pot} {ρ : Pot → ℝ}
    (h : PureDens (settingW τ n w hw) v ρ) (h' : PureDens (settingW τ n w hw) v' ρ) :
    ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨Ψ, hΨ, h1, rfl⟩ := h
  obtain ⟨Ψ', hΨ', h1', hd⟩ := h'
  exact (hk_line_W_cont_stat v v').2 Ψ Ψ' hΨ hΨ' (h1.trans h1'.symm) hd.symm

/-- **The Kohn–Sham potential is unique up to a constant.** -/
theorem ks_unique {vs vs' : Pot} {ρ : Pot → ℝ} (h : PureDens (ksS τ n) vs ρ)
    (h' : PureDens (ksS τ n) vs' ρ) : ∃ k : ℝ, vs - vs' = k • one :=
  pureDens_hk h h'

/-- **The Hxc potential `v_s - v` is unique up to a constant.** -/
theorem hxc_unique {w : Cfg n → ℝ} {hw : Continuous w} {v v' vs vs' : Pot} {ρ : Pot → ℝ}
    (h : PureDens (settingW τ n w hw) v ρ) (h' : PureDens (settingW τ n w hw) v' ρ)
    (hs : PureDens (ksS τ n) vs ρ) (hs' : PureDens (ksS τ n) vs' ρ) :
    ∃ k : ℝ, (vs - v) - (vs' - v') = k • one := by
  obtain ⟨k1, hk1⟩ := pureDens_hk h h'
  obtain ⟨k2, hk2⟩ := ks_unique hs hs'
  refine ⟨k2 - k1, ?_⟩
  rw [sub_smul, ← hk1, ← hk2]
  abel

/-! ### The Kohn–Sham equations -/

/-- **The Kohn–Sham equations for fermions.** For every `v_s` there are orthonormal `C²` orbitals
`φ_j'' = (v_s - λ_j) φ_j` on `[0, 1]`, vanishing at the walls, such that a density is the density
of a normalised ground state of `v_s` iff it is `Σ_j φ_j²`. -/
theorem ksDens_fer (v : Pot) : ∃ (φ : Fin (n + 1) → ℝ → ℝ) (lam : Fin (n + 1) → ℝ),
    (∀ j, φ j ∈ Box.Dom) ∧
    (∀ j, ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv (φ j)) x = (ext v x - lam j) * φ j x) ∧
    (∀ j k, ∫ x, φ j x * φ k x ∂μ1 = if j = k then 1 else 0) ∧
    ∀ ρ, PureDens (ksS .fer n) v ρ ↔ ρ = fun u => ∫ t, ext u t * ∑ j, φ j t ^ 2 ∂μ1 := by
  obtain ⟨φ, lam, Λ, hφ, hode, hon, hle, hbound⟩ := Spectral.exists_orbitals v n
  have hnorm : ∀ j, ∫ x, φ j x * φ j x ∂μ1 = 1 := fun j => by rw [hon]; simp
  have hD := slater_mem hφ
  have hQ := Q_slater hφ hode
  have hpos := ip_slater_pos hφ hon
  have hlow : ∀ φ' ∈ DomF n, (∑ j, lam j) * ip (μ := μN n) φ' φ' ≤ Q (freeS .fer n) v φ' :=
    fun φ' h => lower_bound_fer h v hφ hbound hle hnorm
  have hGS : IsGS (freeS .fer n) v (slater φ) := ⟨hD, hpos, fun φ' hφ' => by
    rw [hQ]; nlinarith [mul_le_mul_of_nonneg_left (hlow φ' hφ') hpos.le]⟩
  have hW : IsGS (ksS .fer n) v (slater φ) := isGS_W_of_isGS hGS
  have hc : ∀ j, Continuous (φ j) := fun j => (hφ j).1.continuous
  set N : ℝ := (Nat.factorial (n + 1) : ℝ)
  have hN : 0 < N := by positivity
  set c := (√N)⁻¹
  have hc0 : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hN).ne'
  have hcc : c * c * N = 1 := by
    simp only [c]; rw [← mul_inv, Real.mul_self_sqrt hN.le, inv_mul_cancel₀ hN.ne']
  have hW1 : ip (μ := μN n) (c • slater φ) (c • slater φ) = 1 := by
    rw [ip_smul_self]
    simp only [ip]
    rw [integral_slater_sq hc hon, hcc]
  have hdens : dens (ksS .fer n) (c • slater φ) =
      fun u => ∫ t, ext u t * ∑ j, φ j t ^ 2 ∂μ1 := by
    funext u
    change ∫ x, LN n u x * ((c • slater φ) x * (c • slater φ) x) ∂μN n = _
    have e : (fun x => LN n u x * ((c • slater φ) x * (c • slater φ) x)) =
        fun x => (c * c) * (LN n u x * (slater φ x * slater φ x)) := by
      funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e, integral_const_mul, integral_LN_slater hc hon u, ← mul_assoc, hcc, one_mul]
  have hG := isGS_smul hW hc0
  refine ⟨φ, lam, hφ, hode, hon, fun ρ => ⟨?_, ?_⟩⟩
  · rintro ⟨Ψ, hΨ, h1, rfl⟩
    obtain ⟨a, ha⟩ := gs_unique_W hΨ hG
    rw [← hdens]
    exact dens_eq_of_ae_smul ha h1 hW1
  · rintro rfl
    exact ⟨_, hG, hW1, hdens⟩

/-! ### Bosons -/

/-- **The product of a normalised box ground state is a ground state of free bosons.** -/
theorem prodS_isGS_of {v : Pot} {φ : ℝ → ℝ} (hφ : IsGS Box.setting v φ)
    (h1 : ∫ t, φ t ^ 2 ∂μ1 = 1) : IsGS (freeS .bos n) v (prodS φ) := by
  obtain ⟨ψ, hψ, hE, -, -⟩ := gs_data' v
  set E := Estar v
  have hD := hφ.1
  have hip1 : ip (μ := μ1) φ φ = 1 := by rw [ip_eq_sq]; exact h1
  have hpψ := hψ.2.1
  have hQψ : Q Box.setting v ψ = E * ip (μ := μ1) ψ ψ := by
    rw [energy, div_eq_iff hpψ.ne'] at hE; exact hE
  have hQφ : Q Box.setting v φ = E := by
    have a := hφ.2.2 ψ hψ.1
    have b := hψ.2.2 φ hD
    rw [hQψ, hip1] at a b
    have a' : Q Box.setting v φ ≤ E := le_of_mul_le_mul_right (by linarith) hpψ
    have b' : E ≤ Q Box.setting v φ := le_of_mul_le_mul_right (by linarith) hpψ
    linarith
  have h1d : ∫ x, (deriv φ x ^ 2 + Wof v E x * φ x ^ 2) ∂μ1 = 0 := by
    rw [← Q_sub_eq v E hD, hQφ, hip1]; ring
  have hΨ : prodS (n := n) φ ∈ DomB n := prodS_mem hD
  have hslices : ∀ k, ∫ x, sk v E k (prodS φ) x ∂μN n = 0 := by
    intro k
    rw [slice_energy v E k hΨ]
    refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
    set c := ∏ j, φ (y j)
    have hs : (fun t => prodS φ (Fin.insertNth k t y : Cfg n)) = fun t => φ t * c := by
      funext t; exact prodS_insertNth φ k t y
    have hsm : (fun t => φ t * c) ∈ Box.Dom := hs ▸ slice_mem hΨ k y
    simp only [Pi.zero_apply]
    rw [hs, Q_sub_eq v E hsm]
    have : ∀ x, deriv (fun t => φ t * c) x ^ 2 + Wof v E x * (φ x * c) ^ 2 =
        c ^ 2 * (deriv φ x ^ 2 + Wof v E x * φ x ^ 2) := by
      intro x; rw [deriv_mul_const (diff_of_mem hD x)]; ring
    simp only [this, integral_const_mul, h1d, mul_zero]
  have hQΨ : Q (freeS .bos n) v (prodS φ) =
      (n + 1) * E * ip (μ := μN n) (prodS φ) (prodS φ) := by
    have := Q_slices v E hΨ
    simp only [hslices, Finset.sum_const_zero] at this
    linarith
  have hposΨ : 0 < ip (μ := μN n) (prodS (n := n) φ) (prodS φ) := by
    rw [ip_prodS h1]; exact one_pos
  refine ⟨hΨ, hposΨ, fun φ' hφ' => ?_⟩
  rw [hQΨ]
  nlinarith [mul_le_mul_of_nonneg_left (lower_bound_free v hφ') hposΨ.le]

lemma integral_mul_const_mul (u : Pot) (a : ℝ) (f : ℝ → ℝ) :
    ∫ t, ext u t * (a * f t) ∂μ1 = a * ∫ t, ext u t * f t ∂μ1 := by
  rw [← integral_const_mul]; congr 1; funext t; ring

/-- The lift of a normalised box ground state to `N` free bosons on `H¹₀`, with its density. -/
lemma ks_prodS {v : Pot} {φ : ℝ → ℝ} (hφ : IsGS Box.setting v φ) (h1 : ∫ t, φ t ^ 2 ∂μ1 = 1) :
    IsGS (ksS .bos n) v (prodS φ) ∧ ip (μ := μN n) (prodS (n := n) φ) (prodS φ) = 1 ∧
      dens (ksS .bos n) (prodS φ) = fun u => ∫ t, ext u t * ((n + 1) * φ t ^ 2) ∂μ1 :=
  ⟨isGS_W_of_isGS (prodS_isGS_of hφ h1), ip_prodS h1,
    funext fun u => dens_prodS hφ.1.1.continuous h1 u⟩

/-- **The Kohn–Sham density of `N` bosons** is `N φ₀²`, `φ₀` the normalised box ground state. -/
theorem ksDens_bos (v : Pot) : ∃ φ, IsGS Box.setting v φ ∧ ∫ t, φ t ^ 2 ∂μ1 = 1 ∧
    ∀ ρ, PureDens (ksS .bos n) v ρ ↔ ρ = fun u => ∫ t, ext u t * ((n + 1) * φ t ^ 2) ∂μ1 := by
  obtain ⟨φ, hφN⟩ := Box.exists_isNGS v
  have hφ : IsGS Box.setting v φ :=
    isGS_of_isNGS (fun φ _ _ => integral_nonneg fun t => mul_self_nonneg _) hφN
  have h1 : ∫ t, φ t ^ 2 ∂μ1 = 1 := by rw [← ip_eq_sq]; exact hφN.1.2
  obtain ⟨hG, hG1, hd⟩ := ks_prodS (n := n) hφ h1
  refine ⟨φ, hφ, h1, fun ρ => ⟨?_, ?_⟩⟩
  · rintro ⟨Ψ, hΨ, hΨ1, rfl⟩
    obtain ⟨a, ha⟩ := gs_unique_W hΨ hG
    rw [← hd]
    exact dens_eq_of_ae_smul ha hΨ1 hG1
  · rintro rfl
    exact ⟨_, hG, hG1, hd⟩

/-- **Bosonic Kohn–Sham `v`-representability, exactly**: `ρ = N g²` with `g` `C²`, zero at the
walls, positive inside, normalised, and `g'' = q g` on `(0, 1)` for a continuous `q`. -/
theorem ksRep_bos_iff (ρ : Pot → ℝ) :
    KSRep .bos n ρ ↔ ∃ g q, BoxRep g q ∧ ρ = fun u => ∫ t, ext u t * ((n + 1) * g t ^ 2) ∂μ1 := by
  constructor
  · rintro ⟨v, hρ⟩
    obtain ⟨φ, hφ, h1, hiff⟩ := ksDens_bos (n := n) v
    have hbox : PureVRep Box.setting (dens Box.setting φ) :=
      ⟨v, φ, hφ, by rw [ip_eq_sq]; exact h1, rfl⟩
    obtain ⟨g, q, hg, hgd⟩ := (pureVRep_box_iff _).1 hbox
    refine ⟨g, q, hg, ?_⟩
    rw [(hiff ρ).1 hρ]
    funext u
    rw [integral_mul_const_mul, integral_mul_const_mul]
    have := congrFun hgd u
    rw [dens_eq_sq] at this
    exact congrArg _ this
  · rintro ⟨g, q, hg, rfl⟩
    obtain ⟨hG, hG1, hd⟩ := ks_prodS (n := n) (isGS_of_boxRep hg).1 hg.2.2.1
    exact ⟨q, _, hG, hG1, hd⟩

/-! ### The Kohn–Sham decomposition of the energy -/

/-- The non-interacting kinetic functional `T_s = F_{w = 0}`. -/
noncomputable def Ts (τ : Stat) (n : ℕ) (ρ : Pot → ℝ) : EReal := liebF (ksS τ n) ρ

/-- The Hartree-exchange-correlation energy `E_Hxc = F - T_s`. -/
noncomputable def EHxc (τ : Stat) (w : Cfg n → ℝ) (hw : Continuous w) (ρ : Pot → ℝ) : EReal :=
  liebF (settingW τ n w hw) ρ - Ts τ n ρ

lemma isNGS_of_isGS_one {S : Setting (μN n) Pot} {v : Pot} {ψ : Cfg n → ℝ} (h : IsGS S v ψ)
    (h1 : ip (μ := μN n) ψ ψ = 1) : IsNGS S v ψ :=
  ⟨⟨h.1, h1⟩, fun φ hφ => by
    have := h.2.2 φ hφ.1
    rwa [hφ.2, h1, mul_one, mul_one] at this⟩

/-- **The Kohn–Sham decomposition.** Let `Ψ` be a normalised ground state of `v` (interaction `w`)
and `Φ` a normalised Kohn–Sham ground state of `v_s` with the same density `ρ`. Then `T_s(ρ)` is
the kinetic energy of `Φ`, `E_Hxc(ρ)` is finite, and `E = T_s(ρ) + ∫ v ρ + E_Hxc(ρ)`. -/
theorem ks_decomposition {w : Cfg n → ℝ} {hw : Continuous w} {v vs : Pot} {Ψ Φ : Cfg n → ℝ}
    (hΨ : IsGS (settingW τ n w hw) v Ψ) (hΨ1 : ip (μ := μN n) Ψ Ψ = 1)
    (hΦ : IsGS (ksS τ n) vs Φ) (hΦ1 : ip (μ := μN n) Φ Φ = 1)
    (hd : dens (ksS τ n) Φ = dens (settingW τ n w hw) Ψ) :
    Ts τ n (dens (settingW τ n w hw) Ψ) = (((ksS τ n).h0 Φ Φ : ℝ) : EReal) ∧
      EHxc τ w hw (dens (settingW τ n w hw) Ψ) =
        (((settingW τ n w hw).h0 Ψ Ψ - (ksS τ n).h0 Φ Φ : ℝ) : EReal) ∧
      Q (settingW τ n w hw) v Ψ = (ksS τ n).h0 Φ Φ + dens (settingW τ n w hw) Ψ v +
        ((settingW τ n w hw).h0 Ψ Ψ - (ksS τ n).h0 Φ Φ) := by
  have hT : Ts τ n (dens (settingW τ n w hw) Ψ) = (((ksS τ n).h0 Φ Φ : ℝ) : EReal) := by
    rw [Ts, ← hd]; exact (lieb_line_W_cont_of (isNGS_of_isGS_one hΦ hΦ1)).1
  have hF := (lieb_line_W_cont_of (isNGS_of_isGS_one hΨ hΨ1)).1
  refine ⟨hT, ?_, ?_⟩
  · rw [EHxc, hF, hT, EReal.coe_sub]
  · simp only [Q, dens]; ring

/-! ### One particle -/

lemma wPot_zero : wPot (fun _ => (0 : ℝ)) continuous_const = 0 :=
  ContinuousMap.ext fun _ => rfl

/-- **Kohn–Sham for one particle**: every interacting ground-state density is a Kohn–Sham density,
with `v_s = v + w`. -/
theorem ks_exists_one {w : Cfg 0 → ℝ} {hw : Continuous w} {v : Pot} {ρ : Pot → ℝ}
    (h : PureDens (settingW τ 0 w hw) v ρ) : PureDens (ksS τ 0) (v + wPot w hw) ρ := by
  have hb := (pureDens_one_iff v ρ).1 h
  refine (pureDens_one_iff (w := fun _ => 0) (hw := continuous_const) _ ρ).2 ?_
  rwa [wPot_zero, add_zero]

/-- Every interacting ground-state density of one particle is Kohn–Sham `v`-representable. -/
theorem ksRep_of_vrep_one {w : Cfg 0 → ℝ} {hw : Continuous w} {ρ : Pot → ℝ}
    (h : PureVRep (settingW τ 0 w hw) ρ) : KSRep τ 0 ρ :=
  let ⟨_, hv⟩ := h
  ⟨_, ks_exists_one hv⟩

end DFT.Continuum.Line
