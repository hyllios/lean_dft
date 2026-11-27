/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Applications.LiebMattisW

/-!
# The Lieb–Mattis theorem for the total spin, continuous potentials

`EspinW a` (`Line/SpinWeak`) is the lowest energy of a fermionic spin-orbital state with `H¹₀`
components and total spin `S = a - N/2`. For continuous `v` and continuous relabelling-invariant
`w`:

* `lower_bound_WC`: every such state has energy at least the sector ground-state energy `E(a, b)`
  (the multiplet argument, with the `H¹₀` variational principle in the top sector);
* `upper_bound_WC`: the sector ground state `Φ` lifts to a fermionic spin-orbital state `liftW Φ`
  of total spin exactly `S`, with energy `E(a, b)`. Its raised component lies in the
  `E`-eigenspace (`EigSp`, closed under relabelling and sums, containing `Φ` by `el_all`), so it
  would be an eigenstate of type `(a + 1, b - 1)` with energy `E(a, b) < E(a + 1, b - 1)`
  (`lieb_mattis_W`) unless it vanishes;
* **`EspinW_eq_cont`**: `E(S) = E(a, b)`; **`lieb_mattis_total_W_cont`**: `E(S) < E(S + 1)`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ}

/-! ### Relabelling on `H¹₀` -/

/-- Relabelling of `H¹₀` functions. -/
noncomputable def relW (σ : Equiv.Perm (Fin (n + 1))) : W0 n →ₗ[ℝ] W0 n where
  toFun f := ⟨fun x => (f : Cfg n → ℝ) (pm σ x), comp_pm_mem_W0 f.2 σ⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

lemma relW_apply (σ : Equiv.Perm (Fin (n + 1))) (f : W0 n) (x : Cfg n) :
    (relW σ f : Cfg n → ℝ) x = (f : Cfg n → ℝ) (pm σ x) := rfl

lemma relW_relW_inv (σ : Equiv.Perm (Fin (n + 1))) (f : W0 n) : relW σ (relW σ⁻¹ f) = f :=
  Subtype.ext (funext fun x => by simp only [relW_apply, pm_inv_pm])

section forms

variable (w : Cfg n → ℝ) (hw : Continuous w) (v : C01) (hws : ∀ σ x, w (pm σ x) = w x)

lemma BQW_symm' (f g : W0 n) : BQW w hw v f g = BQW w hw v g f := by
  rw [BQW_apply, BQW_apply, kinB_symm, potB_symm]

include hws in
lemma BQW_rel (σ : Equiv.Perm (Fin (n + 1))) (f g : W0 n) :
    BQW w hw v (relW σ f) (relW σ g) = BQW w hw v f g := by
  have h1 := BQW_pm w hw v hws (f + g) σ
  have h2 := BQW_pm w hw v hws f σ
  have h3 := BQW_pm w hw v hws g σ
  change BQW w hw v (relW σ (f + g)) (relW σ (f + g)) = _ at h1
  change BQW w hw v (relW σ f) (relW σ f) = _ at h2
  change BQW w hw v (relW σ g) (relW σ g) = _ at h3
  simp only [map_add, LinearMap.add_apply] at h1
  rw [BQW_symm' w hw v (relW σ g) (relW σ f), BQW_symm' w hw v g f] at h1
  linarith

lemma BipW_rel (σ : Equiv.Perm (Fin (n + 1))) (f g : W0 n) :
    BipW (relW σ f) (relW σ g) = BipW f g := by
  rw [BipW_apply, BipW_apply]
  exact integral_pm σ (fun x => (f : Cfg n → ℝ) x * (g : Cfg n → ℝ) x)

/-- The energy form is `h₀ + ⟨·, Σ v ·⟩`. -/
lemma BQW_eq_h0W (f g : W0 n) :
    BQW w hw v f g =
      h0W n w f g + ∫ x, LN n v x * ((f : Cfg n → ℝ) x * (g : Cfg n → ℝ) x) ∂μN n := by
  rw [BQW_apply, kinB, potB, h0W]
  have hfg := int_mul_L2 f.2.1 g.2.1
  obtain ⟨C1, hC1⟩ := ae_bound_cont (n := n) (continuous_LN v)
  obtain ⟨C2, hC2⟩ := ae_bound_cont (n := n) hw
  have e : (fun x => Vt w v x * ((f : Cfg n → ℝ) x * (g : Cfg n → ℝ) x)) = fun x =>
      w x * ((f : Cfg n → ℝ) x * (g : Cfg n → ℝ) x) +
        LN n v x * ((f : Cfg n → ℝ) x * (g : Cfg n → ℝ) x) := by
    funext x; simp only [Vt]; ring
  rw [e, integral_add (hfg.bdd_mul hw.aestronglyMeasurable hC2)
    (hfg.bdd_mul (continuous_LN v).aestronglyMeasurable hC1)]
  ring

/-- The `E`-eigenspace of the weak Hamiltonian, tested against all of `H¹₀`. -/
def EigSp (E : ℝ) : Submodule ℝ (W0 n) where
  carrier := {χ | ∀ φ, BQW w hw v χ φ = E * BipW χ φ}
  add_mem' {f g} hf hg φ := by simp only [map_add, LinearMap.add_apply, hf φ, hg φ]; ring
  zero_mem' φ := by simp
  smul_mem' c f hf φ := by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hf φ]; ring

include hws in
lemma relW_mem_EigSp {E : ℝ} {χ : W0 n} (hχ : χ ∈ EigSp w hw v E)
    (σ : Equiv.Perm (Fin (n + 1))) : relW σ χ ∈ EigSp w hw v E := fun φ => by
  conv_lhs => rw [← relW_relW_inv σ φ]
  conv_rhs => rw [← relW_relW_inv σ φ]
  rw [BQW_rel w hw v hws, BipW_rel, hχ]

include hws in
/-- A ground state of mixed symmetry lies in its eigenspace. -/
lemma mem_EigSp_of_GS {a : ℕ} {Φ : Cfg n → ℝ} (hΦ : IsGS (settingWS (ymix a) w hw) v Φ) :
    (⟨Φ, h1W_of_mem hΦ.1⟩ : W0 n) ∈
      EigSp w hw v (Q (settingWS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ) := fun φ => by
  rw [BQW_eq_h0W, BipW_apply]
  exact el_all hw hws hΦ φ.2

end forms

/-! ### The lift of a spatial state -/

open Classical in
/-- The fermionic spin-orbital state built from `Φ`: the antisymmetrisation of `δ_{s, sc a} Φ`. -/
noncomputable def liftW (a : ℕ) (Φ : W0 n) (s : SpinC n) : W0 n :=
  ∑ σ, if rel σ s = sc n a then sgn σ • relW σ Φ else 0

lemma liftW_apply (a : ℕ) (Φ : W0 n) (s : SpinC n) (x : Cfg n) :
    evW x (liftW a Φ s) =
      ∑ σ, if rel σ s = sc n a then sgn σ * (Φ : Cfg n → ℝ) (pm σ x) else 0 := by
  classical
  simp only [liftW, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs <;> simp [relW_apply]

lemma FermW_liftW (a : ℕ) (Φ : W0 n) : FermW (liftW a Φ) := by
  classical
  refine ae_of_all _ fun x ρ s => ?_
  rw [liftW_apply, liftW_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ρ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulLeft, rel_rel, ← pm_mul]
  by_cases h : rel (ρ * σ) s = sc n a
  · simp only [h, ite_true, sgn_mul]
    linear_combination (-(sgn σ * (Φ : Cfg n → ℝ) (pm (ρ * σ) x))) * sgn_mul_self ρ
  · simp [h]

lemma Pc_liftW {a : ℕ} (Φ : W0 n) (ha : a ≤ n + 1) : Pc a (liftW a Φ) = liftW a Φ := by
  classical
  funext s
  simp only [Pc_apply]
  split_ifs with hs
  · rfl
  · symm
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [ite_eq_right]
    intro h
    apply hs
    rw [← nup_rel σ s, h, nup_sc ha]

lemma liftW_sc_ae {a : ℕ} {Φ : W0 n} (hanti : AntiY a (Φ : Cfg n → ℝ)) :
    (liftW a Φ (sc n a) : Cfg n → ℝ) =ᵐ[μN n] fun x => cardY n a * (Φ : Cfg n → ℝ) x := by
  classical
  filter_upwards [altY_ae_of_antiY hanti] with x hx
  change evW x (liftW a Φ (sc n a)) = _
  rw [liftW_apply, ← hx]
  simp only [altY]
  exact Finset.sum_congr rfl fun σ _ => by simp only [rel_sc_iff]

lemma liftW_mem {w : Cfg n → ℝ} {hw : Continuous w} {v : C01} (hws : ∀ σ x, w (pm σ x) = w x)
    {E : ℝ} {a : ℕ} {Φ : W0 n} (hΦ : Φ ∈ EigSp w hw v E) (s : SpinC n) :
    liftW a Φ s ∈ EigSp w hw v E := by
  classical
  refine Submodule.sum_mem _ fun σ _ => ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (relW_mem_EigSp w hw v hws hΦ σ)
  · exact Submodule.zero_mem _

lemma Sp_mem {w : Cfg n → ℝ} {hw : Continuous w} {v : C01} {E : ℝ} {u : SpinC n → W0 n}
    (hu : ∀ s, u s ∈ EigSp w hw v E) (s : SpinC n) : Sp u s ∈ EigSp w hw v E := by
  rw [Sp_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs
  · exact hu _
  · exact Submodule.zero_mem _

/-! ### The bounds -/

section bounds

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : C01} (hws : ∀ σ x, w (pm σ x) = w x)
include hws

/-- **The lower bound** for states of total spin `S' = a' - N/2 ≥ 0`, continuous potentials. -/
theorem lower_bound_WC {a' : ℕ} (ha' : ((n : ℝ) + 1) / 2 ≤ a') (ha'N : a' ≤ n + 1)
    {Φ : Cfg n → ℝ} (hΦ : IsGS (settingWS (ymix a') w hw) v Φ)
    {u : SpinC n → W0 n} (hFu : FermW u) (heig : EigW (lamS n a') u) :
    Q (settingWS (ymix a') w hw) v Φ / ip (μ := μN n) Φ Φ * ipSW u ≤ QSW w hw v u := by
  refine multiplet_lb (BQW w hw v) BipW BipW_symm BipW_self_nonneg
    (fun f h => BQW_zero_of_BipW w hw v h)
    (fun u => FermW u ∧ EigW (lamS n a') u) (fun u hu => ⟨FermW_Sp hu.1, EigW_Sp hu.2⟩)
    (fun u c hu => ⟨FermW_Pc hu.1 c, EigW_Pc hu.2 c⟩) ha' (fun u hu s => ?_) (fun u hu s => ?_)
    (fun φ hφ hc => ?_) ⟨hFu, heig⟩
  · rw [BQW_congr w hw v (f := u s) (g := lamS n a' • u s) (f' := u s) (g' := S2 u s)
      (Filter.EventuallyEq.refl _ _) (ae_S2 hu.2 s).symm, map_smul, smul_eq_mul]
  · rw [BipW_congr (f := u s) (g := lamS n a' • u s) (f' := u s) (g' := S2 u s)
      (Filter.EventuallyEq.refl _ _) (ae_S2 hu.2 s).symm, map_smul, smul_eq_mul]
  · rw [sector_reduce_W (BQW w hw v) (fun f f' h => BQW_congr w hw v h h)
        (BQW_pm w hw v hws) hφ.1 hc,
      sector_reduce_W BipW (fun f f' h => BipW_congr h h) BipW_pm hφ.1 hc]
    set f := φ (sc n a')
    have hfD : (f : Cfg n → ℝ) ∈ DomWS (ymix (n := n) a') :=
      ⟨f.2.1, f.2.2, fun σ hσ => sym_sc_W hφ.1 a' σ hσ⟩
    have h := le_Q_of_isGS hΦ hfD
    have hQf : Q (settingWS (ymix a') w hw) v f = BQW w hw v f f := by
      rw [BQW_eq_h0W]; rfl
    rw [hQf] at h
    have hK := (card_sector_pos (n := n) (c := a') ha'N).le
    rw [BipW_apply]
    change _ ≤ _ * (BQW w hw v f f)
    have : ip (μ := μN n) (f : Cfg n → ℝ) f = ∫ x, (f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x ∂μN n :=
      rfl
    rw [this] at h
    nlinarith

/-- **The upper bound**: the sector ground state lifts to a state of total spin exactly
`S = a - N/2` with the same energy (`a ≥ b ≥ 1`). -/
theorem upper_bound_WC {a b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a)
    {Φ : Cfg n → ℝ} (hΦ : IsGS (settingWS (ymix a) w hw) v Φ) :
    ∃ u, SpinClassW a u ∧
      QSW w hw v u / ipSW u = Q (settingWS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ := by
  classical
  have ha : a ≤ n + 1 := by omega
  set E := Q (settingWS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ
  set Φw : W0 n := ⟨Φ, h1W_of_mem hΦ.1⟩
  have hΦE : Φw ∈ EigSp w hw v E := mem_EigSp_of_GS w hw v hws hΦ
  set u := liftW a Φw
  have hFu : FermW u := FermW_liftW a Φw
  have hPu : Pc a u = u := Pc_liftW Φw ha
  have huE : ∀ s, u s ∈ EigSp w hw v E := liftW_mem hws hΦE
  -- the raised state vanishes
  obtain ⟨Ψ, hΨ, -, -⟩ := exists_unique_gs_WY (n := n) (a + 1) hw v
  have hlm := lieb_mattis_W hws hab hb1 hba hΦ hΨ
  set R := Sp u (sc n (a + 1))
  have hRE : R ∈ EigSp w hw v E := Sp_mem huE _
  have hR0 : BipW R R = 0 := by
    rcases (BipW_self_nonneg R).eq_or_lt with h | hpos
    · exact h.symm
    · exfalso
      have hRD : (R : Cfg n → ℝ) ∈ DomWS (ymix (n := n) (a + 1)) :=
        ⟨R.2.1, R.2.2, fun σ hσ => sym_sc_W (FermW_Sp hFu) (a + 1) σ hσ⟩
      have hle := le_Q_of_isGS hΨ hRD
      have hQR : Q (settingWS (ymix (a + 1)) w hw) v R = E * BipW R R := by
        rw [← hRE R, BQW_eq_h0W]; rfl
      rw [hQR] at hle
      change _ * BipW R R ≤ E * BipW R R at hle
      have := (mul_le_mul_iff_of_pos_right hpos).1 hle
      linarith
  have hSp0 : ∀ s, ((Sp u s : W0 n) : Cfg n → ℝ) =ᵐ[μN n] 0 := by
    have hPSp : Pc (a + 1) (Sp u) = Sp u := by rw [← Sp_Pc, hPu]
    have hsum := sector_reduce_W BipW (fun f f' h => BipW_congr h h) BipW_pm (FermW_Sp hFu) hPSp
    rw [hR0, mul_zero] at hsum
    intro s
    refine ae_zero_of_BipW ?_
    exact (Finset.sum_eq_zero_iff_of_nonneg fun t _ => BipW_self_nonneg _).1 hsum s
      (Finset.mem_univ s)
  -- so `u` has total spin `a - N/2`
  have heig : EigW (lamS n a) u := by
    filter_upwards [ae_all_iff.2 hSp0] with x hx
    intro s
    have hS2 := congrArg (fun T : Module.End ℝ (SpinC n → W0 n) => T u s)
      (S2_eq (n := n) (V := W0 n))
    simp only [Module.End.mul_apply, LinearMap.add_apply] at hS2
    rw [hS2, Pi.add_apply, Pi.add_apply, map_add, map_add, Sm_map, Sz_map, Sz_map]
    have hz : (fun t => evW x (Sp u t)) = 0 := funext fun t => hx t
    rw [hz, map_zero]
    simp only [Pi.zero_apply, Sz_apply, smul_eq_mul, zero_add, evW_apply, Submodule.coe_smul,
      Pi.smul_apply]
    by_cases hs : nup s = a
    · simp only [Mz, hs, lamS]; ring
    · have : u s = 0 := by rw [← hPu]; simp [Pc_apply, hs]
      simp [this]
  -- energy and norm
  set K := ((Finset.univ.filter fun s : SpinC n => nup s = a).card : ℝ)
  have hK : 0 < K := card_sector_pos ha
  have hY := cardY_pos (n := n) (a := a)
  have hsc := liftW_sc_ae (a := a) (Φ := Φw) (antiY_of_mem hΦ.1)
  have hae : ((cardY n a • Φw : W0 n) : Cfg n → ℝ) =ᵐ[μN n] (u (sc n a) : Cfg n → ℝ) := by
    filter_upwards [hsc] with x hx; rw [hx]; rfl
  have hQ : QSW w hw v u = K * (cardY n a * cardY n a * BQW w hw v Φw Φw) := by
    rw [QSW, sector_reduce_W (BQW w hw v) (fun f f' h => BQW_congr w hw v h h)
      (BQW_pm w hw v hws) hFu hPu, BQW_congr w hw v hae hae]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  have hI : ipSW u = K * (cardY n a * cardY n a * BipW Φw Φw) := by
    rw [ipSW, sector_reduce_W BipW (fun f f' h => BipW_congr h h) BipW_pm hFu hPu,
      BipW_congr hae hae]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  have hipΦ : 0 < BipW Φw Φw := hΦ.2.1
  have hBQ : BQW w hw v Φw Φw = E * BipW Φw Φw := hΦE Φw
  refine ⟨u, ⟨hFu, by rw [hI]; positivity, heig⟩, ?_⟩
  rw [hQ, hI, hBQ]
  field_simp

/-- **`E(S)` is the ground-state energy of the spatial sector `S_z = S`**, continuous potentials
(`a ≥ b ≥ 1`). -/
theorem EspinW_eq_cont {a b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a)
    {Φ : Cfg n → ℝ} (hΦ : IsGS (settingWS (ymix a) w hw) v Φ) :
    EspinW w hw v a = ((Q (settingWS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ : ℝ) : EReal) := by
  refine le_antisymm ?_ (le_iInf₂ fun u hu => ?_)
  · obtain ⟨u, hu, he⟩ := upper_bound_WC hws hab hb1 hba hΦ
    rw [← he]; exact iInf₂_le u hu
  · refine EReal.coe_le_coe_iff.2 ?_
    have hlb := lower_bound_WC hws (a' := a) (by
      have : (b : ℝ) ≤ a := by exact_mod_cast hba
      have : (a : ℝ) + b = n + 1 := by exact_mod_cast hab
      linarith) (by omega) hΦ hu.1 hu.2.2
    rw [le_div_iff₀ hu.2.1]; linarith

/-- **The Lieb–Mattis theorem for the total spin, continuous potentials**: `E(S) < E(S + 1)` for
`S ≥ 0`, over fermionic spin-orbital states of finite kinetic energy. -/
theorem lieb_mattis_total_W_cont {a b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a) :
    EspinW w hw v a < EspinW w hw v (a + 1) := by
  obtain ⟨Φ, hΦ, -, -⟩ := exists_unique_gs_WY (n := n) a hw v
  obtain ⟨Ψ, hΨ, -, -⟩ := exists_unique_gs_WY (n := n) (a + 1) hw v
  have hlm := lieb_mattis_W hws hab hb1 hba hΦ hΨ
  rw [EspinW_eq_cont hws hab hb1 hba hΦ]
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hlm) (le_iInf₂ fun u hu => ?_)
  refine EReal.coe_le_coe_iff.2 ?_
  have hlb := lower_bound_WC hws (a' := a + 1) (by
    have : (b : ℝ) ≤ a := by exact_mod_cast hba
    have : (a : ℝ) + b = n + 1 := by exact_mod_cast hab
    push_cast; linarith) (by omega) hΨ hu.1 hu.2.2
  rw [le_div_iff₀ hu.2.1]; linarith

end bounds

end DFT.Continuum.Line
