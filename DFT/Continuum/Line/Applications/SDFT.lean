/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.HK.HKY
import DFT.Continuum.Line.HK.Nondeg

/-!
# Spin-density functional theory on a line

`N` spin-½ fermions on `[0, 1]` with a spin-independent interaction `w` (continuous), a scalar
potential `v` and a collinear magnetic field `b` coupling to `σ_z`:
`H = -Δ + Σ_k (v(x_k) + σ_k b(x_k)) + w`. The Hamiltonian conserves `S_z`; in the sector with `a`
spins up the spatial wave function has the Young symmetry `ymix a`, the first `a` particles see
`v↑ = v + b` and the others `v↓ = v - b` (`LS a (v↑, v↓)`), and the spin densities `(ρ, m)` are
equivalent to `(ρ↑, ρ↓)`, the density functional on pairs `(v↑, v↓)`.

* `settingSD a w hw`: the `H¹₀` setting of the sector, with potentials in `C01 × C01`;
* `isGS_SD_iff`: ground states of `(v↑, v↓)` are the ground states of `settingWS (ymix a)` with
  interaction `w + LS a (v↑, v↓)`; hence existence (`exists_isNGS_SD`), unique continuation
  (`gs_ne_zero_SD`) and nondegeneracy (`gs_unique_SD`) for continuous potentials;
* `sep_SD`, `rigid_two`: separation, and rigidity for two species;
* **`hk_SD`**: equal norms and equal spin densities force `v↑ - v↑'` to be constant when `a ≥ 1`
  and `v↓ - v↓'` to be constant when `a ≤ N - 1`;
* **`sdft_hk_mixed`**: in a sector with both spin species, `(ρ, m)` determines `v` and `b` up to
  constants; **`sdft_hk_polarised`**: in the fully polarised sector it determines only `v + b`,
  and **`sdft_nonunique`**: there `(v + d, b - d)` has the same ground states for every potential
  `d`, so nothing more can be determined.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ} {a : ℕ}

/-! ### The spin-resolved coupling -/

/-- `Σ_{k < a} v↑(x_k) + Σ_{k ≥ a} v↓(x_k)`. -/
noncomputable def LS (a : ℕ) : C01 × C01 →ₗ[ℝ] (Cfg n → ℝ) where
  toFun p := fun x => ∑ k : Fin (n + 1), SturmLiouville.iccExt (if (k : ℕ) < a then p.1 else p.2) (x k)
  map_add' p q := by
    funext x
    simp only [Pi.add_apply, ← Finset.sum_add_distrib, Prod.fst_add, Prod.snd_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp [SturmLiouville.iccExt]
  map_smul' r p := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, Prod.smul_fst,
      Prod.smul_snd]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp [SturmLiouville.iccExt]

lemma LS_apply (p : C01 × C01) (x : Cfg n) :
    LS a p x = ∑ k : Fin (n + 1), SturmLiouville.iccExt (if (k : ℕ) < a then p.1 else p.2) (x k) := rfl

lemma continuous_LS (p : C01 × C01) : Continuous (LS (n := n) a p) :=
  show Continuous fun x : Cfg n => ∑ k : Fin (n + 1),
      SturmLiouville.iccExt (if (k : ℕ) < a then p.1 else p.2) (x k) from
    continuous_finsetSum _ fun k _ => (continuous_iccExt _).comp (continuous_apply k)

lemma LS_pm (p : C01 × C01) {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) (x : Cfg n) :
    LS a p (pm σ x) = LS a p x := by
  simp only [LS_apply, pm_apply]
  rw [← Equiv.sum_comp σ (fun k => SturmLiouville.iccExt (if (k : ℕ) < a then p.1 else p.2) (x k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hσ k]

/-- In the fully polarised sector only `v↑` couples. -/
lemma LS_full (u d : C01) : LS (n := n) (n + 1) (u, d) = LN n u := by
  funext x
  simp only [LS_apply, LN, LinearMap.coe_mk, AddHom.coe_mk]
  exact Finset.sum_congr rfl fun k _ => by simp [k.isLt]

/-! ### The setting -/

/-- The sector with `a` spins up, with spin-resolved potentials `(v↑, v↓)`. -/
noncomputable def settingSD (a : ℕ) (w : Cfg n → ℝ) (hw : Continuous w) :
    Setting (μN n) (C01 × C01) where
  D := DomWS (ymix a)
  h0 := h0W n w
  h0_add := (settingWS (ymix a) w hw).h0_add
  h0_smul := (settingWS (ymix a) w hw).h0_smul
  h0_symm := (settingWS (ymix a) w hw).h0_symm
  L := LS a
  int_L p ψ φ hψ hφ := by
    obtain ⟨C, hC⟩ := ae_bound_cont (continuous_LS (n := n) (a := a) p)
    exact (int_mul_L2 hψ.1 hφ.1).bdd_mul (continuous_LS p).aestronglyMeasurable hC
  int_sq ψ φ hψ hφ := int_mul_L2 hψ.1 hφ.1

section setting

variable {w : Cfg n → ℝ} {hw : Continuous w}

lemma continuous_wLS (hw : Continuous w) (p : C01 × C01) :
    Continuous fun x => w x + LS (n := n) a p x := hw.add (continuous_LS p)

/-- The energy of `(v↑, v↓)` is the energy at zero potential with interaction `w + LS (v↑, v↓)`. -/
lemma Q_SD_eq (p : C01 × C01) {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomWS (ymix (n := n) a)) :
    Q (settingSD a w hw) p ψ = Q (settingWS (ymix a) _ (continuous_wLS (a := a) hw p)) 0 ψ := by
  change h0W n w ψ ψ + ∫ x, LS a p x * (ψ x * ψ x) ∂μN n =
    h0W n (fun x => w x + LS a p x) ψ ψ + ∫ x, LN n 0 x * (ψ x * ψ x) ∂μN n
  have hsq := int_mul_L2 hψ.1 hψ.1
  obtain ⟨C1, hC1⟩ := ae_bound_cont (n := n) hw
  obtain ⟨C2, hC2⟩ := ae_bound_cont (continuous_LS (n := n) (a := a) p)
  have e : ∫ x, (w x + LS a p x) * (ψ x * ψ x) ∂μN n =
      ∫ x, w x * (ψ x * ψ x) ∂μN n + ∫ x, LS a p x * (ψ x * ψ x) ∂μN n := by
    rw [← integral_add (hsq.bdd_mul hw.aestronglyMeasurable hC1)
      (hsq.bdd_mul (continuous_LS p).aestronglyMeasurable hC2)]
    congr 1; funext x; ring
  simp only [h0W, map_zero, Pi.zero_apply, zero_mul, integral_zero, add_zero, e]
  ring

/-- **Ground states of the sector are ground states of a `settingWS` problem.** -/
theorem isGS_SD_iff (p : C01 × C01) {ψ : Cfg n → ℝ} :
    IsGS (settingSD a w hw) p ψ ↔
      IsGS (settingWS (ymix a) _ (continuous_wLS (a := a) hw p)) 0 ψ := by
  constructor
  · rintro ⟨hD, hpos, hmin⟩
    refine ⟨hD, hpos, fun φ hφ => ?_⟩
    have := hmin φ hφ
    rwa [Q_SD_eq p hD, Q_SD_eq p hφ] at this
  · rintro ⟨hD, hpos, hmin⟩
    refine ⟨hD, hpos, fun φ hφ => ?_⟩
    have := hmin φ hφ
    rwa [← Q_SD_eq p hD, ← Q_SD_eq p hφ] at this

theorem isNGS_SD_iff (p : C01 × C01) {ψ : Cfg n → ℝ} :
    IsNGS (settingSD a w hw) p ψ ↔
      IsNGS (settingWS (ymix a) _ (continuous_wLS (a := a) hw p)) 0 ψ := by
  constructor
  · rintro ⟨⟨hD, hn⟩, hmin⟩
    refine ⟨⟨hD, hn⟩, fun φ hφ => ?_⟩
    have := hmin φ hφ
    rwa [Q_SD_eq p hD, Q_SD_eq p hφ.1] at this
  · rintro ⟨⟨hD, hn⟩, hmin⟩
    refine ⟨⟨hD, hn⟩, fun φ hφ => ?_⟩
    have := hmin φ hφ
    rwa [← Q_SD_eq p hD, ← Q_SD_eq p hφ.1] at this

/-- **Ground states exist** for all continuous `v↑`, `v↓`, `w`. -/
theorem exists_isNGS_SD (hw : Continuous w) (p : C01 × C01) :
    ∃ ψ, IsNGS (settingSD a w hw) p ψ :=
  (exists_isNGS_WY_cont a (continuous_wLS (a := a) hw p) 0).imp fun _ h => (isNGS_SD_iff p).2 h

/-- **Unique continuation** in the sector. -/
theorem gs_ne_zero_SD {p : C01 × C01} {ψ : Cfg n → ℝ} (hψ : IsGS (settingSD a w hw) p ψ) :
    ∀ᵐ x ∂μN n, ψ x ≠ 0 :=
  gs_ne_zero_WY ((isGS_SD_iff p).1 hψ)

/-- **Nondegeneracy** in the sector, for all continuous `v↑`, `v↓`, `w`. -/
theorem gs_unique_SD {p : C01 × C01} {ψ φ : Cfg n → ℝ} (hψ : IsGS (settingSD a w hw) p ψ)
    (hφ : IsGS (settingSD a w hw) p φ) : ∃ c : ℝ, ψ =ᵐ[μN n] c • φ :=
  gs_unique_WY ((isGS_SD_iff p).1 hψ) ((isGS_SD_iff p).1 hφ)

lemma h0SD_null (hw : Continuous w) {φ : Cfg n → ℝ} (hφ : φ ∈ DomWS (ymix (n := n) a))
    (h0 : ip (μ := μN n) φ φ = 0) : 0 ≤ (settingSD a w hw).h0 φ φ :=
  h0W_null (s := ymix a) hw hφ h0

/-- **Separation** in the sector. -/
theorem sep_SD (w : Cfg n → ℝ) (hw : Continuous w) : Sep (settingSD (n := n) a w hw) := by
  intro p c ψ hψ h
  set g : Cfg n → ℝ := fun x => (LS a p x - c) * ψ x
  have hgc : Continuous fun x => LS (n := n) a p x - c := (continuous_LS p).sub continuous_const
  obtain ⟨C, hC⟩ := ae_bound_cont hgc
  have hg : Integrable g (μN n) :=
    (hψ.1.integrable one_le_two).bdd_mul hgc.aestronglyMeasurable hC
  have hgs : ∀ σ, YG a σ → ∀ᵐ x ∂μN n, g (pm σ x) = sgn σ * g x := fun σ hσ => by
    filter_upwards [hψ.2.2 σ hσ] with x hx
    change ψ (pm σ x) = sgn σ * ψ x at hx
    simp only [g, LS_pm p hσ, hx]; ring
  exact ae_eq_zero_of_integral_altY_L1 hg hgs h

end setting

/-! ### Rigidity for two species -/

/-- A continuous potential with `ext v` constant on `(0, 1)` is a constant. -/
lemma const_of_ext_eq {v : C01} {c : ℝ} (h : ∀ t ∈ Ioo (0 : ℝ) 1, SturmLiouville.iccExt v t = c) :
    ∃ k : ℝ, v = k • one := by
  have hC : EqOn (SturmLiouville.iccExt v) (fun _ => c) (Icc 0 1) :=
    EqOn.of_subset_closure h (continuous_iccExt v).continuousOn continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one])
  refine ⟨c, ?_⟩
  ext t
  have := hC t.2
  simp only [SturmLiouville.iccExt, projIcc_val] at this
  simp [one, this]

/-- **Rigidity for two species.** If `Σ_{k<a} v↑(x_k) + Σ_{k≥a} v↓(x_k)` is a.e. constant on the
cube, then `v↑` is constant when `a ≥ 1` and `v↓` is constant when `a ≤ N - 1`. -/
theorem rigid_two {p : C01 × C01} {c : ℝ} (h : LS (n := n) a p =ᵐ[μN n] fun _ => c) :
    (1 ≤ a → ∃ k : ℝ, p.1 = k • one) ∧ (a < n + 1 → ∃ k : ℝ, p.2 = k • one) := by
  have hO : EqOn (LS (n := n) a p) (fun _ => c) (Cube n) :=
    Measure.eqOn_open_of_ae_eq h isOpen_cube (continuous_LS p).continuousOn continuousOn_const
  set x0 : Cfg n := fun _ => 1 / 2
  have hx0 : x0 ∈ Cube n := fun _ _ => ⟨by norm_num, by norm_num⟩
  -- moving one particle `k0` inside the cube
  have key : ∀ k0 : Fin (n + 1), ∀ t ∈ Ioo (0 : ℝ) 1,
      SturmLiouville.iccExt (if (k0 : ℕ) < a then p.1 else p.2) t =
        SturmLiouville.iccExt (if (k0 : ℕ) < a then p.1 else p.2) (1 / 2) := by
    intro k0 t ht
    have hxt : Function.update x0 k0 t ∈ Cube n := fun j _ => by
      by_cases hj : j = k0
      · subst hj; simpa using ht
      · simpa [Function.update_of_ne hj] using hx0 j (mem_univ j)
    have h1 := hO hxt
    have h2 := hO hx0
    simp only at h1 h2
    have hd : LS a p (Function.update x0 k0 t) - LS a p x0 =
        SturmLiouville.iccExt (if (k0 : ℕ) < a then p.1 else p.2) t -
          SturmLiouville.iccExt (if (k0 : ℕ) < a then p.1 else p.2) (1 / 2) := by
      rw [LS_apply, LS_apply, ← Finset.sum_sub_distrib, Finset.sum_eq_single k0]
      · simp [x0]
      · intro k _ hk; simp [Function.update_of_ne hk]
      · intro h; exact absurd (Finset.mem_univ k0) h
    linarith
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · have := key ⟨0, Nat.succ_pos n⟩
    simp only [show (0 : ℕ) < a from ha, ↓reduceIte] at this
    exact const_of_ext_eq this
  · have := key (Fin.last n)
    simp only [Fin.val_last, show ¬ (n < a) by omega, ↓reduceIte] at this
    exact const_of_ext_eq this

/-! ### Hohenberg–Kohn for spin densities -/

section hk

variable {w : Cfg n → ℝ} {hw : Continuous w}

/-- **Hohenberg–Kohn for the spin-resolved densities.** Ground states of `(v↑, v↓)` and
`(v↑', v↓')` in the sector with `a` spins up, with the same norm and the same densities
`(ρ↑, ρ↓)`, force `v↑ - v↑'` to be constant if `a ≥ 1` and `v↓ - v↓'` to be constant if
`a ≤ N - 1`. -/
theorem hk_SD {p p' : C01 × C01} {ψ ψ' : Cfg n → ℝ} (hψ : IsGS (settingSD a w hw) p ψ)
    (hψ' : IsGS (settingSD a w hw) p' ψ') (hn : ip (μ := μN n) ψ ψ = ip (μ := μN n) ψ' ψ')
    (hd : dens (settingSD a w hw) ψ = dens (settingSD a w hw) ψ') :
    (1 ≤ a → ∃ k : ℝ, p.1 - p'.1 = k • one) ∧ (a < n + 1 → ∃ k : ℝ, p.2 - p'.2 = k • one) := by
  obtain ⟨c, hL⟩ := L_ae_const_of_ucp (sep_SD w hw) hψ (weak_hk hψ hψ' hn hd)
    (gs_ne_zero_SD hψ)
  exact rigid_two hL

/-- The spin-resolved potentials of a scalar potential `v` and a field `b`: `(v + b, v - b)`. -/
def pvb (v b : C01) : C01 × C01 := (v + b, v - b)

/-- The density `ρ`, as a functional on scalar potentials: `v ↦ ∫ Σ_k v(x_k) ψ²`. -/
noncomputable def rhoSD (a : ℕ) (w : Cfg n → ℝ) (hw : Continuous w) (ψ : Cfg n → ℝ) (v : C01) :
    ℝ :=
  dens (settingSD a w hw) ψ (pvb v 0)

/-- The magnetisation `m`, as a functional on fields: `b ↦ ∫ Σ_k σ_k b(x_k) ψ²`. -/
noncomputable def magSD (a : ℕ) (w : Cfg n → ℝ) (hw : Continuous w) (ψ : Cfg n → ℝ) (b : C01) :
    ℝ :=
  dens (settingSD a w hw) ψ (pvb 0 b)

lemma dens_SD_add {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomWS (ymix (n := n) a)) (p q : C01 × C01) :
    dens (settingSD a w hw) ψ (p + q) =
      dens (settingSD a w hw) ψ p + dens (settingSD a w hw) ψ q := by
  simp only [dens, pf, map_add, Pi.add_apply, add_mul]
  exact integral_add ((settingSD a w hw).int_L p ψ ψ hψ hψ)
    ((settingSD a w hw).int_L q ψ ψ hψ hψ)

/-- **Equal `(ρ, m)` means equal spin-resolved densities.** -/
theorem dens_SD_eq_of_rho_mag {ψ ψ' : Cfg n → ℝ} (hψ : ψ ∈ DomWS (ymix (n := n) a))
    (hψ' : ψ' ∈ DomWS (ymix (n := n) a)) (hρ : ∀ v, rhoSD a w hw ψ v = rhoSD a w hw ψ' v)
    (hm : ∀ b, magSD a w hw ψ b = magSD a w hw ψ' b) :
    dens (settingSD a w hw) ψ = dens (settingSD a w hw) ψ' := by
  funext p
  have e : p = pvb ((1 / 2 : ℝ) • (p.1 + p.2)) 0 + pvb 0 ((1 / 2 : ℝ) • (p.1 - p.2)) := by
    refine Prod.ext ?_ ?_ <;> simp only [pvb, Prod.fst_add, Prod.snd_add] <;> module
  rw [e, dens_SD_add hψ, dens_SD_add hψ']
  exact congrArg₂ (· + ·) (hρ _) (hm _)

/-- **SDFT, both spin species present.** In a sector with `1 ≤ a ≤ N - 1` spins up, ground states
of `(v, b)` and `(v', b')` with the same norm, the same density `ρ` and the same magnetisation `m`
force `v - v'` and `b - b'` to be constant. -/
theorem sdft_hk_mixed (ha1 : 1 ≤ a) (ha2 : a < n + 1) {v b v' b' : C01} {ψ ψ' : Cfg n → ℝ}
    (hψ : IsGS (settingSD a w hw) (pvb v b) ψ) (hψ' : IsGS (settingSD a w hw) (pvb v' b') ψ')
    (hn : ip (μ := μN n) ψ ψ = ip (μ := μN n) ψ' ψ')
    (hρ : ∀ u, rhoSD a w hw ψ u = rhoSD a w hw ψ' u)
    (hm : ∀ u, magSD a w hw ψ u = magSD a w hw ψ' u) :
    (∃ k : ℝ, v - v' = k • one) ∧ ∃ k : ℝ, b - b' = k • one := by
  obtain ⟨h1, h2⟩ := hk_SD hψ hψ' hn (dens_SD_eq_of_rho_mag hψ.1 hψ'.1 hρ hm)
  obtain ⟨k1, hk1⟩ := h1 ha1
  obtain ⟨k2, hk2⟩ := h2 ha2
  simp only [pvb] at hk1 hk2
  refine ⟨⟨(k1 + k2) / 2, ?_⟩, ⟨(k1 - k2) / 2, ?_⟩⟩
  · have : v - v' = (1 / 2 : ℝ) • ((v + b - (v' + b')) + (v - b - (v' - b'))) := by
      module
    rw [this, hk1, hk2]; module
  · have : b - b' = (1 / 2 : ℝ) • ((v + b - (v' + b')) - (v - b - (v' - b'))) := by
      module
    rw [this, hk1, hk2]; module

/-- **SDFT, fully polarised.** In the sector with all `N` spins up, equal norms, densities and
magnetisations force only `v + b` to agree up to a constant. -/
theorem sdft_hk_polarised {v b v' b' : C01} {ψ ψ' : Cfg n → ℝ}
    (hψ : IsGS (settingSD (n + 1) w hw) (pvb v b) ψ)
    (hψ' : IsGS (settingSD (n + 1) w hw) (pvb v' b') ψ')
    (hn : ip (μ := μN n) ψ ψ = ip (μ := μN n) ψ' ψ')
    (hρ : ∀ u, rhoSD (n + 1) w hw ψ u = rhoSD (n + 1) w hw ψ' u)
    (hm : ∀ u, magSD (n + 1) w hw ψ u = magSD (n + 1) w hw ψ' u) :
    ∃ k : ℝ, (v + b) - (v' + b') = k • one :=
  (hk_SD hψ hψ' hn (dens_SD_eq_of_rho_mag hψ.1 hψ'.1 hρ hm)).1 (by omega)

/-- **The SDFT non-uniqueness.** In the fully polarised sector, `(v + d, b - d)` has exactly the
ground states of `(v, b)`, for every potential `d`: the spin densities cannot determine `v` and `b`
separately. -/
theorem sdft_nonunique (v b d : C01) {ψ : Cfg n → ℝ} :
    IsGS (settingSD (n + 1) w hw) (pvb v b) ψ ↔
      IsGS (settingSD (n + 1) w hw) (pvb (v + d) (b - d)) ψ := by
  have hL : (settingSD (n := n) (n + 1) w hw).L (pvb v b) =
      (settingSD (n := n) (n + 1) w hw).L (pvb (v + d) (b - d)) := by
    change LS (n + 1) (v + b, v - b) = LS (n + 1) (v + d + (b - d), v + d - (b - d))
    rw [LS_full, LS_full, show v + d + (b - d) = v + b by abel]
  have hQ : ∀ φ, Q (settingSD (n := n) (n + 1) w hw) (pvb v b) φ =
      Q (settingSD (n + 1) w hw) (pvb (v + d) (b - d)) φ := fun φ => by
    simp only [Q, pf, hL]
  simp only [IsGS, hQ]

end hk

end DFT.Continuum.Line
