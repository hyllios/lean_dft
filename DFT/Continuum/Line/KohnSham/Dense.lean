/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.General.Ekeland
import DFT.Continuum.Line.KohnSham.KohnSham

/-!
# `v`-representable densities are dense (`N` particles on `H¹₀`)

For `N` bosons or fermions on `[0, 1]` with continuous `v` and any continuous interaction `w`,
pure-state `v`-representable densities are dense, in the dual norm of `C([0, 1])`, among all
densities of finite Lieb functional, in particular among all `N`-representable densities. With
`w = 0` this says that **Kohn–Sham `v`-representable densities are dense**.

The `N = 1` proof (`Box/Diff`) used shooting. Here the converse of Hellmann–Feynman comes from
compactness in coefficient space instead: along `v + t u`, `t → 0`, the sine coefficients of the
ground states have bounded kinetic energy, so a subsequence converges in `ℓ²`; the limit is a
ground state of `v`, which is unique, so the densities converge.

* `gsErW`: the ground-state energy as a real function; `densLW`: the density of a normalised state
  as a functional of norm `≤ N`.
* `supergrad_of_isNGSW` (Hellmann–Feynman), `gsErW_lipschitz`, `gsErW_concave`,
  `liebF_of_supergradW`, `dense_supergradW` (Brøndsted–Rockafellar).
* `exists_subseq_adm`: compactness of admissible coefficient sequences with bounded kinetic energy.
* `tendsto_dens_line`: ground-state densities are continuous along lines, up to a subsequence.
* **`supergrad_eqW`**: every supergradient of `E` at `v` is the density of the ground state of `v`.
* **`dense_pureVRepW`**, **`dense_pureVRepW_of_nst`**: `v`-representable densities are dense.
* **`ks_dense`**: Kohn–Sham `v`-representable densities are dense among `N`-representable ones.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w}

/-! ### Compactness in coefficient space -/

/-- Normalised admissible sequences with bounded kinetic energy have a subsequence converging in
`ℓ²` to a normalised admissible sequence. -/
theorem exists_subseq_adm {s : SymT n} {c : ℕ → (Fin (n + 1) → ℕ) → ℝ} (hc : ∀ j, Adm s (c j))
    {M : ℝ} (hM : ∀ j, ∑' m, lam m * c j m ^ 2 ≤ M) :
    ∃ (a : (Fin (n + 1) → ℕ) → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Adm s a ∧
      (∀ m, Tendsto (fun j => c (φ j) m) atTop (𝓝 (a m))) ∧
      Tendsto (fun j => ∑' m, (c (φ j) m - a m) ^ 2) atTop (𝓝 0) := by
  have hbox : ∀ j, c j ∈ Set.univ.pi fun _ : Fin (n + 1) → ℕ => Set.Icc (-1 : ℝ) 1 := fun j =>
    Set.mem_univ_pi.2 fun m => by
      have h : c j m ^ 2 ≤ 1 :=
        (hc j).norm ▸ (hc j).sq.le_tsum m (fun m' _ => sq_nonneg (c j m'))
      exact abs_le.1 ((sq_le_one_iff_abs_le_one _).1 h)
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ : Fin (n + 1) → ℕ => isCompact_Icc).tendsto_subseq hbox
  rw [tendsto_pi_nhds] at hlim
  set d := fun j => c (φ j) with hd_def
  have hd : ∀ j, Adm s (d j) := fun j => hc (φ j)
  have hdM : ∀ j, ∑' m, lam m * d j m ^ 2 ≤ M := fun j => hM (φ j)
  have hlim' : ∀ m, Tendsto (fun j => d j m) atTop (𝓝 (a m)) := hlim
  have hak := lim_sum_le hlim' (fun m => lam_nonneg m) (fun j => (hd j).kin) hdM
  have has := lim_sum_le hlim' (w := fun _ => 1) (B := 1) (fun _ => zero_le_one)
    (fun j => by simpa using (hd j).sq) (fun j => by simpa using (hd j).norm.le)
  simp only [one_mul] at has
  have hsym : InS s a := fun σ hσ m =>
    tendsto_nhds_unique (hlim' (pmI σ m))
      (by simpa only [(hd _).sym σ hσ m] using (hlim' m).const_mul (s.χ σ))
  have hnorm : ∑' m, a m ^ 2 = 1 := by
    refine le_antisymm has.2 (le_of_forall_pos_lt_add fun ε hε => ?_)
    obtain ⟨K, hK⟩ := exists_div_lt (M := M) hε
    have hT : 1 - M / ((K : ℝ) + 1) ≤ ∑ m ∈ box K, a m ^ 2 := by
      refine ge_of_tendsto' (tendsto_finsetSum (box (n := n) K) fun m _ => (hlim' m).pow 2)
        fun j => ?_
      have := sum_box_ge (hd j).sq (hd j).kin (hdM j) K
      rwa [(hd j).norm] at this
    have := has.1.sum_le_tsum (box K) fun m _ => sq_nonneg (a m)
    linarith
  exact ⟨a, φ, hφ, ⟨⟨has.1, hak.1, hsym⟩, hnorm⟩, hlim',
    tendsto_l2 hlim' (fun j => (hd j).sq) (fun j => (hd j).kin) hdM has.1 hak.1 hak.2⟩

lemma tendsto_Bf {V : Cfg n → ℝ} {C : ℝ} (hK : KBd V C) {d : ℕ → (Fin (n + 1) → ℕ) → ℝ}
    {a : (Fin (n + 1) → ℕ) → ℝ} (hds : ∀ j, Summable fun m => d j m ^ 2)
    (hd1 : ∀ j, ∑' m, d j m ^ 2 = 1) (has : Summable fun m => a m ^ 2) (ha1 : ∑' m, a m ^ 2 = 1)
    (hl2 : Tendsto (fun j => ∑' m, (d j m - a m) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun j => Bf V (d j) (d j)) atTop (𝓝 (Bf V a a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun j => √(C * (∑' m, (d j m - a m) ^ 2) * 1) +
      √(C * 1 * ∑' m, (d j m - a m) ^ 2)) atTop (𝓝 0) := by
    have h1 := ((tendsto_const_nhds (x := C)).mul hl2).mul_const 1
    have h2 := (tendsto_const_nhds (x := C * 1)).mul hl2
    simpa using h1.sqrt.add h2.sqrt
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hb
  have := KBd.abs_Bf_sub_le hK (hds j) has
  rwa [hd1 j, ha1] at this

lemma kBd_cont {V : Cfg n → ℝ} (hV : Continuous V) : ∃ C, KBd V C := by
  obtain ⟨B, hB⟩ := (isCompact_univ_pi fun _ => isCompact_Icc :
    IsCompact (CubeC n)).exists_bound_of_continuousOn hV.continuousOn
  exact ⟨_, kBd_of_continuous hV (B := B) fun x hx => by simpa [Real.norm_eq_abs] using hB x hx⟩

/-! ### The ground-state energy and the density functional -/

/-- The ground-state energy, as a real number. -/
noncomputable def gsErW (τ : Stat) (n : ℕ) (w : Cfg n → ℝ) (hw : Continuous w) (v : Pot) : ℝ :=
  Q (settingW τ n w hw) v (Classical.choose (exists_isNGS_W_cont (n := n) (τ := τ) hw v))

lemma gsErW_spec (v : Pot) : IsNGS (settingW τ n w hw) v
    (Classical.choose (exists_isNGS_W_cont (n := n) (τ := τ) hw v)) :=
  Classical.choose_spec (exists_isNGS_W_cont (n := n) (τ := τ) hw v)

lemma gsErW_le (v : Pot) {ψ : Cfg n → ℝ} (hψ : ψ ∈ Nst (settingW τ n w hw)) :
    gsErW τ n w hw v ≤ Q (settingW τ n w hw) v ψ :=
  (gsErW_spec v).2 ψ hψ

lemma gsErW_eq_of_isNGS {v : Pot} {ψ : Cfg n → ℝ} (h : IsNGS (settingW τ n w hw) v ψ) :
    gsErW τ n w hw v = Q (settingW τ n w hw) v ψ :=
  le_antisymm (gsErW_le v h.1) (h.2 _ (gsErW_spec v).1)

lemma gsE_eqW (v : Pot) : gsE (settingW τ n w hw) v = ((gsErW τ n w hw v : ℝ) : EReal) :=
  gsE_of_isNGS (gsErW_spec v)

lemma abs_LN_le (u : Pot) (x : Cfg n) : |LN n u x| ≤ ((n : ℝ) + 1) * ‖u‖ := by
  change |∑ k, Box.ext u (x k)| ≤ _
  calc |∑ k, Box.ext u (x k)| ≤ ∑ k : Fin (n + 1), |Box.ext u (x k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (n + 1), ‖u‖ := Finset.sum_le_sum fun k _ => abs_ext_le u _
    _ = _ := by simp

section densW

variable {ψ : Cfg n → ℝ}

lemma densW_add (hψ : ψ ∈ DomW τ n) (u u' : Pot) :
    dens (settingW τ n w hw) ψ (u + u') =
      dens (settingW τ n w hw) ψ u + dens (settingW τ n w hw) ψ u' := by
  have i1 : Integrable (fun x => LN n u x * (ψ x * ψ x)) (μN n) :=
    (settingW τ n w hw).int_L u ψ ψ hψ hψ
  have i2 : Integrable (fun x => LN n u' x * (ψ x * ψ x)) (μN n) :=
    (settingW τ n w hw).int_L u' ψ ψ hψ hψ
  change ∫ x, LN n (u + u') x * (ψ x * ψ x) ∂μN n =
    ∫ x, LN n u x * (ψ x * ψ x) ∂μN n + ∫ x, LN n u' x * (ψ x * ψ x) ∂μN n
  rw [← integral_add i1 i2]
  congr 1; funext x; rw [map_add, Pi.add_apply, add_mul]

lemma densW_smul (a : ℝ) (u : Pot) :
    dens (settingW τ n w hw) ψ (a • u) = a * dens (settingW τ n w hw) ψ u := by
  change ∫ x, LN n (a • u) x * (ψ x * ψ x) ∂μN n = a * ∫ x, LN n u x * (ψ x * ψ x) ∂μN n
  rw [← integral_const_mul]
  congr 1; funext x; rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

lemma abs_densW_le (hψ : ψ ∈ Nst (settingW τ n w hw)) (u : Pot) :
    |dens (settingW τ n w hw) ψ u| ≤ ((n : ℝ) + 1) * ‖u‖ := by
  have hsq : Integrable (fun x => ψ x * ψ x) (μN n) := int_mul_L2 hψ.1.1 hψ.1.1
  have h1 : ∫ x, ψ x * ψ x ∂μN n = 1 := hψ.2
  change |∫ x, LN n u x * (ψ x * ψ x) ∂μN n| ≤ _
  rw [← Real.norm_eq_abs]
  calc ‖∫ x, LN n u x * (ψ x * ψ x) ∂μN n‖
      ≤ ∫ x, ((n : ℝ) + 1) * ‖u‖ * (ψ x * ψ x) ∂μN n := by
        refine norm_integral_le_of_norm_le (hsq.const_mul _) (ae_of_all _ fun x => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_self_nonneg (ψ x))]
        exact mul_le_mul_of_nonneg_right (abs_LN_le u x) (mul_self_nonneg _)
    _ = ((n : ℝ) + 1) * ‖u‖ := by rw [integral_const_mul, h1, mul_one]

/-- The density of a normalised state, as a continuous linear functional of norm `≤ N`. -/
noncomputable def densLW (hψ : ψ ∈ Nst (settingW τ n w hw)) : StrongDual ℝ Pot :=
  LinearMap.mkContinuous
    { toFun := dens (settingW τ n w hw) ψ
      map_add' := densW_add hψ.1
      map_smul' := fun a u => by rw [densW_smul]; rfl }
    ((n : ℝ) + 1) (fun u => by rw [Real.norm_eq_abs]; exact abs_densW_le hψ u)

@[simp] lemma densLW_apply (hψ : ψ ∈ Nst (settingW τ n w hw)) (u : Pot) :
    densLW hψ u = dens (settingW τ n w hw) ψ u := rfl

lemma QW_shift (hψ : ψ ∈ DomW τ n) (v v' : Pot) :
    Q (settingW τ n w hw) v' ψ =
      Q (settingW τ n w hw) v ψ + dens (settingW τ n w hw) ψ (v' - v) := by
  change (settingW τ n w hw).h0 ψ ψ + dens (settingW τ n w hw) ψ v' =
    (settingW τ n w hw).h0 ψ ψ + dens (settingW τ n w hw) ψ v + dens (settingW τ n w hw) ψ (v' - v)
  rw [add_assoc, ← densW_add hψ, add_sub_cancel]

end densW

/-- **Hellmann–Feynman inequality.** -/
theorem supergrad_of_isNGSW {v : Pot} {ψ : Cfg n → ℝ} (h : IsNGS (settingW τ n w hw) v ψ)
    (v' : Pot) : gsErW τ n w hw v' ≤ gsErW τ n w hw v + densLW h.1 (v' - v) := by
  rw [densLW_apply, gsErW_eq_of_isNGS h, ← QW_shift h.1.1]
  exact gsErW_le v' h.1

/-- The ground-state energy is `N`-Lipschitz in the sup norm. -/
theorem gsErW_lipschitz (v v' : Pot) :
    |gsErW τ n w hw v - gsErW τ n w hw v'| ≤ ((n : ℝ) + 1) * ‖v - v'‖ := by
  have h1 := supergrad_of_isNGSW (gsErW_spec (τ := τ) (w := w) (hw := hw) v') v
  have h2 := supergrad_of_isNGSW (gsErW_spec (τ := τ) (w := w) (hw := hw) v) v'
  have b1 := abs_densW_le (gsErW_spec (τ := τ) (w := w) (hw := hw) v').1 (v - v')
  have b2 := abs_densW_le (gsErW_spec (τ := τ) (w := w) (hw := hw) v).1 (v' - v)
  rw [densLW_apply] at h1 h2
  rw [norm_sub_rev] at b2
  rw [abs_le]
  constructor <;> linarith [le_abs_self (dens (settingW τ n w hw)
    (Classical.choose (exists_isNGS_W_cont (n := n) (τ := τ) hw v')) (v - v')),
    le_abs_self (dens (settingW τ n w hw)
    (Classical.choose (exists_isNGS_W_cont (n := n) (τ := τ) hw v)) (v' - v))]

theorem continuous_gsErW : Continuous (gsErW τ n w hw) :=
  (LipschitzWith.of_dist_le_mul (K := ⟨(n : ℝ) + 1, by positivity⟩) fun v v' => by
    rw [Real.dist_eq, dist_eq_norm]; exact gsErW_lipschitz v v').continuous

/-- The ground-state energy is concave. -/
theorem gsErW_concave : ConcaveOn ℝ univ (gsErW τ n w hw) := by
  refine ⟨convex_univ, fun v _ v' _ a b ha hb hab => ?_⟩
  set ψ := Classical.choose (exists_isNGS_W_cont (n := n) (τ := τ) hw (a • v + b • v'))
  have hψ := gsErW_spec (τ := τ) (w := w) (hw := hw) (a • v + b • v')
  have hD : ψ ∈ DomW τ n := hψ.1.1
  have h1 := gsErW_le v hψ.1
  have h2 := gsErW_le v' hψ.1
  have hQ : Q (settingW τ n w hw) (a • v + b • v') ψ =
      a * Q (settingW τ n w hw) v ψ + b * Q (settingW τ n w hw) v' ψ := by
    change (settingW τ n w hw).h0 ψ ψ + dens (settingW τ n w hw) ψ (a • v + b • v') =
      a * ((settingW τ n w hw).h0 ψ ψ + dens (settingW τ n w hw) ψ v) +
        b * ((settingW τ n w hw).h0 ψ ψ + dens (settingW τ n w hw) ψ v')
    rw [densW_add hD, densW_smul, densW_smul]
    linear_combination (-((settingW τ n w hw).h0 ψ ψ)) * hab
  simp only [smul_eq_mul]
  change a * gsErW τ n w hw v + b * gsErW τ n w hw v' ≤ Q (settingW τ n w hw) (a • v + b • v') ψ
  rw [hQ]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

lemma gsErW_sub_le {ρ : Pot → ℝ} {c : ℝ} (hF : liebF (settingW τ n w hw) ρ ≤ (c : EReal))
    (v : Pot) : gsErW τ n w hw v - ρ v ≤ c := by
  have := gsE_le_liebF_add (v := v) hF
  rw [gsE_eqW, EReal.coe_le_coe_iff] at this
  linarith

/-- At a supergradient `ρ'` of `E` at `v`, `F(ρ') = E(v) - ρ'(v)`. -/
theorem liebF_of_supergradW {v : Pot} {ρ' : Pot → ℝ}
    (hρ' : ∀ v', gsErW τ n w hw v' - ρ' v' ≤ gsErW τ n w hw v - ρ' v) :
    liebF (settingW τ n w hw) ρ' = ((gsErW τ n w hw v - ρ' v : ℝ) : EReal) := by
  refine le_antisymm (iSup_le fun v' => ?_) ?_
  · rw [gsE_eqW, ← EReal.coe_sub, EReal.coe_le_coe_iff]; exact hρ' v'
  · have := le_liebF (S := settingW τ n w hw) v ρ'
    rwa [gsE_eqW, ← EReal.coe_sub] at this

/-- **Supergradient densities are dense** (Brøndsted–Rockafellar). -/
theorem dense_supergradW (ρ : StrongDual ℝ Pot) {c : ℝ}
    (hF : liebF (settingW τ n w hw) ρ ≤ (c : EReal)) {η : ℝ} (hη : 0 < η) :
    ∃ (v : Pot) (ρ' : StrongDual ℝ Pot), ‖ρ' - ρ‖ ≤ η ∧
      (∀ v', gsErW τ n w hw v' ≤ gsErW τ n w hw v + ρ' (v' - v)) ∧
      liebF (settingW τ n w hw) ρ' = ((gsErW τ n w hw v - ρ' v : ℝ) : EReal) := by
  obtain ⟨v, ρ', hn, hs⟩ := exists_supergrad_near gsErW_concave
    continuous_gsErW.upperSemicontinuous ρ ⟨c, by rintro _ ⟨v, rfl⟩; exact gsErW_sub_le hF v⟩ hη
  refine ⟨v, ρ', hn, hs, liebF_of_supergradW fun v' => ?_⟩
  have := hs v'
  rw [map_sub] at this
  linarith

/-! ### Continuity of ground-state densities along lines -/

/-- **Ground-state densities are continuous along lines**, up to a subsequence: if `Ψ_k` are
normalised ground states of `v + t_k u` with `t_k → 0`, then along a subsequence
`ρ_{Ψ_k}(u) → ρ_{Ψ₀}(u)`, `Ψ₀` the normalised ground state of `v`. -/
theorem tendsto_dens_line {v u : Pot} {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0))
    (ht1 : ∀ k, |t k| ≤ 1) {Ψ : ℕ → Cfg n → ℝ}
    (hΨ : ∀ k, IsNGS (settingW τ n w hw) (v + t k • u) (Ψ k)) {Ψ0 : Cfg n → ℝ}
    (hΨ0 : IsNGS (settingW τ n w hw) v Ψ0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun j => dens (settingW τ n w hw) (Ψ (φ j)) u) atTop
      (𝓝 (dens (settingW τ n w hw) Ψ0 u)) := by
  set E := gsErW τ n w hw v
  set V : Cfg n → ℝ := fun x => LN n v x + w x with hVdef
  have hV : Continuous V := (continuous_LN v).add hw
  obtain ⟨C, hK⟩ := kBd_cont hV
  obtain ⟨Cu, hKu⟩ := kBd_cont (continuous_LN (n := n) u)
  set c : ℕ → (Fin (n + 1) → ℕ) → ℝ := fun k m => cN m (Ψ k) with hcdef
  have h1 : ∀ k, ∫ x, Ψ k x ^ 2 ∂μN n = 1 := fun k => by
    rw [← (hΨ k).1.2]; simp only [ip]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have hc : ∀ k, Adm τ.toSym (c k) := fun k => adm_cNW (hΨ k).1.1 (h1 k)
  set L := ((n : ℝ) + 1) * ‖u‖
  have hL : 0 ≤ L := by positivity
  -- the energy of `Ψ_k` in `v` is close to `E`
  have hQk : ∀ k, Q (settingW τ n w hw) v (Ψ k) ≤ E + 2 * |t k| * L := fun k => by
    have hs := QW_shift (w := w) (hw := hw) (hΨ k).1.1 (v + t k • u) v
    rw [← gsErW_eq_of_isNGS (hΨ k), sub_add_cancel_left] at hs
    have hb := abs_densW_le (hΨ k).1 (-(t k • u))
    rw [norm_neg, norm_smul, Real.norm_eq_abs] at hb
    have hl := gsErW_lipschitz (τ := τ) (w := w) (hw := hw) (v + t k • u) v
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hl
    have e1 : ((n : ℝ) + 1) * (|t k| * ‖u‖) = |t k| * L := by ring
    rw [e1] at hb hl
    linarith [le_abs_self (dens (settingW τ n w hw) (Ψ k) (-(t k • u))),
      le_abs_self (gsErW τ n w hw (v + t k • u) - gsErW τ n w hw v)]
  have hFk : ∀ k, Fn V (c k) ≤ E + 2 * |t k| * L := fun k =>
    (Fn_le_QW (w := w) (hw := hw) v (hΨ k).1.1).trans (hQk k)
  -- uniform kinetic bound
  have hkin : ∀ k, ∑' m, lam m * c k m ^ 2 ≤ E + 2 * L + √C := fun k => by
    have hb := KBd.abs_Bf_le hK (hc k).sq
    rw [(hc k).norm, mul_one] at hb
    have := hFk k
    unfold Fn at this
    have : 2 * |t k| * L ≤ 2 * L := by nlinarith [ht1 k, abs_nonneg (t k)]
    linarith [neg_abs_le (Bf V (c k) (c k))]
  obtain ⟨a, φ, hφ, ha, hlim, hl2⟩ := exists_subseq_adm hc hkin
  have hB : Tendsto (fun j => Bf V (c (φ j)) (c (φ j))) atTop (𝓝 (Bf V a a)) :=
    tendsto_Bf hK (fun j => (hc (φ j)).sq) (fun j => (hc (φ j)).norm) ha.sq ha.norm hl2
  have hBu : Tendsto (fun j => Bf (LN n u) (c (φ j)) (c (φ j))) atTop (𝓝 (Bf (LN n u) a a)) :=
    tendsto_Bf hKu (fun j => (hc (φ j)).sq) (fun j => (hc (φ j)).norm) ha.sq ha.norm hl2
  have htφ : Tendsto (fun j => t (φ j)) atTop (𝓝 0) := ht.comp hφ.tendsto_atTop
  -- lower semicontinuity: `Fn V a ≤ E`
  have hup : Tendsto (fun j => E + 2 * |t (φ j)| * L) atTop (𝓝 E) := by
    have := ((htφ.abs.const_mul 2).mul_const L).const_add E
    simpa using this
  have hle : ∀ T : Finset (Fin (n + 1) → ℕ), ∑ m ∈ T, lam m * a m ^ 2 ≤ E - Bf V a a :=
    fun T => by
      have h := le_of_tendsto_of_tendsto'
        ((tendsto_finsetSum T fun m _ => ((hlim m).pow 2).const_mul (lam m)).add hB) hup
        fun j => by
          have h3 := hFk (φ j)
          unfold Fn at h3
          have h4 := (hc (φ j)).kin.sum_le_tsum T fun m _ =>
            mul_nonneg (lam_nonneg m) (sq_nonneg _)
          linarith
      linarith
  have hkin_a := Real.tsum_le_of_sum_le
    (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg (a m))) hle
  have hFa : Fn V a ≤ E := by unfold Fn; linarith
  -- the limit is a ground state of `v`
  have hD := serW_mem ha.toDir
  have hcN : (fun m => cN m (serW a)) = a := funext (cN_serW ha.sq)
  have hip : ip (μ := μN n) (serW a) (serW a) = 1 := by
    have h := parsevalW (memLp_serW (a := a))
    calc ip (μ := μN n) (serW a) (serW a) = ∫ x, serW a x ^ 2 ∂μN n :=
          integral_congr_ae (ae_of_all _ fun x => by simp [sq])
      _ = ∑' m, cN m (serW a) ^ 2 := h.tsum_eq.symm
      _ = 1 := by simp only [cN_serW ha.sq]; exact ha.norm
  have hQ : Q (settingW τ n w hw) v (serW a) = Fn V a := by
    rw [QW_eq v hD, kinW_serW ha.toDir, Fn, ← Bf_cNW hV memLp_serW, hcN]
  have hNGS : IsNGS (settingW τ n w hw) v (serW a) :=
    ⟨⟨hD, hip⟩, fun φ' hφ' => by rw [hQ]; exact hFa.trans (gsErW_le v hφ')⟩
  -- densities as coefficient forms
  have hdk : ∀ j, dens (settingW τ n w hw) (Ψ (φ j)) u = Bf (LN n u) (c (φ j)) (c (φ j)) :=
    fun j => by rw [Bf_cNW (continuous_LN u) (hΨ (φ j)).1.1.1]; rfl
  have hda : dens (settingW τ n w hw) (serW a) u = Bf (LN n u) a a := by
    rw [show Bf (LN n u) a a = Bf (LN n u) (fun m => cN m (serW a)) (fun m => cN m (serW a)) by
      rw [hcN], Bf_cNW (continuous_LN u) memLp_serW]
    rfl
  have heq : dens (settingW τ n w hw) (serW a) = dens (settingW τ n w hw) Ψ0 := by
    obtain ⟨c', hc'⟩ := gs_unique_W (isGS_W_of_isNGS_W hNGS) (isGS_W_of_isNGS_W hΨ0)
    exact dens_eq_of_ae_smul hc' hip hΨ0.1.2
  refine ⟨φ, hφ, ?_⟩
  rw [← heq, hda]
  simp only [hdk]
  exact hBu

/-! ### The converse of Hellmann–Feynman, and density -/

/-- **Converse of Hellmann–Feynman.** A supergradient of the ground-state energy at `v` is the
density of a normalised ground state of `v`. -/
theorem supergrad_eqW {v : Pot} {ρ' : StrongDual ℝ Pot}
    (hρ' : ∀ v', gsErW τ n w hw v' ≤ gsErW τ n w hw v + ρ' (v' - v)) :
    ∃ ψ, ∃ hψ : IsNGS (settingW τ n w hw) v ψ, ρ' = densLW hψ.1 := by
  set ψ := Classical.choose (exists_isNGS_W_cont (n := n) (τ := τ) hw v)
  have hψ : IsNGS (settingW τ n w hw) v ψ := gsErW_spec v
  have key : ∀ u : Pot, dens (settingW τ n w hw) ψ u ≤ ρ' u := by
    intro u
    set t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have htpos : ∀ k, 0 < t k := fun k => by positivity
    have ht1 : ∀ k, |t k| ≤ 1 := fun k => by
      rw [abs_of_pos (htpos k)]
      exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by positivity)
    choose Ψ hΨ using fun k => exists_isNGS_W_cont (n := n) (τ := τ) hw (v + t k • u)
    obtain ⟨φ, -, hlim⟩ := tendsto_dens_line ht ht1 hΨ hψ
    refine le_of_tendsto' hlim fun j => ?_
    have hE := hρ' (v + t (φ j) • u)
    rw [gsErW_eq_of_isNGS (hΨ (φ j)), QW_shift (hΨ (φ j)).1.1 v, add_sub_cancel_left,
      densW_smul, map_smul, smul_eq_mul] at hE
    have hlow := gsErW_le v (hΨ (φ j)).1
    have : t (φ j) * dens (settingW τ n w hw) (Ψ (φ j)) u ≤ t (φ j) * ρ' u := by linarith
    exact le_of_mul_le_mul_left this (htpos _)
  refine ⟨ψ, hψ, ContinuousLinearMap.ext fun u => le_antisymm ?_ (key u)⟩
  have h := key (-u)
  rw [map_neg, show -u = (-1 : ℝ) • u by simp, densW_smul] at h
  rw [densLW_apply]
  linarith

/-- **`v`-representable densities are dense.** Every density of finite Lieb functional is within
any `η > 0`, in the dual norm of `C([0, 1])`, of the density of a normalised ground state of some
continuous potential. -/
theorem dense_pureVRepW (ρ : StrongDual ℝ Pot) {c : ℝ}
    (hF : liebF (settingW τ n w hw) ρ ≤ (c : EReal)) {η : ℝ} (hη : 0 < η) :
    ∃ (v : Pot) (ρ' : StrongDual ℝ Pot), ‖ρ' - ρ‖ ≤ η ∧ PureDens (settingW τ n w hw) v ρ' := by
  obtain ⟨v, ρ', hn, hs, -⟩ := dense_supergradW ρ hF hη
  obtain ⟨ψ, hψ, rfl⟩ := supergrad_eqW hs
  exact ⟨v, densLW hψ.1, hn, ψ, isGS_W_of_isNGS_W hψ, hψ.1.2, rfl⟩

/-- Every `N`-representable density is a dual-norm limit of pure `v`-representable densities. -/
theorem dense_pureVRepW_of_nst {φ : Cfg n → ℝ} (hφ : φ ∈ Nst (settingW τ n w hw)) {η : ℝ}
    (hη : 0 < η) : ∃ (v : Pot) (ρ' : StrongDual ℝ Pot), ‖ρ' - densLW hφ‖ ≤ η ∧
      PureDens (settingW τ n w hw) v ρ' :=
  dense_pureVRepW (densLW hφ) (liebF_le_h0 hφ) hη

/-- **Kohn–Sham `v`-representable densities are dense** among `N`-representable densities: the
density of any normalised `H¹₀` state is, within any `η > 0` in the dual norm of `C([0, 1])`, the
density of the ground state of `N` non-interacting particles in some continuous potential. -/
theorem ks_dense {φ : Cfg n → ℝ} (hφ : φ ∈ Nst (ksS τ n)) {η : ℝ} (hη : 0 < η) :
    ∃ (vs : Pot) (ρ' : StrongDual ℝ Pot), ‖ρ' - densLW hφ‖ ≤ η ∧ PureDens (ksS τ n) vs ρ' :=
  dense_pureVRepW_of_nst hφ hη

end DFT.Continuum.Line
