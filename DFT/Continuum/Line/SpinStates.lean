/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.SpinAlg

/-!
# Spin-orbital states of `N` spin-½ particles on a line

A spin-orbital state is `Ψ : SpinC n → (Cfg n → ℝ)`, a spatial wave function for each spin
configuration, with `C²` components vanishing on the walls (`D0`), antisymmetric under
simultaneous relabelling of spins and positions (`Ferm`).

* `BQ`, `Bip`: the energy form `h₀ + ⟨v·,·⟩` and the `L²` form, as bilinear forms on `D0`.
  Both see only the open cube (`BQ_congr`, `Bip_congr`) and are invariant under relabelling
  (`BQ_pm`, `Bip_pm`).
* `QS`, `ipS`: the energy and the norm of a spin-orbital state.
* `sc c`: the configuration with spins `0, …, c-1` up; `exists_rel_sc`: every configuration with
  `c` spins up is a relabelling of `sc c`.
* `sector_reduce`: a fermionic state in the sector with `c` spins up has
  `QS = K · BQ(ψ, ψ)` and `ipS = K · Bip(ψ, ψ)`, where `ψ = Ψ (sc c)` and `K = #{s | nup s = c}`.
* `ladder`: for a state of definite `S²` and `S_z`, `S₊` multiplies both `QS` and `ipS` by
  `S(S+1) - M(M+1)`, and `S₋` multiplies `ipS` by `S(S+1) - M(M-1)`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine Function

variable {n : ℕ}

/-! ### The spatial domain and forms -/

/-- No symmetry. -/
def trivS : SymT n := ⟨fun _ => False, fun _ => 1⟩

/-- `C²` functions vanishing on the walls. -/
noncomputable abbrev D0 (n : ℕ) := DomS (trivS (n := n))

lemma mem_D0 {ψ : Cfg n → ℝ} :
    ψ ∈ D0 n ↔ ContDiff ℝ 2 ψ ∧ ∀ x k, (x k = 0 ∨ x k = 1) → ψ x = 0 :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun _ h' => h'.elim, h.2⟩⟩

lemma DomY_le_D0 {a : ℕ} : DomY a n ≤ D0 n := fun _ h => mem_D0.2 ⟨h.1, h.2.2⟩

section forms

variable (w : Cfg n → ℝ) (hw : Continuous w) (v : Pot)

lemma pfT_add_left {f f' g : Cfg n → ℝ} (hf : f ∈ D0 n) (hf' : f' ∈ D0 n) (hg : g ∈ D0 n) :
    pf (settingS trivS w hw) v (f + f') g =
      pf (settingS trivS w hw) v f g + pf (settingS trivS w hw) v f' g := by
  simp only [pf, Pi.add_apply]
  rw [← integral_add ((settingS trivS w hw).int_L v _ _ hf hg)
    ((settingS trivS w hw).int_L v _ _ hf' hg)]
  congr 1; funext x; ring

lemma pfT_smul_left (c : ℝ) (f g : Cfg n → ℝ) :
    pf (settingS trivS w hw) v (c • f) g = c * pf (settingS trivS w hw) v f g := by
  simp only [pf, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]; congr 1; funext x; ring

lemma ipT_add_left {f f' g : Cfg n → ℝ} (hf : f ∈ D0 n) (hf' : f' ∈ D0 n) (hg : g ∈ D0 n) :
    ip (μ := μN n) (f + f') g = ip (μ := μN n) f g + ip (μ := μN n) f' g := by
  have c1 := (mem_D0.1 hf).1.continuous
  have c2 := (mem_D0.1 hf').1.continuous
  have c3 := (mem_D0.1 hg).1.continuous
  simp only [ip, Pi.add_apply]
  rw [← integral_add (f := fun x => f x * g x) (g := fun x => f' x * g x)
    (integrableN (c1.mul c3)) (integrableN (c2.mul c3))]
  congr 1; funext x; ring

lemma ipT_smul_left (c : ℝ) (f g : Cfg n → ℝ) :
    ip (μ := μN n) (c • f) g = c * ip (μ := μN n) f g := by
  simp only [ip, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]; congr 1; funext x; ring

/-- The energy form on `D0`. -/
noncomputable def BQ : D0 n →ₗ[ℝ] D0 n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => (settingS trivS w hw).h0 f g + pf (settingS trivS w hw) v f g)
    (fun f f' g => by
      simp only [Submodule.coe_add]
      rw [(settingS trivS w hw).h0_add _ f.2 _ f'.2 _ g.2, pfT_add_left w hw v f.2 f'.2 g.2]
      ring)
    (fun c f g => by
      simp only [Submodule.coe_smul, smul_eq_mul]
      rw [(settingS trivS w hw).h0_smul c _ f.2 _ g.2, pfT_smul_left]; ring)
    (fun f g g' => by
      simp only [Submodule.coe_add]
      rw [(settingS trivS w hw).h0_symm _ f.2 _ ((D0 n).add_mem g.2 g'.2),
        (settingS trivS w hw).h0_add _ g.2 _ g'.2 _ f.2,
        (settingS trivS w hw).h0_symm _ g.2 _ f.2, (settingS trivS w hw).h0_symm _ g'.2 _ f.2,
        pf_comm, pfT_add_left w hw v g.2 g'.2 f.2, pf_comm _ _ (g : Cfg n → ℝ),
        pf_comm _ _ (g' : Cfg n → ℝ)]
      ring)
    (fun c f g => by
      simp only [Submodule.coe_smul, smul_eq_mul]
      rw [(settingS trivS w hw).h0_symm _ f.2 _ ((D0 n).smul_mem c g.2),
        (settingS trivS w hw).h0_smul c _ g.2 _ f.2, (settingS trivS w hw).h0_symm _ g.2 _ f.2,
        pf_comm, pfT_smul_left, pf_comm _ _ (g : Cfg n → ℝ)]
      ring)

/-- The `L²` form on `D0`. -/
noncomputable def Bip : D0 n →ₗ[ℝ] D0 n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => ip (μ := μN n) (f : Cfg n → ℝ) g)
    (fun f f' g => by simp only [Submodule.coe_add]; exact ipT_add_left f.2 f'.2 g.2)
    (fun c f g => by simp only [Submodule.coe_smul, smul_eq_mul]; exact ipT_smul_left c _ _)
    (fun f g g' => by
      simp only [Submodule.coe_add]
      rw [ip_comm, ipT_add_left g.2 g'.2 f.2, ip_comm _ (g : Cfg n → ℝ),
        ip_comm _ (g' : Cfg n → ℝ)])
    (fun c f g => by
      simp only [Submodule.coe_smul, smul_eq_mul]
      rw [ip_comm, ipT_smul_left, ip_comm _ (g : Cfg n → ℝ)])

lemma BQ_apply (f g : D0 n) :
    BQ w hw v f g = h0N n w f g + ∫ x, LN n v x * ((f : Cfg n → ℝ) x * (g : Cfg n → ℝ) x) ∂μN n :=
  rfl

lemma BQ_self (f : D0 n) : BQ w hw v f f = Q (settingS trivS w hw) v (f : Cfg n → ℝ) := rfl

lemma Bip_apply (f g : D0 n) : Bip f g = ip (μ := μN n) (f : Cfg n → ℝ) g := rfl

lemma Bip_self_nonneg (f : D0 n) : 0 ≤ Bip f f :=
  integral_nonneg fun _ => mul_self_nonneg _

lemma BQ_symm (f g : D0 n) : BQ w hw v f g = BQ w hw v g f := by
  change (settingS trivS w hw).h0 f g + pf (settingS trivS w hw) v f g =
    (settingS trivS w hw).h0 g f + pf (settingS trivS w hw) v g f
  rw [(settingS trivS w hw).h0_symm _ f.2 _ g.2, pf_comm]

lemma Bip_symm (f g : D0 n) : Bip f g = Bip g f := by
  rw [Bip_apply, Bip_apply, ip_comm]

/-- `BQ` only sees the open cube. -/
lemma BQ_congr (f g g' : D0 n) (h : ∀ x ∈ Cube n, (g : Cfg n → ℝ) x = (g' : Cfg n → ℝ) x) :
    BQ w hw v f g = BQ w hw v f g' := by
  rw [BQ_apply, BQ_apply]
  have hev : ∀ x ∈ Cube n, (g : Cfg n → ℝ) =ᶠ[𝓝 x] (g' : Cfg n → ℝ) := fun x hx =>
    Filter.eventuallyEq_of_mem (isOpen_cube.mem_nhds hx) h
  simp only [h0N]
  congr 1
  · congr 1
    · refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [dk, (hev x hx).fderiv_eq]
    · refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
      rw [h x hx]
  · refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
    rw [h x hx]

lemma Bip_congr (f g g' : D0 n) (h : ∀ x ∈ Cube n, (g : Cfg n → ℝ) x = (g' : Cfg n → ℝ) x) :
    Bip f g = Bip f g' := by
  rw [Bip_apply, Bip_apply]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
  rw [h x hx]

end forms

/-! ### Relabelling invariance -/

lemma comp_pm_mem_D0 {f : Cfg n → ℝ} (hf : f ∈ D0 n) (σ : Equiv.Perm (Fin (n + 1))) :
    (fun x => f (pm σ x)) ∈ D0 n := by
  rw [mem_D0] at hf ⊢
  refine ⟨hf.1.comp (contDiff_pm σ), fun x k hk => hf.2 _ (σ⁻¹ k) (by simpa using hk)⟩

section invariance

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} (hws : ∀ σ x, w (pm σ x) = w x)
include hws

lemma BQ_pm (f : D0 n) (σ : Equiv.Perm (Fin (n + 1))) :
    BQ w hw v ⟨_, comp_pm_mem_D0 f.2 σ⟩ ⟨_, comp_pm_mem_D0 f.2 σ⟩ = BQ w hw v f f := by
  have hd : Differentiable ℝ (f : Cfg n → ℝ) := (mem_D0.1 f.2).1.differentiable (by norm_num)
  rw [BQ_apply, BQ_apply]
  simp only [h0N]
  have hk : ∫ x, ∑ k, dk k (fun y => (f : Cfg n → ℝ) (pm σ y)) x *
      dk k (fun y => (f : Cfg n → ℝ) (pm σ y)) x ∂μN n =
      ∫ x, ∑ k, dk k (f : Cfg n → ℝ) x * dk k (f : Cfg n → ℝ) x ∂μN n := by
    simp only [dk_fun_comp_pm hd]
    rw [← integral_pm σ (fun x => ∑ k, dk k (f : Cfg n → ℝ) x * dk k (f : Cfg n → ℝ) x)]
    congr 1; funext x
    exact Equiv.sum_comp σ⁻¹
      (fun j => dk j (f : Cfg n → ℝ) (pm σ x) * dk j (f : Cfg n → ℝ) (pm σ x))
  have hw' : ∫ x, w x * ((f : Cfg n → ℝ) (pm σ x) * (f : Cfg n → ℝ) (pm σ x)) ∂μN n =
      ∫ x, w x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x) ∂μN n := by
    rw [← integral_pm σ (fun x => w x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x))]
    simp only [hws]
  have hL : ∫ x, LN n v x * ((f : Cfg n → ℝ) (pm σ x) * (f : Cfg n → ℝ) (pm σ x)) ∂μN n =
      ∫ x, LN n v x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x) ∂μN n := by
    rw [← integral_pm σ (fun x => LN n v x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x))]
    simp only [LN_pm]
  simp only [hk, hw', hL]

omit hws in
lemma Bip_pm (f : D0 n) (σ : Equiv.Perm (Fin (n + 1))) :
    Bip ⟨_, comp_pm_mem_D0 f.2 σ⟩ ⟨_, comp_pm_mem_D0 f.2 σ⟩ = Bip f f := by
  rw [Bip_apply, Bip_apply]
  exact integral_pm σ (fun x => (f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x)

end invariance

/-! ### Spin-orbital states -/

/-- Antisymmetry under simultaneous relabelling of spins and positions. -/
def Ferm (Ψ : SpinC n → Cfg n → ℝ) : Prop :=
  ∀ σ s x, Ψ (rel σ s) (pm σ x) = sgn σ * Ψ s x

/-- The configuration with spins `0, …, c-1` up. -/
def sc (n c : ℕ) : SpinC n := fun i => decide ((i : ℕ) < c)

lemma rel_sc_iff {c : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : rel σ (sc n c) = sc n c ↔ YG c σ := by
  constructor
  · intro h i
    have := congrFun h i
    simp only [rel, sc, decide_eq_decide] at this
    exact this
  · intro h; funext i; simp only [rel, sc, decide_eq_decide]; exact h i

lemma nup_sc {c : ℕ} (hc : c ≤ n + 1) : nup (sc n c) = c := by
  rw [nup_eq_sum]
  simp only [sc, decide_eq_true_eq]
  rw [Finset.sum_boole, Nat.cast_id]
  rw [Fin.card_filter_val_lt]; omega

lemma subtypeCongr_apply' {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x }) (a : α) :
    Equiv.subtypeCongr e f a = if h : p a then (e ⟨a, h⟩ : α) else (f ⟨a, h⟩ : α) := by
  by_cases h : p a <;> simp [Equiv.subtypeCongr, h]

/-- **Every configuration with `c` spins up is a relabelling of `sc c`.** -/
lemma exists_rel_sc {s : SpinC n} {c : ℕ} (h : nup s = c) :
    ∃ τ : Equiv.Perm (Fin (n + 1)), rel τ (sc n c) = s := by
  classical
  have hc : c ≤ n + 1 := h ▸ nup_le s
  have h1 : Fintype.card {i // s i = true} = Fintype.card {j : Fin (n + 1) // (j : ℕ) < c} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt, min_eq_right hc]
    exact h
  have h2 : Fintype.card {i // ¬ s i = true} =
      Fintype.card {j : Fin (n + 1) // ¬ (j : ℕ) < c} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  set e1 := Fintype.equivOfCardEq h1
  set e2 := Fintype.equivOfCardEq h2
  refine ⟨Equiv.subtypeCongr e1 e2, ?_⟩
  funext i
  simp only [rel, sc, subtypeCongr_apply']
  by_cases hi : s i = true
  · rw [dite_eq_left hi]; simp [hi, (e1 ⟨i, hi⟩).2]
  · rw [dite_eq_right hi]
    have := (e2 ⟨i, hi⟩).2
    simp only [Bool.not_eq_true] at hi
    simp [hi, this]

lemma Ferm_comp {Ψ : SpinC n → Cfg n → ℝ} (hΨ : Ferm Ψ) (τ : Equiv.Perm (Fin (n + 1)))
    (s : SpinC n) (y : Cfg n) : Ψ (rel τ s) y = sgn τ * Ψ s (pm τ⁻¹ y) := by
  have := hΨ τ s (pm τ⁻¹ y)
  rwa [show pm τ (pm τ⁻¹ y) = y from pm_pm_inv τ y] at this

end DFT.Continuum.Line
