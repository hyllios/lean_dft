/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.SpinStates

/-!
# From spin-orbital states to spatial states of mixed symmetry

States are `u : SpinC n → D0 n` (a `C²` spatial component, vanishing on the walls, for each spin
configuration).

* `ev x`: evaluation at `x`; the spin operators commute with linear maps (`Sp_map`, …).
* `FermD`: fermionic antisymmetry; preserved by `S₊` (`FermD_Sp`) and by the sector projections.
* `QS`, `ipS`: energy and norm. `sector_reduce`: in the sector with `c` spins up they are
  `K · B(ψ, ψ)` with `ψ = u (sc c)` of mixed symmetry `(c, N - c)` (`mem_DomY_sc`).
* `ladder_Sp_gen`, `ladder_Sm_gen`, `B_S2`: for a state of definite `S²` (on the cube) and
  `S_z`, `S₊` multiplies both forms by `λ - M(M+1)` and `S₋` multiplies them by `λ - M(M-1)`.
* `lift Φ`: the fermionic spin-orbital state whose component at `sc a` is `#YG · Φ`, for `Φ` of
  mixed symmetry `(a, N - a)`.
* `Strong E f`: `-Δf + (w + Σ v - E) f = 0` on the cube; closed under linear combinations and
  relabelling, and `BQ f f = E · Bip f f` (`BQ_of_strong`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine Function

variable {n : ℕ}

/-! ### Evaluation and linear maps -/

/-- Evaluation at a point. -/
noncomputable def ev (x : Cfg n) : D0 n →ₗ[ℝ] ℝ := (LinearMap.proj x).comp (D0 n).subtype

@[simp] lemma ev_apply (x : Cfg n) (f : D0 n) : ev x f = (f : Cfg n → ℝ) x := rfl

section maps

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

lemma Sp_map (L : V →ₗ[ℝ] W) (u : SpinC n → V) (s : SpinC n) :
    L (Sp u s) = Sp (fun t => L (u t)) s := by
  simp only [Sp_apply, map_sum]; exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma Sm_map (L : V →ₗ[ℝ] W) (u : SpinC n → V) (s : SpinC n) :
    L (Sm u s) = Sm (fun t => L (u t)) s := by
  simp only [Sm_apply, map_sum]; exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma Sz_map (L : V →ₗ[ℝ] W) (u : SpinC n → V) (s : SpinC n) :
    L (Sz u s) = Sz (fun t => L (u t)) s := by
  simp only [Sz_apply, map_smul]

lemma S2_map (L : V →ₗ[ℝ] W) (u : SpinC n → V) (s : SpinC n) :
    L (S2 u s) = S2 (fun t => L (u t)) s := by
  change L ((1 / 2 : ℝ) • (Sp (Sm u) s + Sm (Sp u) s) + Sz (Sz u) s) =
    (1 / 2 : ℝ) • (Sp (Sm fun t => L (u t)) s + Sm (Sp fun t => L (u t)) s) +
      Sz (Sz fun t => L (u t)) s
  rw [map_add, map_smul, map_add, Sp_map, Sm_map, Sz_map,
    show (fun t => L (Sm u t)) = Sm (fun t => L (u t)) from funext (Sm_map L u),
    show (fun t => L (Sp u t)) = Sp (fun t => L (u t)) from funext (Sp_map L u),
    show (fun t => L (Sz u t)) = Sz (fun t => L (u t)) from funext (Sz_map L u)]

lemma Pc_map (L : V →ₗ[ℝ] W) (c : ℕ) (u : SpinC n → V) (s : SpinC n) :
    L (Pc c u s) = Pc c (fun t => L (u t)) s := by
  simp only [Pc_apply]; split_ifs <;> simp

end maps

/-! ### Fermionic states -/

/-- Fermionic antisymmetry of a `D0`-valued spin state. -/
def FermD (u : SpinC n → D0 n) : Prop := Ferm fun s => (u s : Cfg n → ℝ)

lemma FermD_Sp {u : SpinC n → D0 n} (hu : FermD u) : FermD (Sp u) := by
  intro σ s x
  change ev (pm σ x) (Sp u (rel σ s)) = sgn σ * ev x (Sp u s)
  rw [Sp_map, Sp_map, Sp_rel]
  have e : (fun t => ev (pm σ x) (u (rel σ t))) = fun t => sgn σ * ev x (u t) := by
    funext t; exact hu σ t x
  rw [e]
  change Sp ((sgn σ) • fun t => ev x (u t)) s = _
  rw [map_smul]; rfl

lemma FermD_Pc {u : SpinC n → D0 n} (hu : FermD u) (c : ℕ) : FermD (Pc c u) := by
  intro σ s x
  change ev (pm σ x) (Pc c u (rel σ s)) = sgn σ * ev x (Pc c u s)
  simp only [Pc_apply, nup_rel]
  split_ifs
  · exact hu σ s x
  · simp

/-- The component at `sc c` of a fermionic state has mixed symmetry `(c, N - c)`. -/
lemma mem_DomY_sc {u : SpinC n → D0 n} (hu : FermD u) (c : ℕ) :
    (u (sc n c) : Cfg n → ℝ) ∈ DomY c n := by
  have hD := mem_D0.1 (u (sc n c)).2
  refine ⟨hD.1, fun σ hσ x => ?_, hD.2⟩
  have := hu σ (sc n c) x
  rwa [(rel_sc_iff σ).2 hσ] at this

/-! ### Energy and norm -/

/-- A continuous `C²` state of zero norm vanishes on the cube. -/
lemma eq_zero_of_ip_zero' {φ : Cfg n → ℝ} (h2 : ContDiff ℝ 2 φ)
    (h : ip (μ := μN n) φ φ = 0) : ∀ x ∈ Cube n, φ x = 0 := by
  have hc := h2.continuous
  have hae : (fun x => φ x * φ x) =ᵐ[μN n] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (φ x))
      (integrableN (hc.mul hc))).1 h
  have hz : EqOn (fun x => φ x * φ x) (fun _ => 0) (Cube n) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_cube (hc.mul hc).continuousOn continuousOn_const
  exact fun x hx => mul_self_eq_zero.1 (hz hx)

section forms

variable (w : Cfg n → ℝ) (hw : Continuous w) (v : Pot)

/-- The energy of a spin-orbital state. -/
noncomputable def QS (u : SpinC n → D0 n) : ℝ := ∑ s, BQ w hw v (u s) (u s)

/-- The norm of a spin-orbital state. -/
noncomputable def ipS (u : SpinC n → D0 n) : ℝ := ∑ s, Bip (u s) (u s)

lemma ipS_nonneg (u : SpinC n → D0 n) : 0 ≤ ipS u :=
  Finset.sum_nonneg fun _ _ => Bip_self_nonneg _

end forms

/-- Components of zero norm vanish on the cube. -/
lemma eq_zero_of_Bip {f : D0 n} (h : Bip f f = 0) : ∀ x ∈ Cube n, (f : Cfg n → ℝ) x = 0 :=
  eq_zero_of_ip_zero' (mem_D0.1 f.2).1 h

lemma ipS_zero_imp {u : SpinC n → D0 n} (h : ipS u = 0) (s : SpinC n) :
    ∀ x ∈ Cube n, (u s : Cfg n → ℝ) x = 0 := by
  have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => Bip_self_nonneg (u s))).1 h s
    (Finset.mem_univ s)
  exact eq_zero_of_Bip h'

lemma QS_eq_zero_of_ipS {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {u : SpinC n → D0 n}
    (h : ipS u = 0) : QS w hw v u = 0 := by
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [BQ_congr w hw v (u s) (u s) 0 (fun x hx => by rw [ipS_zero_imp h s x hx]; rfl)]
  simp

/-! ### Sector reduction -/

lemma B_sector_term (B : D0 n →ₗ[ℝ] D0 n →ₗ[ℝ] ℝ)
    (hB : ∀ (f : D0 n) σ, B ⟨_, comp_pm_mem_D0 f.2 σ⟩ ⟨_, comp_pm_mem_D0 f.2 σ⟩ = B f f)
    {u : SpinC n → D0 n} (hu : FermD u) {c : ℕ} {s : SpinC n} (hs : nup s = c) :
    B (u s) (u s) = B (u (sc n c)) (u (sc n c)) := by
  obtain ⟨τ, hτ⟩ := exists_rel_sc hs
  have he : u s = sgn τ • (⟨_, comp_pm_mem_D0 (u (sc n c)).2 τ⁻¹⟩ : D0 n) := by
    apply Subtype.ext; funext y
    rw [← hτ]
    exact Ferm_comp hu τ (sc n c) y
  rw [he, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, hB, ← mul_assoc,
    sgn_mul_self, one_mul]

/-- **Sector reduction.** -/
lemma sector_reduce (B : D0 n →ₗ[ℝ] D0 n →ₗ[ℝ] ℝ)
    (hB : ∀ (f : D0 n) σ, B ⟨_, comp_pm_mem_D0 f.2 σ⟩ ⟨_, comp_pm_mem_D0 f.2 σ⟩ = B f f)
    {u : SpinC n → D0 n} (hu : FermD u) {c : ℕ} (hc : Pc c u = u) :
    ∑ s, B (u s) (u s) =
      ((Finset.univ.filter fun s : SpinC n => nup s = c).card : ℝ) *
        B (u (sc n c)) (u (sc n c)) := by
  classical
  have hz : ∀ s, nup s ≠ c → u s = 0 := fun s hs => by
    rw [← hc]; simp [Pc_apply, hs]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : SpinC n => nup s = c)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun s : SpinC n => ¬ nup s = c)
    fun s hs => by rw [hz s (Finset.mem_filter.1 hs).2]; simp, add_zero]
  rw [Finset.sum_congr rfl fun s hs => B_sector_term B hB hu (Finset.mem_filter.1 hs).2,
    Finset.sum_const, nsmul_eq_mul]

lemma card_sector_pos {c : ℕ} (hc : c ≤ n + 1) :
    0 < ((Finset.univ.filter fun s : SpinC n => nup s = c).card : ℝ) := by
  exact_mod_cast Finset.card_pos.2 ⟨sc n c, by simp [nup_sc hc]⟩

/-! ### The ladder -/

section ladderG

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  {u : SpinC n → V} {c : ℕ} (hc : Pc c u = u) {lam : ℝ}
  (hB2 : ∀ s, B (u s) (S2 u s) = lam * B (u s) (u s))

omit [AddCommGroup V] [Module ℝ V] in
lemma B_Sz_sector {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    {u : SpinC n → V} {c : ℕ} (hc : Pc c u = u) (s : SpinC n) (r : ℕ → ℝ) :
    B (u s) (r (nup s) • u s) = r c * B (u s) (u s) := by
  by_cases hs : nup s = c
  · rw [hs, map_smul, smul_eq_mul]
  · have : u s = 0 := by rw [← hc]; simp [Pc_apply, hs]
    simp [this]

include hc hB2

/-- **`S₊` along a multiplet**, for any bilinear form. -/
lemma ladder_Sp_gen :
    ∑ s, B (Sp u s) (Sp u s) =
      (lam - ((c : ℝ) - ((n : ℝ) + 1) / 2) ^ 2 - ((c : ℝ) - ((n : ℝ) + 1) / 2)) *
        ∑ s, B (u s) (u s) := by
  rw [adj_Sp B u (Sp u), Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hS2 := congrArg (fun T : Module.End ℝ (SpinC n → V) => T u s) (S2_eq (n := n) (V := V))
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply] at hS2
  have hSm : Sm (Sp u) s = S2 u s - Sz (Sz u) s - Sz u s := by rw [hS2]; abel
  rw [hSm, map_sub, map_sub, hB2]
  have h1 : Sz (Sz u) s = (fun k : ℕ => ((k : ℝ) - ((n : ℝ) + 1) / 2) ^ 2) (nup s) • u s := by
    simp only [Sz_apply, smul_smul, Mz]; congr 1; ring
  have h2 : Sz u s = (fun k : ℕ => (k : ℝ) - ((n : ℝ) + 1) / 2) (nup s) • u s := by
    simp only [Sz_apply, Mz]
  rw [h1, h2, B_Sz_sector B hc s (fun k : ℕ => ((k : ℝ) - ((n : ℝ) + 1) / 2) ^ 2),
    B_Sz_sector B hc s (fun k : ℕ => (k : ℝ) - ((n : ℝ) + 1) / 2)]
  ring

/-- **`S₋` along a multiplet**, for any symmetric bilinear form. -/
lemma ladder_Sm_gen (hBs : ∀ f g, B f g = B g f) :
    ∑ s, B (Sm u s) (Sm u s) =
      (lam - ((c : ℝ) - ((n : ℝ) + 1) / 2) ^ 2 + ((c : ℝ) - ((n : ℝ) + 1) / 2)) *
        ∑ s, B (u s) (u s) := by
  rw [← adj_Sp B (Sm u) u, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hBs]
  have hS2 := congrArg (fun T : Module.End ℝ (SpinC n → V) => T u s) (S2_eq (n := n) (V := V))
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply] at hS2
  have hc2 := congrFun (comm_Sp_Sm (n := n) (V := V) u) s
  simp only [Pi.sub_apply, Pi.smul_apply] at hc2
  have hSm' : Sm (Sp u) s = S2 u s - Sz (Sz u) s - Sz u s := by rw [hS2]; abel
  have hSp : Sp (Sm u) s = S2 u s - Sz (Sz u) s + Sz u s := by
    rw [sub_eq_iff_eq_add.1 hc2, hSm', two_smul]; abel
  rw [hSp, map_add, map_sub, hB2]
  have h1 : Sz (Sz u) s = (fun k : ℕ => ((k : ℝ) - ((n : ℝ) + 1) / 2) ^ 2) (nup s) • u s := by
    simp only [Sz_apply, smul_smul, Mz]; congr 1; ring
  have h2 : Sz u s = (fun k : ℕ => (k : ℝ) - ((n : ℝ) + 1) / 2) (nup s) • u s := by
    simp only [Sz_apply, Mz]
  rw [h1, h2, B_Sz_sector B hc s (fun k : ℕ => ((k : ℝ) - ((n : ℝ) + 1) / 2) ^ 2),
    B_Sz_sector B hc s (fun k : ℕ => (k : ℝ) - ((n : ℝ) + 1) / 2)]
  ring

end ladderG

section ladder

variable (B : D0 n →ₗ[ℝ] D0 n →ₗ[ℝ] ℝ) (hBs : ∀ f g, B f g = B g f)
  (hBc : ∀ f g g' : D0 n, (∀ x ∈ Cube n, (g : Cfg n → ℝ) x = (g' : Cfg n → ℝ) x) → B f g = B f g')
  {u : SpinC n → D0 n} {c : ℕ} (hc : Pc c u = u) {lam : ℝ}
  (heig : ∀ s, ∀ x ∈ Cube n, ev x (S2 u s) = lam * ev x (u s))
include hBc heig

lemma B_S2 (s : SpinC n) : B (u s) (S2 u s) = lam * B (u s) (u s) := by
  rw [hBc (u s) (S2 u s) (lam • u s) fun x hx => by
    have := heig s x hx; simpa using this, map_smul, smul_eq_mul]

end ladder

/-! ### Eigenstates of `S²` on the cube -/

/-- `S² u = λ u` on the cube. -/
def EigC (lam : ℝ) (u : SpinC n → D0 n) : Prop :=
  ∀ s, ∀ x ∈ Cube n, ev x (S2 u s) = lam * ev x (u s)

lemma EigC_Sp {lam : ℝ} {u : SpinC n → D0 n} (h : EigC lam u) : EigC lam (Sp u) := by
  intro s x hx
  have hc := congrArg (fun T : Module.End ℝ (SpinC n → D0 n) => T u s)
    (S2_comm_Sp (n := n) (V := D0 n))
  simp only [Module.End.mul_apply] at hc
  rw [hc, Sp_map, Sp_map]
  rw [show (fun t => ev x (S2 u t)) = lam • fun t => ev x (u t) from funext fun t => h t x hx,
    map_smul]
  rfl

lemma EigC_Pc {lam : ℝ} {u : SpinC n → D0 n} (h : EigC lam u) (c : ℕ) : EigC lam (Pc c u) := by
  intro s x hx
  rw [S2_Pc, Pc_map, Pc_map]
  simp only [Pc_apply]
  split_ifs
  · exact h s x hx
  · simp

/-! ### The strong equation -/

section strong

variable (w : Cfg n → ℝ) (hw : Continuous w) (v : Pot) (E : ℝ)

/-- `Δf = (w + Σ v - E) f` on the cube. -/
def Strong (f : Cfg n → ℝ) : Prop :=
  ∀ x ∈ Cube n, lapN f x = (w x + LN n v x - E) * f x

lemma lapN_add {f g : Cfg n → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Cfg n) :
    lapN (f + g) x = lapN f x + lapN g x := by
  simp only [lapN, dkk, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dk_add (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num)) k,
    dk_add ((contDiff_dk hf k).differentiable one_ne_zero)
      ((contDiff_dk hg k).differentiable one_ne_zero) k]
  rfl

lemma lapN_smul {f : Cfg n → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : Cfg n) :
    lapN (c • f) x = c * lapN f x := by
  simp only [lapN, dkk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dk_smul (hf.differentiable (by norm_num)) c k,
    dk_smul ((contDiff_dk hf k).differentiable one_ne_zero) c k]
  rfl

lemma Strong.add {f g : D0 n} (hf : Strong w v E f) (hg : Strong w v E g) :
    Strong w v E ((f + g : D0 n) : Cfg n → ℝ) := by
  intro x hx
  rw [Submodule.coe_add, lapN_add (mem_D0.1 f.2).1 (mem_D0.1 g.2).1, hf x hx, hg x hx,
    Pi.add_apply]; ring

lemma Strong.smul {f : D0 n} (hf : Strong w v E f) (c : ℝ) :
    Strong w v E ((c • f : D0 n) : Cfg n → ℝ) := by
  intro x hx
  rw [Submodule.coe_smul, lapN_smul (mem_D0.1 f.2).1, hf x hx, Pi.smul_apply, smul_eq_mul]; ring

lemma Strong.zero : Strong w v E ((0 : D0 n) : Cfg n → ℝ) := by
  intro x _
  have h0 : ∀ k, dk k (0 : Cfg n → ℝ) = 0 := fun k => by funext y; simp [dk]
  simp [lapN, dkk, h0]

lemma Strong.sum {ι : Type*} (t : Finset ι) {f : ι → D0 n} (hf : ∀ i ∈ t, Strong w v E (f i)) :
    Strong w v E ((∑ i ∈ t, f i : D0 n) : Cfg n → ℝ) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Strong.zero w v E
  | insert b t hb ih =>
    rw [Finset.sum_insert hb]
    exact Strong.add w v E (hf b (Finset.mem_insert_self b t))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma Strong.ite {p : Prop} [Decidable p] {f : D0 n} (hf : Strong w v E f) :
    Strong w v E ((if p then f else 0 : D0 n) : Cfg n → ℝ) := by
  split_ifs
  · exact hf
  · exact Strong.zero w v E

lemma Strong.pm (hws : ∀ σ x, w (pm σ x) = w x) {f : Cfg n → ℝ} (hf2 : ContDiff ℝ 2 f)
    (hf : Strong w v E f) (σ : Equiv.Perm (Fin (n + 1))) : Strong w v E fun x => f (pm σ x) := by
  intro x hx
  rw [lapN_comp_pm hf2 σ x, hf _ (pm_mem_cube.2 hx), hws, LN_pm]

/-- **Solutions of the strong equation have energy `E` per unit norm.** -/
lemma BQ_of_strong {f : D0 n} (hf : Strong w v E f) : BQ w hw v f f = E * Bip f f := by
  have hD := mem_D0.1 f.2
  have hc := hD.1.continuous
  rw [BQ_apply, Bip_apply]
  simp only [h0N]
  have hkin : ∫ x, ∑ k, dk k (f : Cfg n → ℝ) x * dk k (f : Cfg n → ℝ) x ∂μN n =
      -∫ x, lapN (f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x ∂μN n := by
    rw [integral_finsetSum (f := fun k x => dk k (f : Cfg n → ℝ) x * dk k (f : Cfg n → ℝ) x) _
      fun k _ => integrableN ((contDiff_dk hD.1 k).continuous.mul (contDiff_dk hD.1 k).continuous)]
    simp only [ibpN0 hD.1 hD.1 hD.2]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum
      (f := fun k x => dkk k (f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x) _
      fun k _ => integrableN ((continuous_dkk hD.1 k).mul hc)]
    congr 2; funext x; simp only [lapN, Finset.sum_mul]
  have hlap : ∫ x, lapN (f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x ∂μN n =
      ∫ x, (w x + LN n v x - E) * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x) ∂μN n := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
    rw [hf x hx]; ring
  rw [hkin, hlap]
  have i1 := integrableN
    (F := fun x => (w x + LN n v x - E) * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x))
    (((hw.add (continuous_LN v)).sub continuous_const).mul (hc.mul hc))
  have i2 := integrableN (F := fun x => w x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x))
    (hw.mul (hc.mul hc))
  have i3 := integrableN (F := fun x => LN n v x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x))
    ((continuous_LN v).mul (hc.mul hc))
  have hsum : ∫ x, w x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x) ∂μN n +
      ∫ x, LN n v x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x) ∂μN n -
      ∫ x, (w x + LN n v x - E) * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x) ∂μN n =
      E * ∫ x, (f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x ∂μN n := by
    rw [← integral_add (f := fun x => w x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x))
      (g := fun x => LN n v x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x)) i2 i3,
      ← integral_sub (f := fun x => w x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x) +
        LN n v x * ((f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x)) (i2.add i3) i1,
      ← integral_const_mul]
    congr 1; funext x; ring
  change _ = E * ∫ x, (f : Cfg n → ℝ) x * (f : Cfg n → ℝ) x ∂μN n
  linarith

end strong

/-! ### Lifting a state of mixed symmetry -/

section lift

variable {a : ℕ}

/-- The spin-orbital state built from a spatial state `Φ`: the antisymmetrisation of
`δ_{s, sc a} Φ`. -/
noncomputable def lift (a : ℕ) {Φ : Cfg n → ℝ} (hΦ : Φ ∈ D0 n) (s : SpinC n) : D0 n :=
  open Classical in
  ∑ σ, if rel σ s = sc n a then sgn σ • (⟨fun x => Φ (pm σ x), comp_pm_mem_D0 hΦ σ⟩ : D0 n)
    else 0

lemma lift_apply {Φ : Cfg n → ℝ} (hΦ : Φ ∈ D0 n) (s : SpinC n) (x : Cfg n) :
    (lift a hΦ s : Cfg n → ℝ) x =
      ∑ σ, if rel σ s = sc n a then sgn σ * Φ (pm σ x) else 0 := by
  classical
  change ev x (lift a hΦ s) = _
  simp only [lift, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs <;> simp

lemma rel_rel (σ ρ : Equiv.Perm (Fin (n + 1))) (s : SpinC n) :
    rel σ (rel ρ s) = rel (ρ * σ) s := rfl

lemma FermD_lift {Φ : Cfg n → ℝ} (hΦ : Φ ∈ D0 n) : FermD (lift a hΦ) := by
  classical
  intro ρ s x
  change (lift a hΦ (rel ρ s) : Cfg n → ℝ) (pm ρ x) = sgn ρ * (lift a hΦ s : Cfg n → ℝ) x
  rw [lift_apply, lift_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ρ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulLeft, rel_rel, ← pm_mul]
  by_cases h : rel (ρ * σ) s = sc n a
  · simp only [h, ite_true, sgn_mul]
    linear_combination (-(sgn σ * Φ (pm (ρ * σ) x))) * sgn_mul_self ρ
  · simp [h]

lemma Pc_lift {Φ : Cfg n → ℝ} (hΦ : Φ ∈ D0 n) (ha : a ≤ n + 1) : Pc a (lift a hΦ) = lift a hΦ := by
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

open Classical in
lemma lift_sc {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomY a n) :
    lift a (DomY_le_D0 hΦ) (sc n a) =
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => YG a σ).card : ℝ) •
        (⟨Φ, DomY_le_D0 hΦ⟩ : D0 n) := by
  classical
  apply Subtype.ext; funext x
  rw [lift_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : YG a σ
  · rw [ite_eq_left ((rel_sc_iff σ).2 hσ), ite_eq_left hσ,
      show Φ (pm σ x) = sgn σ * Φ x from hΦ.2.1 σ hσ x,
      ← mul_assoc, sgn_mul_self]; simp
  · rw [ite_eq_right (fun h => hσ ((rel_sc_iff σ).1 h)), ite_eq_right hσ]; simp

end lift

end DFT.Continuum.Line
