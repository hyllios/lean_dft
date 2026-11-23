/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.General

/-!
# States of mixed exchange symmetry, and their ground states

For spin-½ particles with a spin-independent Hamiltonian, the sector with `a` particles of spin
up and `b = N - a` of spin down is described by spatial wave functions that are antisymmetric
under relabellings of the first `a` particles and of the last `b` particles, and have no symmetry
under exchanges between the two groups.

* `DomS s`, `settingS s`: the `C²` states and the Hohenberg–Kohn setting for any symmetry type
  `s : SymT n` (a set of relabellings and a character on it).
* `YG a`: the Young subgroup of relabellings preserving `{0, …, a - 1}`; `ymix a`: the symmetry
  type `(YG a, sign)`.
* `exists_adm_ymix`: normalised admissible coefficient sequences of type `ymix a` exist.
* `exists_isGS_S`, `exists_isGS_smoothS`: **ground states of mixed symmetry exist** (for the
  kernel bound of `Sine/Mixed`, in particular for `Σ_k v(x_k) + w` smooth on the closed cube).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Sine

variable {n : ℕ}

/-! ### States of a symmetry type -/

/-- `C²` states of symmetry type `s`, vanishing on the walls. -/
def DomS (s : SymT n) : Submodule ℝ (Cfg n → ℝ) where
  carrier := {ψ | ContDiff ℝ 2 ψ ∧ (∀ σ, s.G σ → ∀ x, ψ (pm σ x) = s.χ σ * ψ x) ∧
    ∀ x k, (x k = 0 ∨ x k = 1) → ψ x = 0}
  add_mem' ha hb := ⟨ha.1.add hb.1, fun σ hσ x => by
      simp [ha.2.1 σ hσ x, hb.2.1 σ hσ x]; ring,
    fun x k hk => by simp [ha.2.2 x k hk, hb.2.2 x k hk]⟩
  zero_mem' := ⟨contDiff_const, fun _ _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' r _ ha := ⟨ha.1.const_smul r, fun σ hσ x => by simp [ha.2.1 σ hσ x]; ring,
    fun x k hk => by simp [ha.2.2 x k hk]⟩

lemma cont_kin0 {ψ φ : Cfg n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hφ : ContDiff ℝ 2 φ) :
    Continuous fun x => ∑ k, dk k ψ x * dk k φ x :=
  continuous_finsetSum _ fun k _ =>
    (contDiff_dk hψ k).continuous.mul (contDiff_dk hφ k).continuous

/-- The Hohenberg–Kohn setting for states of symmetry type `s`. -/
noncomputable def settingS (s : SymT n) (w : Cfg n → ℝ) (hw : Continuous w) :
    Setting (μN n) Pot where
  D := DomS s
  h0 := h0N n w
  h0_add a ha b hb c hc := by
    have e : ∀ k, dk k (a + b) = dk k a + dk k b :=
      dk_add (ha.1.differentiable (by norm_num)) (hb.1.differentiable (by norm_num))
    simp only [h0N, e, Pi.add_apply]
    have ia := integrableN (cont_kin0 ha.1 hc.1)
    have ib := integrableN (cont_kin0 hb.1 hc.1)
    have ja := integrableN (hw.mul (ha.1.continuous.mul hc.1.continuous))
    have jb := integrableN (hw.mul (hb.1.continuous.mul hc.1.continuous))
    have h1 : ∫ x, ∑ k, (dk k a x + dk k b x) * dk k c x ∂μN n =
        ∫ x, ∑ k, dk k a x * dk k c x ∂μN n + ∫ x, ∑ k, dk k b x * dk k c x ∂μN n := by
      rw [← integral_add (f := fun x => ∑ k, dk k a x * dk k c x)
        (g := fun x => ∑ k, dk k b x * dk k c x) ia ib]
      congr 1; funext x; rw [← Finset.sum_add_distrib]; congr 1; funext k; ring
    have h2 : ∫ x, w x * ((a x + b x) * c x) ∂μN n =
        ∫ x, w x * (a x * c x) ∂μN n + ∫ x, w x * (b x * c x) ∂μN n := by
      rw [← integral_add (f := fun x => w x * (a x * c x)) (g := fun x => w x * (b x * c x)) ja jb]
      congr 1; funext x; ring
    rw [h1, h2]; ring
  h0_smul r a ha c hc := by
    have e : ∀ k, dk k (r • a) = r • dk k a := dk_smul (ha.1.differentiable (by norm_num)) r
    simp only [h0N, e, Pi.smul_apply, smul_eq_mul]
    have h1 : ∫ x, ∑ k, r * dk k a x * dk k c x ∂μN n =
        r * ∫ x, ∑ k, dk k a x * dk k c x ∂μN n := by
      rw [← integral_const_mul]; congr 1; funext x; rw [Finset.mul_sum]; congr 1; funext k; ring
    have h2 : ∫ x, w x * (r * a x * c x) ∂μN n = r * ∫ x, w x * (a x * c x) ∂μN n := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [h1, h2]; ring
  h0_symm ψ _ φ _ := by
    simp only [h0N]
    congr 1
    · congr 1; funext x; congr 1; funext k; ring
    · congr 1; funext x; ring
  L := LN n
  int_L v ψ φ hψ hφ := integrableN ((continuous_LN v).mul (hψ.1.continuous.mul hφ.1.continuous))
  int_sq ψ φ hψ hφ := integrableN (hψ.1.continuous.mul hφ.1.continuous)

/-! ### The Young subgroup -/

/-- Relabellings that map the first `a` particles among themselves. -/
def YG (a : ℕ) (σ : Equiv.Perm (Fin (n + 1))) : Prop := ∀ i, ((σ i : ℕ) < a ↔ (i : ℕ) < a)

lemma YG_one (a : ℕ) : YG a (1 : Equiv.Perm (Fin (n + 1))) := fun _ => Iff.rfl

lemma YG_mul {a : ℕ} {σ ρ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) (hρ : YG a ρ) :
    YG a (σ * ρ) := fun i => (hσ (ρ i)).trans (hρ i)

lemma YG_inv {a : ℕ} {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) : YG a σ⁻¹ := fun i => by
  have := hσ (σ⁻¹ i)
  rw [show σ (σ⁻¹ i) = i by simp] at this
  exact this.symm

/-- Antisymmetry within the first `a` and within the last `N - a` particles. -/
noncomputable def ymix (a : ℕ) : SymT n := ⟨YG a, sgn⟩

/-- `DomS (ymix a)`: states antisymmetric within each of the two groups. -/
noncomputable abbrev DomY (a n : ℕ) := DomS (ymix (n := n) a)

/-! ### Coefficients -/

lemma cN_InS_S {s : SymT n} {φ : Cfg n → ℝ} (hφ : φ ∈ DomS s) : InS s fun m => cN m φ :=
  fun σ hσ m => by
    change cN (pmI σ m) φ = s.χ σ * cN m φ
    rw [cN_eq, cN_eq, ← integral_pm σ, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [smd_pm, hφ.2.1 σ hσ x]; ring

lemma Dir_cN_S {s : SymT n} {φ : Cfg n → ℝ} (hφ : φ ∈ DomS s) : Dir s fun m => cN m φ :=
  ⟨(hasSum_ip hφ.1.continuous).summable, by simpa [lam] using (hasSum_kin0 hφ.1 hφ.2.2).summable,
    cN_InS_S hφ⟩

lemma Q_eq_Fn_S {s : SymT n} {w : Cfg n → ℝ} (hw : Continuous w) (v : Pot) {φ : Cfg n → ℝ}
    (hφ : φ ∈ DomS s) :
    Q (settingS s w hw) v φ = Fn (fun x => LN n v x + w x) fun m => cN m φ := by
  have hc := hφ.1.continuous
  have hVc : Continuous fun x => LN n v x + w x := (continuous_LN v).add hw
  rw [Fn, Bf_cN hVc hc]
  have hk : ∑' m, lam m * cN m φ ^ 2 = ∫ x, ∑ k, dk k φ x * dk k φ x ∂μN n := by
    simpa [lam] using (hasSum_kin0 hφ.1 hφ.2.2).tsum_eq
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

/-! ### An admissible sequence of mixed symmetry -/

/-- The multi-index `m₀ = (0, 1, …, n)`. -/
def m0 (n : ℕ) : Fin (n + 1) → ℕ := fun i => i

lemma m0_injective : Function.Injective (m0 n) := fun _ _ h => Fin.ext h

lemma pmI_m0_eq {ρ ρ' : Equiv.Perm (Fin (n + 1))} (h : pmI ρ (m0 n) = pmI ρ' (m0 n)) : ρ = ρ' := by
  ext i
  have := congrFun h i
  simp only [pmI, m0] at this
  exact congrArg Fin.val (Fin.ext this)

/-- The Young antisymmetrisation of `δ_{m₀}`. -/
noncomputable def cY (a : ℕ) (m : Fin (n + 1) → ℕ) : ℝ :=
  open Classical in ∑ ρ : Equiv.Perm (Fin (n + 1)), if YG a ρ ∧ m = pmI ρ (m0 n) then sgn ρ else 0

lemma cY_InS (a : ℕ) : InS (ymix (n := n) a) (cY a) := by
  classical
  intro σ hσ m
  change cY a (pmI σ m) = sgn σ * cY a m
  simp only [cY, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight σ⁻¹) _ _ fun ρ => ?_
  simp only [Equiv.coe_mulRight]
  have hσ' : YG a σ := hσ
  have hiff : YG a (ρ * σ⁻¹) ↔ YG a ρ :=
    ⟨fun h => by simpa using YG_mul h hσ', fun h => YG_mul h (YG_inv hσ')⟩
  have hm : pmI σ m = pmI ρ (m0 n) ↔ m = pmI (ρ * σ⁻¹) (m0 n) := by
    constructor
    · intro h
      have := congrArg (pmI σ⁻¹) h
      rwa [pmI_pmI, pmI_pmI, mul_inv_cancel, pmI_one] at this
    · intro h
      rw [h, pmI_pmI, inv_mul_cancel_right]
  simp only [hiff, hm]
  split_ifs
  · rw [sgn_mul, sgn_inv]
    linear_combination (-sgn ρ) * sgn_mul_self σ
  · ring

lemma cY_m0 (a : ℕ) : cY a (m0 n) = 1 := by
  classical
  simp only [cY]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (n + 1)))]
  · simp [YG_one, pmI_one, sgn_one]
  · intro ρ _ hρ
    refine ite_eq_right_iff.2 fun h => ?_
    exact (hρ (pmI_m0_eq (ρ := ρ) (ρ' := 1) (by rw [pmI_one]; exact h.2.symm))).elim
  · simp

lemma cY_support (a : ℕ) (m : Fin (n + 1) → ℕ)
    (hm : m ∉ Finset.univ.image fun ρ : Equiv.Perm (Fin (n + 1)) => pmI ρ (m0 n)) :
    cY a m = 0 := by
  classical
  refine Finset.sum_eq_zero fun ρ _ => ?_
  refine ite_eq_right_iff.2 fun h => ?_
  exact (hm (h.2 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ ρ))).elim

/-- **Normalised admissible sequences of mixed symmetry exist.** -/
lemma exists_adm_ymix (a : ℕ) : ∃ c : (Fin (n + 1) → ℕ) → ℝ, Adm (ymix (n := n) a) c := by
  classical
  set T := Finset.univ.image fun ρ : Equiv.Perm (Fin (n + 1)) => pmI ρ (m0 n)
  have hz : ∀ m ∉ T, cY a m = 0 := cY_support a
  have hD : Dir (ymix (n := n) a) (cY a) :=
    ⟨summable_of_ne_finset_zero (s := T) fun m hm => by simp [hz m hm],
      summable_of_ne_finset_zero (s := T) fun m hm => by simp [hz m hm], cY_InS a⟩
  set S := ∑' m, cY a m ^ 2
  have hS : 0 < S := by
    have h1 : cY a (m0 n) ^ 2 ≤ S :=
      hD.sq.le_tsum (m0 n) fun m _ => sq_nonneg _
    rw [cY_m0, one_pow] at h1
    linarith
  set c := (√S)⁻¹
  refine ⟨fun m => c * cY a m, Dir_smul hD c, ?_⟩
  simp only [mul_pow]
  rw [tsum_mul_left, inv_pow, Real.sq_sqrt hS.le, inv_mul_cancel₀ hS.ne']

/-! ### Existence of ground states -/

section existence

variable {V : Cfg n → ℝ} {b : (Fin (n + 1) → ℕ) → ℝ} (hb0 : ∀ l, 0 ≤ b l) (hbS : Summable b)
  (hK : ∀ m' m, |Ker V m' m| ≤ ∑' l, b l * (if adm m' l m then 1 else 0))
include hb0 hbS hK

/-- The minimiser is a `C²` state of the symmetry type. -/
theorem ser_min2S (hVs : ∀ σ x, V (pm σ x) = V x) {s : SymT n} {a : (Fin (n + 1) → ℕ) → ℝ}
    (ha : Adm s a) (hmin : Fn V a = E0 V s) {r : ℝ} (hr : 1 / 2 < r) (hr2 : r ≤ 2)
    (hG : Summable fun l => b l * om r l) :
    ser a ∈ DomS s ∧ ∀ m, cN m (ser a) = a m := by
  have hEL := (kBd_of_kernel hb0 hbS hK).euler_lagrange hVs ha hmin
  have hq := summable_wt_sq_mul hb0 hbS hK hEL ha.sq hr hr2 hG
  have h0 : Summable fun m => |a m| := Summable.of_nonneg_of_le (fun m => abs_nonneg _)
    (fun m => le_mul_of_one_le_left (abs_nonneg _)
      (one_le_pow₀ (by exact_mod_cast one_le_wt m))) hq
  exact ⟨⟨contDiff_ser2 hq, fun σ hσ x => ser_pm ha.sym σ hσ x, ser_face a⟩, cN_ser h0⟩

end existence

section gs

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {b : (Fin (n + 1) → ℕ) → ℝ}

/-- **Ground states of a symmetry type exist** under the kernel bound. -/
theorem exists_isGS_S {s : SymT n} (hne : ∃ c, Adm s c) (hws : ∀ σ x, w (pm σ x) = w x)
    (hb0 : ∀ l, 0 ≤ b l) (hbS : Summable b)
    (hK : ∀ m' m, |Ker (fun x => LN n v x + w x) m' m| ≤
      ∑' l, b l * (if adm m' l m then 1 else 0))
    {r : ℝ} (hr : 1 / 2 < r) (hr2 : r ≤ 2) (hG : Summable fun l => b l * om r l) :
    ∃ Φ, IsGS (settingS s w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 := by
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hVs : ∀ σ x, V (pm σ x) = V x := fun σ x => by simp only [V, LN_pm, hws]
  obtain ⟨a, ha, hmin⟩ := (kBd_of_kernel hb0 hbS hK).exists_min (V := V) hne
  obtain ⟨hΦ, hcoef⟩ := ser_min2S hb0 hbS hK hVs ha hmin hr hr2 hG
  have hcoef' : (fun m => cN m (ser a)) = a := funext hcoef
  have hip : ip (μ := μN n) (ser a) (ser a) = 1 := by
    rw [ip_eq_tsum hΦ.1.continuous]; simp only [hcoef]; exact ha.norm
  have hQ : Q (settingS s w hw) v (ser a) = E0 V s := by
    rw [Q_eq_Fn_S hw v hΦ, hcoef', hmin]
  refine ⟨ser a, ⟨hΦ, hip ▸ one_pos, fun φ hφ => ?_⟩, hip⟩
  rw [hQ, hip, mul_one, Q_eq_Fn_S hw v hφ, ip_eq_tsum hφ.1.continuous]
  exact (kBd_of_kernel hb0 hbS hK).Fn_ge (Dir_cN_S hφ)

/-- **Ground states of mixed symmetry exist** whenever `Σ_k v(x_k) + w(x)` agrees on the closed
cube with a `C^{2N}` function. -/
theorem exists_isGS_smoothS (a : ℕ) (hws : ∀ σ x, w (pm σ x) = w x) {F : Cfg n → ℝ}
    (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F) (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x) :
    ∃ Φ, IsGS (settingS (ymix a) w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 := by
  obtain ⟨b, hb0, hbS, hK, hG⟩ := kernel_of_smooth ((continuous_LN v).add hw) hF hVF
  exact exists_isGS_S (exists_adm_ymix a) hws hb0 hbS hK (by norm_num) (by norm_num) hG

end gs

end DFT.Continuum.Line
