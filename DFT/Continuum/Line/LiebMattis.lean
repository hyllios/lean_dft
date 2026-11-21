/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.LiebMattisSign

/-!
# The Lieb–Mattis theorem on a line

For `N = n + 1` spin-½ particles on `[0, 1]` with a spin-independent Hamiltonian
`-Δ + Σ_k v(x_k) + w(x)` (`w` invariant under relabelling, `Σ_k v(x_k) + w` smooth on the closed
cube), the sector with `a` particles of spin up and `b = N - a` of spin down is described by
spatial wave functions antisymmetric within the first `a` and within the last `b` particles. Let
`E(a, b)` be its ground-state energy. **Lieb–Mattis**:

`E(a, b) < E(a + 1, b - 1)` whenever `a ≥ b ≥ 1`,

so polarising the ground state costs energy (`lieb_mattis`).

The proof. Let `g` be a ground state of type `(a + 1, b - 1)` with energy `E'`. Its Young
antisymmetrisation `f = Σ_{σ ∈ YG a} sgn σ · g ∘ σ` (the lowering operator `S₋`, up to a factor)
has type `(a, b)`, solves the same Schrödinger equation, and so has energy `E'`. Hence
`E(a, b) ≤ E'`. If equality held, `f` would be a ground state of type `(a, b)` and have a strict
sign on the region where each group is ordered (`gs_sign_RY`). But at two explicit configurations
`C₁, C₂` of that region, in which every spin-down particle but the last sits on a spin-up one, all
terms of `f` vanish except those moving the last spin-down particle, and these have a common sign
that flips between `C₁` and `C₂` (one spin-up particle is moved above the last spin-down one).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ} {a : ℕ}

/-! ### Derivatives of finite sums and of the Young antisymmetrisation -/

lemma dk_finsum {ι : Type*} (s : Finset ι) {F : ι → Cfg n → ℝ}
    (hF : ∀ i, Differentiable ℝ (F i)) (k : Fin (n + 1)) :
    dk k (fun y => ∑ i ∈ s, F i y) = fun x => ∑ i ∈ s, dk k (F i) x := by
  funext x
  simp only [dk]
  rw [show (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, F i from
    funext fun y => (Finset.sum_apply y s F).symm, fderiv_sum (fun i _ => (hF i x))]
  simp

lemma dk_const_mul' {F : Cfg n → ℝ} (hF : Differentiable ℝ F) (c : ℝ) (k : Fin (n + 1)) :
    dk k (fun y => c * F y) = fun x => c * dk k F x := by
  funext x
  simp only [dk]
  rw [fderiv_const_mul (hF x)]
  simp

/-- The coefficients of the Young antisymmetrisation. -/
noncomputable def cYG (a : ℕ) (σ : Equiv.Perm (Fin (n + 1))) : ℝ :=
  open Classical in if YG a σ then sgn σ else 0

lemma altY_eq (g : Cfg n → ℝ) :
    altY a g = fun x => ∑ σ : Equiv.Perm (Fin (n + 1)), cYG a σ * g (pm σ x) := by
  classical
  funext x
  simp only [altY, cYG]
  refine Finset.sum_congr rfl fun _ _ => ?_
  split_ifs <;> simp

lemma lapN_altY {g : Cfg n → ℝ} (hg : ContDiff ℝ 2 g) (x : Cfg n) :
    lapN (altY a g) x = altY a (lapN g) x := by
  have hd : ∀ σ : Equiv.Perm (Fin (n + 1)), Differentiable ℝ fun y => g (pm σ y) := fun σ =>
    (hg.comp (contDiff_pm σ)).differentiable (by norm_num)
  have hd1 : ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ k,
      Differentiable ℝ (dk k fun y => g (pm σ y)) := fun σ k =>
    (contDiff_dk (hg.comp (contDiff_pm σ)) k).differentiable one_ne_zero
  rw [altY_eq, altY_eq]
  simp only [lapN, dkk]
  have e1 : ∀ k, dk k (fun y => ∑ σ : Equiv.Perm (Fin (n + 1)), cYG a σ * g (pm σ y)) =
      fun y => ∑ σ : Equiv.Perm (Fin (n + 1)), cYG a σ * dk k (fun z => g (pm σ z)) y := by
    intro k
    rw [dk_finsum _ (fun σ => (hd σ).const_mul (cYG a σ)) k]
    funext y
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [dk_const_mul' (hd σ)]
  have e2 : ∀ k, dk k (fun y => ∑ σ : Equiv.Perm (Fin (n + 1)),
      cYG a σ * dk k (fun z => g (pm σ z)) y) x =
      ∑ σ : Equiv.Perm (Fin (n + 1)), cYG a σ * dk k (dk k fun z => g (pm σ z)) x := by
    intro k
    rw [dk_finsum _ (fun σ => (hd1 σ k).const_mul (cYG a σ)) k]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [dk_const_mul' (hd1 σ k)]
  simp only [e1, e2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have := lapN_comp_pm hg σ x
  simp only [lapN, dkk] at this
  exact this

lemma altY_wall {g : Cfg n → ℝ} (hgw : ∀ x k, (x k = 0 ∨ x k = 1) → g x = 0) (x : Cfg n)
    (k : Fin (n + 1)) (hk : x k = 0 ∨ x k = 1) : altY a g x = 0 := by
  classical
  simp only [altY]
  refine Finset.sum_eq_zero fun σ _ => ?_
  split_ifs
  · rw [hgw (pm σ x) (σ⁻¹ k) (by simpa using hk), mul_zero]
  · rfl

lemma altY_memY {g : Cfg n → ℝ} (hg : ContDiff ℝ 2 g)
    (hgw : ∀ x k, (x k = 0 ∨ x k = 1) → g x = 0) : altY a g ∈ DomY a n :=
  ⟨contDiff_altY hg, fun _ hσ x => altY_pm g hσ x, fun x k hk => altY_wall hgw x k hk⟩

/-! ### The lowered state has the energy of `g` -/

section energy

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} (hws : ∀ σ x, w (pm σ x) = w x)
include hws

/-- If `g` solves `-Δg + (V - E') g = 0` on the cube, so does its Young antisymmetrisation, and
its energy is `E' ⟨f, f⟩`. -/
lemma Q_altY {c : ℕ} {g : Cfg n → ℝ} (hg : IsGS (settingS (ymix c) w hw) v g) :
    Q (settingS (ymix a) w hw) v (altY a g) =
      Q (settingS (ymix c) w hw) v g / ip (μ := μN n) g g *
        ip (μ := μN n) (altY a g) (altY a g) := by
  have hD : g ∈ DomY c n := hg.1
  set E := Q (settingS (ymix c) w hw) v g / ip (μ := μN n) g g
  set f := altY a g
  have hfD : f ∈ DomY a n := altY_memY hD.1 hD.2.2
  have heq := strong_eq_Y hws hg
  -- the strong equation for `f`
  have hfeq : ∀ x ∈ Cube n, lapN f x = (w x + LN n v x - E) * f x := by
    intro x hx
    rw [show f = altY a g from rfl, lapN_altY hD.1, altY_eq (g := lapN g), altY_eq (g := g)]
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have := heq (pm σ x) (pm_mem_cube.2 hx)
    rw [hws, LN_pm] at this
    linear_combination (-cYG a σ) * this
  have hc := hfD.1.continuous
  -- the kinetic energy by parts
  have hkin : ∫ x, ∑ k, dk k f x * dk k f x ∂μN n = -∫ x, lapN f x * f x ∂μN n := by
    rw [integral_finsetSum (f := fun k x => dk k f x * dk k f x) _ fun k _ =>
      integrableN ((contDiff_dk hfD.1 k).continuous.mul (contDiff_dk hfD.1 k).continuous)]
    simp only [ibpN0 hfD.1 hfD.1 hfD.2.2]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum (f := fun k x => dkk k f x * f x) _
      fun k _ => integrableN ((continuous_dkk hfD.1 k).mul hc)]
    congr 2; funext x; simp only [lapN, Finset.sum_mul]
  rw [QS_eq v hfD, hkin]
  have hlap : ∫ x, lapN f x * f x ∂μN n = ∫ x, (w x + LN n v x - E) * (f x * f x) ∂μN n := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
    rw [hfeq x hx]; ring
  rw [hlap]
  have i1 := integrableN (F := fun x => (w x + LN n v x - E) * (f x * f x))
    (((hw.add (continuous_LN v)).sub continuous_const).mul (hc.mul hc))
  have i2 := integrableN (F := fun x => (LN n v x + w x) * (f x * f x))
    (((continuous_LN v).add hw).mul (hc.mul hc))
  have hsub : ∫ x, (LN n v x + w x) * (f x * f x) ∂μN n -
      ∫ x, (w x + LN n v x - E) * (f x * f x) ∂μN n = E * ∫ x, f x * f x ∂μN n := by
    rw [← integral_sub i2 i1, ← integral_const_mul]
    congr 1; funext x; ring
  change _ = E * ∫ x, f x * f x ∂μN n
  linarith

end energy

/-! ### Two configurations of the ordered region -/

/-- Ranks of the first configuration: spin up `0, …, a-b` at the bottom, then the spin-down
particles `a, …, n` at ranks `a-b+1, a-b+3, …`, each but the last shared with a spin-up one. -/
def rk1 (a b i : ℕ) : ℕ :=
  if i ≤ a - b then i else if i < a then (a - b + 1) + 2 * (i - (a - b + 1))
  else (a - b + 1) + 2 * (i - a)

/-- Ranks of the second configuration: as `rk1`, with spin-up particle `a - 1` at the top. -/
def rk2 (a b n i : ℕ) : ℕ :=
  if i + 1 ≤ a - b then i else if i + 1 < a then (a - b) + 2 * (i - (a - b))
  else if i + 1 = a then n + 1 else (a - b) + 2 * (i - a)

/-- A configuration from ranks. -/
noncomputable def cfgR (n : ℕ) (r : ℕ → ℕ) : Cfg n := fun i => ((r i : ℝ) + 1) / (n + 3)

lemma cfgR_lt {r : ℕ → ℕ} {i j : Fin (n + 1)} : cfgR n r i < cfgR n r j ↔ r i < r j := by
  simp only [cfgR]
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  constructor
  · intro h; exact_mod_cast (by linarith : (r i : ℝ) < r j)
  · intro h; have : (r i : ℝ) < r j := by exact_mod_cast h
    linarith

lemma cfgR_eq {r : ℕ → ℕ} {i j : Fin (n + 1)} : cfgR n r i = cfgR n r j ↔ r i = r j := by
  simp only [cfgR]
  rw [div_left_inj' (by positivity)]
  constructor
  · intro h; exact_mod_cast (by linarith : (r i : ℝ) = r j)
  · intro h; rw [h]

lemma cfgR_mem_cube {r : ℕ → ℕ} (hr : ∀ i : Fin (n + 1), r i ≤ n + 1) : cfgR n r ∈ Cube n := by
  intro i _
  have h := hr i
  have h' : (r i : ℝ) + 1 < n + 3 := by
    have : (r i : ℝ) ≤ n + 1 := by exact_mod_cast h
    linarith
  refine ⟨?_, ?_⟩
  · simp only [cfgR]; positivity
  · simp only [cfgR]; rw [div_lt_one (by positivity)]; exact h'

lemma cfgR_mem_RY {r : ℕ → ℕ} (hr : ∀ i : Fin (n + 1), r i ≤ n + 1)
    (hmono : ∀ i j : Fin (n + 1), i < j → SameB a i j → r i < r j) : cfgR n r ∈ RY a n :=
  ⟨cfgR_mem_cube hr, fun i j hij hs => cfgR_lt.2 (hmono i j hij hs)⟩

section config

variable {b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a)
include hab hb1 hba

omit hb1 in
lemma rk1_le (i : Fin (n + 1)) : rk1 a b i ≤ n + 1 := by
  have := i.2; unfold rk1; split_ifs <;> omega

lemma rk2_le (i : Fin (n + 1)) : rk2 a b n i ≤ n + 1 := by
  have := i.2; unfold rk2; split_ifs <;> omega

omit hb1 in
lemma rk1_mono (i j : Fin (n + 1)) (hij : i < j) (hs : SameB a i j) : rk1 a b i < rk1 a b j := by
  have := i.2; have := j.2; have hij' : (i : ℕ) < j := hij
  simp only [SameB] at hs; unfold rk1; split_ifs <;> omega

omit hb1 in
lemma rk2_mono (i j : Fin (n + 1)) (hij : i < j) (hs : SameB a i j) :
    rk2 a b n i < rk2 a b n j := by
  have := i.2; have := j.2; have hij' : (i : ℕ) < j := hij
  simp only [SameB] at hs; unfold rk2; split_ifs <;> omega

/-- Every spin-down particle but the last shares its position with a spin-up one. -/
lemma rk1_cover (q : Fin (n + 1)) (hq1 : a ≤ (q : ℕ)) (hq2 : (q : ℕ) < n) :
    ∃ i : Fin (n + 1), (i : ℕ) < a ∧ rk1 a b i = rk1 a b q :=
  ⟨⟨a - b + 1 + (q - a), by omega⟩, by simp only; omega, by
    simp only [rk1]; split_ifs <;> omega⟩

lemma rk2_cover (q : Fin (n + 1)) (hq1 : a ≤ (q : ℕ)) (hq2 : (q : ℕ) < n) :
    ∃ i : Fin (n + 1), (i : ℕ) < a ∧ rk2 a b n i = rk2 a b n q :=
  ⟨⟨a - b + (q - a), by omega⟩, by simp only; omega, by
    simp only [rk2]; split_ifs <;> omega⟩

lemma rk1_top (i : Fin (n + 1)) (hi : (i : ℕ) < n) : rk1 a b i < rk1 a b (Fin.last n) := by
  have := i.2; simp only [Fin.val_last]; unfold rk1; split_ifs <;> omega

lemma rk2_top (i : Fin (n + 1)) (hi : (i : ℕ) < n) (hi' : (i : ℕ) + 1 ≠ a) :
    rk2 a b n i < rk2 a b n (Fin.last n) := by
  have := i.2; simp only [Fin.val_last]; unfold rk2; split_ifs <;> omega

lemma rk2_top' (i : Fin (n + 1)) (hi' : (i : ℕ) + 1 = a) :
    rk2 a b n (Fin.last n) < rk2 a b n i := by
  have := i.2; simp only [Fin.val_last]; unfold rk2; split_ifs <;> omega

end config

/-! ### The sign of the lowered state at the two configurations -/

section sign

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} (hws : ∀ σ x, w (pm σ x) = w x)
  {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
  (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x)
  {b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a)
include hws hF hVF hab hb1 hba

omit hws hF hVF hba in
/-- **The common sign of the surviving terms.** For a configuration `C` of the ordered region in
which every spin-down particle but the last shares its position with a spin-up one, and the
last spin-down particle is above all other spin-down ones, `s₀ · ε · Q · f(C) > 0`, where `ε` is
the sign of `Π_{i<a} (C_last - C_i)`. -/
lemma sign_altY {g : Cfg n → ℝ} (hg : IsGS (settingS (ymix (a + 1)) w hw) v g) {s₀ : ℝ}
    (hs₀ : s₀ = 1 ∨ s₀ = -1)
    (hpos : ∀ y ∈ Cube n, NoSame (a + 1) y → 0 < s₀ * (SY (a + 1) y * g y))
    {C : Cfg n} (hC : C ∈ RY a n) {ε : ℝ}
    (hε : (∏ i : Fin (n + 1), if (i : ℕ) < a then Real.sign (C (Fin.last n) - C i) else 1) = ε)
    (hcov : ∀ q : Fin (n + 1), a ≤ (q : ℕ) → (q : ℕ) < n →
      ∃ i : Fin (n + 1), (i : ℕ) < a ∧ C i = C q)
    (hAtop : ∀ i : Fin (n + 1), (i : ℕ) < a → C i ≠ C (Fin.last n))
    (hBtop : ∀ j : Fin (n + 1), a ≤ (j : ℕ) → (j : ℕ) < n → C j < C (Fin.last n)) :
    0 < s₀ * ε * (∏ j : Fin (n + 1), if a < (j : ℕ) then (-1 : ℝ) else 1) * altY a g C := by
  classical
  have hD : g ∈ DomY (a + 1) n := hg.1
  have ha : a < n + 1 := by omega
  set p : Fin (n + 1) := ⟨a, ha⟩
  set Qc : ℝ := ∏ j : Fin (n + 1), if a < (j : ℕ) then (-1 : ℝ) else 1
  have hCc : C ∈ Cube n := hC.1
  have hns : NoSame a C := NoSame.of_RY hC
  rw [altY_eq, Finset.mul_sum]
  -- each term is nonnegative, and positive for `σ = swap p last`
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)), YG a σ → σ p = Fin.last n →
      0 < s₀ * ε * Qc * (sgn σ * g (pm σ C)) := by
    intro σ hσ hσp
    set y := pm σ C
    have hy : y ∈ Cube n := pm_mem_cube.2 hCc
    have hnsA : NoSame a y := hns.pm hσ
    -- no collisions in the grouping `a + 1`
    have hnsB : NoSame (a + 1) y := by
      intro i j hij hs
      simp only [y, pm_apply]
      by_cases hi : (i : ℕ) < a + 1 <;> by_cases hj : (j : ℕ) < a + 1
      · -- both in the first group of `a + 1`
        by_cases hia : (i : ℕ) = a
        · have : i = p := Fin.ext hia
          subst this
          rw [hσp]
          have hj' : (j : ℕ) < a := by have : j ≠ p := hij.symm; omega
          exact (hAtop (σ j) ((hσ j).2 hj')).symm
        by_cases hja : (j : ℕ) = a
        · have : j = p := Fin.ext hja
          subst this
          rw [hσp]
          exact hAtop (σ i) ((hσ i).2 (by omega))
        exact hns (σ i) (σ j) (fun h => hij (σ.injective h))
          (by simp only [SameB, hσ i, hσ j]; omega)
      · exact absurd hs (by simp only [SameB]; omega)
      · exact absurd hs (by simp only [SameB]; omega)
      · exact hns (σ i) (σ j) (fun h => hij (σ.injective h))
          (by simp only [SameB, hσ i, hσ j]; omega)
    have h1 := hpos y hy hnsB
    -- `sgn σ = SY a y`
    have h2 : SY a y = sgn σ := by rw [SY_pm' hσ hCc hns, SY_RY hC, mul_one]
    have h3 := SY_mul_SY_succ (p := p) rfl hnsA
    -- `Rlow` and `Rhigh` at `y`
    have hlow : Rlow a p y = ε := by
      rw [← hε, Rlow, ← Equiv.prod_comp σ (fun i' : Fin (n + 1) =>
        if (i' : ℕ) < a then Real.sign (C (Fin.last n) - C i') else 1)]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [y, pm_apply, hσp]
      exact if_congr (hσ i).symm rfl rfl
    have hhigh : Rhigh a p y = Qc := by
      rw [Rhigh]
      refine Finset.prod_congr rfl fun j _ => ?_
      split_ifs with hj
      · simp only [y, pm_apply, hσp]
        have hσj : a ≤ (σ j : ℕ) := not_lt.1 fun h => by have := (hσ j).1 h; omega
        have hσj' : (σ j : ℕ) < n := by
          have hne : σ j ≠ Fin.last n := fun e => by
            have : j = p := σ.injective (e.trans hσp.symm)
            rw [this] at hj; simp [p] at hj
          have := (σ j).2
          have : (σ j : ℕ) ≠ n := fun e => hne (Fin.ext e)
          omega
        exact Real.sign_of_neg (sub_neg.2 (hBtop (σ j) hσj hσj'))
      · rfl
    rw [hlow, hhigh] at h3
    -- combine
    have hsgn : sgn σ * sgn σ = 1 := sgn_mul_self σ
    have hss : s₀ * s₀ = 1 := by rcases hs₀ with h | h <;> rw [h] <;> norm_num
    calc 0 < s₀ * (SY (a + 1) y * g y) := h1
      _ = s₀ * ((ε * Qc) * (SY a y * g y)) := by
          rw [← h3, h2]; linear_combination (-(s₀ * SY (a + 1) y * g y)) * hsgn
      _ = s₀ * ε * Qc * (sgn σ * g (pm σ C)) := by rw [h2]; ring
  have hvanish : ∀ σ : Equiv.Perm (Fin (n + 1)), YG a σ → σ p ≠ Fin.last n →
      g (pm σ C) = 0 := by
    intro σ hσ hσp
    have hq1 : a ≤ (σ p : ℕ) := not_lt.1 fun h => by have := (hσ p).1 h; simp [p] at this
    have hq2 : (σ p : ℕ) < n := by
      have := (σ p).2
      have : (σ p : ℕ) ≠ n := fun e => hσp (Fin.ext e)
      omega
    obtain ⟨i0, hi0, hCi0⟩ := hcov (σ p) hq1 hq2
    set i' := σ⁻¹ i0
    have hi' : (i' : ℕ) < a := by
      have := (YG_inv hσ i0).2 hi0; exact this
    refine eq_zero_of_collisionY hD (i := i') (j := p) (fun e => by
      rw [e] at hi'; simp [p] at hi') (by simp only [SameB, p]; omega) ?_
    have hσi : σ i' = i0 := by simp [i']
    simp only [pm_apply, hσi, hCi0]
  set σ0 := Equiv.swap p (Fin.last n)
  have hσ0 : YG a σ0 := YG_swap (by simp only [SameB, p, Fin.val_last]; omega)
  have hσ0p : σ0 p = Fin.last n := Equiv.swap_apply_left _ _
  refine Finset.sum_pos' (fun σ _ => ?_) ⟨σ0, Finset.mem_univ _, ?_⟩
  · simp only [cYG]
    split_ifs with hσ
    · by_cases hσp : σ p = Fin.last n
      · have := hterm σ hσ hσp; linarith
      · rw [hvanish σ hσ hσp]; simp
    · simp
  · simp only [cYG, ite_eq_left hσ0]
    have := hterm σ0 hσ0 hσ0p; linarith

end sign

/-! ### The theorem -/

/-- A `C²` function of zero norm vanishes on the open cube. -/
lemma eq_zero_of_ip_zero' {φ : Cfg n → ℝ} (h2 : ContDiff ℝ 2 φ)
    (h : ip (μ := μN n) φ φ = 0) : ∀ x ∈ Cube n, φ x = 0 := by
  have hc := h2.continuous
  have hae : (fun x => φ x * φ x) =ᵐ[μN n] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (φ x))
      (integrableN (hc.mul hc))).1 h
  have hz : EqOn (fun x => φ x * φ x) (fun _ => 0) (Cube n) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_cube (hc.mul hc).continuousOn continuousOn_const
  exact fun x hx => mul_self_eq_zero.1 (hz hx)

section main

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} (hws : ∀ σ x, w (pm σ x) = w x)
  {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
  (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x)
include hws hF hVF

/-- **The Lieb–Mattis theorem on a line.** With `a` particles of spin up and `b` of spin down,
`a + b = N`, `a ≥ b ≥ 1`: the ground-state energy of the sector `(a, b)` is strictly below that
of `(a + 1, b - 1)`. -/
theorem lieb_mattis {b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a)
    {Φ Ψ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a) w hw) v Φ)
    (hΨ : IsGS (settingS (ymix (a + 1)) w hw) v Ψ) :
    Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ <
      Q (settingS (ymix (a + 1)) w hw) v Ψ / ip (μ := μN n) Ψ Ψ := by
  set E := Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ
  set E' := Q (settingS (ymix (a + 1)) w hw) v Ψ / ip (μ := μN n) Ψ Ψ
  set f := altY a Ψ
  have hfD : f ∈ DomY a n := altY_memY hΨ.1.1 hΨ.1.2.2
  have hQf : Q (settingS (ymix a) w hw) v f = E' * ip (μ := μN n) f f := Q_altY hws hΨ
  obtain ⟨s₀, hs₀, hpos⟩ := gs_SY_pos hws hF hVF hΨ
  set Qc : ℝ := ∏ j : Fin (n + 1), if a < (j : ℕ) then (-1 : ℝ) else 1
  -- the two configurations
  set C1 := cfgR n (rk1 a b)
  set C2 := cfgR n (rk2 a b n)
  have hC1 : C1 ∈ RY a n := cfgR_mem_RY (rk1_le hab hba) (rk1_mono hab hba)
  have hC2 : C2 ∈ RY a n := cfgR_mem_RY (rk2_le hab hb1 hba) (rk2_mono hab hba)
  have hlast : ((Fin.last n : Fin (n + 1)) : ℕ) = n := Fin.val_last n
  have hε1 : (∏ i : Fin (n + 1), if (i : ℕ) < a then Real.sign (C1 (Fin.last n) - C1 i) else 1)
      = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    split_ifs with hi
    · exact Real.sign_of_pos (sub_pos.2 (cfgR_lt.2 (rk1_top hab hb1 hba i (by omega))))
    · rfl
  have hε2 : (∏ i : Fin (n + 1), if (i : ℕ) < a then Real.sign (C2 (Fin.last n) - C2 i) else 1)
      = -1 := by
    have ha1 : a - 1 < n + 1 := by omega
    rw [Finset.prod_eq_single (⟨a - 1, ha1⟩ : Fin (n + 1))]
    · simp only [show a - 1 < a by omega, ite_true]
      exact Real.sign_of_neg (sub_neg.2 (cfgR_lt.2 (rk2_top' hab hb1 hba _ (by simp; omega))))
    · intro i _ hi
      split_ifs with hia
      · refine Real.sign_of_pos (sub_pos.2 (cfgR_lt.2 (rk2_top hab hb1 hba i (by omega) ?_)))
        intro e; exact hi (Fin.ext (by simp; omega))
      · rfl
    · simp
  have hS1 := sign_altY hab hb1 hΨ hs₀ hpos hC1 hε1
    (fun q h1 h2 => (rk1_cover hab hb1 hba q h1 h2).imp fun i hi => ⟨hi.1, cfgR_eq.2 hi.2⟩)
    (fun i hi => fun e => (ne_of_lt (rk1_top hab hb1 hba i (by omega))) (cfgR_eq.1 e))
    (fun j _ hj2 => cfgR_lt.2 (rk1_top hab hb1 hba j hj2))
  have hS2 := sign_altY hab hb1 hΨ hs₀ hpos hC2 hε2
    (fun q h1 h2 => (rk2_cover hab hb1 hba q h1 h2).imp fun i hi => ⟨hi.1, cfgR_eq.2 hi.2⟩)
    (fun i hi => fun e => by
      by_cases h : (i : ℕ) + 1 = a
      · exact (ne_of_lt (rk2_top' hab hb1 hba i h)) (cfgR_eq.1 e).symm
      · exact (ne_of_lt (rk2_top hab hb1 hba i (by omega) h)) (cfgR_eq.1 e))
    (fun j hj1 hj2 => cfgR_lt.2 (rk2_top hab hb1 hba j hj2 (by omega)))
  change 0 < s₀ * 1 * Qc * f C1 at hS1
  change 0 < s₀ * (-1) * Qc * f C2 at hS2
  -- `f ≠ 0`, so `E ≤ E'`
  have hf1 : f C1 ≠ 0 := fun h => by rw [h, mul_zero] at hS1; exact lt_irrefl 0 hS1
  have hipf : 0 < ip (μ := μN n) f f := by
    by_contra hle
    have h0 : ip (μ := μN n) f f = 0 :=
      le_antisymm (not_lt.1 hle) (integral_nonneg fun x => mul_self_nonneg _)
    exact hf1 (eq_zero_of_ip_zero' hfD.1 h0 C1 hC1.1)
  have hle : E ≤ E' := by
    have := hΦ.2.2 f hfD
    rw [hQf] at this
    have hp := hΦ.2.1
    rw [div_le_iff₀ hp]
    nlinarith
  refine lt_of_le_of_ne hle fun heq => ?_
  -- otherwise `f` is a ground state of type `(a, b)`
  have hfGS : IsGS (settingS (ymix a) w hw) v f := by
    refine ⟨hfD, hipf, fun φ hφ => ?_⟩
    rw [hQf, ← heq]
    have := le_Q_of_isGS hΦ hφ
    nlinarith
  set X := s₀ * Qc
  have e1 : 0 < X * f C1 := by
    have : s₀ * 1 * Qc * f C1 = X * f C1 := by simp only [X]; ring
    linarith
  have e2 : 0 < -(X * f C2) := by
    have : s₀ * (-1) * Qc * f C2 = -(X * f C2) := by simp only [X]; ring
    linarith
  rcases gs_sign_RY hws hF hVF hfGS with h | h
  · have a1 := h C1 hC1
    have a2 := h C2 hC2
    rcases le_or_gt X 0 with hX | hX <;> nlinarith
  · have a1 := h C1 hC1
    have a2 := h C2 hC2
    rcases le_or_gt X 0 with hX | hX <;> nlinarith

end main

end DFT.Continuum.Line
