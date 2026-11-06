/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.TDDFT.Global

/-!
# Lattice TDDFT with complex hopping (magnetic flux)

A Hermitian hopping matrix `H = A + iB` (`A` real symmetric, `B` real antisymmetric, e.g. Peierls
phases) gives, for `ψ = x + iy`, the Schrödinger equation `ẋ = A_v y + B x`, `ẏ = -A_v x + B y`
(`schrC`), with `A_v = A + diag(Σ_i v_i n_i)`.

It is the real symmetric hopping `H̃ = [[A, -B], [B, A]]` (`dblH`) on the doubled configuration
space `C × Bool`, through the embedding `ψ ↦ ((x, y), (y, -x))` (`dbl`), which doubles densities:

* `dbl_schrC`: `dbl` maps complex-hopping trajectories to trajectories of the doubled system;
* `proj_schr`: conversely the linear map `proj` maps doubled trajectories to complex-hopping ones;
* `anti_norm_hasDerivAt`: the component of a doubled trajectory outside the image of `dbl` has
  conserved norm, so a doubled trajectory starting at `dbl ψ0` stays in the image.

Hence `td_existence_complex`, `td_uniqueness_complex` (Farzanehpour–Tokatly Theorem 1) and
`td_global_complex` (blow-up alternative) with complex hopping, with `Ω` defined through the doubled
system. `omegaC_zero`: without flux this `Ω` is the original one.
-/

namespace DFT

open Matrix Set Filter Topology

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

/-- The doubled real symmetric matrix `[[A, -B], [B, A]]` of `A + iB`. -/
def dblH (A B : Matrix C C ℝ) : Matrix (C × Bool) (C × Bool) ℝ := fun p q =>
  cond p.2 (cond q.2 (A p.1 q.1) (B p.1 q.1)) (cond q.2 (-B p.1 q.1) (A p.1 q.1))

/-- Occupations on the doubled configuration space. -/
def dblN (n : V → C → ℝ) : V → C × Bool → ℝ := fun i p => n i p.1

/-- The embedding `x + iy ↦ ((x, y), (y, -x))`. -/
def dbl (ψ : (C → ℝ) × (C → ℝ)) : (C × Bool → ℝ) × (C × Bool → ℝ) :=
  (fun p => cond p.2 (ψ.2 p.1) (ψ.1 p.1), fun p => cond p.2 (-ψ.1 p.1) (ψ.2 p.1))

/-- The four blocks of a doubled state. -/
def blk (X : C × Bool → ℝ) (b : Bool) : C → ℝ := fun c => X (c, b)

/-- Projection of a doubled state onto a complex state (`proj ∘ dbl = id`). -/
noncomputable def proj (Ψ : (C × Bool → ℝ) × (C × Bool → ℝ)) : (C → ℝ) × (C → ℝ) :=
  ((1 / 2 : ℝ) • (blk Ψ.1 false - blk Ψ.2 true), (1 / 2 : ℝ) • (blk Ψ.1 true + blk Ψ.2 false))

/-- The component of a doubled state outside the image of `dbl`. -/
def anti (Ψ : (C × Bool → ℝ) × (C × Bool → ℝ)) : (C → ℝ) × (C → ℝ) :=
  (blk Ψ.1 false + blk Ψ.2 true, blk Ψ.1 true - blk Ψ.2 false)

/-- The Schrödinger vector field for the hopping `A + iB` in real coordinates. -/
noncomputable def schrC (A B : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ)
    (ψ : (C → ℝ) × (C → ℝ)) : (C → ℝ) × (C → ℝ) :=
  (hamN A n v *ᵥ ψ.2 + B *ᵥ ψ.1, -(hamN A n v *ᵥ ψ.1) + B *ᵥ ψ.2)

section algebra

omit [Fintype C] [DecidableEq C] in
lemma dblH_isSymm {A B : Matrix C C ℝ} (hA : A.IsSymm) (hB : Bᵀ = -B) : (dblH A B).IsSymm := by
  have hB' : ∀ a b, B b a = -B a b := fun a b => by
    have := congrFun (congrFun hB a) b; simpa using this
  ext ⟨a, x⟩ ⟨b, y⟩
  cases x <;> cases y <;> simp only [transpose_apply, dblH, Bool.cond_true, Bool.cond_false] <;>
    first
    | exact hA.apply _ _
    | exact hB' _ _
    | rw [hB', neg_neg]

omit [Fintype C] [DecidableEq V] in
lemma hamN_dbl (A B : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) :
    hamN (dblH A B) (dblN n) v = dblH (hamN A n v) B := by
  ext ⟨a, x⟩ ⟨b, y⟩
  cases x <;> cases y <;> simp [hamN, dblH, dblN, diagonal_apply, Prod.ext_iff]

omit [DecidableEq C] in
lemma dblH_mulVec_false (M B : Matrix C C ℝ) (X : C × Bool → ℝ) (c : C) :
    (dblH M B *ᵥ X) (c, false) = (M *ᵥ blk X false) c - (B *ᵥ blk X true) c := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool, dblH, blk, Bool.cond_true,
    Bool.cond_false, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

omit [DecidableEq C] in
lemma dblH_mulVec_true (M B : Matrix C C ℝ) (X : C × Bool → ℝ) (c : C) :
    (dblH M B *ᵥ X) (c, true) = (B *ᵥ blk X false) c + (M *ᵥ blk X true) c := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool, dblH, blk, Bool.cond_true,
    Bool.cond_false, Finset.sum_add_distrib]
  ring

omit [DecidableEq C] in
lemma blk_dblH_mulVec (M B : Matrix C C ℝ) (X : C × Bool → ℝ) :
    blk (dblH M B *ᵥ X) false = M *ᵥ blk X false - B *ᵥ blk X true ∧
    blk (dblH M B *ᵥ X) true = B *ᵥ blk X false + M *ᵥ blk X true := by
  constructor <;> funext c
  · exact dblH_mulVec_false M B X c
  · exact dblH_mulVec_true M B X c

omit [DecidableEq V] in
/-- `dbl` maps the complex-hopping vector field to the doubled one. -/
lemma dbl_schrC (A B : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) (ψ : (C → ℝ) × (C → ℝ)) :
    schr (dblH A B) (dblN n) v (dbl ψ) = dbl (schrC A B n v ψ) := by
  have h1 : blk (dbl ψ).1 false = ψ.1 := rfl
  have h2 : blk (dbl ψ).1 true = ψ.2 := rfl
  have h3 : blk (dbl ψ).2 false = ψ.2 := rfl
  have h4 : blk (dbl ψ).2 true = -ψ.1 := rfl
  have e1 : ∀ (φ : (C → ℝ) × (C → ℝ)) c, (dbl φ).1 (c, false) = φ.1 c := fun _ _ => rfl
  have e2 : ∀ (φ : (C → ℝ) × (C → ℝ)) c, (dbl φ).1 (c, true) = φ.2 c := fun _ _ => rfl
  have e3 : ∀ (φ : (C → ℝ) × (C → ℝ)) c, (dbl φ).2 (c, false) = φ.2 c := fun _ _ => rfl
  have e4 : ∀ (φ : (C → ℝ) × (C → ℝ)) c, (dbl φ).2 (c, true) = -φ.1 c := fun _ _ => rfl
  ext ⟨c, b⟩ <;> cases b <;>
    simp only [schr, hamN_dbl, Pi.neg_apply, dblH_mulVec_false, dblH_mulVec_true, h1, h2, h3, h4,
      e1, e2, e3, e4, schrC, Pi.add_apply, mulVec_neg] <;> ring

omit [DecidableEq V] in
/-- `proj` maps the doubled vector field to the complex-hopping one. -/
lemma proj_schr (A B : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ)
    (Ψ : (C × Bool → ℝ) × (C × Bool → ℝ)) :
    proj (schr (dblH A B) (dblN n) v Ψ) = schrC A B n v (proj Ψ) := by
  obtain ⟨h1, h2⟩ := blk_dblH_mulVec (hamN A n v) B Ψ.1
  obtain ⟨h3, h4⟩ := blk_dblH_mulVec (hamN A n v) B Ψ.2
  have hneg : ∀ (X : C × Bool → ℝ) b, blk (-X) b = -blk X b := fun _ _ => rfl
  simp only [proj, schr, schrC, hamN_dbl, hneg, h1, h2, h3, h4, mulVec_smul, mulVec_add,
    mulVec_sub]
  ext c <;> simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul] <;>
    ring

omit [Fintype C] [DecidableEq C] in
@[simp] lemma proj_dbl (ψ : (C → ℝ) × (C → ℝ)) : proj (dbl ψ) = ψ := by
  ext c <;> simp [proj, dbl, blk] <;> ring

omit [Fintype C] [DecidableEq C] in
lemma anti_dbl (ψ : (C → ℝ) × (C → ℝ)) : anti (dbl ψ) = 0 := by
  ext c <;> simp [anti, dbl, blk]

omit [Fintype C] [DecidableEq C] in
lemma dbl_proj_of_anti {Ψ : (C × Bool → ℝ) × (C × Bool → ℝ)} (h : anti Ψ = 0) :
    dbl (proj Ψ) = Ψ := by
  have h1 : ∀ c, Ψ.1 (c, false) + Ψ.2 (c, true) = 0 := fun c => congrFun (congrArg Prod.fst h) c
  have h2 : ∀ c, Ψ.1 (c, true) - Ψ.2 (c, false) = 0 := fun c => congrFun (congrArg Prod.snd h) c
  ext ⟨c, b⟩ <;> cases b <;> simp [dbl, proj, blk] <;> linarith [h1 c, h2 c]

omit [Fintype V] [DecidableEq V] in
/-- The doubled density is twice the density. -/
lemma tdens_dbl (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) (i : V) :
    tdens (dblN n) (dbl ψ) i = 2 * tdens n ψ i := by
  simp only [tdens, Qf, Nmat, mulVec_diagonal, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool,
    dbl, dblN, Bool.cond_true, Bool.cond_false, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

omit [DecidableEq V] in
/-- The vector field of the component outside the image of `dbl`. -/
lemma anti_schr (A B : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ)
    (Ψ : (C × Bool → ℝ) × (C × Bool → ℝ)) :
    anti (schr (dblH A B) (dblN n) v Ψ) =
      (-(hamN A n v *ᵥ (anti Ψ).2) - B *ᵥ (anti Ψ).1,
        hamN A n v *ᵥ (anti Ψ).1 - B *ᵥ (anti Ψ).2) := by
  obtain ⟨h1, h2⟩ := blk_dblH_mulVec (hamN A n v) B Ψ.1
  obtain ⟨h3, h4⟩ := blk_dblH_mulVec (hamN A n v) B Ψ.2
  have hneg : ∀ (X : C × Bool → ℝ) b, blk (-X) b = -blk X b := fun _ _ => rfl
  simp only [anti, schr, hamN_dbl, hneg, h1, h2, h3, h4, mulVec_add, mulVec_sub]
  ext c <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] <;> ring

end algebra

section calculus

variable (C) in
/-- `proj` as a continuous linear map. -/
noncomputable def projL : ((C × Bool → ℝ) × (C × Bool → ℝ)) →L[ℝ] ((C → ℝ) × (C → ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := proj
      map_add' := fun Ψ Φ => by ext c <;> simp [proj, blk] <;> ring
      map_smul' := fun r Ψ => by ext c <;> simp [proj, blk] <;> ring }

variable (C) in
/-- `anti` as a continuous linear map. -/
noncomputable def antiL : ((C × Bool → ℝ) × (C × Bool → ℝ)) →L[ℝ] ((C → ℝ) × (C → ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := anti
      map_add' := fun Ψ Φ => by ext c <;> simp [anti, blk] <;> ring
      map_smul' := fun r Ψ => by ext c <;> simp [anti, blk, mul_sub] }

variable (C) in
/-- `dbl` as a continuous linear map. -/
noncomputable def dblL : ((C → ℝ) × (C → ℝ)) →L[ℝ] ((C × Bool → ℝ) × (C × Bool → ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := dbl
      map_add' := fun ψ φ => by ext ⟨c, b⟩ <;> cases b <;> simp [dbl, add_comm]
      map_smul' := fun r ψ => by ext ⟨c, b⟩ <;> cases b <;> simp [dbl] }

omit [DecidableEq C] in
lemma proj_hasDerivAt {Ψ : ℝ → (C × Bool → ℝ) × (C × Bool → ℝ)}
    {Ψ' : (C × Bool → ℝ) × (C × Bool → ℝ)}
    {t : ℝ} (h : HasDerivAt Ψ Ψ' t) : HasDerivAt (fun s => proj (Ψ s)) (proj Ψ') t :=
  (projL C).hasFDerivAt.comp_hasDerivAt t h

omit [DecidableEq C] in
lemma anti_hasDerivAt {Ψ : ℝ → (C × Bool → ℝ) × (C × Bool → ℝ)}
    {Ψ' : (C × Bool → ℝ) × (C × Bool → ℝ)}
    {t : ℝ} (h : HasDerivAt Ψ Ψ' t) : HasDerivAt (fun s => anti (Ψ s)) (anti Ψ') t :=
  (antiL C).hasFDerivAt.comp_hasDerivAt t h

omit [DecidableEq C] in
lemma dbl_hasDerivAt {ψ : ℝ → (C → ℝ) × (C → ℝ)} {ψ' : (C → ℝ) × (C → ℝ)} {t : ℝ}
    (h : HasDerivAt ψ ψ' t) : HasDerivAt (fun s => dbl (ψ s)) (dbl ψ') t :=
  (dblL C).hasFDerivAt.comp_hasDerivAt t h

omit [DecidableEq C] in
lemma dot_sym {M : Matrix C C ℝ} (hM : M.IsSymm) (u w : C → ℝ) :
    (M *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (M *ᵥ w) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]

omit [DecidableEq C] in
lemma dot_antisym {B : Matrix C C ℝ} (hB : Bᵀ = -B) (u : C → ℝ) : (B *ᵥ u) ⬝ᵥ u = 0 := by
  have h : (B *ᵥ u) ⬝ᵥ u = -((B *ᵥ u) ⬝ᵥ u) := by
    conv_lhs => rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hB, neg_mulVec,
      neg_dotProduct]
  linarith

omit [DecidableEq V] in
/-- **The unphysical component has conserved norm.** -/
lemma anti_norm_hasDerivAt {A B : Matrix C C ℝ} (hA : A.IsSymm) (hB : Bᵀ = -B) {n : V → C → ℝ}
    {v : V → ℝ} {Ψ : ℝ → (C × Bool → ℝ) × (C × Bool → ℝ)} {t : ℝ}
    (h : HasDerivAt Ψ (schr (dblH A B) (dblN n) v (Ψ t)) t) :
    HasDerivAt (fun s => Qf 1 (anti (Ψ s))) 0 t := by
  have hq := anti_hasDerivAt h
  rw [anti_schr] at hq
  set q := anti (Ψ t)
  have h1 := hasDerivAt_bil 1 (hasDerivAt_fst' hq) (hasDerivAt_fst' hq)
  have h2 := hasDerivAt_bil 1 (hasDerivAt_snd' hq) (hasDerivAt_snd' hq)
  refine (h1.add h2).congr_deriv ?_
  have hM := hamN_isSymm hA n v
  simp only [one_mulVec, sub_dotProduct, neg_dotProduct, dotProduct_sub, dotProduct_neg]
  rw [dot_sym hM, dot_sym hM, dotProduct_comm q.1 (B *ᵥ q.1), dotProduct_comm q.2 (B *ᵥ q.2),
    dot_antisym hB, dot_antisym hB, dotProduct_comm q.2 (hamN A n v *ᵥ q.1), dot_sym hM]
  ring

lemma eq_zero_of_Qf_one {q : (C → ℝ) × (C → ℝ)} (h : Qf 1 q = 0) : q = 0 := by
  rw [Qf_one_eq] at h
  have h1 := Finset.sum_nonneg (s := Finset.univ) (fun c _ => mul_self_nonneg (q.1 c))
  have h2 := Finset.sum_nonneg (s := Finset.univ) (fun c _ => mul_self_nonneg (q.2 c))
  have e1 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => mul_self_nonneg (q.1 c))).mp
    (by linarith)
  have e2 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => mul_self_nonneg (q.2 c))).mp
    (by linarith)
  ext c
  · exact mul_self_eq_zero.mp (e1 c (Finset.mem_univ c))
  · exact mul_self_eq_zero.mp (e2 c (Finset.mem_univ c))

end calculus

section main

/-- The v-representability set for the hopping `A + iB` (through the doubled system). -/
def omegaC (A B : Matrix C C ℝ) (n : V → C → ℝ) : Set ((C → ℝ) × (C → ℝ)) :=
  {ψ | dbl ψ ∈ omega (dblH A B) (dblN n)}

/-- The current for the hopping `A + iB`. -/
noncomputable def tcurC (A B : Matrix C C ℝ) (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) (i : V) : ℝ :=
  tcur (dblH A B) (dblN n) (dbl ψ) i / 2

/-- The potential determined by the state and `n̈` for the hopping `A + iB`. -/
noncomputable def vC (A B : Matrix C C ℝ) (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) (s : V → ℝ) :
    V → ℝ :=
  vfb (dblH A B) (dblN n) (dbl ψ) ((2 : ℝ) • s)

variable {A B : Matrix C C ℝ} {n : V → C → ℝ} {Ntot : ℝ} (hA : A.IsSymm) (hB : Bᵀ = -B)
  (hN : ∀ c, ∑ i, n i c = Ntot) [Nonempty V]
  {nn nd ndd : ℝ → V → ℝ} (hnd : ∀ t, HasDerivAt nn (nd t) t)
  (hndd : ∀ t, HasDerivAt nd (ndd t) t) (hcont : Continuous ndd) (hsum : ∀ t, ∑ i, ndd t i = 0)

omit [DecidableEq V] [Nonempty V] in
include hnd in
lemma hnd2 (t : ℝ) :
    HasDerivAt (fun s => (2 : ℝ) • nn s) ((2 : ℝ) • nd t) t := by
  change HasDerivAt ((2 : ℝ) • nn) _ t
  exact (hnd t).const_smul 2

include hsum in
omit [DecidableEq V] [Nonempty V] in
lemma hsum2 (t : ℝ) : ∑ i, ((2 : ℝ) • ndd t) i = 0 := by
  simp [← Finset.mul_sum, hsum t]

omit [Fintype V] [DecidableEq V] [Nonempty V] in
lemma tdens_eq_of_dbl {ψ : (C → ℝ) × (C → ℝ)} {Ψ : (C × Bool → ℝ) × (C × Bool → ℝ)}
    (h : Ψ = dbl ψ) {m : V → ℝ} (hd : ∀ i, tdens (dblN n) Ψ i = ((2 : ℝ) • m) i) (i : V) :
    tdens n ψ i = m i := by
  have := hd i
  rw [h, tdens_dbl] at this
  simp only [Pi.smul_apply, smul_eq_mul] at this
  linarith

include hA hB hN hnd hndd hcont hsum

/-- **Lattice TDDFT with complex hopping, existence.** For a Hermitian hopping `A + iB` (e.g. with
magnetic flux), an initial state in `Ω` reproducing `n(t₀)` and `ṅ(t₀)`, and a target density with
continuous `n̈`, `Σ_i n̈_i = 0`, there is near `t₀` a Schrödinger evolution driven by a potential
with `Σ_i v_i = 0` whose density is `n(t)`. -/
theorem td_existence_complex {t0 : ℝ} {ψ0 : (C → ℝ) × (C → ℝ)} (hψ0 : ψ0 ∈ omegaC A B n)
    (hρ0 : ∀ i, tdens n ψ0 i = nn t0 i) (hj0 : ∀ i, tcurC A B n ψ0 i = nd t0 i) :
    ∃ ε > 0, ∃ ψ : ℝ → (C → ℝ) × (C → ℝ), ψ t0 = ψ0 ∧
      ∀ t ∈ Ioo (t0 - ε) (t0 + ε),
        HasDerivAt ψ (schrC A B n (vC A B n (ψ t) (ndd t)) (ψ t)) t ∧
        ∑ i, vC A B n (ψ t) (ndd t) i = 0 ∧ ∀ i, tdens n (ψ t) i = nn t i := by
  have hH := dblH_isSymm hA hB
  have hN2 : ∀ p : C × Bool, ∑ i, dblN n i p = Ntot := fun p => hN p.1
  obtain ⟨ε, hε, Ψ, hΨ0, hΨ⟩ := td_existence (t0 := t0) (nn := fun s => (2 : ℝ) • nn s)
    (nd := fun s => (2 : ℝ) • nd s) (ndd := fun s => (2 : ℝ) • ndd s) hH hN2 (hnd2 hnd)
    (hnd2 hndd) (hcont.const_smul (2 : ℝ)) (hsum2 hsum) hψ0
    (fun i => by rw [tdens_dbl, hρ0]; simp)
    (fun i => by
      have := hj0 i
      simp only [tcurC] at this
      simp only [Pi.smul_apply, smul_eq_mul]
      linarith)
  -- the unphysical component stays zero
  have ht0 : t0 ∈ Ioo (t0 - ε) (t0 + ε) := ⟨by linarith, by linarith⟩
  have hdbl : ∀ t ∈ Ioo (t0 - ε) (t0 + ε), Ψ t = dbl (proj (Ψ t)) := by
    intro t ht
    have h0 := const_of_hasDerivAt_zero (fun s hs => anti_norm_hasDerivAt hA hB (hΨ s hs).1) ht ht0
    rw [hΨ0, anti_dbl] at h0
    have : Qf 1 (anti (Ψ t)) = 0 := by rw [h0]; simp [Qf]
    exact (dbl_proj_of_anti (eq_zero_of_Qf_one this)).symm
  refine ⟨ε, hε, fun s => proj (Ψ s), by simp [hΨ0], fun t ht => ⟨?_, ?_, ?_⟩⟩
  · have := proj_hasDerivAt (hΨ t ht).1
    rw [proj_schr] at this
    simp only [vC]
    rw [← hdbl t ht]
    exact this
  · simp only [vC]
    rw [← hdbl t ht]
    exact (hΨ t ht).2.1
  · exact tdens_eq_of_dbl (hdbl t ht) (hΨ t ht).2.2

omit hN hsum [Nonempty V] in
/-- **Lattice TDDFT with complex hopping, uniqueness.** Two evolutions from the same state of `Ω`
with density `n(t)` (potentials with `Σ_i v_i = 0`) coincide near `t₀`, and so do their
potentials. -/
theorem td_uniqueness_complex {t0 : ℝ} {ψ0 : (C → ℝ) × (C → ℝ)} (hψ0 : ψ0 ∈ omegaC A B n)
    {ψ1 ψ2 : ℝ → (C → ℝ) × (C → ℝ)} {v1 v2 : ℝ → V → ℝ}
    (h1 : ∀ᶠ t in 𝓝 t0, HasDerivAt ψ1 (schrC A B n (v1 t) (ψ1 t)) t ∧ ∑ i, v1 t i = 0 ∧
      ∀ i, tdens n (ψ1 t) i = nn t i)
    (h2 : ∀ᶠ t in 𝓝 t0, HasDerivAt ψ2 (schrC A B n (v2 t) (ψ2 t)) t ∧ ∑ i, v2 t i = 0 ∧
      ∀ i, tdens n (ψ2 t) i = nn t i)
    (h10 : ψ1 t0 = ψ0) (h20 : ψ2 t0 = ψ0) :
    ψ1 =ᶠ[𝓝 t0] ψ2 ∧ v1 =ᶠ[𝓝 t0] v2 := by
  have hH := dblH_isSymm hA hB
  have lift : ∀ {ψ : ℝ → (C → ℝ) × (C → ℝ)} {v : ℝ → V → ℝ},
      (∀ᶠ t in 𝓝 t0, HasDerivAt ψ (schrC A B n (v t) (ψ t)) t ∧ ∑ i, v t i = 0 ∧
        ∀ i, tdens n (ψ t) i = nn t i) →
      ∀ᶠ t in 𝓝 t0, HasDerivAt (fun s => dbl (ψ s)) (schr (dblH A B) (dblN n) (v t) (dbl (ψ t))) t ∧
        ∑ i, v t i = 0 ∧ ∀ i, tdens (dblN n) (dbl (ψ t)) i = ((2 : ℝ) • nn t) i := by
    intro ψ v h
    filter_upwards [h] with t ht
    refine ⟨?_, ht.2.1, fun i => ?_⟩
    · rw [dbl_schrC]; exact dbl_hasDerivAt ht.1
    · rw [tdens_dbl, ht.2.2 i]; simp
  obtain ⟨hψ, hv⟩ := td_uniqueness (nn := fun s => (2 : ℝ) • nn s)
    (nd := fun s => (2 : ℝ) • nd s) (ndd := fun s => (2 : ℝ) • ndd s) hH (hnd2 hnd) (hnd2 hndd)
    (hcont.const_smul (2 : ℝ)) (ψ0 := dbl ψ0) hψ0 (lift h1) (lift h2) (by simp [h10])
    (by simp [h20])
  refine ⟨?_, hv⟩
  filter_upwards [hψ] with t ht
  have := congrArg proj ht
  simpa using this

omit hN hnd hndd hcont hsum [Nonempty V] in
/-- A doubled TDDFT solution on `[t₀, s]` starting at `dbl ψ0` is a complex-hopping solution. -/
lemma complex_of_dbl {t0 s : ℝ} {ψ0 : (C → ℝ) × (C → ℝ)}
    {Ψ : ℝ → (C × Bool → ℝ) × (C × Bool → ℝ)} (hΨ0 : Ψ t0 = dbl ψ0)
    (hΨ : ∀ t ∈ Icc t0 s, Ψ t ∈ omega (dblH A B) (dblN n) ∧
      HasDerivAt Ψ (schr (dblH A B) (dblN n) (vfb (dblH A B) (dblN n) (Ψ t) ((2 : ℝ) • ndd t))
        (Ψ t)) t ∧
      ∑ i, vfb (dblH A B) (dblN n) (Ψ t) ((2 : ℝ) • ndd t) i = 0 ∧
      ∀ i, tdens (dblN n) (Ψ t) i = ((2 : ℝ) • nn t) i) :
    ∀ t ∈ Icc t0 s, proj (Ψ t) ∈ omegaC A B n ∧
      HasDerivAt (fun s => proj (Ψ s))
        (schrC A B n (vC A B n (proj (Ψ t)) (ndd t)) (proj (Ψ t))) t ∧
      ∑ i, vC A B n (proj (Ψ t)) (ndd t) i = 0 ∧ ∀ i, tdens n (proj (Ψ t)) i = nn t i := by
  have hdbl : ∀ t ∈ Icc t0 s, Ψ t = dbl (proj (Ψ t)) := by
    intro t ht
    have h0 := const_on_Icc (fun u hu => anti_norm_hasDerivAt hA hB (hΨ u hu).2.1) t ht
    rw [hΨ0, anti_dbl] at h0
    have : Qf 1 (anti (Ψ t)) = 0 := by rw [h0]; simp [Qf]
    exact (dbl_proj_of_anti (eq_zero_of_Qf_one this)).symm
  intro t ht
  have e := hdbl t ht
  refine ⟨?_, ?_, ?_, tdens_eq_of_dbl e (hΨ t ht).2.2.2⟩
  · change dbl (proj (Ψ t)) ∈ omega (dblH A B) (dblN n)
    rw [← e]; exact (hΨ t ht).1
  · have := proj_hasDerivAt (hΨ t ht).2.1
    rw [proj_schr] at this
    simp only [vC]
    rw [← e]
    exact this
  · simp only [vC]
    rw [← e]
    exact (hΨ t ht).2.2.1

/-- **Lattice TDDFT with complex hopping, blow-up alternative.** For every `T ≥ t₀`, either the
potential exists on all of `[t₀, T]`, or the evolution comes arbitrarily close to the boundary of
`Ω` before `T`. -/
theorem td_global_complex {t0 T : ℝ} (hT : t0 ≤ T) {ψ0 : (C → ℝ) × (C → ℝ)}
    (hψ0 : ψ0 ∈ omegaC A B n) (hρ0 : ∀ i, tdens n ψ0 i = nn t0 i)
    (hj0 : ∀ i, tcurC A B n ψ0 i = nd t0 i) :
    (∃ ψ : ℝ → (C → ℝ) × (C → ℝ), ψ t0 = ψ0 ∧ ∀ t ∈ Icc t0 T, ψ t ∈ omegaC A B n ∧
      HasDerivAt ψ (schrC A B n (vC A B n (ψ t) (ndd t)) (ψ t)) t ∧
      ∑ i, vC A B n (ψ t) (ndd t) i = 0 ∧ ∀ i, tdens n (ψ t) i = nn t i) ∨
    ∀ δ > 0, ∃ s ∈ Icc t0 T, ∃ ψ : ℝ → (C → ℝ) × (C → ℝ), ψ t0 = ψ0 ∧
      (∀ t ∈ Icc t0 s, ψ t ∈ omegaC A B n ∧
        HasDerivAt ψ (schrC A B n (vC A B n (ψ t) (ndd t)) (ψ t)) t ∧
        ∑ i, vC A B n (ψ t) (ndd t) i = 0 ∧ ∀ i, tdens n (ψ t) i = nn t i) ∧
      |(kJ (dblH A B) (dblN n) (dbl (ψ s))).det| < δ := by
  have hH := dblH_isSymm hA hB
  have hN2 : ∀ p : C × Bool, ∑ i, dblN n i p = Ntot := fun p => hN p.1
  rcases td_global (nn := fun s => (2 : ℝ) • nn s) (nd := fun s => (2 : ℝ) • nd s)
      (ndd := fun s => (2 : ℝ) • ndd s) hH hN2 (hnd2 hnd) (hnd2 hndd) (hsum2 hsum)
      (hcont.const_smul (2 : ℝ)) hT hψ0 (fun i => by rw [tdens_dbl, hρ0]; simp)
      (fun i => by
        have := hj0 i
        simp only [tcurC] at this
        simp only [Pi.smul_apply, smul_eq_mul]
        linarith) with ⟨Ψ, hΨ0, hΨ⟩ | h
  · exact Or.inl ⟨fun s => proj (Ψ s), by simp [hΨ0], complex_of_dbl hA hB hΨ0 hΨ⟩
  · refine Or.inr fun δ hδ => ?_
    obtain ⟨s, hs, Ψ, hΨ0, hΨ, hdet⟩ := h δ hδ
    refine ⟨s, hs, fun s => proj (Ψ s), by simp [hΨ0], complex_of_dbl hA hB hΨ0 hΨ, ?_⟩
    have e : Ψ s = dbl (proj (Ψ s)) := by
      have h0 := const_on_Icc (fun u hu => anti_norm_hasDerivAt hA hB (hΨ u hu).2.1) s
        ⟨hs.1, le_rfl⟩
      rw [hΨ0, anti_dbl] at h0
      have : Qf 1 (anti (Ψ s)) = 0 := by rw [h0]; simp [Qf]
      exact (dbl_proj_of_anti (eq_zero_of_Qf_one this)).symm
    rw [← e]; exact hdet

end main

section zeroFlux

omit [DecidableEq C] in
lemma dblH_mul_zero (M M' : Matrix C C ℝ) : dblH M 0 * dblH M' 0 = dblH (M * M') 0 := by
  ext ⟨a, x⟩ ⟨b, y⟩
  cases x <;> cases y <;>
    simp [dblH, Matrix.mul_apply, Fintype.sum_prod_type]

omit [Fintype C] [DecidableEq C] in
lemma dblH_sub_zero (M M' : Matrix C C ℝ) : dblH (M - M') 0 = dblH M 0 - dblH M' 0 := by
  ext ⟨a, x⟩ ⟨b, y⟩
  cases x <;> cases y <;> simp [dblH]

omit [Fintype C] [Fintype V] [DecidableEq V] in
lemma Nmat_dbl (n : V → C → ℝ) (i : V) : Nmat (dblN n) i = dblH (Nmat n i) 0 := by
  ext ⟨a, x⟩ ⟨b, y⟩
  cases x <;> cases y <;> simp [Nmat, dblN, dblH, diagonal_apply, Prod.ext_iff]

omit [DecidableEq C] in
lemma Qf_dbl_zero (M : Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) :
    Qf (dblH M 0) (dbl ψ) = 2 * Qf M ψ := by
  have h1 : blk (dbl ψ).1 false = ψ.1 := rfl
  have h2 : blk (dbl ψ).1 true = ψ.2 := rfl
  have h3 : blk (dbl ψ).2 false = ψ.2 := rfl
  have h4 : blk (dbl ψ).2 true = -ψ.1 := rfl
  have e1 : ∀ c, (dbl ψ).1 (c, false) = ψ.1 c := fun _ => rfl
  have e2 : ∀ c, (dbl ψ).1 (c, true) = ψ.2 c := fun _ => rfl
  have e3 : ∀ c, (dbl ψ).2 (c, false) = ψ.2 c := fun _ => rfl
  have e4 : ∀ c, (dbl ψ).2 (c, true) = -ψ.1 c := fun _ => rfl
  simp only [Qf, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool, dblH_mulVec_false,
    dblH_mulVec_true, h1, h2, h3, h4, e1, e2, e3, e4, zero_mulVec, Pi.zero_apply, sub_zero,
    zero_add, mulVec_neg, Pi.neg_apply]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

omit [Fintype V] [DecidableEq V] in
lemma kfb_dbl_zero (A : Matrix C C ℝ) (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) :
    kfb (dblH A 0) (dblN n) (dbl ψ) = (2 : ℝ) • kfb A n ψ := by
  ext i j
  simp only [kfb, Nmat_dbl, dblH_mul_zero, ← dblH_sub_zero, Qf_dbl_zero, Matrix.smul_apply,
    smul_eq_mul]
  ring

omit [DecidableEq V] in
/-- With column sums of `K` zero, `(c K + 𝟙𝟙ᵀ) w = 0` iff `K w = 0` and `Σ w = 0` (`c ≠ 0`). -/
lemma kJ_ker_iff [Nonempty V] {K : Matrix V V ℝ} (hcol : ∀ j, ∑ i, K i j = 0) {c : ℝ}
    (hc : c ≠ 0) (w : V → ℝ) :
    (c • K + onesM) *ᵥ w = 0 ↔ K *ᵥ w = 0 ∧ ∑ j, w j = 0 := by
  constructor
  · intro h
    have hcomp : ∀ i, c * (K *ᵥ w) i + ∑ j, w j = 0 := fun i => by
      have := congrFun h i
      rw [add_mulVec, smul_mulVec, onesM_mulVec] at this
      simpa using this
    have htot : ∑ i, (c * (K *ᵥ w) i + ∑ j, w j) = 0 := by simp [hcomp]
    have hK : ∑ i, (K *ᵥ w) i = 0 := by
      simp only [mulVec, dotProduct]
      rw [Finset.sum_comm]
      simp [← Finset.sum_mul, hcol]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hK, mul_zero, zero_add, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at htot
    have hs : ∑ j, w j = 0 := by
      rcases mul_eq_zero.mp htot with h | h
      · exact absurd h (by exact_mod_cast Fintype.card_ne_zero)
      · exact h
    refine ⟨funext fun i => ?_, hs⟩
    have := hcomp i
    rw [hs, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hc
  · rintro ⟨hK, hs⟩
    rw [add_mulVec, smul_mulVec, onesM_mulVec, hK]
    funext i; simp [hs]

/-- **Zero flux.** For real hopping (`B = 0`) the v-representability set of the doubled
description is the original one, so the complex-hopping theorems contain the real ones (and, `Ω`
being open, they apply to all states of `Ω` for small enough flux). -/
theorem omegaC_zero [Nonempty V] {A : Matrix C C ℝ} (hA : A.IsSymm) {n : V → C → ℝ} {Ntot : ℝ}
    (hN : ∀ c, ∑ i, n i c = Ntot) : omegaC A 0 n = omega A n := by
  ext ψ
  have hcol := kfb_sum_left A hN hA ψ
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have h1 : (1 : ℝ) ≠ 0 := one_ne_zero
  simp only [omegaC, omega, Set.mem_ofPred_eq, kJ, kfb_dbl_zero]
  rw [not_iff_not.symm, not_not, not_not, ← exists_mulVec_eq_zero_iff, ← exists_mulVec_eq_zero_iff]
  have e : kfb A n ψ + onesM = (1 : ℝ) • kfb A n ψ + onesM := by rw [one_smul]
  rw [e]
  simp only [kJ_ker_iff hcol h2, kJ_ker_iff hcol h1]

end zeroFlux

end DFT
