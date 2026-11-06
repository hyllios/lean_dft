/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.TDDFT.GroundStart
import LatticeDFT.KohnSham.Existence

/-!
# Time-dependent Kohn–Sham on the lattice (van Leeuwen's theorem)

* `density_c2`: the density of any trajectory driven by a continuous potential is `C²`, with
  `n̈ = q - K v` continuous and `Σ_i n̈_i = 0`.
* `van_leeuwen`: the density `n(t)` of any trajectory of one system (Hamiltonian `H0`, any
  interaction) can be reproduced locally in time by a second system `H0'` (for instance the
  non-interacting Kohn–Sham system), starting from any state of `Ω'` with the same initial density
  and current; the potential of the second system is unique (gauge `Σ_i v_i = 0`).
* `td_kohn_sham`: spinless lattice fermions. Start the interacting system from any real state
  (for instance a ground state) and let it evolve under any continuous potential. If the initial
  density is the density of a pure non-interacting ground state of `H_s(v_s)`, and `v_s` is
  outside a closed, nowhere dense, null set, then a unique time-dependent Kohn–Sham potential
  reproduces the interacting density near `t₀`.
-/

namespace LatticeDFT

open Matrix Set Filter Topology MeasureTheory

variable {C C' V : Type*} [Fintype C] [DecidableEq C] [Fintype C'] [DecidableEq C'] [Fintype V]
  [DecidableEq V]

omit [DecidableEq C] [DecidableEq V] in
lemma continuous_Qf (A : Matrix C C ℝ) : Continuous (Qf A) := by
  unfold Qf
  simp only [dotProduct, mulVec]
  fun_prop

omit [Fintype V] [DecidableEq V] in
/-- A real state carries no current. -/
lemma tcur_real (H0 : Matrix C C ℝ) (n : V → C → ℝ) (x : C → ℝ) (i : V) :
    tcur H0 n (x, 0) i = 0 := by
  simp [tcur]

section density

variable {H0 : Matrix C C ℝ} {n : V → C → ℝ} {Ntot : ℝ} (hH0 : H0.IsSymm)
  (hN : ∀ c, ∑ i, n i c = Ntot) {ψ : ℝ → (C → ℝ) × (C → ℝ)} {v : ℝ → V → ℝ}
  (hψ : ∀ t, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t) (hv : Continuous v)

/-- Second time derivative of the density along a trajectory: `n̈ = q - K v`. -/
def ddens (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ψ : ℝ → (C → ℝ) × (C → ℝ)) (v : ℝ → V → ℝ)
    (t : ℝ) (i : V) : ℝ :=
  qsrc H0 n (ψ t) i - ∑ j, kfb H0 n (ψ t) i j * v t j

include hH0 hψ in
omit [DecidableEq V] in
lemma ddens_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => fun i => tcur H0 n (ψ s) i) (ddens H0 n ψ v t) t :=
  hasDerivAt_pi.mpr fun i => tcur_hasDerivAt hH0 (hψ t) i

include hH0 hψ in
omit [DecidableEq V] in
lemma dens_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => fun i => tdens n (ψ s) i) (fun i => tcur H0 n (ψ t) i) t :=
  hasDerivAt_pi.mpr fun i => tdens_hasDerivAt hH0 (hψ t) i

include hψ hv in
omit [DecidableEq V] in
lemma continuous_ddens : Continuous (ddens H0 n ψ v) := by
  have hc : Continuous ψ := continuous_iff_continuousAt.mpr fun t => (hψ t).continuousAt
  refine continuous_pi fun i => ?_
  simp only [ddens, qsrc, kfb]
  have h1 := (continuous_Qf (H0 * Nmat n i * H0 - H0 * H0 * Nmat n i)).comp hc
  have h2 : ∀ j, Continuous fun t =>
      Qf (H0 * Nmat n i * Nmat n j - Nmat n j * H0 * Nmat n i) (ψ t) :=
    fun j => (continuous_Qf _).comp hc
  have h3 : ∀ j, Continuous fun t => v t j := fun j => (continuous_apply j).comp hv
  exact (continuous_const.mul h1).sub
    (continuous_finsetSum _ fun j _ => (continuous_const.mul (h2 j)).mul (h3 j))

include hH0 hN in
omit [DecidableEq V] in
lemma ddens_sum (t : ℝ) : ∑ i, ddens H0 n ψ v t i = 0 := by
  simp only [ddens, Finset.sum_sub_distrib, qsrc_sum H0 hN]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, kfb_sum_left H0 hN hH0, zero_mul, Finset.sum_const_zero, sub_zero]

end density

section vanLeeuwen

variable {H0 : Matrix C C ℝ} {n : V → C → ℝ} {Ntot : ℝ} (hH0 : H0.IsSymm)
  (hN : ∀ c, ∑ i, n i c = Ntot) {ψ : ℝ → (C → ℝ) × (C → ℝ)} {v : ℝ → V → ℝ}
  (hψ : ∀ t, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t) (hv : Continuous v)
  {H0' : Matrix C' C' ℝ} {n' : V → C' → ℝ} {Ntot' : ℝ} (hH0' : H0'.IsSymm)
  (hN' : ∀ c, ∑ i, n' i c = Ntot') [Nonempty V]

include hH0 hN hψ hv hH0' hN'

/-- **Lattice van Leeuwen theorem, existence.** Let `ψ(t)` be a trajectory of a system `(H0, n)`
(any interaction) driven by a continuous potential `v(t)`. Let `φ0` be a state of a second system
`(H0', n')` in its v-representability set `Ω'`, with the same density and current as `ψ(t₀)`.
Then, near `t₀`, the second system driven by some potential `v'(t)` (with `Σ_i v'_i = 0`) evolves
from `φ0` with exactly the density of `ψ(t)`. -/
theorem van_leeuwen {t0 : ℝ} {φ0 : (C' → ℝ) × (C' → ℝ)} (hφ0 : φ0 ∈ omega H0' n')
    (hρ0 : ∀ i, tdens n' φ0 i = tdens n (ψ t0) i)
    (hj0 : ∀ i, tcur H0' n' φ0 i = tcur H0 n (ψ t0) i) :
    ∃ ε > 0, ∃ φ : ℝ → (C' → ℝ) × (C' → ℝ), φ t0 = φ0 ∧
      ∀ t ∈ Ioo (t0 - ε) (t0 + ε),
        HasDerivAt φ (schr H0' n' (vfb H0' n' (φ t) (ddens H0 n ψ v t)) (φ t)) t ∧
        ∑ i, vfb H0' n' (φ t) (ddens H0 n ψ v t) i = 0 ∧
        ∀ i, tdens n' (φ t) i = tdens n (ψ t) i :=
  td_existence (nn := fun s i => tdens n (ψ s) i) (nd := fun s i => tcur H0 n (ψ s) i) hH0' hN'
    (dens_hasDerivAt hH0 hψ) (ddens_hasDerivAt hH0 hψ) (continuous_ddens hψ hv)
    (ddens_sum hH0 hN) hφ0 hρ0 hj0

omit hN hN' [Nonempty V] in
/-- **Lattice van Leeuwen theorem, uniqueness.** Two trajectories of the second system from the same
state `φ0 ∈ Ω'`, both reproducing the density of `ψ(t)` with gauge-fixed potentials, coincide near
`t₀`, and so do their potentials. -/
theorem van_leeuwen_unique {t0 : ℝ} {φ0 : (C' → ℝ) × (C' → ℝ)} (hφ0 : φ0 ∈ omega H0' n')
    {φ1 φ2 : ℝ → (C' → ℝ) × (C' → ℝ)} {v1 v2 : ℝ → V → ℝ}
    (h1 : ∀ᶠ t in 𝓝 t0, HasDerivAt φ1 (schr H0' n' (v1 t) (φ1 t)) t ∧ ∑ i, v1 t i = 0 ∧
      ∀ i, tdens n' (φ1 t) i = tdens n (ψ t) i)
    (h2 : ∀ᶠ t in 𝓝 t0, HasDerivAt φ2 (schr H0' n' (v2 t) (φ2 t)) t ∧ ∑ i, v2 t i = 0 ∧
      ∀ i, tdens n' (φ2 t) i = tdens n (ψ t) i)
    (h10 : φ1 t0 = φ0) (h20 : φ2 t0 = φ0) :
    φ1 =ᶠ[𝓝 t0] φ2 ∧ v1 =ᶠ[𝓝 t0] v2 :=
  td_uniqueness (nn := fun s i => tdens n (ψ s) i) (nd := fun s i => tcur H0 n (ψ s) i) hH0'
    (dens_hasDerivAt hH0 hψ) (ddens_hasDerivAt hH0 hψ) (continuous_ddens hψ hv) hφ0 h1 h2 h10 h20

/-- Existence and uniqueness in one statement, for an initial state `φ0 ∈ Ω'`. -/
theorem van_leeuwen_unique' {t0 : ℝ} {φ0 : (C' → ℝ) × (C' → ℝ)} (hφ0 : φ0 ∈ omega H0' n')
    (hρ0 : ∀ i, tdens n' φ0 i = tdens n (ψ t0) i)
    (hj0 : ∀ i, tcur H0' n' φ0 i = tcur H0 n (ψ t0) i) :
    ∃ φ : ℝ → (C' → ℝ) × (C' → ℝ), ∃ vs : ℝ → V → ℝ, φ t0 = φ0 ∧
      (∀ᶠ t in 𝓝 t0, HasDerivAt φ (schr H0' n' (vs t) (φ t)) t ∧ ∑ i, vs t i = 0 ∧
        ∀ i, tdens n' (φ t) i = tdens n (ψ t) i) ∧
      ∀ φ' : ℝ → (C' → ℝ) × (C' → ℝ), ∀ vs' : ℝ → V → ℝ, φ' t0 = φ0 →
        (∀ᶠ t in 𝓝 t0, HasDerivAt φ' (schr H0' n' (vs' t) (φ' t)) t ∧ ∑ i, vs' t i = 0 ∧
          ∀ i, tdens n' (φ' t) i = tdens n (ψ t) i) →
        φ' =ᶠ[𝓝 t0] φ ∧ vs' =ᶠ[𝓝 t0] vs := by
  obtain ⟨ε, hε, φ, h0, hφ⟩ := van_leeuwen hH0 hN hψ hv hH0' hN' hφ0 hρ0 hj0
  have hev : ∀ᶠ t in 𝓝 t0,
      HasDerivAt φ (schr H0' n' (vfb H0' n' (φ t) (ddens H0 n ψ v t)) (φ t)) t ∧
      ∑ i, vfb H0' n' (φ t) (ddens H0 n ψ v t) i = 0 ∧ ∀ i, tdens n' (φ t) i = tdens n (ψ t) i :=
    Filter.mem_of_superset (Ioo_mem_nhds (show t0 - ε < t0 by linarith)
      (show t0 < t0 + ε by linarith)) fun t ht => hφ t ht
  exact ⟨φ, _, h0, hev, fun φ' vs' h0' h' =>
    van_leeuwen_unique hH0 hψ hv hH0' hφ0 h' hev h0' h0⟩

end vanLeeuwen

universe u

variable {M N : ℕ}

/-- **Time-dependent Kohn–Sham for lattice fermions.** Spinless fermions on a connected graph with
symmetric hopping of a common sign. Outside a closed, nowhere dense, Lebesgue-null set `Z` of
static potentials the following holds. Let `φ0` be a (real) ground state of the non-interacting
Hamiltonian `H_s(v_s)` with `v_s ∉ Z`. Let `ψ(t)` be any trajectory of any system on the same sites
(for instance the interacting lattice fermions), driven by a continuous potential and real at `t₀`
(for instance starting from its ground state), with the same density as `φ0` at `t₀`. Then near
`t₀` there is a Kohn–Sham trajectory from `φ0`, driven by a gauge-fixed potential `v_s(t)`, with
exactly the density of `ψ(t)`; trajectory and potential are unique. -/
theorem td_kohn_sham [NeZero M] {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hN0 : 0 < N) (hNM : N < M) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      ∀ vs0 ∉ Z, ∀ φ0 : Conf M N → ℝ,
        IsGroundState (hamN (H0Fw G t (0 : Conf M N → ℝ)) occF vs0) φ0 →
      ∀ {C : Type u} [Fintype C] [DecidableEq C] (H0 : Matrix C C ℝ) (n : Fin M → C → ℝ)
        (Ntot : ℝ), H0.IsSymm → (∀ c, ∑ i, n i c = Ntot) →
      ∀ (ψ : ℝ → (C → ℝ) × (C → ℝ)) (v : ℝ → Fin M → ℝ),
        (∀ t, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t) → Continuous v →
      ∀ t0, (ψ t0).2 = 0 → (∀ i, tdens occF (φ0, 0) i = tdens n (ψ t0) i) →
        ∃ φ : ℝ → (Conf M N → ℝ) × (Conf M N → ℝ), ∃ vs : ℝ → Fin M → ℝ, φ t0 = (φ0, 0) ∧
          (∀ᶠ t' in 𝓝 t0, HasDerivAt φ (schr (H0Fw G t 0) occF (vs t') (φ t')) t' ∧
            ∑ i, vs t' i = 0 ∧ ∀ i, tdens occF (φ t') i = tdens n (ψ t') i) ∧
          ∀ φ' : ℝ → (Conf M N → ℝ) × (Conf M N → ℝ), ∀ vs' : ℝ → Fin M → ℝ, φ' t0 = (φ0, 0) →
            (∀ᶠ t' in 𝓝 t0, HasDerivAt φ' (schr (H0Fw G t 0) occF (vs' t') (φ' t')) t' ∧
              ∑ i, vs' t' i = 0 ∧ ∀ i, tdens occF (φ' t') i = tdens n (ψ t') i) →
            φ' =ᶠ[𝓝 t0] φ ∧ vs' =ᶠ[𝓝 t0] vs := by
  obtain ⟨Z, hcl, hint, hvol, hZ⟩ := generic_ground_mem_omega hG htsym hts hN0 hNM 0
  refine ⟨Z, hcl, hint, hvol,
    fun vs0 hvs0 φ0 hφ0 C _ _ H0 n Ntot hH0 hN ψ v hψ hv t0 hreal hρ0 => ?_⟩
  have hj0 : ∀ i, tcur (H0Fw G t 0) occF (φ0, 0) i = tcur H0 n (ψ t0) i := by
    intro i
    have : ψ t0 = ((ψ t0).1, 0) := Prod.ext rfl hreal
    rw [tcur_real, this, tcur_real]
  exact van_leeuwen_unique' hH0 hN hψ hv (H0Fw_isSymm G htsym 0) sum_occF (hZ vs0 hvs0 φ0 hφ0)
    hρ0 hj0

end LatticeDFT
