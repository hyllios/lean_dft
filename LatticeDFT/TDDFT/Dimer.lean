/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.TDDFT.KohnSham

/-!
# A reality check: one particle on two sites

The general TDDFT machinery, evaluated on the simplest nontrivial system: one particle hopping
between two sites (`H = -T σₓ`), occupations `n_i(c) = δ_ic`. For `ψ = x + iy` write
`b = Re(ψ̄₀ψ₁) = x₀x₁ + y₀y₁` (the bond order) and `f = x₁y₀ - x₀y₁ = -Im(ψ̄₀ψ₁)`.

* `kfb_dimer`, `qsrc_dimer`, `tcur_dimer`: the force-balance matrix is `2Tb [[1,-1],[-1,1]]`,
  the source is `q₀ = 2T²(n₁ - n₀)`, the current is `ṅ₀ = 2Tf`.
* `mem_omega_dimer_iff`: `det(K + 𝟙𝟙ᵀ) = 8Tb`, so `Ω = {T ≠ 0, b ≠ 0}`.
* `speed_limit`: `ṅ₀² ≤ 4T² n₀ n₁` for every state, with equality exactly outside `Ω`
  (`b² + f² = n₀n₁`).
* `dimer_td_potential`: along any trajectory, the potential is fixed by the density alone:
  `(v₀ - v₁)² (4T² n₀n₁ - ṅ₀²) = (n̈₀ + 2T²(n₀ - n₁))²`, the known closed form
  `Δv = ∓(d̈ + 4T²d)/√(4T²(1 - d²) - ḋ²)` for `d = n₀ - n₁`, `n₀ + n₁ = 1`.
* `vfb_dimer`: the general potential map `vfb` of `td_existence` reduces to
  `v₀ - v₁ = (q₀ - s₀)/(2Tb)`.
* `dimer_eigen_mem_omega`: every real eigenstate (ground or excited) lies in `Ω`.
* `rabi_hasDerivAt`, `rabi_not_mem_omega`: the free Rabi oscillation from a localised state,
  `n₀ = cos²(Tt)`, never enters `Ω`: it moves at the speed limit at all times.
-/

namespace LatticeDFT

namespace Dimer

open Matrix

/-- The dimer hopping Hamiltonian `-T σₓ`. -/
def H (T : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => if i = j then 0 else -T

/-- Site occupations of the single particle: `n_i(c) = δ_ic`. -/
def occ : Fin 2 → Fin 2 → ℝ := fun i c => if i = c then 1 else 0

/-- The bond order `Re(ψ̄₀ψ₁)`. -/
def bond (ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ := ψ.1 0 * ψ.1 1 + ψ.2 0 * ψ.2 1

/-- The flow `-Im(ψ̄₀ψ₁)` (the current from site 1 to site 0 is `2T` times it). -/
def flow (ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ := ψ.1 1 * ψ.2 0 - ψ.1 0 * ψ.2 1

lemma H_apply (T : ℝ) (i j : Fin 2) : H T i j = if i = j then 0 else -T := rfl

lemma H_mulVec (T : ℝ) (x : Fin 2 → ℝ) : H T *ᵥ x = ![-(T * x 1), -(T * x 0)] := by
  ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, H_apply]

lemma hamN_zero_dimer (T : ℝ) : hamN (H T) occ 0 = H T := by
  simp [hamN]

lemma H_isSymm (T : ℝ) : (H T).IsSymm := by
  ext i j; simp [H, eq_comm]

lemma tdens_dimer (ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (i : Fin 2) :
    tdens occ ψ i = ψ.1 i ^ 2 + ψ.2 i ^ 2 := by
  fin_cases i <;> simp [Qf, tdens, Nmat, occ, dotProduct, mulVec, diagonal_apply] <;> ring

lemma tcur_dimer (T : ℝ) (ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    tcur (H T) occ ψ 0 = 2 * T * flow ψ ∧ tcur (H T) occ ψ 1 = -(2 * T * flow ψ) := by
  constructor <;>
    simp [tcur, flow, H, Nmat, occ, dotProduct, mulVec, diagonal_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.of_apply] <;> ring

lemma kfb_dimer (T : ℝ) (ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    kfb (H T) occ ψ = !![2 * T * bond ψ, -(2 * T * bond ψ); -(2 * T * bond ψ), 2 * T * bond ψ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qf, kfb, bond, H, Nmat, occ, dotProduct, mulVec, diagonal_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.of_apply] <;> ring

lemma qsrc_dimer (T : ℝ) (ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    qsrc (H T) occ ψ 0 = 2 * T ^ 2 * (tdens occ ψ 1 - tdens occ ψ 0) ∧
      qsrc (H T) occ ψ 1 = 2 * T ^ 2 * (tdens occ ψ 0 - tdens occ ψ 1) := by
  simp only [tdens_dimer]
  constructor <;>
    simp [Qf, qsrc, H, Nmat, occ, dotProduct, mulVec, diagonal_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.of_apply] <;> ring

lemma det_kJ_dimer (T : ℝ) (ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    (kJ (H T) occ ψ).det = 8 * T * bond ψ := by
  rw [kJ, kfb_dimer, det_fin_two]
  simp [onesM]
  ring

/-- Lagrange's identity: `b² + f² = |ψ₀|² |ψ₁|² = n₀ n₁`. -/
lemma bond_sq_add_flow_sq (ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    bond ψ ^ 2 + flow ψ ^ 2 = tdens occ ψ 0 * tdens occ ψ 1 := by
  rw [tdens_dimer, tdens_dimer]; simp only [bond, flow]; ring

/-- **`Ω` for the dimer**: the bond order must not vanish. -/
theorem mem_omega_dimer_iff {T : ℝ} {ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)} :
    ψ ∈ omega (H T) occ ↔ T ≠ 0 ∧ bond ψ ≠ 0 := by
  change (kJ (H T) occ ψ).det ≠ 0 ↔ _
  rw [det_kJ_dimer]
  constructor
  · intro h; exact ⟨fun hT => h (by simp [hT]), fun hb => h (by simp [hb])⟩
  · rintro ⟨hT, hb⟩; exact mul_ne_zero (mul_ne_zero (by norm_num) hT) hb

/-- **Speed limit.** For every state, `ṅ₀² ≤ 4T² n₀ n₁`. -/
theorem speed_limit (T : ℝ) (ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    tcur (H T) occ ψ 0 ^ 2 ≤ 4 * T ^ 2 * (tdens occ ψ 0 * tdens occ ψ 1) := by
  rw [(tcur_dimer T ψ).1, ← bond_sq_add_flow_sq]
  nlinarith [sq_nonneg (T * bond ψ)]

/-- The speed limit is attained exactly outside `Ω`. -/
theorem speed_limit_eq_iff {T : ℝ} (hT : T ≠ 0) (ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    tcur (H T) occ ψ 0 ^ 2 = 4 * T ^ 2 * (tdens occ ψ 0 * tdens occ ψ 1) ↔
      ψ ∉ omega (H T) occ := by
  rw [mem_omega_dimer_iff, (tcur_dimer T ψ).1, ← bond_sq_add_flow_sq]
  constructor
  · rintro h ⟨-, hb⟩
    apply hb
    have h2 : (T * bond ψ) ^ 2 = 0 := by nlinarith
    exact (mul_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)).resolve_left hT
  · intro h
    have hb : bond ψ = 0 := by by_contra hb; exact h ⟨hT, hb⟩
    rw [hb]; ring

/-- The second derivative of `n₀` along a trajectory, explicitly. -/
lemma ddens_dimer (T : ℝ) (ψ : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)) (v : ℝ → Fin 2 → ℝ) (t : ℝ) :
    ddens (H T) occ ψ v t 0 = 2 * T ^ 2 * (tdens occ (ψ t) 1 - tdens occ (ψ t) 0) -
      2 * T * bond (ψ t) * (v t 0 - v t 1) := by
  simp only [ddens, (qsrc_dimer T _).1, kfb_dimer, Fin.sum_univ_two]
  simp
  ring

/-- **The dimer TDDFT potential in closed form.** Along any trajectory driven by any potential,
`ṅ₀ = j₀`, `j̇₀ = n̈₀`, and the potential difference is determined by the density alone:
`(v₀ - v₁)² (4T² n₀ n₁ - ṅ₀²) = (n̈₀ + 2T²(n₀ - n₁))²`. With `d = n₀ - n₁` and `n₀ + n₁ = 1` this is
`Δv = ∓(d̈ + 4T²d)/√(4T²(1 - d²) - ḋ²)`; the denominator vanishes exactly on the boundary of `Ω`. -/
theorem dimer_td_potential {T : ℝ} {ψ : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)} {v : ℝ → Fin 2 → ℝ}
    (hψ : ∀ t, HasDerivAt ψ (schr (H T) occ (v t) (ψ t)) t) (t : ℝ) :
    HasDerivAt (fun s => tdens occ (ψ s) 0) (tcur (H T) occ (ψ t) 0) t ∧
      HasDerivAt (fun s => tcur (H T) occ (ψ s) 0) (ddens (H T) occ ψ v t 0) t ∧
      (v t 0 - v t 1) ^ 2 *
          (4 * T ^ 2 * (tdens occ (ψ t) 0 * tdens occ (ψ t) 1) - tcur (H T) occ (ψ t) 0 ^ 2) =
        (ddens (H T) occ ψ v t 0 + 2 * T ^ 2 * (tdens occ (ψ t) 0 - tdens occ (ψ t) 1)) ^ 2 := by
  refine ⟨tdens_hasDerivAt (H_isSymm T) (hψ t) 0, tcur_hasDerivAt (H_isSymm T) (hψ t) 0, ?_⟩
  rw [ddens_dimer, (tcur_dimer T _).1, ← bond_sq_add_flow_sq]
  ring

/-- **The general potential map, evaluated.** In `Ω`, the potential `vfb` of `td_existence` (gauge
`v₀ + v₁ = 0`) has `v₀ - v₁ = (q₀ - s₀)/(2Tb)`, with `q₀ = 2T²(n₁ - n₀)` and `s = n̈`. -/
theorem vfb_dimer {T : ℝ} {ψ : (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hΩ : ψ ∈ omega (H T) occ)
    {s : Fin 2 → ℝ} (hs : s 0 + s 1 = 0) :
    vfb (H T) occ ψ s 0 - vfb (H T) occ ψ s 1 =
      (qsrc (H T) occ ψ 0 - s 0) / (2 * T * bond ψ) := by
  obtain ⟨hT, hb⟩ := mem_omega_dimer_iff.mp hΩ
  set w := (qsrc (H T) occ ψ 0 - s 0) / (4 * T * bond ψ) with hw
  have hq := qsrc_dimer T ψ
  have key := vfb_unique (H0 := H T) (n := occ) (s := s) (v := ![w, -w]) hΩ
    (by simp [Fin.sum_univ_two]) (fun i => by
      fin_cases i
      · simp [kfb_dimer, Fin.sum_univ_two, hw]; field_simp; ring
      · simp [kfb_dimer, Fin.sum_univ_two, hw]
        rw [hq.2, show s 1 = -s 0 by linarith, hq.1]; field_simp; ring)
  rw [← key]
  simp [hw]
  field_simp
  ring

/-- **Every real eigenstate of the dimer lies in `Ω`**, ground or excited, for every potential:
an eigenvector of `-Tσₓ + diag v` with `T ≠ 0` has no zero component. -/
theorem dimer_eigen_mem_omega {T : ℝ} (hT : T ≠ 0) {v : Fin 2 → ℝ} {x : Fin 2 → ℝ} {E : ℝ}
    (hx : hamN (H T) occ v *ᵥ x = E • x) (hx0 : x ≠ 0) :
    ((x, 0) : (Fin 2 → ℝ) × (Fin 2 → ℝ)) ∈ omega (H T) occ := by
  rw [mem_omega_dimer_iff]
  refine ⟨hT, ?_⟩
  have e0 : v 0 * x 0 - T * x 1 = E * x 0 := by
    have := congrFun hx 0
    simp [hamN, H, occ, mulVec, dotProduct, Fin.sum_univ_two, diagonal_apply] at this
    linarith
  have e1 : v 1 * x 1 - T * x 0 = E * x 1 := by
    have := congrFun hx 1
    simp [hamN, H, occ, mulVec, dotProduct, Fin.sum_univ_two, diagonal_apply] at this
    linarith
  simp only [bond, Pi.zero_apply, mul_zero, add_zero]
  intro h
  apply hx0
  rcases mul_eq_zero.mp h with h0 | h1
  · have h1 : x 1 = 0 := by
      have : T * x 1 = 0 := by rw [h0] at e0; linarith
      exact (mul_eq_zero.mp this).resolve_left hT
    ext i; fin_cases i <;> simp [h0, h1]
  · have h0 : x 0 = 0 := by
      have : T * x 0 = 0 := by rw [h1] at e1; linarith
      exact (mul_eq_zero.mp this).resolve_left hT
    ext i; fin_cases i <;> simp [h0, h1]

/-- The free Rabi oscillation from site `0`: `ψ(t) = (cos Tt, i sin Tt)`. -/
noncomputable def rabi (T t : ℝ) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (![Real.cos (T * t), 0], ![0, Real.sin (T * t)])

/-- `rabi` solves the Schrödinger equation without potential. -/
theorem rabi_hasDerivAt (T t : ℝ) : HasDerivAt (rabi T) (schr (H T) occ 0 (rabi T t)) t := by
  have hc : HasDerivAt (fun s => Real.cos (T * s)) (-Real.sin (T * t) * T) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_cos (T * t)).comp t ((hasDerivAt_id t).const_mul T)
  have hsn : HasDerivAt (fun s => Real.sin (T * s)) (Real.cos (T * t) * T) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sin (T * t)).comp t ((hasDerivAt_id t).const_mul T)
  have hx : HasDerivAt (fun s => (rabi T s).1) ![-Real.sin (T * t) * T, 0] t := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa [rabi] using hc
    · simpa [rabi] using hasDerivAt_const t (0 : ℝ)
  have hy : HasDerivAt (fun s => (rabi T s).2) ![0, Real.cos (T * t) * T] t := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa [rabi] using hasDerivAt_const t (0 : ℝ)
    · simpa [rabi] using hsn
  convert hx.prodMk hy using 1
  simp only [schr, hamN_zero_dimer, H_mulVec, rabi]
  refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;> simp <;> ring

lemma tdens_rabi (T t : ℝ) : tdens occ (rabi T t) 0 = Real.cos (T * t) ^ 2 := by
  simp [tdens_dimer, rabi]

/-- **The Rabi oscillation never enters `Ω`.** A particle released from one site has zero bond
order at all times: it moves at the speed limit, and no potential can change `n̈` at any instant. -/
theorem rabi_not_mem_omega (T t : ℝ) : rabi T t ∉ omega (H T) occ := by
  rw [mem_omega_dimer_iff]
  rintro ⟨-, hb⟩
  exact hb (by simp [bond, rabi])

end Dimer

end LatticeDFT
