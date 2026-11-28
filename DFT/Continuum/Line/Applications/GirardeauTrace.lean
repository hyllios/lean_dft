/-
Copyright (c) 2026 lean_dft contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefano Pittalis
-/
import QM.ManyBody.Girardeau
import DFT.Continuum.Line.HK.ChamberTrace
import DFT.Continuum.Line.Applications.HardCoreW

/-!
# Girardeau image criterion on the Dirichlet interval

The symmetric zero-trace states are exactly the images, up to equality almost everywhere,
of antisymmetric Dirichlet Sobolev states for any positive finite particle count.
-/

namespace DFT.Continuum.Line.CollisionTrace

open MeasureTheory MeasureTheory.UnitCube Set SturmLiouville Filter Topology

variable {n : ℕ}

theorem fermion_trace {Ψ : Cfg n → ℝ} (h : Ψ ∈ DomW .fer n) (k : Fin (n + 1)) (j : Fin n) :
    trace k j Ψ (h1W_of_mem h) = 0 := by
  rw [trace_zero]
  obtain ⟨s, hs⟩ := slice_approx (h1W_of_mem h) k
  filter_upwards [hs, coordinate_interior j] with y hy ht
  apply tendsto_nhds_unique (hy.1 _ (Ioo_subset_Icc_self ht))
  refine tendsto_const_nhds.congr (fun m => Eq.symm ?_)
  exact trunc_planeY (memY_of_fer h) _ (Fin.succAbove_ne k j).symm
    ⟨fun _ => (k.succAbove j).isLt, fun _ => k.isLt⟩ (by simp [line])

private theorem alternating_eq (u : Cfg n → ℝ) :
    QM.ManyBody.Girardeau.alternating u = altY (n + 1) u := by
  classical
  funext x
  simp only [QM.ManyBody.Girardeau.alternating, altY, YG_all, ite_true]
  rfl

/-- The image of the Girardeau map on real Dirichlet states is the joint kernel
of the pairwise collision traces within the bosonic sector (Corso, Remark 4.9). -/
theorem collisionTrace_iff {Φ : Cfg n → ℝ} (h : Φ ∈ DomW .bos n) :
    (∀ k j, trace k j Φ (h1W_of_mem h) = 0) ↔
      ∃ Ψ ∈ DomW .fer n, Φ =ᵐ[μN n] mulA Ψ := by
  classical
  let zero := fun f : Cfg n → ℝ => ∀ k j, ∀ᵐ y ∂Sine.piM n, face k j (dW k f) y = 0
  have hz (f : Cfg n → ℝ) (hf : H1W f) : zero f ↔ ∀ k j, trace k j f hf = 0 := by
    exact ⟨fun z k j => (trace_zero hf k j).2 (z k j), fun z k j => (trace_zero hf k j).1 (z k j)⟩
  rw [← hz Φ (h1W_of_mem h)]
  apply QM.ManyBody.Girardeau.image_iff (C := RY (n + 1) n) (regular := {u | H1W u})
    (fermionic := (DomW .fer n : Set (Cfg n → ℝ))) (zeroTrace := zero)
    (fun _ hx => strictMono_of_RY hx) ae_injective
  · filter_upwards [ae_cube, ae_injective] with x hx hi
    obtain ⟨σ, _, hR⟩ := exists_YG_sort (a := n + 1) hx hi
    exact ⟨σ, hR⟩
  · apply ae_all_iff.2
    intro σ
    change ∀ᵐ x ∂μN n, Φ (pm σ x) = Φ x
    simpa only [ch_bos, one_mul] using h.2.2 σ trivial
  · intro hzero
    refine ⟨h.1.indicator measurableSet_RY.nullMeasurableSet,
      fun k => ⟨(RY (n + 1) n).indicator (dW k Φ), ?_⟩⟩
    exact ((chamber_derivative (h1W_of_mem h) ((hz _ (h1W_of_mem h)).1 hzero)
      k (pY (n + 1) n)).congr (indicator_RY_ae Φ)).congr_right (indicator_RY_ae _)
  · intro u hu
    change H1W u at hu
    rw [alternating_eq, DomW_fer_eq]
    have hsum (k : Fin (n + 1)) := isWD_sumY (a := n + 1) (k := k) sgn
      (F := fun _ => u) (G := fun σ => dW (σ⁻¹ k) u) (fun _ _ => hu.1)
      (fun σ _ => dW_spec (hu.2 (σ⁻¹ k)))
    exact ⟨(hsum 0).1, fun k => ⟨_, (hsum k).2⟩, fun _ hρ => ae_of_all _ fun x => altY_pm _ hρ x⟩
  · intro g hg
    exact (hz _ (h1W_of_mem hg)).2 (fermion_trace hg)
  · intro g hg he hzero k j
    filter_upwards [face_sq_congr (h1W_of_mem h) (h1W_of_mem hg) he k j, hzero k j] with y hy hgy
    rw [hgy, zero_pow (by decide)] at hy
    exact sq_eq_zero_iff.mp hy

end DFT.Continuum.Line.CollisionTrace
