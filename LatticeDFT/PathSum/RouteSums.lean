import LatticeDFT.PathSum.FreeFermions
import LatticeDFT.StrongPotential.Resolvent

/-!
# Explicit single-particle route sums

Layer-recursive route sums `Gr`, `alphaExp` (defined for every potential), with `alphaRep_eq_alphaExp` and the
explicit Slater-type sum `DExp` (`D_eq_DExp`).
-/

namespace LatticeDFT

section

open Matrix

variable {M N : ℕ}

section
variable (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : ℝ) (u : Fin M → ℝ)

/-- Layered resolvent route sums. -/
noncomputable def Gr (b a : Fin M) : ℕ → Fin M → ℝ
  | 0, p => if p = b then 1 / (u a - u b) else 0
  | n + 1, p => if G.dist b p = n + 1 then
      (∑ q, (if G.Adj p q ∧ G.dist b q = n then -t * Gr b a n q else 0)) / (u a - u p) else 0

noncomputable def alphaExp (b a : Fin M) : ℝ :=
  (if a = b then 1 else 0) +
    ∑ p, (if G.Adj a p ∧ G.dist b p + 1 = G.dist b a then -t * Gr G t u b a (G.dist b p) p else 0)

end

lemma dist_eq_zero_iff {G : SimpleGraph (Fin M)} (hG : G.Connected) {b p : Fin M} :
    G.dist b p = 0 ↔ p = b := by
  rw [(hG.preconnected b p).dist_eq_zero_iff]; exact eq_comm

theorem Fres_eq_Gr {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected) (t : ℝ)
    {u : Fin M → ℝ} (hu : Function.Injective u) (b a : Fin M) :
    ∀ n p, G.dist b p = n → n < G.dist b a →
      Fres hu (lip_dist hG t b) (SimpleGraph.dist_self (v := b)) p (u a) = Gr G t u b a n p := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    have hpb : p = b := (dist_eq_zero_iff hG).mp hp
    subst hpb
    have hrec := Fres_rec hu (lip_dist hG t p) (SimpleGraph.dist_self (v := p)) p (u a)
      (fun z hz => by
        intro h; have := hu h; subst this; rw [hp] at hz; omega)
    have hsum : ∑ q ∈ Finset.univ.erase p, (if G.dist p q + 1 = G.dist p p then
        (-t • G.adjMatrix ℝ) p q * Fres hu (lip_dist hG t p) (SimpleGraph.dist_self (v := p)) q (u a)
        else 0) = 0 := by
      apply Finset.sum_eq_zero; intro q _; rw [SimpleGraph.dist_self]; simp
    rw [hsum, if_pos rfl, add_zero] at hrec
    have hne : u a - u p ≠ 0 := sub_ne_zero.mpr (fun h => by
      have := hu h; subst this; rw [hp] at *; omega)
    have hG0 : Gr G t u p a 0 p = 1 / (u a - u p) := by simp [Gr]
    rw [hG0, eq_div_iff hne]
    linarith
  | succ n ih =>
    intro p hp hlt
    have hpb : p ≠ b := by intro h; subst h; rw [SimpleGraph.dist_self] at hp; omega
    have hx : ∀ z, G.dist b z ≤ G.dist b p → u a ≠ u z := by
      intro z hz h; have := hu h; subst this; omega
    have hrec := Fres_rec hu (lip_dist hG t b) (SimpleGraph.dist_self (v := b)) p (u a) hx
    rw [if_neg hpb, zero_add] at hrec
    have hne : u a - u p ≠ 0 := sub_ne_zero.mpr (hx p le_rfl)
    have hGs : Gr G t u b a (n + 1) p =
        (∑ q, (if G.Adj p q ∧ G.dist b q = n then -t * Gr G t u b a n q else 0)) / (u a - u p) := by
      simp only [Gr, if_pos hp]
    rw [hGs, eq_div_iff hne, hrec]
    rw [← Finset.sum_erase Finset.univ (a := p)
      (f := fun q => if G.Adj p q ∧ G.dist b q = n then -t * Gr G t u b a n q else 0) (by simp)]
    apply Finset.sum_congr rfl; intro q hq
    have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
    by_cases hadj : G.Adj p q
    · by_cases hdq : G.dist b q = n
      · rw [if_pos (by omega), if_pos ⟨hadj, hdq⟩, ih q hdq (by omega)]
        simp [Matrix.smul_apply, SimpleGraph.adjMatrix_apply, hadj]
      · rw [if_neg (by omega), if_neg (by tauto)]
    · simp [hadj, Matrix.smul_apply, SimpleGraph.adjMatrix_apply]

theorem alphaRep_eq_alphaExp {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected) (t : ℝ)
    {u : Fin M → ℝ} (hu : Function.Injective u) (b a : Fin M) :
    alphaRep (-t • G.adjMatrix ℝ) u hu (fun z => G.dist b z) (lip_dist hG t b) b
      (SimpleGraph.dist_self (v := b)) a a = alphaExp G t u b a := by
  rw [alpha_diag, alphaExp]
  congr 1
  rw [← Finset.sum_erase Finset.univ (a := a)
    (f := fun p => if G.Adj a p ∧ G.dist b p + 1 = G.dist b a then -t * Gr G t u b a (G.dist b p) p else 0)
    (by simp)]
  apply Finset.sum_congr rfl; intro p hp
  by_cases hadj : G.Adj a p
  · by_cases hd : G.dist b p + 1 = G.dist b a
    · rw [if_pos hd, if_pos ⟨hadj, hd⟩, Fres_eq_Gr hG t hu b a _ p rfl (by omega)]
      simp [Matrix.smul_apply, SimpleGraph.adjMatrix_apply, hadj]
    · rw [if_neg hd, if_neg (by tauto)]
  · simp [hadj, Matrix.smul_apply, SimpleGraph.adjMatrix_apply]

/-- Explicit Slater-type sum. -/
noncomputable def DExp (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : ℝ) (u : Fin M → ℝ)
    (c y : Conf M N) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => acost G c (τs y) σ.symm = mopt G c y),
    (Equiv.Perm.sign σ : ℝ) * ∏ l, alphaExp G t u (τs c (σ.symm l)) (τs y l)

theorem D_eq_DExp {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected) (t : ℝ)
    {u : Fin M → ℝ} (hu : Function.Injective u) (c y : Conf M N) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => acost G c (τs y) σ.symm = mopt G c y),
      (Equiv.Perm.sign σ : ℝ) * ∏ l, βsp G hG t u hu c y σ l (τs y l) = DExp G t u c y := by
  apply Finset.sum_congr rfl; intro σ _
  congr 1
  apply Finset.prod_congr rfl; intro l _
  exact alphaRep_eq_alphaExp hG t hu _ _

end

end LatticeDFT
