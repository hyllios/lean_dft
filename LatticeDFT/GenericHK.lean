import LatticeDFT.PathSum.ResonantPoint
import LatticeDFT.Generic.NullSets

/-!
# Generic Hohenberg–Kohn theorem for spinless lattice fermions

`generic_hk_lattice_fermions`: for `N` spinless fermions (`0 < N < M`) on any connected graph with
hopping `t ≠ 0` and any density–density interaction, the potentials at which a ground state is
shared with a potential differing by more than a constant form a closed, nowhere dense,
Lebesgue-null set. `generic_hk_lattice_fermions_w`: the same for edge-dependent hopping amplitudes
of a common sign.
-/

namespace LatticeDFT

section

open Matrix MvPolynomial

variable {M N : ℕ}

/-- Occupations of `N`-particle configurations are rigid when `0 < N < M`. -/
theorem rigid_occF (hN0 : 0 < N) (hNM : N < M) : Rigid (occF : Fin M → Conf M N → ℝ) := by
  classical
  intro w κ h
  refine ⟨w ⟨0, by omega⟩, fun i => ?_⟩
  -- show w i = w j for all i, j
  have key : ∀ i j : Fin M, i ≠ j → w i = w j := by
    intro i j hij
    obtain ⟨s, hsi, hsj, hcard⟩ := Finset.exists_subsuperset_card_eq
      (s := {i}) (t := Finset.univ.erase j) (n := N)
      (by simpa using hij) (by simp; omega) (by simp; omega)
    have hi : i ∈ s := hsi (Finset.mem_singleton_self i)
    have hj : j ∉ s := fun h => (Finset.mem_erase.mp (hsj h)).1 rfl
    set s1 : Conf M N := ⟨s, hcard⟩
    have hcard2 : (insert j (s.erase i)).card = N := by
      rw [Finset.card_insert_of_notMem (fun h => hj (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hi]; omega
    set s2 : Conf M N := ⟨insert j (s.erase i), hcard2⟩
    have e1 := h s1
    have e2 := h s2
    have hsum : ∀ (S : Finset (Fin M)), ∑ k, w k * (if k ∈ S then (1 : ℝ) else 0) =
        ∑ k ∈ S, w k := by
      intro S; simp [Finset.sum_ite_mem]
    simp only [occF] at e1 e2
    rw [hsum] at e1 e2
    simp only [s1, s2] at e1 e2
    rw [Finset.sum_insert (fun h => hj (Finset.mem_of_mem_erase h))] at e2
    rw [← Finset.add_sum_erase _ _ hi] at e1
    linarith
  by_cases hi : i = ⟨0, by omega⟩
  · rw [hi]
  · exact key i ⟨0, by omega⟩ hi

/-- Linear form `Σ_l X_{z l} − Σ_{i ∈ y} X_i`. -/
noncomputable def formZ (y : Conf M N) (z : Fin N → Fin M) : MvPolynomial (Fin M) ℝ :=
  ∑ l, X (z l) - ∑ i, C (occF i y) * X i

/-- Linear form `Σ_i (n_i(s) − n_i(s')) X_i`. -/
noncomputable def formW (s s' : Conf M N) : MvPolynomial (Fin M) ℝ :=
    ∑ i, C (occF i s - occF i s') * X i

lemma eval_formZ (y : Conf M N) (z : Fin N → Fin M) (u : Fin M → ℝ) :
    eval u (formZ y z) = ∑ l, u (z l) - wC u y := by
  simp [formZ, wC, mul_comm]

lemma eval_formW (s s' : Conf M N) (u : Fin M → ℝ) : eval u (formW s s') = wC u s - wC u s' := by
  simp only [formW, wC, map_sum, map_mul, eval_C, eval_X]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

lemma formW_ne_zero {s s' : Conf M N} (h : s ≠ s') : formW s s' ≠ 0 := by
  classical
  have : ¬ s.1 ⊆ s'.1 := by
    intro hsub; apply h; apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by rw [s.2, s'.2])
  obtain ⟨i, his, his'⟩ := Finset.not_subset.mp this
  intro h0
  have := congrArg (eval (fun k => if k = i then (1 : ℝ) else 0)) h0
  rw [eval_formW, map_zero] at this
  simp [wC, occF, his, his', Finset.sum_ite_eq'] at this

lemma formZ_ne_zero {y : Conf M N} {z : Fin N → Fin M}
    (h : ¬ ∃ ρ : Equiv.Perm (Fin N), ∀ l, z l = τs y (ρ l)) : formZ y z ≠ 0 := by
  classical
  intro h0
  have hcount : ∀ i, ((Finset.univ.filter (fun l => z l = i)).card : ℝ) = occF i y := by
    intro i
    have := congrArg (eval (fun k => if k = i then (1 : ℝ) else 0)) h0
    rw [eval_formZ, map_zero] at this
    simp only [wC, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true] at this
    have hc : ∑ l, (if z l = i then (1 : ℝ) else 0) =
        (Finset.univ.filter (fun l => z l = i)).card := by
      simp
    rw [← hc]; linarith
  apply h
  have hinj : Function.Injective z := by
    intro l1 l2 h12
    by_contra hne
    have h2 : 2 ≤ (Finset.univ.filter (fun l => z l = z l1)).card := by
      have : {l1, l2} ⊆ Finset.univ.filter (fun l => z l = z l1) := by
        intro l hl; simp at hl; rcases hl with rfl | rfl <;> simp [h12]
      calc 2 = ({l1, l2} : Finset (Fin N)).card := by rw [Finset.card_pair hne]
        _ ≤ _ := Finset.card_le_card this
    have := hcount (z l1)
    simp only [occF] at this
    have h2r : (2 : ℝ) ≤
        ((Finset.univ.filter (fun l => z l = z l1)).card : ℝ) := by exact_mod_cast h2
    split_ifs at this <;> linarith
  have hmem : ∀ l, z l ∈ y.1 := by
    intro l
    have := hcount (z l)
    have hpos : 0 < (Finset.univ.filter (fun l' => z l' = z l)).card :=
      Finset.card_pos.mpr ⟨l, by simp⟩
    simp only [occF] at this
    split_ifs at this with hm
    · exact hm
    · exfalso
      have hp : (0 : ℝ) <
          ((Finset.univ.filter (fun l' => z l' = z l)).card : ℝ) := by exact_mod_cast hpos
      linarith
  exact exists_perm_of_injective y hinj hmem

/-- **(H*) for spinless lattice fermions** with edge-dependent hopping amplitudes of a common sign.
-/
theorem hstar_lattice_fermions_w {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : Fin M → Fin M → ℝ} {s : ℝ} (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (c : Conf M N)
    (Vint : Conf M N → ℝ) :
    krylovPoly (H0Fw G t Vint) occF c (fun j => (Fintype.equivFin (Conf M N) j : ℕ)) ≠ 0 := by
  classical
  -- polynomial conditions: distinct configuration energies and multiset genericity
  set κ1 := {p : Conf M N × Conf M N // p.1 ≠ p.2}
  set κ2 := {p : Conf M N × (Fin N → Fin M) // ¬ ∃ ρ : Equiv.Perm (Fin N), ∀ l, p.2 l =
      τs p.1 (ρ l)}
  obtain ⟨u, hu, hD, hR⟩ := exists_common_ne (κ := κ1 ⊕ κ2)
    (fun y : Conf M N => fun u => DExp G t u c y) (fun y => ratOn_DExp G t c y)
    (fun y => exists_DExp_ne hG hts c y)
    (fun k => Sum.elim (fun p : κ1 => formW p.1.1 p.1.2) (fun p : κ2 => formZ p.1.1 p.1.2) k)
    (fun k => by
      rcases k with p | p
      · exact formW_ne_zero p.2
      · exact formZ_ne_zero p.2)
  have hw : Function.Injective (wC u : Conf M N → ℝ) := by
    intro s s' h
    by_contra hne
    have := hR (Sum.inl ⟨(s, s'), hne⟩)
    simp only [Sum.elim_inl, eval_formW, h, sub_self] at this
    exact this rfl
  have hgen : ∀ y : Conf M N, ∀ z : Fin N → Fin M, ∑ l, u (z l) = wC u y →
      ∃ ρ : Equiv.Perm (Fin N), ∀ l, z l = τs y (ρ l) := by
    intro y z hz
    by_contra hne
    have := hR (Sum.inr ⟨(y, z), hne⟩)
    simp only [Sum.elim_inr, eval_formZ, hz, sub_self] at this
    exact this rfl
  have hα : ∀ y, alphaRep (Γ (-hopM G t)) (wC u) hw (mopt G c) (lip_mopt hG t c) c
      (mopt_self G c) y y ≠ 0 := by
    intro y
    rw [alpha_eq_D hG t u hu hw c y (hgen y), D_eq_DExp hG t hu c y]
    exact hD y
  exact hstar_of_alpha (lip_mopt hG t c) (mopt_self G c) occF u hw hα Vint

/-- **(H*) for spinless lattice fermions** with uniform hopping `t ≠ 0`. -/
theorem hstar_lattice_fermions {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : ℝ}
    (ht : t ≠ 0) (c : Conf M N) (Vint : Conf M N → ℝ) :
    krylovPoly (H0F G t Vint) occF c (fun j => (Fintype.equivFin (Conf M N) j : ℕ)) ≠ 0 := by
  rw [H0F_eq_H0Fw]
  exact hstar_lattice_fermions_w hG (s := t) (fun _ _ _ => mul_self_pos.mpr ht) c Vint

/-- **Generic Hohenberg–Kohn theorem for spinless lattice fermions, edge-dependent hopping.** The
hopping amplitudes `t a b` (symmetric) may vary from edge to edge, as long as they share a common
sign (no frustration). Then the non-unique potentials are contained in a closed, nowhere dense,
Lebesgue-null set. -/
theorem generic_hk_lattice_fermions_w {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected)
    {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
        (hts : ∀ a b, G.Adj a b → 0 < s * t a b)
    (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUV (H0Fw G t Vint) occF v} ⊆ Z :=
  generic_hk_ae (H0Fw_isSymm G htsym Vint) (rigid_occF hN0 hNM) _
    (fun c => hstar_lattice_fermions_w hG hts c Vint)

/-- **Generic Hohenberg–Kohn theorem for spinless lattice fermions.** For `N` fermions (`0 < N < M`)
on any connected graph with hopping `t ≠ 0` and any density–density interaction, the set of
potentials whose ground state is also the ground state of a potential differing by more than a
constant is contained in a closed, nowhere dense, Lebesgue-null set. This is the special case of
`generic_hk_lattice_fermions_w` with uniform hopping. -/
theorem generic_hk_lattice_fermions {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected)
    {t : ℝ} (ht : t ≠ 0) (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUV (H0F G t Vint) occF v} ⊆ Z := by
  rw [H0F_eq_H0Fw]
  exact generic_hk_lattice_fermions_w hG (fun _ _ => rfl) (s := t)
    (fun _ _ _ => mul_self_pos.mpr ht) hN0 hNM Vint

end

end LatticeDFT
