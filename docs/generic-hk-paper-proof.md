# Generic Hohenberg–Kohn on finite lattices (2026-11-05)

Setting: graph G (M sites), N fermions (1 ≤ N ≤ M−1), configurations C (N-subsets), real symmetric
H(v) = H0 + diag(n(c)·v), H0 = signed hopping + any fixed diagonal interaction. Potentials mod constants: R^{M−1}.
Bad set B = {v : ground state non-degenerate, and ∃ v' ≠ v + const with the same ground state}.
(Equivalently, by the J2/J3 argument: ∃ non-constant w with W(c)=n(c)·w constant on supp ψ0.)

**Hypothesis (H\*)**: ∃ v* such that H(v*) and each principal minor H^{(c)}(v*) share no eigenvalue
(⇔ simple spectrum and every eigenvector nonzero on every configuration).

**Theorem.** Under (H\*):
(a) B ⊂ {R = 0}, R(v) = ∏_c Res_E(det(E−H(v)), det(E−H^{(c)}(v))) a NONZERO polynomial, invariant under constant
    shifts. Hence strong HK holds on an open dense, full-measure set of potentials; dim B ≤ M−2 (codim ≥ 1).
(b) The set of ground-state densities produced by more than one potential, ρ(B), is semialgebraic with
    dim ≤ M−3 inside the (M−1)-dimensional density space (codim ≥ 2).
(c) Both bounds are sharp: 2 fermions on the square (bad v = plane v0+v2=v1+v3, bad ρ = two lines).

Proof.
(a) Full support ⇒ no non-constant w with W constant on all of C (swap one particle: w_i = w_j), so v ∈ B ⇒ ψ0_c = 0
    for some c ⇒ ψ0 restricted is an eigenvector of H^{(c)} with the same eigenvalue ⇒ R_c(v) = 0.
    R_c is a polynomial in v (resultant of monic polys with polynomial coefficients). At v*: p_c(E_j) = ψ_{jc}^2
    ∏_{l≠j}(E_j−E_l) ≠ 0 (from p_c/p = Σ_k ψ_{kc}^2/(E−E_k)), so R_c(v*) ≠ 0. Zero set of a nonzero polynomial:
    closed, nowhere dense, measure zero, dimension ≤ (ambient) − 1. Constant shift moves H and H^{(c)} by the same Nk.
(b) B and ρ are semialgebraic. For v ∈ B with invisible w and gap g, J3 `persist_of_gap` gives v+εw ∈ B with the
    SAME ψ (hence same ρ) for |ε| < g/m (strict gap kept). So every fibre of ρ|_B contains a segment: dim ≥ 1.
    Hardt triviality ⇒ dim ρ(B) ≤ dim B − 1 ≤ M−3. Also ρ(B) is exactly the set of non-uniquely-representable
    (non-degenerate) ground-state densities (weak HK + the J2 strong-HK argument).
(c) generic_hk.py / J3 `square_wall`.

**Status of (H\*)**: certified EXACTLY (integer v, gcd of char. polys mod 2^61−1 = 1 ⇒ resultant ≠ 0 over Z) for
every connected graph with M ≤ 7, every 1 ≤ N ≤ M−1, U ∈ {0,1}: 11,570 cases, 0 exceptions
(scripts/hstar_exact.py, hstar_exact_upper.py, certificates in hstar_certificates*.json).
General proof of (H\*) open (N=1 is the classical generic-diagonal statement; for N>1 the diagonal is restricted to
an M-dim family). Failure of (H\*) would signal a hidden conserved quantity (codim-0 non-uniqueness).

**Dimension count (heuristic, matches all 7 families found)**: for a failure family with zero set Z, support S,
K = null(H0[Z,S]), m_inv = # non-constant invisible directions:
  dim(bad v) = max(dim K + M − 1 − |S|,  m_inv),   dim(bad ρ) = dim(bad v) − m_inv.
Square: dim K = 3 (boundary matrix rank 1 instead of 2 — the twin/hidden-Q structure), dim = 2, ρ-dim 1.
Wheel W4 (atlas 50, M=5, N=2, U=0,1; the only 5-site failure): 4 zeros, dim K = 2, dim = max(0,1) = 1 (just the
invisible line), ρ-dim 0 — isolated bad densities (codim 4).
Census M=4,5 (N=2, U=0,1): failures only on the square and the wheel W4.

## Towards a general proof of (H*) (2026-11-05)
1. Reformulation: (H*) for configuration c ⇔ e_c is a cyclic vector of H(v) for some v ⇔ the Krylov determinant
   det[e_c, He_c, …, H^{L−1}e_c] (a polynomial in v) is not identically zero. (Physics: starting from configuration c,
   the dynamics reaches every eigenstate.)
2. Reduction (rigorous): put v = λu, u generic (all d_y = n(y)·u distinct), λ→∞. Levels are simple and analytic in 1/λ;
   the eigenstate localised on x has amplitude on c equal to A_xc(u) λ^{−k} + O(λ^{−k−1}), k = config-graph distance,
       A_xc(u) = Σ_{shortest paths x=y0→…→yk=c} Π_j H0_{y_j y_{j−1}} / Π_{j≥1} (d_x − d_{y_j}).
   If every A_xc is not identically zero, then for generic u and large λ all eigenvector amplitudes are nonzero ⇒ (H*).
   ("Path-sum lemma": A_xc ≢ 0 for all x ≠ c.)
3. Proven cases of the path-sum lemma:
   - No sign problem (stoquastic H0): evaluate at u = 1_x (x is the unique top config, all d_x − d_y = N − |x∩y| > 0):
     all terms have the same sign ⇒ A_xc ≠ 0. (But then Perron–Frobenius already gives HK everywhere.)
   - N = 1, any signs (frustrated hopping): resonate one shortest path (u = u_x on its intermediates, generic elsewhere);
     that path dominates ⇒ A_xc ≢ 0.
   - Any N, any signs, distance k ≤ 2 (and k = 3 modulo a check that restricted linear forms stay non-proportional):
     partial fractions — distinct configs give pairwise non-proportional forms ℓ_y = (n(x)−n(y))·u, so the pole of each
     intermediate cannot cancel.
4. Obstacle for general k with fermion signs: iterated residues on the hyperplanes {d_x = d_y} can make forms of other
   configurations proportional (commuting moves form "parallelograms" in config space; repeated hops along the same bond),
   so single paths are not isolated and signed sub-sums could in principle cancel.
5. Evidence: A_xc ≢ 0 checked for ALL pairs, all connected graphs M ≤ 6, all N (667 cases, scripts/pathsum.py);
   (H*) itself certified exactly for M ≤ 7 (11,570 cases).
Remark: HK failures need sign cancellations at SPECIAL potentials; violating (H*) would need a cancellation for EVERY
potential — a much stronger requirement, which is why (H*) is expected to hold universally.

## Literature check (2026-11-05, aims literature tool)
- Penz & van Leeuwen, JCP 155, 244111 (2021) [arXiv:2106.15370]: lattice HK counterexamples incl. the
  non-interacting 2-fermion SQUARE (states Ψ_A/Ψ_B, potentials (s,t), |s|>|t|) — our wall is (at U=0) their family.
  Thm 11: non-uv densities ⊂ finite union of linear subspaces ⇒ measure zero (codim ≥ 1). Perron–Frobenius ⇒ HK for
  1 particle and for the linear chain. "Almost all potentials uv" only as an outlook (Sec. IV B).
- Penz & van Leeuwen, Quantum 7, 918 (2023) [arXiv:2206.12366]: non-uv densities closed, measure zero (Cor. 10);
  occur only where degeneracy regions touch each other / the boundary. EXPLICITLY retracts the earlier potential-side
  claim ("premature conclusion that the set of non-uv potentials has measure zero"); degeneracy in v-space only
  "expected" to be rare.
- Penz & van Leeuwen, JCP 161 (2024) [arXiv:2407.20260]: restates D_m closed, measure zero; v-space rarity "in many examples".
What looks NEW here: (i) non-uv potentials AND degenerate-GS potentials have measure zero (proved via resultant/
discriminant ≢ 0), rigorous for all connected M ≤ 7 by exact certificate, general modulo the path-sum lemma;
(ii) codim ≥ 2 for non-uv densities of non-degenerate ground states (they have codim ≥ 1);
(iii) hidden-involution/twin mechanism of the square wall, persistence with interactions (U=1), the wheel W4
(isolated bad densities), Lean proofs (J2/J3).
Caveat: spinful Hubbard has SU(2) multiplets for every v ⇒ (H*) fails globally; must be applied per (S, S_z) sector.

## PROOF of the path-sum lemma, hence of (H*), for spinless fermions (2026-11-05)
Setting: connected G, 1 ≤ N ≤ M−1, hopping t on every edge (any sign; more generally any real t_e with
Σ_routes Π t_e ≠ 0 over shortest routes of each site pair), ANY fixed configuration-diagonal interaction.

Step 1 (interaction drops out). For H = λD(u) + H0 + V, u generic (all d_y distinct), the eigenvector localised on x
has c-amplitude A_xc(u)λ^{−k} + O(λ^{−k−1}); A_xc depends only on hopping and d's, not on V. So compute it at V=0.
Step 2 (Slater). At V=0 the eigenvector is det[φ_{x_i}(c_j)], with single-particle orbitals φ_a(b) = a_ab(u)λ^{−d(a,b)}(1+O(1/λ)),
a_ab(u) = Σ_{shortest routes a→b} Π_e t_e / Π_{z on route, z≠a}(u_a − u_z). Hence the leading term is λ^{−m} D(u),
  D(u) = Σ_{π ∈ Opt} sign(π) Π_i a_{x_i, c_π(i)}(u),   m = min-cost assignment (graph metric), Opt = optimal bijections.
Since each hop moves one particle one step, k ≥ m; so D ≢ 0 ⇒ k = m and A_xc = ±D ≢ 0.
(Numerical check: scripts/slater_check.py, 324 pairs, |A|=|D| to 1e-13, k=m always.)
Step 3 (choose π0). There is an optimal π0 fixing x∩c pointwise (triangle inequality: reroute s→c_j, x_i→s into
x_i→c_j, s→s). Let n' = |x∖c| = # particles moved by π0. Pair classes K_i = {x_i, c_π0(i)} (disjoint), other sites singletons.
Step 4 (resonant limit). Let V = {u : u_{x_i} = u_{c_π0(i)} for moved i}, take u = u* + εδ, u* generic in V, ε→0.
A factor 1/(u_{x_i} − u_z) is singular iff z ∈ K_i∖{x_i} = {c_π0(i)}; a shortest route visits it at most once. So the term of π
has pole order ≤ #{moved i : c_π0(i) lies on a shortest route x_i → c_π(i)}. Order n' forces, for all moved i,
d(x_i,c_π(i)) = d(x_i,c_π0(i)) + d(c_π0(i),c_π(i)); summing and using optimality of π gives d(c_π0(i),c_π(i)) = 0, i.e. π = π0.
So D = ε^{−n'} sign(π0) Π_moved S_i(u*)/(−δ_i) + O(ε^{−n'+1}), S_i = Σ_routes Π t_e / Π_{interior z}(u_{x_i} − u_z).
Step 5. S_i ≢ 0 on V: shift the class K_i to +∞ inside V (interior sites are not in K_i): S_i ≈ (Σ_routes Π t_e)/u^{d−1} ≠ 0.
V is a linear space, so Π S_i ≢ 0 on V; pick u* with Π S_i(u*) ≠ 0 ⇒ D ≢ 0. ∎
Consequence: for generic u and large λ, H(λu) has simple spectrum and every eigenvector is nonzero on every
configuration ⇒ (H*) ⇒ THEOREM (generic HK) holds for ALL finite connected lattices, all fillings, all diagonal
interactions (spinless fermions): non-uv and degenerate-GS potentials lie in a proper algebraic hypersurface
(measure zero, nowhere dense); non-uv ground-state densities (non-degenerate) have codimension ≥ 2.
Physics of the proof: in the strong-potential limit the many-body sign problem reduces to the sign of a permutation,
and a resonance (near-degenerate pairs start/target) singles out one assignment, so Pauli signs cannot cancel.
Spinful Hubbard: NOT covered by this proof (charge-degenerate spin configurations ⇒ degenerate perturbation theory);
covered sector-wise by exact certificates (M ≤ 5 all sectors, U ∈ {1,4}; M = 6 running), only exception the trivial
N=M fully polarised sector (density ≡ 1).

## Independent review (2026-11-05): "correct with fixable gaps" — corrections adopted
1. HOPPING HYPOTHESIS (the one real overclaim): Step 5 needs Σ_{shortest routes a→b} Π t_e ≠ 0 for all site pairs.
   Holds for uniform t (either sign), any t_e > 0, any gauge-unfrustrated real hopping. Fails for frustrated/complex
   hopping (π-flux square: opposite-corner routes cancel). Since (H*) is polynomial in (v, t_e) and holds at uniform t,
   it also holds for GENERIC t_e (outside a proper algebraic subset, real or complex). For ALL nonzero frustrated t_e it
   remains open — but the reviewer's search found no counterexample in 54,512 cases (all connected 4–6-site graphs, all
   ±1 sign patterns, π-flux and complex-flux squares, random 7-site graphs).
2. Degenerate GS ⊂ {R=0}: by Cauchy interlacing a multiple eigenvalue of H is an eigenvalue of every principal minor.
3. Step 1 genericity: need all N-subset sums d_y distinct; A_xc, D are rational functions of u; the ε-limit of Step 4 is
   taken on the rational function after the 1/λ expansion at generic u.
4. A_xc = ±D: sign from determinant ordering/normalisation and (−1)^d convention.
5. Steps 3–4 details: rerouting terminates (fixed common sites strictly increase); classes pairwise disjoint; equality
   case also forces π = π0 on unmoved particles; define δ_i := δ_{x_i} − δ_{c_π0(i)}.
6. Complex Hermitian H0: replace ψ² by |ψ|²; (a),(b) carry over once (H*) holds.
7. (b): persistence needs |ε|·2‖W‖∞ < gap; fibres have dim ≥ 1 mod constants (w non-constant); HK step needs only v
   non-degenerate; B and ρ|_B semialgebraic by Tarski–Seidenberg.
8. Hypotheses to state: spinless; configuration-diagonal interaction (pair/correlated hopping break Step 1);
   G connected, 1 ≤ N ≤ M−1; hopping condition of item 1.

## Lean status (2026-11-05)
J4.lean (no sorry, standard axioms): Krylov criterion (an eigenvector vanishing on c makes det[e_c, He_c, …] = 0 —
cleaner than resultants and needs NO non-degeneracy), Krylov determinant as MvPolynomial in v, identity theorem ⇒
nonzero polynomial cannot vanish on an open set, and
  `generic_hk`: Rigid n ∧ (∀c, KrylovPoly_c ≠ 0) ⇒ non-uv potentials ⊂ closed set with empty interior.
J4sq.lean: (H*) for 2 fermions on the square verified IN LEAN (six exact 6×6 determinants at v = (−3,−3,−2,0):
64, −432, −448, −448, −432, 64) ⇒ `square_generic_hk` fully formal.
Remaining for a fully general formal proof: (i) measure-zero (Fubini induction on variables) — moderate;
(ii) general (H*) = path-sum lemma: needs 1/λ asymptotics of eigenvectors (or an algebraic substitute) — heavy;
(iii) codim-2 densities: semialgebraic dimension theory absent from Mathlib — very heavy, likely skip.
J5.lean (2026-11-05, no sorry, standard axioms): `volume_zeroSet` (zero set of a nonzero real MvPolynomial in
finitely many variables is Lebesgue-null; Fubini induction via finSuccEquiv + piFinSuccAbove), `generic_hk_ae`
(non-uv potentials ⊂ closed, nowhere dense, null set, given Rigid + (H*)), `square_generic_hk_ae` (fully formal).
Remaining: general (H*) (path-sum lemma).
