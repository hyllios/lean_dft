# Roadmap: quantum mechanics → many-body theory → Green's functions → DFT

Living document: update the status table, the track entries and the log as things land. Finished work is documented in the
blueprint and [`MODULES.md`](MODULES.md); this file keeps only status, pointers and the plans for open items.
Structure and rules: [`ARCHITECTURE.md`](ARCHITECTURE.md), [`AGENTS.md`](AGENTS.md). Main results: [`MAIN_RESULTS.md`](MAIN_RESULTS.md).

## 0. Strategy

Two lanes run in parallel.

- **Fast lane: everything exact in finite dimensions** (finite Hilbert spaces, lattices, finitely many modes): the postulates of
  QM, angular momentum, Fock space and Wick's theorem, Green's functions and linear response, Hartree–Fock, RDMFT, lattice DFT
  and TDDFT. Provable today with Mathlib; this is where lean_dft gets its speed.
- **Slow lane: continuum operator theory** (unbounded spectral theorem, Stone, Kato–Rellich, Hardy, Coulomb self-adjointness,
  then Lieb–Thirring, Lieb–Oxford, Thomas–Fermi). Genuine analysis, reviewed upstream at human speed. **Physlib is building
  this lane**; we contribute there instead of duplicating it.

The lanes meet through **limit theorems** (lattice → continuum, finite volume → thermodynamic limit), each research-grade.

## 1. Where things live

| Material | Library / source |
|---|---|
| Pure mathematics Mathlib lacks | `ForMathlib` → Mathlib PRs |
| Basic QM (expectation values, uncertainty, unbounded operators, bounded Stone) | **Physlib**, re-exported by `QM/Basic.lean` |
| Density matrices, partial trace, entropy, channels | **Physlib's `QuantumInfo`** |
| Fermionic Wick algebra (QFT form) | **Physlib** `QFT/PerturbationTheory/WickAlgebra` (cannot express state expectations) |
| Finite-dimensional QM, many-body theory, Green's functions, response | `QM` → PhyslibAlpha → Physlib |
| Density-functional theory | `DFT` |

Not in Mathlib v4.36.0 (checked 2026-11-25): unbounded spectral theorem, unbounded Stone, Kato–Rellich, Hardy (Physlib has
started spectral measures); explicit (θ, φ) coordinates on spheres (only `Measure.toSphere`); Fock space and CAR/CCR as Hilbert
space objects (now ours, B1).

## 2. Status at a glance (2026-11-27)

Status: ✅ done · 🟡 partly done · ⬜ not started.

| Track | Done | Open |
|---|---|---|
| A. Finite-dimensional QM | A1–A5, A4+ | A4++ spherical harmonics (approved), A6 Kato cusp, A7 Sturm oscillation (statements pending approval) |
| B. Many-body, finitely many modes | B1–B3, B3+ | B4 Gibbs/KMS, B5 Borland–Dennis and pinning (proposal) |
| C. Green's functions | C1 for eigenstates | C1 rest, C2–C7 |
| D. DFT | D0, D4, D5 | D1–D3 |
| E. Continuum operator theory | — | E1–E6 (with Physlib) |
| F. Research frontier | F1 numerics/paper side | F1 in Lean, F2, F3 |

## 3. Tracks

### A. Foundations of QM, finite-dimensional (`QM/Finite`, `QM/Spin`, `QM/AngularMomentum`, `QM/ManyBody`)
- A1 ✅ States, observables, Born rule, uncertainty (Physlib; bridge `QM/Finite/States`, sanity theorem `QM/Finite/Qubit`).
- A2 ✅ Time evolution, Ehrenfest, propagator, adiabatic theorem (`QM/Finite/{Evolution,Propagator,Adiabatic,Riesz}`).
- A3 ✅ Schmidt decomposition, natural orbitals.
- A4 ✅ N spins ½, su(2) ladder theorem. A4+ ✅ angular momentum: spin-j, coupling, Clebsch–Gordan, Racah, 3j/6j/9j,
  Biedenharn–Elliott, orbital `L` on harmonic polynomials, bridge to Physlib's `𝐋` (`QM/AngularMomentum`).
- A4++ ⬜ Spherical harmonics (**statements approved 2026-11-26**; plan in §6.1).
- A5 ✅ Ground states, configurations, Slater determinants, (anti)symmetrizers.
- A6 ⬜ Kato cusp conditions, three tiers (plan in §6.2).
- A7 ⬜ Sturm oscillation theorem (statements drafted in `blueprint/src/chapters/sturm.tex`, **pending approval**; plan in §6.3).

### B. Many-body theory with finitely many modes (`QM/ManyBody`, `QM/Thermal`)
- B1 ✅ Fock space with Jordan–Wigner signs, CAR, number operator, particle–hole, bridges to the lattice and spin code.
- B2 ✅ One-body operators, 1-RDM conditions, density N-representability, 2-RDM (P, Q, G), mode rotations, Coleman.
- B3 ✅ Slater states and Wick's theorem (`QuasiFree`), mixed quasi-free states (`QuasiFreeMixed`), Hartree–Fock and Lieb's
  variational principle (`HartreeFock`). Conventions: `γ_ij = ⟨c_i† c_j⟩`, `D_ij,kl = ⟨c_i† c_j† c_l c_k⟩`.
- B3+ ✅ No unfilled shells in Hartree–Fock (Bach–Lieb–Loss–Solovej), HF equations (`HartreeFockAufbau`).
- B4 ⬜ Gibbs states, KMS condition, Gibbs variational principle, Peierls–Bogoliubov.
- B5 ⬜ Borland–Dennis constraints for `∧³ℂ⁶`, then Schilling's pinning (proposal, high risk; plan in §6.4).

### C. Green's functions, exact in finite dimensions (`QM/Green`, `QM/Response`)
Statements for C1–C3 are in the blueprint (Part III), approved 2026-11-26.
- C1 🟡 Retarded Green's function, Lehmann representation, spectral function for an eigenstate. Remaining: Gibbs-state version
  (with B4), time-ordered and advanced functions, two-site Hubbard sanity theorem.
- C2 ⬜ Self-energy via Dyson's equation; Herglotz property; HF self-energy as the large-|z| limit.
- C3 ⬜ Galitskii–Migdal; Koopmans; quasiparticle poles.
- C4 ⬜ Matsubara formalism (KMS ⇒ (anti)periodicity, Matsubara sums as residues).
- C5 ⬜ Coupling-constant expansion: convergent for small coupling in finite dimensions; Feynman rules at first and second order.
  Later: Luttinger–Ward / Baym–Kadanoff.
- C6 ⬜ Two-particle Green's functions, Kubo formula, f-sum rule, fluctuation–dissipation.
- C7 ⬜ N-representability of the one-body Green's function (proposal, speculative; plan in §6.5).

### D. DFT (`DFT`)
- D0 ✅ Lattice DFT (HK, generic HK, Kohn–Sham, TDDFT, RDMFT); continuum on a line (H¹₀, unique continuation, HK, Neumann
  walls, measure potentials).
- D1 ⬜ Adiabatic connection and coupling-constant integration of E_xc (lattice); exact conditions (concavity, piecewise
  linearity in N for ensembles).
- D2 ⬜ Sham–Schlüter equation (lattice); Kohn–Sham versus interacting response (Dyson-like equation with f_xc).
- D3 ⬜ RDMFT ↔ quasi-free states (B3).
- D4 ✅ Unified framework for finite-dimensional functional theories (Wang, Liebert, Penz, Schilling, arXiv:2606.06676;
  statements approved 2026-11-26; blueprint chapter `unified`; code in `DFT/Scope`).
  Stage 1 ✅ ranges, functionals, Lieb duality, Hohenberg–Kohn, critical states, ensemble v-representability, abelian ranges;
  instances: lattice DFT (`latticeScope`; the lattice Kohn–Sham existence proofs now go through it), RDMFT (Coleman), spin
  chains. Stage 2 ✅ eigenstate v-representability (no non-redundancy needed), continuity of `F_e`.
  Stage 3 ✅ reduction of scope, purification (`F_p` of the purified scope is `F_e`), Bloch sphere and ball, double qubit
  (exact `F_p`, `F_e < F_p` at an interior point). Not covered: w-ensemble purification (§VII.C), Lie-algebra scopes and
  moment maps (§VIII), generalized Pauli constraints.
- D5 ✅ Exact Kohn–Sham with Neumann walls and `H⁻¹` potentials (Corso's Theorems 2.12, 2.15, Lemma 6.2;
  `DFT/Continuum/Line/Neumann{,KS}`).

### E. Continuum operator theory (contributions to Physlib / Mathlib)
- E1 ⬜ Spectral theorem for unbounded self-adjoint operators, functional calculus (**coordinate with Physlib**).
- E2 ⬜ Stone's theorem for unbounded generators.
- E3 ⬜ Hardy inequality in ℝ³; Kato–Rellich; **self-adjointness of atomic and molecular Hamiltonians** (flagship).
- E4 ⬜ Min–max principle; HVZ (later).
- E5 ⬜ Lieb–Thirring, Lieb–Oxford, Thomas–Fermi (connects to the Lieb–Oxford project).
- E6 ⬜ Integration on spheres in ℝ³ (semiclassical-xc, A4++) → Mathlib.

### F. Research frontier (always keep one running)
- F1 🟡 Semiclassical expansion of exchange (`../semiclassical-xc/`): coefficients 7/81, 8/81, 10/81 reproduced (all known);
  ours: the exact t-representation, shape universality, a rigorous proof. Next: Tier 1 in Lean, paper proof of Tier 2.
- F2 ⬜ Lattice → continuum limits of HK/KS; thermodynamic limits.
- F3 ⬜ Generic pure-state v-representability in lattice DFT (conjecture, high risk; plan in §6.6).

## 4. Next steps (as of 2026-11-27)

1. **A7** Sturm oscillation: approve the statements, then Tier 1 (Jacobi matrices) and Tier 2 (Prüfer angle).
2. **A4++** spherical harmonics: stages A → B → C → D.
3. **C1 remainder**, then **C2 + B4**, then C3.
4. **A6** Kato cusp, Tiers 1–2.
5. Speculative: **F3** numerics first; **B5** after a literature check for an elementary proof of the Borland–Dennis inequality.
6. In parallel: semiclassical-xc Tier 1 (F1); first contact with Physlib about E1/E3.

## 5. How we work

- **Morning (Miguel, ~15 min):** pick 1–3 blueprint nodes; write or approve the *statements* (the one step that cannot be
  delegated: proofs are machine-checked, definitions and statements are not).
- **Day (agents):** prove. Parallel agents work on independent nodes (one folder each, registered in `docs/LOCKS.md`);
  builds on the shared host run with `LEAN_NUM_THREADS=16`.
- **Evening (Miguel, ~15 min):** read the statement diff, not the proof diff. Merge.
- **Weekly:** refactor and deduplicate; upstream candidates (`ForMathlib` → Mathlib, `QM` → PhyslibAlpha).
- **On each Physlib release:** bump the tag, rebuild, run all checks (`AGENTS.md` §6).
- **Monthly:** written summary; decide whether something is paper-worthy.

Quality controls: CI checks (`ARCHITECTURE.md`); a sanity theorem with a known value for every key definition; keep at least
one research-grade target alive (Track F); search Mathlib, Physlib and Zulip before starting a new area; small files with
minimal imports; the blueprint plus `README`, `ARCHITECTURE`, `AGENTS` and this roadmap must suffice for a newcomer.

## 6. Plans for open items

### 6.1 A4++ Spherical harmonics (statements approved 2026-11-26)
Notation `S2 = sphere (0 : Space 3) 1`, `σ = (volume : Measure (Space 3)).toSphere`. Pure maths (Fischer decomposition, sphere
integrals, associated Legendre functions) in `ForMathlib`; physics in `QM/AngularMomentum/SphericalHarmonics/`, one file per stage.
- Stage A: `σ_univ : σ univ = 4π`; `sphRestrict : Poly3 →ₗ[ℂ] C(S2, ℂ)`; `sphericalHarmonics l := (harmonic l).map sphRestrict`;
  `sphRestrict` injective on homogeneous polynomials of degree `l`; `finrank_sphericalHarmonics : = 2l + 1`.
- Stage B (orthogonality): `p ∈ H_l`, `q ∈ H_l'`, `l ≠ l'` ⇒ `∫ conj p · q dσ = 0`; the same for `L_z` eigenvectors with
  `m ≠ m'`. Proof: eigenvectors of Physlib's symmetric `𝓛²` (`𝓛_z`) with different eigenvalues; polar coordinates factor the
  integral over ℝ³ into a positive radial integral times the sphere integral.
- Stage C (explicit `Y_lm`, Condon–Shortley): `assocLegendre l m` by Rodrigues; `Ylm l m : Poly3` with `Ylm_mem_harmonic`,
  `Lz_Ylm`, `Lp_Ylm : Lp Y_lm = √((l-m)(l+m+1)) Y_l,m+1` (and `Lm_Ylm`), `Ylm_spherical` (the θ, φ formula with normalisation
  `√((2l+1)/(4π) · (l-m)!/(l+m)!)`), `Ylm_orthonormal`. Norm via `‖L₋Y‖² = (l+m)(l-m+1)‖Y‖²`, so only `∫|x+iy|^{2l} dσ`
  is computed (Gaussian integral).
- Stage D (completeness): Fischer decomposition `P_n = H_n ⊕ r² P_{n-2}`; `Ylm_hilbertBasis` (Stone–Weierstrass on S²).
- Stage E (later, not approved): addition theorem.

### 6.2 A6 Kato cusp conditions
- Tier 1: `u ∈ C²[0, ∞)` solving `-(1/2μ)(u'' + 2u'/r) + (q/r) u = E u` for `r > 0` has `u'(0) = 2μ q u(0)` (nuclear cusp
  `μ = 1`, `q = -Z`; electron–electron `μ = ½`, `q = 1`).
- Tier 2: `e^{-Zr}` satisfies the nuclear cusp; the spherical-average form reduces to Tier 1.
- Tier 3: Kato's theorem (1957) for N-electron Coulomb eigenfunctions; needs elliptic regularity, sphere integrals (E6,
  A4++) and the Coulomb domain (E3). Research scale, possibly with Physlib.

### 6.3 A7 Sturm oscillation (statements in `sturm.tex`, pending approval)
In 1D the eigenvalues are simple and the n-th eigenfunction has exactly n nodes (in higher dimensions only Courant's bound).
- Tier 1 (`ForMathlib`/`QM/Finite`): a Jacobi matrix with negative off-diagonal entries has simple eigenvalues, and its n-th
  eigenvector has nonzero end entries and exactly n sign changes (Sturm sequences of leading minors). Also gives the nodal
  structure of the lattice chain.
- Tier 2 (`ForMathlib/Analysis/SturmLiouville/`): `-ψ'' + Wψ = Eψ` on `[0, 1]`, Dirichlet, `W` continuous: simplicity,
  positive ground state, interlacing zeros, the n-th eigenfunction has exactly n simple zeros in `(0, 1)`. Route: Prüfer angle,
  increasing in `E`, eigenvalues where `θ(1; E) = (n+1)π`; reuses `SturmLiouville/{Solve,Sturm,Expand,Eigen}`. Needs continuous
  dependence of the shooting solution on `E`.
- Tier 3 (optional): Courant's nodal theorem on `H¹₀(0, 1)`.

### 6.4 B5 Borland–Dennis and pinning (proposal)
For `∧³ℂ⁶` the natural occupations satisfy `λ₁ + λ₆ = λ₂ + λ₅ = λ₃ + λ₄ = 1` and `λ₄ ≤ λ₅ + λ₆`: the first formalized
generalized Pauli constraint and the model case `B_p ≠ B_e` for RDMFT (D4). Equalities from a normal form via mode rotations;
the inequality needs an elementary proof (literature check first: Borland–Dennis 1972, Ruskai 2007; Klyachko's route is out
of reach). Follow-up: pinning and quasipinning (Schilling, Gross, Christandl, PRL 2013): saturation `λ₄ = λ₅ + λ₆` forces `Ψ`
into the span of `|123⟩, |145⟩, |246⟩` (kernel of `n̂₅ + n̂₆ − n̂₄`), with a stability estimate near saturation.

### 6.5 C7 N-representability of the Green's function (proposal)
Which matrix-valued `G(z)` are Green's functions of an `N`-particle state? Necessary: (i) Herglotz with a positive spectral
measure of mass 1; (ii) hole and particle parts positive, the hole part integrating to `γ` with `0 ≤ γ ≤ 1`, `tr γ = N`;
(iii) pole weights are sums of rank-one terms, with pole counts bounded by the `N ± 1` sector dimensions. Questions:
sufficiency for free Hamiltonians; with `H` fixed, the first moment is tied to `h` and the HF self-energy (a D4-style scope).
Trap: do not impose removal poles below addition poles (that is convexity of `E(N)`, false in general; a counterexample
Hamiltonian is a good sanity theorem). After C2, B4 and D4.

### 6.6 F3 Generic pure-state v-representability (conjecture)
For generic `H₀`, every density in the hypersimplex outside a null set is the density of a pure ground state of some `H(v)`;
exceptions come from degeneracies (D4 gives only eigenstate representability). Tools: `DFT/Lattice/Generic`, `GenericHK`.
First step: numerics on small lattices; the conjecture may be false.

## Log
- 2026-11-25: roadmap written; Physlib inspected. Decisions (Miguel): depend on Physlib; QM inside lean_dft as a second
  library. Reorganization: libraries ForMathlib ← QM ← DFT, layered folders, CI checks, ARCHITECTURE, AGENTS, MODULES,
  MAIN_RESULTS.
- 2026-11-26: roadmap moved into the repository. A1–A5, A4+, B1, B2 done; C1 for eigenstates. B3 statements approved and B3
  done. Items A4++ (approved), A6, B3+, B5, C7, D4 (approved), F3 added.
- 2026-11-27: B3+ done; A7 added (statements pending approval). D5 done (Corso). D4 stages 1–2 done in `DFT/Scope`, with
  lattice, RDMFT and spin-chain instances; the lattice Kohn–Sham existence proofs rebuilt on the framework (−480 lines,
  weaker hypotheses; `ks_potential_exists(_interior)` generalised with approval). Roadmap reorganised. D4 stage 3 done
  (reduction, purification, Bloch, double qubit): D4 complete.
