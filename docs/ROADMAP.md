# Roadmap: quantum mechanics → many-body theory → Green's functions → DFT

Living document. Update the status markers and the log at the bottom as things land.
Structure and rules: [`ARCHITECTURE.md`](ARCHITECTURE.md), [`AGENTS.md`](AGENTS.md). Main results: [`MAIN_RESULTS.md`](MAIN_RESULTS.md).

## 0. Strategy

There are two lanes running in parallel.

- **Fast lane: everything that is exact in finite dimensions.** Finite Hilbert spaces, finite lattices, finite sets of modes.
  A large part of theoretical physics is *exactly* true there and provable today with Mathlib:
  - the postulates of QM, spin and angular momentum, Fock space and CAR/CCR, Wick's theorem;
  - Green's functions, the Lehmann representation, Dyson's equation, Matsubara/KMS, linear response and sum rules;
  - Hartree–Fock, RDMFT, lattice DFT and TDDFT.

  This is where lean_dft got its speed. Most of a many-body textbook's content can be covered here within months.
- **Slow lane: continuum operator theory.** The spectral theorem for unbounded operators, Stone's theorem, Kato–Rellich, Hardy's
  inequality, self-adjointness of Coulomb Hamiltonians; after that, Lieb–Thirring, Lieb–Oxford, Thomas–Fermi and semiclassics.
  This is genuine analysis, and upstream review runs at human speed. **Physlib is already building this lane**, so we
  contribute there instead of duplicating it.

The two lanes meet through **limit theorems** (lattice → continuum, finite volume → thermodynamic limit, finite modes → field
theory). Each one is a research-grade result.

## 1. Where things live

| Material | Library / source |
|---|---|
| Pure mathematics we need and Mathlib lacks | `ForMathlib` → Mathlib PRs |
| Basic QM: expectation values, variances, uncertainty, unbounded operators, spectral theory of closed operators, bounded Stone | **Physlib** (`Physlib/QuantumMechanics`), re-exported by `QM/Basic.lean` |
| Density matrices, partial trace, entropy, channels | **Physlib's `QuantumInfo`** (comes with the Physlib dependency) |
| Fermionic Wick algebra and contractions (QFT form) | **Physlib** `Physlib/QFT/PerturbationTheory/WickAlgebra`: check it before writing B3 |
| Generic finite-dimensional QM and many-body theory, Green's functions, response | `QM` → PhyslibAlpha → Physlib |
| Density-functional theory | `DFT` |

### What Mathlib v4.36.0 has (checked 2026-11-25)

| Need | In Mathlib? |
|---|---|
| Finite-dimensional spectral theorem, Rayleigh quotients, matrix exponential, CFC for C*-algebras | yes |
| Unbounded operators (`LinearPMap`), adjoint, `IsSelfAdjoint` | definitions and basics (Physlib builds on them) |
| Schwartz space, Fourier transform, Plancherel, tempered distributions, Sobolev spaces H^{s,p} | yes |
| Spectral theorem for unbounded self-adjoint operators, Stone (unbounded), Kato–Rellich, Hardy | **no** (Physlib: spectral measures started; Stone for bounded generators) |
| Integration on spheres | generalized polar coordinates (`Measure.toSphere`, `measurePreserving_homeomorphUnitSphereProd`); **no** explicit (θ, φ) coordinates |
| Fock space as a Hilbert space, CAR/CCR, quasi-free states | **no** (Physlib: only the QFT Wick algebra) |

## 2. Tracks

Status: ✅ done · 🟡 partly done · ⬜ not started. Details of finished items are in the blueprint and `MODULES.md`;
this section keeps only pointers.

### Track A: foundations of QM, finite-dimensional (`QM/Finite`, `QM/Spin`, `QM/AngularMomentum`, `QM/ManyBody`)
- A1 ✅ States, observables, Born rule, uncertainty (Physlib, `QM/Basic.lean`); density matrices (QuantumInfo); bridge
  `QM/Finite/States`, qubit sanity theorem `QM/Finite/Qubit`.
- A2 ✅ Time evolution, Heisenberg picture, Ehrenfest (`QM/Finite/Evolution`); propagator (`QM/Finite/Propagator`,
  `ForMathlib/Analysis/ODE/Linear`); adiabatic theorem (`QM/Finite/Adiabatic`, `QM/Finite/Riesz`).
- A3 ✅ Schmidt decomposition (`QM/Finite/Schmidt`); natural orbitals (`QM/ManyBody/NaturalOrbitals`).
- A4 ✅ N spin-½ particles (`QM/Spin/SpinAlg`, `QM/Spin/ClebschGordan`); su(2) ladder theorem (`QM/AngularMomentum/Ladder`).
- A4+ ✅ Angular momentum (`QM/AngularMomentum`): spin-j representation (`SpinRep`), coupling `J = L + S` and `L₁ + L₂`
  (`Coupling`, `CGSeries`), Clebsch–Gordan coefficients and Racah's formula (`CGCoeff`), 3j/6j/9j and Biedenharn–Elliott
  (`ThreeJ`, `Recoupling`, `SixJ`, `NineJ`, `BiedenharnElliott`), orbital `L = -i r × ∇` on harmonic polynomials (`Orbital`,
  `ForMathlib/Algebra/MvPolynomial/Harmonic`), bridge to Physlib's `𝐋` on Schwartz functions and on L²(ℝ³) (`Schwartz`).
- A4++ ⬜ Spherical harmonics (requested by Miguel 2026-11-26; **statements approved 2026-11-26**). Notation:
  `S2 = sphere (0 : Space 3) 1`, `σ = (volume : Measure (Space 3)).toSphere`. Layout: pure maths (Fischer decomposition,
  sphere integrals, associated Legendre functions) in `ForMathlib`; physics in `QM/AngularMomentum/SphericalHarmonics/`,
  one file per stage.
  - Stage A, spherical harmonics on S²: `σ_univ : σ univ = 4π`; `sphRestrict : Poly3 →ₗ[ℂ] C(S2, ℂ)`;
    `sphericalHarmonics l := (harmonic l).map sphRestrict`; `sphRestrict` injective on homogeneous polynomials of degree `l`;
    `finrank_sphericalHarmonics : = 2l + 1`.
  - Stage B, orthogonality: `p ∈ H_l`, `q ∈ H_l'`, `l ≠ l'` ⇒ `∫ conj p · q dσ = 0`; the same for `L_z` eigenvectors with
    `m ≠ m'`. Proof plan: `pG`, `qG` are eigenvectors of Physlib's symmetric `𝓛²` (`𝓛_z`) with different eigenvalues, and
    polar coordinates factor `∫_{ℝ³}` into a positive radial integral times `∫_{S²}`.
  - Stage C, explicit `Y_lm` (Condon–Shortley): `assocLegendre l m` by Rodrigues,
    `(-1)^m (1-t²)^{m/2} d^{l+m}/dt^{l+m} (t²-1)^l / (2^l l!)`; `Ylm l m : Poly3` with `Ylm_mem_harmonic` (`|m| ≤ l`),
    `Lz_Ylm : Lz Y = m Y`, `Lp_Ylm : Lp Y_lm = √((l-m)(l+m+1)) Y_l,m+1` (and `Lm_Ylm`),
    `Ylm_spherical : Y_lm(sin θ cos φ, sin θ sin φ, cos θ) = √((2l+1)/(4π) · (l-m)!/(l+m)!) P_l^m(cos θ) e^{imφ}`,
    `Ylm_orthonormal : ∫ conj Y_lm · Y_l'm' dσ = δ_ll' δ_mm'`. Proof plan for the norm: `‖L₋Y‖² = (l+m)(l-m+1)‖Y‖²` by
    symmetry, so only `∫|x+iy|^{2l} dσ` is computed (Gaussian integral).
  - Stage D, completeness: Fischer decomposition `P_n = H_n ⊕ r² P_{n-2}` (homogeneous polynomials); `Ylm_hilbertBasis`:
    the `Y_lm`, `|m| ≤ l`, form a Hilbert basis of `L²(S², σ)` (Stone–Weierstrass on S², continuous functions dense in L²).
  - Stage E (later, not yet approved): addition theorem `Σ_m Y_lm(u) conj Y_lm(v) = (2l+1)/(4π) P_l(u·v)`.
- A5 ✅ Ground states (`QM/Finite/GroundState`), configurations and Slater determinants (`QM/ManyBody`), symmetrizer and
  antisymmetrizer (`QM/ManyBody/Symmetrizer`).
- A6 ⬜ Kato cusp conditions (requested by Miguel 2026-11-26), in three tiers.
  Tier 1: if `u ∈ C²[0, ∞)` solves `-(1/2μ)(u'' + 2u'/r) + (q/r) u = E u` for `r > 0`, then `u'(0) = 2μ q u(0)` (nuclear cusp
  `μ = 1`, `q = -Z`; electron–electron cusp `μ = ½`, `q = 1`).
  Tier 2: `e^{-Zr}` satisfies the nuclear cusp; the spherical-average form reduces to Tier 1 for spherical states.
  Tier 3: Kato's theorem (1957) for N-electron Coulomb eigenfunctions. Needs elliptic regularity, integration on spheres
  (E6, A4++) and the Coulomb domain (E3): research scale, possibly with Physlib.

### Track B: many-body theory with finitely many modes (`QM/ManyBody`, `QM/Thermal`)
- B1 ✅ Fock space over `Fin M` modes with Jordan–Wigner signs and the CAR (`QM/ManyBody/Fock`), number operator (`Number`),
  particle–hole transformation (`ParticleHole`), bridge to the lattice code (`DFT/Lattice/Fermions/FockBridge`), spin bridge
  (`QM/ManyBody/Spin`, `DFT/Lattice/Spin/FockBridge`).
- B2 ✅ One-body operators (`OneBody`), 1-RDM conditions (`RDM`), density N-representability (`DFT/Lattice/RDMFT/DensityRep`),
  2-RDM with P, Q, G (`RDM2`), mode rotations (`ModeRotation`), Coleman's theorem (`DFT/Lattice/RDMFT/Coleman`).
- B3 ⬜ Quasi-free states, **Wick's theorem** for finitely many modes, Hartree–Fock as the minimum over quasi-free states (Lieb's
  variational principle). Check Physlib's Wick algebra (`Physlib/QFT/PerturbationTheory/WickAlgebra`) first.
- B4 ⬜ Gibbs states, the KMS condition, the Gibbs variational principle, Peierls–Bogoliubov.

### Track C: Green's functions, exact in finite dimensions (`QM/Green`, `QM/Response`)
Statements for C1–C3 are in the blueprint (Part III), approved 2026-11-26.
- C1 🟡 Retarded Green's function, Lehmann representation, spectral function for an eigenstate (`QM/Green/Lehmann`,
  `QM/Green/Spectral`, `ForMathlib/Analysis/PoissonKernel`). Remaining: Gibbs-state version (with B4), time-ordered and
  advanced functions, the two-site Hubbard sanity theorem.
- C2 ⬜ Self-energy defined by **Dyson's equation**; Herglotz property; the HF self-energy as the large-|z| limit.
- C3 ⬜ Galitskii–Migdal formula; Koopmans; quasiparticle poles.
- C4 ⬜ Matsubara formalism: KMS ⇒ (anti)periodicity, Matsubara sums as residues.
- C5 ⬜ Coupling-constant expansion: analytic in finite dimensions ⇒ the diagram series converges for small coupling; Feynman
  rules at first and second order. Later, as research: Luttinger–Ward / Baym–Kadanoff conserving approximations.
- C6 ⬜ Two-particle Green's functions, linear response (**Kubo formula**), f-sum rule, fluctuation–dissipation theorem.

### Track D: DFT (`DFT`), ongoing
- D0 ✅ Lattice DFT (HK, generic HK, Kohn–Sham, TDDFT, RDMFT); continuum on a line (H¹₀, unique continuation, HK, Neumann walls,
  measure potentials). See MODULES.md.
- D1 ⬜ Adiabatic connection and coupling-constant integration of E_xc (lattice); exact conditions (concavity, piecewise
  linearity in N for ensembles).
- D2 ⬜ Link to Track C: the Sham–Schlüter equation (lattice), Kohn–Sham versus interacting response (Dyson-like equation with f_xc).
- D3 ⬜ RDMFT ↔ quasi-free states (B3).

### Track E: continuum operator theory (contributions to Physlib / Mathlib)
- E1 ⬜ Spectral theorem for unbounded self-adjoint operators (multiplication-operator form), functional calculus: **coordinate
  with Physlib** (their spectral measures).
- E2 ⬜ Stone's theorem for unbounded generators (Physlib has the bounded case).
- E3 ⬜ Hardy inequality in ℝ³; Kato–Rellich; **self-adjointness of atomic and molecular Hamiltonians** (Kato 1951). This is a flagship,
  missing in Physlib.
- E4 ⬜ Min–max principle; HVZ (later).
- E5 ⬜ Lieb–Thirring, Lieb–Oxford, Thomas–Fermi (Lieb–Simon). This connects to the Lieb–Oxford project.
- E6 ⬜ Integration on spheres in ℝ³ (needed by the semiclassical-xc sphere-overlap lemma) → Mathlib. Mathlib's `toSphere` and
  polar decomposition cover the general part; A4++ will add the S² specifics (total area, Gaussian moments).

### Track F: research frontier (always keep one running)
- F1 🟡 Semiclassical expansion of exchange (`../semiclassical-xc/`): the coefficients 7/81 (screening), 8/81 (temperature) and
  10/81 (bare Coulomb) are reproduced, and all three values and both crossovers turn out to be known in the literature. What is ours:
  the exact t-representation, shape universality, and a rigorous proof (not done yet).
  Next: Tier 1 in Lean (`ForMathlib` + `DFT`), the paper proof of Tier 2.
- F2 ⬜ Lattice → continuum limits of HK/KS; thermodynamic limits.

## 3. Operating procedure (the daily routine)

- **Morning (Miguel, ~15 min):** pick 1–3 blueprint nodes; write or approve the *statements*. This is the one step that cannot be
  delegated: proofs are machine-checked, **definitions and statements are not**.
- **Day (agents):** prove. Parallel agents work on independent nodes (one folder each, registered in `docs/LOCKS.md`).
  On the shared host, builds run with `LEAN_NUM_THREADS=16` and a memory limit.
- **Evening (Miguel, ~15 min):** read the statement diff, not the proof diff. Merge.
- **Weekly:** refactor and deduplicate; upstream candidates (`ForMathlib` → Mathlib, `QM` → PhyslibAlpha); reduce the heartbeat backlog.
- **On each Physlib release:** bump the Physlib tag (this brings Lean and Mathlib), rebuild, run all checks (`AGENTS.md` §6).
- **Monthly:** a written summary; decide whether something is paper-worthy (formalized new results go to arXiv with the code).

## 4. Quality and risk controls

- **Checks in CI** (`ARCHITECTURE.md`): axiom audit with self-test, hygiene (forbidden constructs, duplicate names), layering,
  module index, main results, blueprint references.
- **Definition audits:** every key definition (Green's function, self-energy, KMS state, …) gets a sanity theorem reproducing a known
  value (free particle, two-site Hubbard spectral function, harmonic oscillator).
- **Avoid vanity formalization:** textbook coverage is infrastructure; keep at least one research-grade target (Track F) alive.
- **Duplication:** search Mathlib, Physlib (incl. QuantumInfo) and Zulip before starting any new area.
- **Build time and memory:** keep files small and imports minimal (imports must reflect real use); cap parallelism on the shared host.
- **Continuity:** the blueprint plus `README`, `ARCHITECTURE`, `AGENTS` and this roadmap must be enough for a new person or agent to continue.

## 5. Next steps (as of 2026-11-26)

Done: A1–A5 (with A4+), B1, B2, most of C1.
1. **A4++ spherical harmonics** (approved): stages A → B → C → D in order.
2. **C1 remainder:** time-ordered and advanced functions, two-site Hubbard sanity theorem.
3. **C2 + B4** (self-energy, Gibbs states and KMS), then C3.
4. **B3** Wick's theorem and quasi-free states (check Physlib's Wick algebra first).
5. **A6** Kato cusp, Tiers 1–2.
6. In parallel: semiclassical-xc Tier 1 (F1); first contact with Physlib about E1/E3.

## Log
- 2026-11-25: roadmap written; Physlib inspected (~437k lines). Decisions (Miguel): depend on Physlib, our work is meant to
  end up in it; QM lives inside lean_dft as a second library. Reorganization (tag `pre-reorg-2026-11-25` → release
  `v4.36.0`): libraries ForMathlib ← QM ← DFT, layered folders, CI checks, ARCHITECTURE, AGENTS, MODULES, MAIN_RESULTS.
- 2026-11-26: roadmap moved into the repository; heartbeat backlog closed; generated certificates reproducible in CI.
- 2026-11-26: B1 and B2 complete (Fock space, CAR, number operator, lattice bridge, particle–hole; RDMs, P/Q/G, mode
  rotations, Coleman); spin bridge. `DFT.generic_hk_hubbard` removed from the main results; main-results check strict.
- 2026-11-26: C1 Lehmann representation for an eigenstate.
- 2026-11-26: A1–A5 complete, including the adiabatic theorem (A2).
- 2026-11-26: A4+ complete: Clebsch–Gordan, Racah, 3j/6j/9j, Biedenharn–Elliott, orbital `L` on harmonic polynomials,
  bridge to Physlib's `𝐋` (Schwartz space and L²(ℝ³)). General su(2) theory moved from `QM/Spin` to `QM/AngularMomentum`.
- 2026-11-26: items A6 (Kato cusp) and A4++ (spherical harmonics, statements approved) added; roadmap cleaned up.
