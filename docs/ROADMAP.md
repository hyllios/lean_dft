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
| 3D spherical coordinates for non-radial integrands | **no** (only 2D polar and radial integrals) |
| Fock space as a Hilbert space, CAR/CCR, quasi-free states | **no** (Physlib: only the QFT Wick algebra) |

## 2. Tracks

Status: ✅ done · 🟡 partly done · ⬜ not started. Effort estimates assume the current working mode (Miguel daily plus agents).

### Track A: foundations of QM, finite-dimensional (`QM/Finite`, `QM/Spin`, `QM/ManyBody`)
- A1 🟡 States, observables, Born rule, expectation values, uncertainty: **from Physlib** (`QM/Basic.lean`). Density matrices and
  partial trace: **from QuantumInfo**; to do: a bridge lemma connecting the two and a sanity theorem (a qubit).
- A2 ⬜ Time evolution as the matrix exponential, the Heisenberg picture, Ehrenfest-type identities, the adiabatic theorem (finite-dimensional,
  gapped). Check Physlib's `UnitaryOneParameterGroup` (bounded generators) first.
- A3 ⬜ Tensor products, Schmidt decomposition (→ natural orbitals, links to N-representability). Check QuantumInfo first.
- A4 🟡 Spin algebra of N spin-½ particles: `QM/Spin/SpinAlg`. To do: su(2) irreps, Clebsch–Gordan in small cases.
- A5 🟡 Ground states in finite dimensions (`QM/Finite/GroundState`), configurations and Slater determinants (`QM/ManyBody`).
  To do: symmetrizer and antisymmetrizer as projections.

### Track B: many-body theory with finitely many modes (`QM/ManyBody`, `QM/Thermal`)
- B1 🟡 Fock space over `Fin M` modes, CAR, number operator, particle–hole transformation. **Approved 2026-11-26; Fock space
  and CAR proved** (`QM/ManyBody/Fock`: matrix form and bounded operators on the Hilbert space); **number operator proved**
  (`QM/ManyBody/Number`). Next: the bridge to the lattice code.
  Design (blueprint Part III): a concrete Fock space, functions `Finset (Fin M) → ℂ` (dimension 2^M), with Jordan–Wigner
  signs; first theorems: CAR, the number operator, and the **bridge** `Σ h_ij c_i† c_j = Γ h` on the N-particle sector, which
  connects all of the existing lattice DFT. The lattice code (`DFT/Lattice/Fermions/SecondQuantization`) works only at fixed N with
  real matrices, so it cannot host `c_i` itself. Physlib's Wick algebra is abstract and QFT-oriented (no finite-mode Hilbert
  space); use it later for Wick's theorem (B3) via its universality property, if our operators satisfy its hypotheses.
- B2 ⬜ One-body operators in second quantization; one- and two-body RDMs; Coleman's N-representability for the 1-RDM.
  `DFT/Lattice/RDMFT` has pieces to reuse.
- B3 ⬜ Quasi-free states, **Wick's theorem** for finitely many modes, Hartree–Fock as the minimum over quasi-free states (Lieb's
  variational principle).
- B4 ⬜ Gibbs states, the KMS condition, the Gibbs variational principle, Peierls–Bogoliubov.

### Track C: Green's functions, exact in finite dimensions (`QM/Green`, `QM/Response`)
Statements for C1–C3 are drafted in the blueprint (Part III), **pending approval**.
- C1 ⬜ Time-ordered, retarded and advanced one-body Green's functions; **Lehmann representation**; spectral function, positivity,
  sum rules.
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
- E6 ⬜ Integration on spheres in ℝ³ (needed by the semiclassical-xc sphere-overlap lemma) → Mathlib.

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

## 5. Next steps (from 2026-11-26)

1. **Housekeeping from the reorganization:** curate `MAIN_RESULTS.md` (Miguel) and then make its blueprint check strict; replace
   the 9 stale theorem names in the README. (Heartbeat backlog: closed on 2026-11-26, all 49 overrides have a reason.)
2. **Approve the Part III statements** in the blueprint (Fock space, CAR, Gibbs/KMS, Lehmann, self-energy, Herglotz, Galitskii–Migdal),
   or amend them.
3. **A1/A2:** the bridge between Physlib's operators and QuantumInfo's density matrices; time evolution in finite dimensions.
4. **B1 decision and implementation:** the representation of Fock space (generic part of the lattice second quantization vs. Physlib's
   Wick algebra), then CAR.
5. **C1:** the Lehmann representation, with the two-site Hubbard model as the sanity theorem.
6. In parallel: C2 + B4; semiclassical-xc Tier 1 (F1); first contact with Physlib about E1/E3.

## Log
- 2026-11-25: roadmap written (in the parent folder, as `FORMALIZATION_ROADMAP.md`).
- 2026-11-25: Physlib inspected: ~437k lines, it covers basic QM and is building the continuum operator theory. Decision (Miguel):
  depend on it; our work is meant to end up in it eventually.
- 2026-11-25: decision (Miguel): QM lives inside lean_dft as a second library, not as a separate repository.
- 2026-11-25: reorganization of lean_dft (tag `pre-reorg-2026-11-25` → release `v4.36.0`): Lean/Mathlib v4.36.0 via Physlib;
  libraries ForMathlib ← QM ← DFT; layered folders with imports from true dependencies; CI checks; ARCHITECTURE, AGENTS,
  MODULES, MAIN_RESULTS.
- 2026-11-26: roadmap moved into the repository (`docs/ROADMAP.md`) and updated to the state after the reorganization.
- 2026-11-26: heartbeat backlog closed (all overrides justified; check enforcing); generated certificates reproducible (CI).
- 2026-11-26: B1 proposal written (concrete Fock space + bridge to the lattice code), awaiting approval.
- 2026-11-26: Part III statements approved. Fock space, c_i†/c_i (Jordan–Wigner), c_i = (c_i†)† and the CAR proved
  (`QM/ManyBody/Fock`), as matrix identities and as identities of bounded operators on the Fock Hilbert space.
- 2026-11-26: number operator proved (`QM/ManyBody/Number`): n̂_i|s⟩ = [i∈s]|s⟩ (= occF on N-particle configurations),
  N̂|s⟩ = |s||s⟩, both self-adjoint, n̂_i² = n̂_i; N̂ self-adjoint on the Fock Hilbert space.
