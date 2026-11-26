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
- A1 ✅ States, observables, Born rule, expectation values, uncertainty: **from Physlib** (`QM/Basic.lean`). Density matrices and
  partial trace: **from QuantumInfo**. Bridge (`QM/Finite/States`) and qubit sanity theorem (`QM/Finite/Qubit`) done 2026-11-26.
- A2 🟡 Time evolution, the Heisenberg picture and Ehrenfest done 2026-11-26 (`QM/Finite/Evolution`, on Physlib's
  `UnitaryOneParameterGroup`, for bounded self-adjoint H on any complex Hilbert space). Remaining: the adiabatic theorem
  (finite-dimensional, gapped; Kato's argument), deferred by Miguel as a separate project.
- A3 ✅ Schmidt decomposition and product states (`QM/Finite/Schmidt`, on QuantumInfo's `Ket` and partial traces) and natural
  orbitals (`QM/ManyBody/NaturalOrbitals`) done 2026-11-26.
- A4 ✅ Spin algebra of N spin-½ particles: `QM/Spin/SpinAlg`. su(2) ladder theorem (`QM/Spin/Ladder`) and Clebsch–Gordan for
  two and three spins (`QM/Spin/ClebschGordan`) done 2026-11-26.
- A4+ ⬜ Coupling of angular momenta (requested by Miguel 2026-11-26). (i) Orbital angular momentum and spin: `J = L + S` on
  functions `SpinC n → V` satisfies the su(2) relations when `L` does on `V`; `l ⊗ ½ = (l + ½) ⊕ (l − ½)` with explicit
  highest weights and the spin–orbit values `L·S = l/2, −(l+1)/2`. (ii) The sum of two angular momenta `L₁ + L₂`:
  `j₁ ⊗ j₂ = |j₁ − j₂| ⊕ … ⊕ (j₁ + j₂)`, with highest weights and dimension count. (iii) Clebsch–Gordan coefficients: the
  recursion from `J₋`, orthogonality, Racah's closed formula, Wigner 3j symbols and their symmetries; then the recoupling
  of three and four angular momenta (6j and 9j symbols, Biedenharn–Elliott). Optional: a concrete orbital `L = -i r × ∇`
  on homogeneous harmonic polynomials of degree `l` (spin-`l` irreducible representation).
- A5 ✅ Ground states in finite dimensions (`QM/Finite/GroundState`), configurations and Slater determinants (`QM/ManyBody`).
  Symmetrizer and antisymmetrizer as orthogonal projections (`QM/ManyBody/Symmetrizer`) done 2026-11-26.

### Track B: many-body theory with finitely many modes (`QM/ManyBody`, `QM/Thermal`)
- B1 ✅ Fock space over `Fin M` modes, CAR, number operator, particle–hole transformation. **Approved 2026-11-26; Fock space
  and CAR proved** (`QM/ManyBody/Fock`: matrix form and bounded operators on the Hilbert space); **number operator proved**
  (`QM/ManyBody/Number`); **bridge to the lattice code proved** (`DFT/Lattice/Fermions/FockBridge`); **particle–hole transformation proved**
  (`QM/ManyBody/ParticleHole`). B1 complete 2026-11-26.
  Design (blueprint Part III): a concrete Fock space, functions `Finset (Fin M) → ℂ` (dimension 2^M), with Jordan–Wigner
  signs; first theorems: CAR, the number operator, and the **bridge** `Σ h_ij c_i† c_j = Γ h` on the N-particle sector, which
  connects all of the existing lattice DFT. The lattice code (`DFT/Lattice/Fermions/SecondQuantization`) works only at fixed N with
  real matrices, so it cannot host `c_i` itself. Physlib's Wick algebra is abstract and QFT-oriented (no finite-mode Hilbert
  space); use it later for Wick's theorem (B3) via its universality property, if our operators satisfy its hypotheses.
- B2 ✅ One- and two-body RDMs; Coleman's N-representability for the 1-RDM. One-body operators done (`QM/ManyBody/OneBody`).
  **Statements approved 2026-11-26** (blueprint Part III). **Proved:** the 1-RDM necessary conditions (`QM/ManyBody/RDM`) and
  the N-representability of the density (`DFT/Lattice/RDMFT/DensityRep`); the 2-RDM with antisymmetry, contraction, trace and
  the P, Q, G conditions (`QM/ManyBody/RDM2`); mode rotations U(u) (`QM/ManyBody/ModeRotation`) and Coleman's theorem
  (`DFT/Lattice/RDMFT/Coleman`). B2 complete 2026-11-26. Statements: γ_ij = ⟨c_i† c_j⟩ (Miguel's choice, as in the
  lattice code), necessary conditions 0 ≤ γ ≤ 1 and tr γ = N, N-representability of the density (pure and ensemble),
  the 2-RDM with antisymmetry, contraction and trace, the P, Q, G conditions, mode rotations U(u), Coleman's theorem
  (kept in B2). Order: 1-RDM conditions, density, 2-RDM, mode rotations, Coleman. `DFT/Lattice/RDMFT` has pieces to reuse.
- B3 ⬜ Quasi-free states, **Wick's theorem** for finitely many modes, Hartree–Fock as the minimum over quasi-free states (Lieb's
  variational principle).
- B4 ⬜ Gibbs states, the KMS condition, the Gibbs variational principle, Peierls–Bogoliubov.

### Track C: Green's functions, exact in finite dimensions (`QM/Green`, `QM/Response`)
Statements for C1–C3 are in the blueprint (Part III), **approved 2026-11-26**.
- C1 🟡 Time-ordered, retarded and advanced one-body Green's functions; **Lehmann representation**; spectral function, positivity,
  sum rules. **Proved 2026-11-26** for an eigenstate (`QM/Green/Lehmann`, `QM/Green/Spectral`): G^R from e^{-iHt}, the Lehmann
  representation in time and frequency, positive weights summing to 1, A = -π⁻¹ Im G(ω+i0) = Σ W_k δ(ω-ω_k). Remaining: the
  Gibbs-state version (with B4), time-ordered and advanced functions, the two-site Hubbard sanity theorem.
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

## 5. Next steps (from 2026-11-26, after B1)

1. **Housekeeping done:** `MAIN_RESULTS.md` has every result in the blueprint, and the check is strict in CI.
2. **Approved 2026-11-26:** the particle–hole statement and the C1–C3 statements (Lehmann, self-energy, Herglotz,
   Galitskii–Migdal).
3. **B2 follow-up done:** the spin bridge (`QM/ManyBody/Spin`, `DFT/Lattice/Spin/FockBridge`).
4. **C1 (mostly done):** remaining are the time-ordered and advanced functions and the two-site Hubbard sanity theorem.
5. **A2:** time evolution in finite dimensions (A1 done). `QM/Green/Lehmann` already has `e^{-iHt}` on the Fock space.
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
- 2026-11-26: bridge proved (`QM/ManyBody/OneBody`, `DFT/Lattice/Fermions/FockBridge`). On N-particle configurations the
  matrix of Σ h_ij c_i† c_j is the lattice Γ h, the operator conserves the particle number, and H0F and hamN (H0F …)
  are restrictions of second-quantized Hamiltonians. Creation strings have the lattice determinants as coefficients.
- 2026-11-26: the lattice RDM is the Fock-space one (`DFT/Lattice/RDMFT/FockRDM`): γ_ij = ⟨Ψ, c_i† c_j Ψ⟩.
- 2026-11-26: particle–hole transformation proved (`QM/ManyBody/ParticleHole`): P|s⟩ = |sᶜ⟩ is a self-adjoint unitary
  involution, P c_i† P = (-1)^i c_i, P n̂_i P = 1 - n̂_i, P N̂ P = M - N̂, and one-body operators go to tr h minus the
  staggered transpose. B1 complete.
- 2026-11-26: B2 statements written (pending approval): 1-RDM and density N-representability, 2-RDM with P, Q, G, mode
  rotations, Coleman.
- 2026-11-26: B2 statements approved. 1-RDM conditions γ = γ†, 0 ≤ γ ≤ 1, tr γ = N (states and ensembles) and
  N-representability of the density (pure and ensemble, nonnegative coefficients) proved. Next: 2-RDM, then mode rotations and Coleman.
- 2026-11-26: 2-RDM proved (`QM/ManyBody/RDM2`): antisymmetry, Hermiticity, Σ_k D_ik,jk = (N-1)γ_ij, trace N(N-1), and the
  P, Q, G conditions with Q and G as explicit affine functions of D and γ, for states and ensembles.
- 2026-11-26: mode rotations proved (`QM/ManyBody/ModeRotation`). Orbital operators c†(φ) obey {c(χ), c†(φ)} = ⟨χ, φ⟩,
  an orbital annihilator acts on a creation string by Laplace expansion, and two strings overlap by the Gram determinant.
  From this U(u) is unitary, fixes the vacuum, commutes with N̂, satisfies U c_i† U† = Σ_j u_ji c_j† and U(uv) = U(u)U(v),
  and γ(UΨ) = ū γ uᵀ. Cauchy–Binet was not needed. The sorted-mode lemmas moved from `FockBridge` to `QM/ManyBody/Fock`.
- 2026-11-26: Coleman's theorem proved (`DFT/Lattice/RDMFT/Coleman`). γ is the 1-RDM of an N-particle ensemble iff it is
  Hermitian, 0 ≤ γ ≤ 1 and tr γ = N. B2 complete.
- 2026-11-26: particle–hole and C1–C3 statements approved. Spin-bridge statement written and approved.
- 2026-11-26: spin bridge proved (`QM/ManyBody/Spin`, `DFT/Lattice/Spin/FockBridge`). With the up modes first, the spin
  one-body operator acts on product functions f ⊗ g factor by factor (the down parities cancel in each hopping term), so on
  the (N↑, N↓) sector it is `kronSum (Γ h↑) (Γ h↓)`. The Hubbard operator restricts to `hubbard U`, and `H0S G t (hubbard U)`
  and `hamN (H0S …) occS v` are restrictions of Fock Hamiltonians.
- 2026-11-26: `DFT.generic_hk_hubbard` removed from the main results. The main-results blueprint check is now strict.
- 2026-11-26: C1 Lehmann representation proved (`QM/Green/Lehmann`, `QM/Green/Spectral`, `ForMathlib/Analysis/PoissonKernel`).
  For an eigenstate Ψ of a Hermitian H, G^R_ij(t) = -iθ(t)⟨Ψ, {c_i(t), c_j†} Ψ⟩ with e^{-iHt} the operator exponential. Its
  Laplace transform is Σ_k W_k/(z - ω_k) for Im z > 0, the weights are rank-one positive semidefinite and sum to 1, and
  -π⁻¹ Im G(ω+iη) → Σ_k W_k δ(ω - ω_k) against bounded continuous functions (Poisson kernel approximate identity).
- 2026-11-26: A1 complete. `QM/Finite/States` connects Physlib and QuantumInfo: for a ket, QuantumInfo's `exp_val` of the pure
  state is Physlib's `expectedValue`, Physlib's variance is ⟨T²⟩ - ⟨T⟩², the Born rule over an eigenbasis, and tr ρT as a
  mixture over the spectral decomposition. `QM/Finite/Qubit`: Bloch decomposition, |r|² = 2 tr ρ² - 1 ≤ 1 with equality
  iff pure, and Δσx Δσy ≥ |⟨σz⟩| from Physlib's Robertson inequality.
- 2026-11-26: A4 and A5 complete. `QM/Spin/Ladder`: the su(2) ladder theorem (highest weight, 2m ∈ ℕ, the (2m+1)-dimensional
  invariant subspace, every ladder stops in finite dimension), with `QM/Spin/SpinAlg` as an instance. `QM/Spin/ClebschGordan`:
  S² = 1 + P₀₁ and S² = ¾ + ΣP_ij, triplet and singlet basis, (S² − 15/4)(S² − 3/4) = 0, quartet and two doublets.
  `QM/ManyBody/Symmetrizer`: 𝒮 and 𝒜 are idempotent, absorb permutations, have the (anti)symmetric functions as ranges,
  annihilate each other for N ≥ 2, are self-adjoint, and 𝒜 of a product is the Slater determinant over N!.
- 2026-11-26: roadmap item A4+ added (L + S, L₁ + L₂, Clebsch–Gordan coefficients, 6j/9j recoupling).
- 2026-11-26: A2 (without the adiabatic theorem) and A3 complete. `QM/Finite/Evolution`: unitarity, U(t+s) = U(t)U(s), the
  Schrödinger equation with uniqueness, the Heisenberg equation A' = i[H, A(t)], Ehrenfest and conservation laws.
  `QM/Finite/Schmidt`: ψ = Σ √λ_k u_k ⊗ v_k, tr ρ₁ⁿ = tr ρ₂ⁿ, product ⇔ ρ₁ pure ⇔ Schmidt rank one.
  `QM/ManyBody/NaturalOrbitals`: a mode rotation diagonalizes γ, with occupations in [0, 1] summing to N.
