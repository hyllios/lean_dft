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
- A4 ✅ N spin-½ particles (`QM.Spin.Algebra`, `QM/Spin/ClebschGordan`); su(2) ladder theorem (`QM/AngularMomentum/Ladder`).
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

- A7 ⬜ Sturm oscillation theorem (requested by Miguel 2026-11-27; Tier 1 and 2 statements drafted in
  `blueprint/src/chapters/sturm.tex`, pending approval): in 1D the eigenvalues
  are simple and the n-th eigenfunction (counting from 0) has exactly n nodes. Specific to 1D: in higher dimensions
  only Courant's upper bound holds. Three tiers.
  Tier 1 (finite-dimensional warm-up, `ForMathlib`/`QM/Finite`): a real symmetric tridiagonal (Jacobi) matrix with
  negative off-diagonal entries has simple eigenvalues, and its n-th eigenvector has no zero entry at either end and
  exactly n sign changes (Gantmacher–Krein). Proof via Sturm sequences of the leading principal minors (interlacing).
  Also gives the nodal structure of the lattice chain in `DFT/Lattice`.
  Tier 2 (continuum, `ForMathlib/Analysis/SturmLiouville/`): `-ψ'' + Wψ = Eψ` on `[0, 1]`, Dirichlet, `W` continuous.
  Simplicity (Wronskian); the ground state has no interior zero; Sturm comparison between consecutive eigenfunctions
  (zeros interlace); the n-th eigenfunction of the Green-operator expansion (`SturmLiouville/Expand`, `SturmLiouville/Eigen`) has
  exactly n zeros in `(0, 1)`, all simple. Route: Prüfer angle `θ(t; E)`, `y = r sin θ`, `y' = r cos θ`, strictly
  increasing in `E`, with the eigenvalues exactly where `θ(1; E) = (n+1)π`. Reuses the shooting solution (`SturmLiouville/Solve`)
  and the Sturm-type facts already proved in `SturmLiouville/Sturm` (`exists_zero_of_le` is a Sturm comparison).
  Needs: continuous dependence of the shooting solution on `E` (check `SturmLiouville/Solve`, `SturmLiouville/Extend`).
  Tier 3 (optional): Courant's nodal theorem (at most n+1 nodal domains, variational) on `H¹₀(0, 1)`, as the part
  that survives in higher dimensions.

### Track B: many-body theory with finitely many modes (`QM/ManyBody`, `QM/Thermal`)
- B1 ✅ Fock space over `Fin M` modes with Jordan–Wigner signs and the CAR (`QM/ManyBody/Fock`), number operator (`Number`),
  particle–hole transformation (`ParticleHole`), bridge to the lattice code (`DFT/Lattice/Fermions/FockBridge`), spin bridge
  (`QM/ManyBody/Spin`, `DFT/Lattice/Spin/FockBridge`).
- B2 ✅ One-body operators (`OneBody`), 1-RDM conditions (`RDM`), density N-representability (`DFT/Lattice/RDMFT/DensityRep`),
  2-RDM with P, Q, G (`RDM2`), mode rotations (`ModeRotation`), Coleman's theorem (`DFT/Lattice/RDMFT/Coleman`).
- B3 ✅ Quasi-free states, Wick's theorem, Hartree–Fock and Lieb's variational principle (**statements approved
  2026-11-26**). Physlib's Wick algebra (abstract, time-ordered QFT operators) cannot express state expectation values, so
  Wick's theorem is proved directly from `ModeRotation` (Laplace expansion, Gram determinants). Conventions as in `RDM`:
  `γ_ij = ⟨c_i† c_j⟩`, `D_ij,kl = ⟨c_i† c_j† c_l c_k⟩`.
  - Step 1 ✅ (2026-11-26), `QM/ManyBody/QuasiFree` (Slater states): `slaterState u s := U(u)|s⟩`; `slaterState_isNState`;
    `rdm1_slater_proj` (γ Hermitian, γ² = γ, tr γ = N); `exists_slater_of_proj` (every rank-N projection is the γ of a
    Slater state); `wick_slater`: `⟨Ψ, c_{i₀}† ⋯ c_{iₙ₋₁}† c_{jₙ₋₁} ⋯ c_{j₀} Ψ⟩ = det (γ_{i_a j_b})`; `rdm2_slater`:
    `D_ij,kl = γ_ik γ_jl − γ_il γ_jk`.
  - Step 2 ✅ (2026-11-26, with general Cauchy–Binet in `ForMathlib/LinearAlgebra/Matrix/CauchyBinet`), `QM/ManyBody/QuasiFreeMixed` (gauge-invariant mixed quasi-free states, needed for B4): `quasiFree γ` for
    `0 ≤ γ ≤ 1`, `= U(u)(⊗_k diag(1 − n_k, n_k))U(u)†`; `quasiFree_isDensityMatrix`; `rdm1_quasiFree : tr(ρ_γ c_i† c_j) = γ_ij`;
    `wick_quasiFree : tr(ρ_γ c† ⋯ c) = det (γ_{i_a j_b})`.
  - Step 3 ✅ (2026-11-26, with compactness of the unitary group in `ForMathlib/Topology/Instances/UnitaryGroup`), `QM/ManyBody/HartreeFock`: `twoBody V = ½ Σ V_ij,kl c_i† c_j† c_l c_k`, `ham h V = oneBody h + twoBody V`,
    `hfEnergy h V γ = Re(Σ h_ij γ_ij + ½ Σ V_ij,kl (γ_ik γ_jl − γ_il γ_jk))`; `energy_slater` (`⟨H⟩ = E_HF(γ)` on Slater
    states); `lieb_variational` (V ⪰ 0 on the pair space: for `0 ≤ γ ≤ 1`, `tr γ = N` there is a rank-N projection P with
    `E_HF(P) ≤ E_HF(γ)`; proof: shift between two fractional eigenvalues, E_HF is concave in the shift);
    `exists_hf_minimizer` (a Slater minimizer over all admissible γ); `ground_le_hf` (`E₀(N) ≤ E_HF(γ)` for all admissible γ).
- B3+ ✅ No unfilled shells in Hartree–Fock (Bach–Lieb–Loss–Solovej 1994; statements approved and proved
  2026-11-27), `QM/ManyBody/HartreeFockAufbau`: Fock matrix `fockMat`; `hf_first_order`; `hf_aufbau` (for `V ⪰ 0` and a
  minimizing rank-N projection `P`, `Re⟨x, F x⟩ ≤ Re⟨y, F y⟩` for unit `x` occupied, `y` unoccupied); `hf_offDiag`,
  `hf_equation` (`F(P) Pᵀ = Pᵀ F(P)`).
- B5 ⬜ Pure-state N-representability: the Borland–Dennis constraints (proposed 2026-11-26, high gain / high risk,
  statements not yet drafted). For `N = 3`, `M = 6` (`∧³ℂ⁶`, dimension 20), the natural occupations `λ₁ ≥ … ≥ λ₆` of
  every pure state satisfy `λ₁ + λ₆ = λ₂ + λ₅ = λ₃ + λ₄ = 1` and `λ₄ ≤ λ₅ + λ₆`; to our knowledge the first formalized
  generalized Pauli constraint, and the model example where pure and ensemble RDMFT differ (`Bp ≠ Be`, D4). Plan: the
  equalities from a normal form of `Ψ ∈ ∧³ℂ⁶` (mode rotations, `QM/ManyBody/ModeRotation`); the inequality needs an
  elementary proof (literature check first: Borland–Dennis 1972, Ruskai 2007; Klyachko's representation-theoretic
  route is out of reach). Risk: no usable elementary proof of the inequality.
  - Follow-up (Schilling): pinning and quasipinning (Schilling, Gross, Christandl, PRL 2013). If a constraint is
    saturated (`λ₄ = λ₅ + λ₆`), `Ψ` obeys a selection rule: it lies in the span of the natural-orbital configurations
    annihilated by the operator `D̂ = n̂₅ + n̂₆ − n̂₄` (here `|123⟩, |145⟩, |246⟩`); and a stability estimate for
    quasipinning (distance of `Ψ` from that span controlled by `λ₅ + λ₆ − λ₄`). See also D4, which is Schilling et al.'s
    unified framework.
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
- C7 ⬜ N-representability of the one-body Green's function (proposed 2026-11-26, speculative, statements not yet
  drafted). Which matrix-valued `G(z)` are Green's functions of an `N`-particle state? Necessary layers: (i) Herglotz,
  positive matrix spectral measure of total mass `1` (`{c_i, c_j†} = δ_ij`; C1 for eigenstates); (ii) hole and particle
  parts separately positive, the hole part integrating to `γ`, which obeys Coleman (`0 ≤ γ ≤ 1`, `tr γ = N`; B2);
  (iii) pole weights are sums of rank-one terms `⟨Ψ|c_i†|k⟩⟨k|c_j|Ψ⟩`, with the number of poles bounded by the
  dimensions of the `N ± 1` sectors. Questions: are (i)–(iii) sufficient when the Hamiltonian is free (conjecture:
  almost)? With `H` fixed, the first moment is tied to `h` plus the HF self-energy (B3, D4-style scope). Trap: for
  ground states do *not* impose removal poles below addition poles (IP ≥ EA ⇔ convexity of `E(N)`, false for general
  finite-dimensional `H`; a counterexample Hamiltonian is a good sanity theorem). After C2, B4 and D4.

### Track D: DFT (`DFT`), ongoing
- D0 ✅ Lattice DFT (HK, generic HK, Kohn–Sham, TDDFT, RDMFT); continuum on a line (H¹₀, unique continuation, HK, Neumann walls,
  measure potentials). See MODULES.md.
- D1 ⬜ Adiabatic connection and coupling-constant integration of E_xc (lattice); exact conditions (concavity, piecewise
  linearity in N for ensembles).
- D2 ⬜ Link to Track C: the Sham–Schlüter equation (lattice), Kohn–Sham versus interacting response (Dyson-like equation with f_xc).
- D3 ⬜ RDMFT ↔ quasi-free states (B3).
- D4 ⬜ Unified framework for finite-dimensional functional theories, after Wang, Liebert, Penz, Schilling,
  arXiv:2606.06676 (proposed by Miguel 2026-11-26; **statements approved 2026-11-26**, blueprint chapter `unified`). Layout:
  `DFT/Scope/` (abstract theory), instances in the existing folders; general convex analysis in `ForMathlib`.
  Goal: prove the structural results once and re-derive lattice DFT, RDMFT and spin-DFT as instances.
  Notation: `d`-dimensional Hilbert space `Fin d → ℂ`, states are unit vectors `ψ` or density matrices `Γ`
  (`Γ ⪰ 0`, `tr Γ = 1`).
  - Definitions. `structure Scope (V) (d)`: a finite-dimensional real vector space `V`, a linear map
    `ι : V →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ` with Hermitian values, and a Hermitian `H₀`; `H v = H₀ + ι v`.
    Density `dens Γ : Module.Dual ℝ V := v ↦ Re tr(Γ ι v)`, `densPure ψ` for `Γ = |ψ⟩⟨ψ|`.
    Ranges `Bp = densPure '' {unit ψ}`, `Be = dens '' {density matrices}`. Energy
    `E v = inf_ψ Re⟨ψ, H v ψ⟩`. Constrained-search functionals `Fp ρ, Fe ρ : EReal` (`inf ⟨H₀⟩` over states
    with density `ρ`, `⊤` off the range). `IsCritical ψ :⇔ ∃ v, ι v ∉ ℝ·1 ∧ ψ is an eigenvector of ι v`;
    `Bc` (densities of critical states), `Br = Bp \ Bc`. `IsAbelian :⇔ the ι v commute`. `NoRedundancy :⇔
    ι injective ∧ 1 ∉ range ι`.
  - Stage 1 (geometry, duality, Hohenberg–Kohn):
    `isCompact_Bp`, `isCompact_Be`, `Be_eq_convexHull_Bp`; `Bp_eq_Be_of_abelian` (and both are the convex hull of
    the finitely many joint-eigenvalue densities); `Fp_attained`, `Fe_attained` (minimizers exist on the ranges);
    `E_eq_iInf_Fp`, `E_eq_iInf_Fe` (`E v = inf_ρ (F ρ + ρ v)`); `convexOn_Fe`; `lowerSemicontinuous_Fp`,
    `lowerSemicontinuous_Fe`; `Fe_le_Fp`; `Fe_eq_sup` (`Fe ρ = sup_v (E v − ρ v)` on `Be`);
    `Fe_greatest_convex_lsc_minorant` (`G` convex, lsc, `G ≤ Fp` ⇒ `G ≤ Fe`);
    `isCritical_iff` (under `NoRedundancy`: critical ⇔ `ψ, B₁ψ, …, B_mψ` linearly dependent over ℝ ⇔ their real
    Gram determinant vanishes);
    `weak_hk` (equal ground-state densities for `v₁, v₂` ⇒ each ground state of `H v₁` is one of `H v₂`; also for
    ensembles); `strong_hk` (`ρ ∈ Br` with a pure ground state of `H v` and of `H v'` ⇒ `ι (v − v') ∈ ℝ·1`, so
    `v = v'` under `NoRedundancy`); `ensemble_vrep` (every `ρ` in the intrinsic interior of `Be` is the density of
    an ensemble ground state of some `H v`, with `−v` a subgradient of `Fe`); `Fp_eq_Fe_of_pure_gs` (Lemma 5.7).
    Instances: lattice DFT (`Be` is the hypersimplex), RDMFT (`Be = {0 ≤ γ ≤ 1, tr γ = N}`, via Coleman), spin
    chains (`Be = [−1, 1]^m`); `KohnSham/Duality` restated as an instance.
  - Stage 2 (representability by eigenstates): `eigenstate_vrep` (Thm 5.3(i)): every `ρ ∈ Br` is
    `densPure ψ` for a unit `ψ` with `H v ψ = λ ψ` for some `v`, `λ`, and `ψ` attains `Fp ρ` (Lagrange multiplier
    on the unit sphere; check whether the paper's omission of `NoRedundancy` here is harmless);
    `continuousOn_Fe` (on the intrinsic interior of `Be`).
  - Stage 3 (change of scope and examples): reduction of scope (`dens` of `S ∘ f` is `f* ∘ dens`) and
    purification (`Fe` of `S` equals `Fp` of the purified scope on `H ⊗ H`, §VII.B; exact form to be checked against
    the paper); Bloch example (`Bp` the unit sphere, `Be` the ball, so `Bp` need not be convex); the double-qubit
    example with `Fe < Fp` at an interior point (Appendix A), if its values are exact.
  - Out of scope for now: the moment-map description of Lie-algebra scopes (§VIII) and the generalized Pauli
    constraints, which need Kirwan/Atiyah–Guillemin–Sternberg convexity.

- D5 🟡 Exact Kohn–Sham with Neumann walls and `H⁻¹` potentials (Corso's Theorem 2.12; chosen by Miguel 2026-11-27).
  Phase 1 ✅ (2026-11-27, `DFT/Continuum/Line/NeumannKS`; statements approved the same day): Lieb = Levy–Lieb on `D_N`,
  weak-* continuity of the inverse map `ρ ↦ v_ρ`, Gateaux differentiability of the Lieb functional (`dF = -v_ρ`), the
  exact KS potential `v + v_Hxc`, Hartree split for pair interactions.
  Phase 2 ⬜ (statements approved 2026-11-27; blueprint, continuum chapter, last section): abstract
  form eigenbasis (ForMathlib), Neumann orbitals for `H⁻¹` potentials, non-interacting ground states (Slater /
  product), `T_KS = F_0` (Corso Lemma 6.2), bosonic `F_0` = von Weizsäcker, Levy minimisers exist, Aufbau (Corso Thm 2.15).

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
- F3 ⬜ Generic pure-state ground-state v-representability in lattice DFT (proposed 2026-11-26, high gain / high risk,
  conjecture). For generic `H₀` (hopping and interaction), every density in the hypersimplex outside a Lebesgue-null set
  is the density of a pure ground state of some `H(v)`; the exceptions come from degeneracies. D4's Theorem 5.3(i) gives
  only eigenstate representability. Tools: the generic-HK machinery (`DFT/Lattice/Generic`, `GenericHK`). First step:
  numerics on small lattices (do the non-pure-representable regions have positive measure?); the conjecture may be false.

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
1. **B3 done** (2026-11-26).
2. **A4++ spherical harmonics** (approved): stages A → B → C → D in order.
3. **C1 remainder:** time-ordered and advanced functions, two-site Hubbard sanity theorem.
4. **C2 + B4** (self-energy, Gibbs states and KMS), then C3.
5. **A6** Kato cusp, Tiers 1–2.
6. **D4** unified functional-theory framework: statements approved; stages 1 → 2 → 3.
7. **A7** Sturm oscillation: Tier 1 (Jacobi matrices) first, then Tier 2 (Prüfer angle); statements drafted, pending approval.
8. Speculative (2026-11-26): **B3+** done (2026-11-27); **F3** numerics first; **B5** Borland–Dennis
   after a literature check for an elementary proof of the inequality, then Schilling's pinning.
9. In parallel: semiclassical-xc Tier 1 (F1); first contact with Physlib about E1/E3.

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
- 2026-11-26: B3 statements approved (Slater states and Wick, mixed quasi-free states, HF and Lieb's variational principle).
- 2026-11-26: item D4 added (unified framework after arXiv:2606.06676); statements drafted, pending approval.
- 2026-11-26: items B3+ (no unfilled shells), B5 (Borland–Dennis, Schilling's pinning) and F3 (generic pure-state
  v-representability) added as proposals.
- 2026-11-26: item C7 (N-representability of the Green's function) added as a proposal.
- 2026-11-26: D4 statements approved; blueprint chapter `unified` added (no Lean yet).
- 2026-11-27: B3+ done (no unfilled shells, Hartree–Fock equations).
- 2026-11-27: item A7 (Sturm oscillation theorem) added.
