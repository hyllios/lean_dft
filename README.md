# lean_dft — density-functional theory formalized in Lean 4: lattices, and first steps to the continuum

A Lean 4 / Mathlib formalization of the foundations of density-functional theory (DFT) for finite lattice
systems. It covers ground states, the Hohenberg–Kohn (HK) theorem and its failures, second-quantized lattice
fermions, a **generic Hohenberg–Kohn theorem** (spinless, and spin-resolved for spinful electrons), and
**Kohn–Sham theory**: existence and generic uniqueness of Kohn–Sham potentials, and convergence of the
regularised Kohn–Sham iteration. It then treats time-dependent DFT on lattices and takes first steps to
the continuum: Hohenberg–Kohn on a general configuration space, conditional on unique continuation, and an
unconditional case (one particle in a box).

All proofs use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and there is no `sorry`.

**Website:** <https://hyllios.github.io/lean_dft/>. It has the blueprint, a human-readable account of every
definition and theorem with links to the Lean code ([web](https://hyllios.github.io/lean_dft/blueprint/),
[pdf](https://hyllios.github.io/lean_dft/blueprint.pdf),
[dependency graph](https://hyllios.github.io/lean_dft/blueprint/dep_graph_document.html)).

## Main results

### Generic Hohenberg–Kohn theorem

```lean
theorem DFT.generic_hk_lattice_fermions
    {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : ℝ} (ht : t ≠ 0) (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUV (H0F G t Vint) occF v} ⊆ Z
```

Take `N` spinless fermions on any connected lattice (graph) with `M` sites, hopping `t ≠ 0`, and any
density–density interaction. Call a potential `v` bad if some ground state of `H(v)` is also a ground state
of a potential that differs from `v` by more than a constant. The bad potentials lie in a closed, nowhere
dense set of Lebesgue measure zero. So the HK theorem holds for almost every potential, although it fails on
lattices in general (Penz & van Leeuwen, *J. Chem. Phys.* **155**, 244111 (2021)). Penz & van Leeuwen,
*Quantum* **7**, 918 (2023), left this potential-side statement open.

`generic_hk_lattice_fermions_w` extends the theorem to edge-dependent, symmetric hopping amplitudes `t a b`
that all have the same sign.

### Spin-resolved generic Hohenberg–Kohn theorem

`generic_hk_spin`: for `N↑` spin-up and `N↓` spin-down electrons (`0 < Nσ < M`) on a connected lattice,
with spin-conserving hopping of a common sign and any diagonal interaction (e.g. Hubbard,
`generic_hk_hubbard`), the spin-dependent potentials `(v↑, v↓)` at which some ground state is shared with
a potential differing by more than a separate constant on each spin form a closed, nowhere dense,
Lebesgue-null set. The separate constants are the known non-uniqueness of spin-DFT (a uniform magnetic
field along the quantisation axis); generically there is no other. The proof shows that the
strong-potential leading coefficient of the two species factorises into the spinless ones.
In spin-DFT language (`generic_hk_spin_field`, with `v↑ = v - B`, `v↓ = v + B`): a uniform shift of the
magnetic field `B` never changes the ground state (`groundState_field_shift`), and for almost every
`(v, B)` it is the only freedom besides the usual constant in `v`.

### Time-dependent DFT

Lattice TDDFT reduces to ODEs (Farzanehpour & Tokatly, *Phys. Rev. B* **86**, 125130 (2012)): the
force-balance equation `K(ψ) v = q(ψ) - n̈` lets one eliminate the potential, which gives a nonlinear
Schrödinger equation.

* `td_existence`, `td_uniqueness` (their Theorem 1): from an initial state in
  `Ω = {det(K + 𝟙𝟙ᵀ) ≠ 0}` that reproduces `n(t₀)` and `ṅ(t₀)`, every density with continuous `n̈` is
  produced, locally in time, by a potential that is unique up to a constant (Picard–Lindelöf).
* Their Theorem 2 claims every ground state on a connected lattice is in `Ω`. `square_kMat_degenerate`
  shows it is false: a ground state shared by two different potentials (two fermions on the square) has a
  non-constant zero mode of `K` (`kMat_shared`).
* `generic_ground_mem_omega`: the corrected statement. For almost every static potential, every ground
  state of lattice fermions is in `Ω`, so TDDFT starting from it is well posed.
* `td_global` (continuation in time): the norm is conserved, so the only way the TDDFT solution can
  stop is by reaching the boundary of `Ω`. For every `T`, either the potential exists on all of
  `[t₀, T]`, or the evolution comes arbitrarily close to `det(K + 𝟙𝟙ᵀ) = 0` before `T`. Solutions
  are unique on the whole interval (`goodOn_unique`).
* Complex hopping (magnetic flux): `td_existence_complex`, `td_uniqueness_complex`,
  `td_global_complex`. A Hermitian hopping `A + iB` is the real symmetric hopping
  `[[A, -B], [B, A]]` on a doubled lattice; the unphysical half has conserved norm, so it stays
  zero. Without flux nothing changes (`omegaC_zero`).
* `generic_flux_ground_mem_omegaC`: TDDFT with flux from the ground state. For common-sign hopping
  `A` and any flux pattern `B`, for all but finitely many flux strengths `r` (hopping `A + irB`),
  almost every potential has all its (complex) ground states in `Ω`. The proof uses a doubled
  Krylov criterion (both real components of each configuration); without flux its determinant is
  the square of the real one, so along the flux family it is a polynomial in `r` that is nonzero
  at `r = 0`.
* `generic_peierls_ground_mem_omegaC`: the same with genuine Peierls phases, hopping
  `t_ab e^{iθ φ_ab}` (any antisymmetric pattern `φ`, field strength `θ`). The doubled Krylov
  determinant is now real-analytic in `θ` and nonzero at `θ = 0`, so by the principle of isolated
  zeros the bad field strengths form a closed set without accumulation points (finite in every
  bounded interval, `0` excluded); off it, almost every potential has all its ground states in `Ω`.
* Spin-resolved TDDFT (`TDDFT/Spin`): with two conserved particle numbers the force-balance matrix
  of `(n↑, n↓)` always has two zero modes, so the theory is run on `2M - 1` reduced observables with a
  single conserved sum, and all spinless results apply. `generic_ground_mem_omega_spin`: for almost
  every spin-dependent potential every ground state lies in `Ω` (via the spin-resolved (H\*) and the
  invariance of Krylov determinants under constant energy shifts). `td_spin_existence`,
  `td_spin_uniqueness`: the spin densities `(ρ↑, ρ↓)(t)` determine `(v↑, v↓)(t)` up to one constant
  per spin.
* Frozen densities (`TDDFT/Frozen`): an eigenstate of `H0` whose configurations all have the same
  occupations is an eigenstate for every potential, so its density never moves, whatever `v(t)` is,
  and the potential is completely undetermined. `not_mem_omega_of_frozen` derives `ψ ∉ Ω` from
  `td_uniqueness`. For the half-filled Hubbard dimer the `S_z = 0` triplet is such a state for every
  `t` and `U` (`hubbard_triplet_frozen`, `hubbard_triplet_not_mem_omega`): total-density TDDFT for
  spinful electrons fails for it outright.
* Towards the continuum (`Continuum/General/HK`): Hohenberg–Kohn for a configuration space `(X, μ)` (e.g.
  `ℝ^{3N}`), with the kinetic energy and interaction as a bilinear form on a form domain and one-body
  potentials coupled by `Σᵢ w(xᵢ)`. `hk_of_ucp`: same density ⇒ potentials differ by a constant,
  assuming separation (fundamental lemma), rigidity of the coupling, and unique continuation of the
  ground state. `lattice_hk_of_hstar` recovers the lattice theorem: there, unique continuation is
  "no zero amplitude", supplied by (H\*).
  `hk_box` (`Continuum/Box/Basic`) is an unconditional continuum case: one particle on `[0, 1]` with hard
  walls and a continuous potential. A ground state solves `ψ'' = (v - E)ψ`, its zeros cannot
  accumulate (ODE uniqueness), so it vanishes only on a null set, and equal densities `ψ² = ψ'²` force
  `v - v'` to be constant. Ground states exist for every continuous potential (`exists_isGS`, by
  shooting and the Picone inequality), so `hk_box_complete` needs no assumption at all.
  `hk_pair_of_ucp` (`Continuum/Pair/Basic`): two particles on `[0, 1]` (bosons or fermions, continuous
  interaction). Everything is proved except unique continuation of the ground state on the square,
  which in two dimensions is genuine PDE theory.
  For two non-interacting bosons it is proved (`hk_free_bosons`, `Continuum/Pair/Free`): every ground
  state is `k ψ₀(x₁)ψ₀(x₂)` (slicing + equality case of Picone), so the theorem is unconditional.
  The Lieb functional (`Continuum/General/Lieb`): `F(ρ) = sup_v (E(v) − ρ(v))` lies below the constrained
  search, gives back `E(v) = inf_ψ (F(ρ_ψ) + ρ_ψ(v))`, is convex, and has `-v` as a subgradient at a
  ground-state density of `v`; Hohenberg–Kohn says this subgradient is unique up to constants
  (`subgrad_unique`). In the box this is unconditional (`lieb_box`).
  Interacting bosons (`Continuum/Pair/Bosons`): ground states solve the 2D Schrödinger equation
  classically and, by Hopf's strong maximum principle, a ground state that does not change sign has
  no zeros. The sign property itself is proved in the `C²` form domain (`Continuum/Pair/Sign`):
  ground states have zero gradient at their zeros, and the Hopf boundary lemma then rules out sign
  changes. So `hk_interacting_bosons` holds for every continuous symmetric interaction, with no
  assumption beyond the existence of ground states.
* Dimer reality check (`TDDFT/Dimer`): for one particle on two sites the general machinery gives
  `K = 2Tb [[1,-1],[-1,1]]` with `b = Re(ψ̄₀ψ₁)`, so `Ω = {b ≠ 0}`; the speed limit
  `ṅ₀² ≤ 4T² n₀n₁` holds with equality exactly outside `Ω`; the potential is
  `(v₀ - v₁)² (4T² n₀n₁ - ṅ₀²) = (n̈₀ + 2T²(n₀ - n₁))²`, the known closed form; every eigenstate lies in
  `Ω`, while the Rabi oscillation of a particle released from one site never does.
* `van_leeuwen` (van Leeuwen's theorem on the lattice): the density of any trajectory of any system,
  driven by a continuous potential, is reproduced locally in time by any other system on the same
  sites, starting from a state in its own `Ω` with the same initial density and current. The
  potential of the second system is unique (`van_leeuwen_unique`).
* `td_kohn_sham`: time-dependent Kohn–Sham. Start the interacting system from any real state
  (e.g. its ground state). If the initial density is that of a pure non-interacting ground state of
  `H_s(v_s)`, with `v_s` outside a closed, nowhere dense, null set, then a unique time-dependent
  Kohn–Sham potential reproduces the interacting density near `t₀`.
* `td_kohn_sham_ensemble`: the same without the pure-state assumption. Any ground-state ensemble
  `Γ` of `H_s(v_s)` (as produced by `ks_potential_exists`) works: `Γ = Σ_k b_k b_kᵀ` (`ens_purify`),
  and the ensemble members evolve under one common, unique Kohn–Sham potential. The proof
  purifies the ensemble into one state on configurations `C × κ` and reuses van Leeuwen's theorem
  (`van_leeuwen_ens`).

### Kohn–Sham theory

| Theorem | Statement |
|---|---|
| `ks_potential_exists_interior` | every density with `0 < ρ_i < 1` and `Σ ρ_i = N` is the ground-state (ensemble) density of a non-interacting system in some potential |
| `ks_potential_generic_unique` | for almost every potential, the non-interacting ground state determines the Kohn–Sham potential up to a constant (the generic HK theorem with no interaction); `_w`: edge-dependent hopping |
| `aufbau_lowest` | a set of orbitals minimises the non-interacting energy exactly when it consists of the lowest orbitals |
| `lattice_myksoda` | the regularised KS iteration (MYKSODA; Penz, Laestadius, Tellgren, Ruggenthaler, *PRL* **123**, 037401 (2019)): energies decrease, limit points exist and are regularised ground states, and the KS potentials converge along subsequences |

`lattice_myksoda` is the corrected statement from the paper's erratum. The original paper's convergence
proof is wrong.

## Structure

The library `DFT` has two parts. `DFT/Lattice/` holds everything on finite lattices (namespace `DFT`);
`DFT/Continuum/` holds the general configuration-space theory (namespace `DFT.Continuum`), which takes
the lattice results as a special case. Module paths below are relative to these two folders.

### `DFT/Lattice/`

| Module | Content |
|---|---|
| `Basic/GroundState` | Rayleigh-quotient ground states; ground states are eigenvectors |
| `Basic/Spectral` | existence of ground states; ground-state energy |
| `Basic/SingleParticle` | single-particle HK theorem; failure for frustrated hopping |
| `HK/Basic` | many-body Hamiltonian `hamN`, density, weak and strong HK, spin-DFT-type non-uniqueness |
| `HK/Examples` | HK counterexamples: two fermions on a triangle and on a square |
| `HK/Gap` | gapped ground states and invisible potential directions |
| `HK/SquareWall` | HK fails on the whole plane `v₀+v₂ = v₁+v₃` of the two-fermion square (hidden involution) |
| `Generic/Krylov` | Krylov criterion; (H\*) ⇒ HK on an open dense set |
| `Generic/NullSets` | zero sets of nonzero polynomials are null; (H\*) ⇒ HK almost everywhere |
| `Generic/RationalFunctions` | rational functions on generic points; simultaneous non-vanishing |
| `Generic/SquareCertificate` | (H\*) for the square by exact computation in Lean |
| `Fermions/Configurations` | `N`-particle configurations, occupations |
| `Fermions/Slater` | Slater determinants in first quantization |
| `Fermions/SecondQuantization` | second quantization `Γ h` via determinants; `H0F` (uniform) and `H0Fw` (edge-dependent hopping) |
| `Fermions/FirstQuantization` | many-body powers as signed sums of single-particle powers |
| `Fermions/CauchyBinet` | Cauchy–Binet for Slater determinants; orthonormality of Slater states |
| `StrongPotential/*` | strong-potential leading coefficients, power sums, explicit coefficients |
| `PathSum/*` | optimal assignments, free-fermion leading coefficients, route sums, resonance argument |
| `GenericHK` | the generic HK theorem (uniform and edge-dependent hopping) |
| `KohnSham/Aufbau` | aufbau: non-interacting ground states are Slater determinants of the lowest orbitals |
| `KohnSham/Duality` | Lieb's functional, convex duality |
| `KohnSham/Maximizer`, `KohnSham/Representability` | ensemble v-representability (maximiser, limit argument, separation) |
| `KohnSham/Existence` | existence of Kohn–Sham potentials for lattice fermions |
| `KohnSham/Hypersimplex` | interior densities are positive mixtures of configurations; KS potentials for every density with `0 < ρ_i < 1` |
| `KohnSham/Uniqueness` | generic uniqueness of the Kohn–Sham potential |
| `Spin/Symmetric`, `Spin/HubbardCertificates` | generic HK with a symmetry (sector-wise Krylov condition); total-density HK for the Hubbard dimer and triangle |
| `Spin/KronSum`, `Spin/SpinResolved`, `Spin/SpinField` | two spin species: Kronecker sums, factorisation of the leading coefficients, spin-resolved generic HK; the same in terms of `(v, B)` |
| `TDDFT/ForceBalance` | force-balance matrix at a ground state: f-sum rule, counterexample to Farzanehpour–Tokatly Theorem 2, generic v-representability of ground states |
| `TDDFT/Dynamics`, `TDDFT/Existence`, `TDDFT/GroundStart` | continuity and force-balance equations, local existence and uniqueness of the TDDFT potential, TDDFT from generic ground states |
| `TDDFT/Global` | uniform Picard–Lindelöf steps, norm conservation, blow-up alternative and global uniqueness for lattice TDDFT |
| `TDDFT/ComplexHopping` | lattice TDDFT with complex (Peierls) hopping via a doubled real system |
| `TDDFT/FluxGround` | ground states with flux: doubled Krylov criterion, generic flux strengths |
| `TDDFT/Peierls` | ground states with Peierls phases `t e^{iθφ}`: analytic dependence on the field, isolated bad field strengths |
| `TDDFT/Spin` | spin-resolved TDDFT: reduced observables with one conserved sum, Krylov shift invariance, generic ground-state start, existence and uniqueness of `(v↑, v↓)` up to one constant per spin |
| `TDDFT/Frozen` | frozen densities: eigenstates whose configurations share one occupation pattern keep their density under every potential; the Hubbard-dimer triplet lies outside `Ω` for all `t`, `U` |
| `TDDFT/Dimer` | reality check: one particle on two sites; `Ω = {bond order ≠ 0}`, speed limit, closed-form TD potential, Rabi oscillation outside `Ω` (numerical check in `scripts/dimer_check.py`) |
| `TDDFT/KohnSham` | van Leeuwen's theorem, time-dependent Kohn–Sham from a generic ground state |
| `TDDFT/Ensemble` | purification of ensembles, van Leeuwen's theorem for ensembles, time-dependent Kohn–Sham from a ground-state ensemble |
| `Convex/MoreauYosida` | Moreau–Yosida envelope and proximal map on a compact convex domain |
| `KohnSham/Iteration`, `KohnSham/RegularizedKS` | convergence of the regularised Kohn–Sham iteration (MYKSODA, corrected form) |

### `DFT/Continuum/`

| Module | Content |
|---|---|
| `General/HK` | Hohenberg–Kohn on a general configuration space `(X, μ)`, conditional on separation, rigidity and unique continuation |
| `General/FromLattice` | the lattice as the counting-measure instance; (H\*) supplies unique continuation |
| `General/Lieb` | the Lieb functional `F(ρ) = sup_v (E(v) − ρ(v))`: constrained-search bound, variational principle, convexity, subgradients ⇔ ground states, HK as uniqueness of the subgradient |
| `Box/Basic` | one particle in a box with a continuous potential: separation, rigidity, the Schrödinger equation, unique continuation (ODE uniqueness), `hk_box` |
| `Box/Solve`, `Box/Sturm`, `Box/Picone`, `Box/PiconeEq`, `Box/Extend`, `Box/Ground` | existence of ground states by shooting (truncated Picard–Lindelöf + Grönwall, Sturm comparison, Picone inequality and its equality case, cutoff extension); `hk_box_complete` |
| `Box/Lieb` | the Lieb functional in the box, unconditional (`lieb_box`) |
| `Pair/Basic` | two particles in a box (bosons or fermions, continuous interaction): separation, rigidity, one-body density; `hk_pair_of_ucp` conditional on unique continuation |
| `Pair/Free` | two free bosons: lower bound `2E₀` by slicing, product ground state, every ground state is `k ψ₀⊗ψ₀`; `hk_free_bosons`, unconditional |
| `Pair/Strong`, `Pair/MaxPrinciple`, `Pair/Bosons` | interacting bosons: ground states are classical solutions, Hopf's strong maximum principle; `hk_bosons` assumes only that the ground state does not change sign |
| `Pair/Nodal`, `Pair/Hopf`, `Pair/Sign` | interacting bosons do not change sign: zero gradient at zeros (smoothed-`|Φ|` competitors), Hopf boundary lemma; `hk_interacting_bosons`: HK for two interacting bosons, no extra assumption |
| `Sobolev/Weak` | weak derivatives on open subsets of the plane: uniqueness, classical case, linearity, limits; chain rule for `|f|` and Kato's inequality (first step of the Perron–Frobenius argument) |

About 13,000 lines of Lean in total.

## Further material

* `blueprint/`: LaTeX source of the blueprint. CI builds it into the website above. To build it locally, run
  `pip install leanblueprint`, then `leanblueprint web` or `leanblueprint pdf`.
* `docs/generic-hk-paper-proof.md`: the informal proof of the generic HK theorem, with the literature context
  and an independent review.
* `docs/formalization-log.md`: how the formal proofs were assembled.
* `scripts/`: Python scripts used for exploration and for exact certificates, e.g. (H\*) for all connected
  graphs up to 7 sites, and sector by sector for the spinful Hubbard model up to 6 sites. Outputs are in
  `scripts/data/`.

## Building

```bash
lake exe cache get   # download the Mathlib cache
lake build
```

Requires the Lean toolchain in `lean-toolchain` (currently `v4.36.0-rc2`) and Mathlib as pinned in
`lake-manifest.json`.

## Scope and open directions

* Spinful (Hubbard) fermions: the spin-resolved theorem (spin-dependent potentials) is proved. For the
  total density with a spin-independent potential, `generic_hk_sym` reduces generic HK to a sector-wise
  Krylov condition (spin sectors), proved by exact certificates for the Hubbard dimer and triangle
  (`hubbard_dimer_generic_hk_ae`, `hubbard_triangle_generic_hk_ae`) and checked numerically up to 6
  sites; a proof for all lattices is open (the strong-potential limit is degenerate).
* Frustrated or complex hopping: the general proof needs hopping amplitudes of a common sign. Frustrated
  hopping (e.g. π-flux) can genuinely fail.
* Codimension ≥ 2 of the non-uniquely v-representable densities: proved on paper, not formalized.
* Time-dependent DFT: local existence, global uniqueness, the blow-up alternative, complex (Peierls)
  hopping and spin-resolved densities are proved; how long a given solution actually stays in `Ω` is
  not controlled. TDDFT for the total density of spinful electrons (spin-independent potential) runs
  in the same framework, but whether its ground states generically lie in `Ω` is the time-dependent
  face of the open total-density problem above.

## License

Apache 2.0 (see `LICENSE`), the same license as Mathlib.

## Authors

Miguel A. L. Marques. The formalization was developed with the assistance of Claude (Anthropic).
