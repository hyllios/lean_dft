# LatticeDFT — density-functional theory on lattices, formalized in Lean 4

A Lean 4 / Mathlib formalization of the foundations of density-functional theory (DFT) for finite lattice
systems. It covers ground states, the Hohenberg–Kohn (HK) theorem and its failures, second-quantized lattice
fermions, a **generic Hohenberg–Kohn theorem** (spinless, and spin-resolved for spinful electrons), and
**Kohn–Sham theory**: existence and generic uniqueness of Kohn–Sham potentials, and convergence of the
regularised Kohn–Sham iteration.

All proofs use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and there is no `sorry`.

**Website:** <https://hyllios.github.io/lean_dft/>. It has the blueprint, a human-readable account of every
definition and theorem with links to the Lean code ([web](https://hyllios.github.io/lean_dft/blueprint/),
[pdf](https://hyllios.github.io/lean_dft/blueprint.pdf),
[dependency graph](https://hyllios.github.io/lean_dft/blueprint/dep_graph_document.html)).

## Main results

### Generic Hohenberg–Kohn theorem

```lean
theorem LatticeDFT.generic_hk_lattice_fermions
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
| `Convex/MoreauYosida` | Moreau–Yosida envelope and proximal map on a compact convex domain |
| `KohnSham/Iteration`, `KohnSham/RegularizedKS` | convergence of the regularised Kohn–Sham iteration (MYKSODA, corrected form) |

About 6,000 lines of Lean in total.

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
* Time-dependent DFT: local existence and uniqueness are proved; global-in-time statements (how long a
  solution stays in `Ω`) and complex hopping are open.

## License

Apache 2.0 (see `LICENSE`), the same license as Mathlib.

## Authors

Miguel A. L. Marques. The formalization was developed with the assistance of Claude (Anthropic).
