# LatticeDFT — density-functional theory on lattices, formalized in Lean 4

A Lean 4 / Mathlib formalization of the foundations of density-functional theory (DFT) for finite lattice
systems: ground states, the Hohenberg–Kohn (HK) theorem and its failures, second-quantized lattice fermions,
and a **generic Hohenberg–Kohn theorem**.

## Main result

```lean
theorem LatticeDFT.generic_hk_lattice_fermions
    {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : ℝ} (ht : t ≠ 0) (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUV (H0F G t Vint) occF v} ⊆ Z
```

For `N` spinless fermions on any connected lattice (graph) with `M` sites, hopping `t ≠ 0` and any
density–density interaction, the external potentials `v` for which some ground state of `H(v)` is also a
ground state of a potential differing from `v` by more than a constant form a closed, nowhere dense,
Lebesgue-null set. In other words, the HK theorem holds for almost every potential, although it fails on
lattices in general (Penz & van Leeuwen, *J. Chem. Phys.* **155**, 244111 (2021)). The potential-side
statement was left open in Penz & van Leeuwen, *Quantum* **7**, 918 (2023).

The proof uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and contains no `sorry`.

## Structure

| Module | Content |
|---|---|
| `Basic/GroundState` | Rayleigh-quotient ground states; ground states are eigenvectors |
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
| `Fermions/SecondQuantization` | second quantization `Γ h` via determinants; `H0F` |
| `Fermions/FirstQuantization` | many-body powers as signed sums of single-particle powers |
| `Fermions/CauchyBinet` | Cauchy–Binet for Slater determinants; orthonormality of Slater states |
| `StrongPotential/*` | strong-potential leading coefficients, power sums, explicit coefficients |
| `PathSum/*` | optimal assignments, free-fermion leading coefficients, route sums, resonance argument |
| `GenericHK` | the main theorem |
| `KohnSham/Aufbau` | aufbau: non-interacting ground states are Slater determinants of the lowest orbitals |
| `KohnSham/Uniqueness` | generic uniqueness of the Kohn–Sham potential |
| `Basic/Spectral` | existence of ground states; ground-state energy |
| `KohnSham/Duality` | Lieb's functional, convex duality |
| `KohnSham/Maximizer`, `KohnSham/Representability` | ensemble v-representability (maximiser, limit argument, separation) |
| `KohnSham/Existence` | existence of Kohn–Sham potentials for lattice fermions |
| `KohnSham/Iteration`, `Convex/MoreauYosida`, `KohnSham/RegularizedKS` | convergence of the regularised Kohn–Sham iteration (MYKSODA, Penz et al. 2019 with erratum) |
| `KohnSham/Hypersimplex` | interior densities are positive mixtures of configurations; every density with 0 < ρᵢ < 1 has a Kohn–Sham potential |

**Blueprint.** A human-readable description of every definition, lemma and theorem, with proofs and links to
the Lean declarations, is in `blueprint/` (LaTeX, built by CI into a website with a dependency graph and a PDF:
<https://hyllios.github.io/lean_dft/blueprint/>). To build it locally: `pip install leanblueprint`, then
`leanblueprint web` or `leanblueprint pdf`.

`docs/generic-hk-paper-proof.md` contains the informal proof (with the literature context and an independent
review); `docs/formalization-log.md` documents how the formal proof was assembled.

`scripts/` contains Python scripts used for exploration and for exact certificates (e.g. (H\*) for all
connected graphs up to 7 sites, and sector-wise for the spinful Hubbard model up to 6 sites), with outputs in
`scripts/data/`.

## Building

```bash
lake exe cache get   # download the Mathlib cache
lake build
```

Requires the Lean toolchain in `lean-toolchain` and Mathlib as pinned in `lake-manifest.json`.

## Scope and open directions

* Spinful (Hubbard) fermions: certified by exact computation for small lattices, not yet in the general proof.
* Frustrated or complex hopping: the general proof covers uniform hopping `t ≠ 0`.
* Codimension ≥ 2 of the non-uniquely v-representable densities: proved on paper, not formalized.
* Kohn–Sham: aufbau, Lieb duality, ensemble v-representability (existence of KS potentials for strictly
  positive mixtures of configuration densities) and generic uniqueness are proved; the hypersimplex
  description of interior densities and the regularized KS iteration are open targets in the blueprint.
* Planned: time-dependent DFT.

## Authors

Miguel A. L. Marques. The formalization was developed with the assistance of Claude (Anthropic).
