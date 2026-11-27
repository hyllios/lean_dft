# Architecture of lean_dft

The repository holds three Lean libraries, strictly layered. The layering is checked in CI by
`scripts/check_layers.py`: no import may go against the order below, and inside a library no two folders may import
each other, directly or through a loop. Rules for contributors are in [`AGENTS.md`](AGENTS.md); plans in
[`ROADMAP.md`](ROADMAP.md).

```
Mathlib  ←  Physlib (leanprover-community/physlib, pinned tag; brings Mathlib)
   ↑            ↑
ForMathlib  ←  QM  ←  DFT
```

| Library | Content | May import | Upstream target |
|---|---|---|---|
| `ForMathlib` | Pure mathematics with no physics: convex analysis (Ekeland, Brøndsted–Rockafellar, Moreau–Yosida), weak derivatives, eigenbases of compact operators, zero sets of polynomials, … Paths mirror Mathlib areas. | Mathlib | Mathlib |
| `QM` | Generic quantum mechanics and many-body theory, not specific to DFT: ground states in finite dimensions, configurations and Slater determinants, the spin algebra; later Fock space, Green's functions, linear response. Basic QM (expectation values, variances, uncertainty, unbounded operators) comes from Physlib (`QM/Basic.lean`). | Mathlib, Physlib, ForMathlib | Physlib (via PhyslibAlpha) |
| `DFT` | Density-functional theory: lattice (`DFT/Lattice`) and continuum (`DFT/Continuum`). | all of the above | — |

Code moved into `ForMathlib`/`QM` from `DFT` takes the namespace of the object it is about (Mathlib's where one
exists, e.g. `SturmLiouville`, `CompactEigenbasis`); call sites are updated in the same commit, without deprecation
aliases (`AGENTS.md` §5). Some earlier moves still carry `DFT.…` names (e.g. `ForMathlib/Analysis/Convex`,
`QM/ManyBody`); they are renamed when touched or upstreamed.

## `DFT/Scope`

The abstract theory of finite-dimensional functional theories (after Wang–Liebert–Penz–Schilling): a Hermitian `H₀` and
observables `B_i` on `𝕜^d`, densities `ρ_i = ⟨B_i⟩`, the ranges `B_p`, `B_e`, the functionals `F_p`, `F_e`, duality,
Hohenberg–Kohn and representability. It imports no other `DFT` folder; concrete theories (`Lattice`, …) import it and
state themselves as instances (`Lattice/KohnSham/Duality`: `latticeScope`).
Internal order: `Basic` → `Ranges` → `Functionals` → `Duality` → `Representability`; `HK` needs only `Basic`.

## `DFT/Lattice`: folder order (each folder may only import folders above it in this list)

1. `Basic`: single-particle Hamiltonians, spectral facts
2. `HK`: many-body Hamiltonian and density on a configuration space (`HK/Basic`), Hohenberg–Kohn and its failures, gaps
3. `Fermions`: first and second quantization on lattices, Cauchy–Binet
4. `Generic`: ingredients of the generic HK theorem (Krylov criterion, null sets, elimination, square certificates and plane)
5. `StrongPotential`: strong-potential expansion, power sums, resolvent
6. `PathSum`: path sums, resonance, resonant point
7. `GenericHK.lean` + `GenericHK/`: the generic Hohenberg–Kohn theorem and its consequences (sign gauge, shortest-path signs, density dimension)
8. `KohnSham`: Kohn–Sham existence, uniqueness, representability, the regularized iteration
9. `Spin`: spin-resolved and symmetric settings, Hubbard certificates
10. `RDMFT`: reduced-density-matrix functional theory
11. `TDDFT`: lattice TDDFT (force balance, existence, frozen densities, ensembles)
12. `Bridge`: worked examples connecting the above (square, triangle, Hubbard, …)

## `DFT/Continuum`: folder order

1. `General`: Hohenberg–Kohn on a general configuration space (conditional on unique continuation), Lieb functional, v-representability
2. `Box`: one particle in a box: an unconditional HK theorem, Sturm/Picone, v-representable densities
3. `Spectral`: Green operator and eigen-expansions on an interval
4. `Line/Core`, then `Line/Free`: N particles on a line; free bosons and fermions have ground states
5. `Sine`: sine-basis expansions (they use `Line/Core` and `Line/Free`)
6. `Line/H1` → `Line/GroundState` → `Line/UCP` → `Line/Symmetry` → `Line/HK` → `Line/Applications` → `Line/KohnSham` → `Line/Regularity`:
   the H¹₀ theory in the order it is built (representability, ground states, unique continuation, exchange-symmetry sectors,
   HK theorems, specific systems, Kohn–Sham and v-representability, regularity of densities)
7. `Line/MeasurePotential`, `Line/Neumann`: measure potentials; Neumann walls and H⁻¹ potentials
8. `Line/NeumannKS`: the exact Kohn–Sham scheme with Neumann walls (Lieb functional, its differentiability, E_Hxc, E_xc)

The order follows the true dependencies (constants used by proofs), not only the import lines. When a file needs
something from a folder further down this list, the thing it needs is in the wrong place: move it down, or move the
file up. Never import upwards.

## Where does a new file go?

1. Pure mathematics with no physics → `ForMathlib/<Mathlib area>/…`. Check Mathlib first.
2. Quantum mechanics or many-body theory that is not about densities as variables → `QM/…`. Check Physlib first.
3. Otherwise → `DFT/…`, in the lowest folder whose material it needs.

## Checks (all run in CI, see `.github/workflows/blueprint.yml`)

| Check | Command |
|---|---|
| Build | `lake build ForMathlib QM DFT` (on the shared host: `LEAN_NUM_THREADS=16`) |
| Axiom audit + self-test | `scripts/check_axioms.sh`, `scripts/test_axiom_check.sh` |
| Hygiene (forbidden constructs, duplicate names; heartbeat and docstring report) | `python3 scripts/check_hygiene.py` |
| Layering | `python3 scripts/check_layers.py` |
| Blueprint references | `lake exe checkdecls blueprint/lean_decls` |

## Versions

Lean and Mathlib versions are those of the pinned Physlib tag (`lakefile.toml`, `lean-toolchain`). See `AGENTS.md` §6.
