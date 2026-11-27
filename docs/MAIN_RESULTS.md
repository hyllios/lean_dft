# Main results

The declarations listed here are the main results of the repository. Rules (`AGENTS.md` §4):

- every name listed here must exist (checked by `scripts/check_main_results.py`, enforcing);
- every name listed here must be referenced in the blueprint with `\lean{...}` (same script with `--strict`, enforcing);
- changing the *statement* of a listed result needs explicit approval by Miguel.

**Status (2026-11-25): seeded automatically** from the declarations named in the README section "Main results".
2026-11-26: `DFT.generic_hk_hubbard` removed by Miguel (it is a corollary of `DFT.generic_hk_spin`). Every listed
result is now in the blueprint, and CI runs the blueprint check with `--strict`.

| Declaration | In blueprint |
|---|---|
| `DFT.aufbau_lowest` | yes |
| `DFT.Continuum.Box.exists_isGS` | yes |
| `DFT.Continuum.Box.hk_box` | yes |
| `DFT.Continuum.Box.hk_box_complete` | yes |
| `DFT.Continuum.Box.lieb_box` | yes |
| `DFT.Continuum.hk_of_ucp` | yes |
| `DFT.Continuum.lattice_hk_of_hstar` | yes |
| `DFT.Continuum.Line.hasDerivAt_liebNH` | yes |
| `DFT.Continuum.Line.hasDerivAt_xcNH` | yes |
| `DFT.Continuum.Line.ks_exact` | yes |
| `DFT.Continuum.Line.gs_free_fer` | yes |
| `DFT.Continuum.Line.ks_aufbau` | yes |
| `DFT.Continuum.Line.tksNH_attained` | yes |
| `DFT.Continuum.Line.liebNH_bos_free` | yes |
| `DFT.Continuum.Line.exists_neuOrbitals` | yes |
| `DFT.Continuum.Spectral.exists_orbitals` | yes |
| `DFT.Scope.Be_eq_convexHull_Bp` | yes |
| `DFT.Scope.Fe_eq_iSup` | yes |
| `DFT.Scope.le_Fe_of_convexOn` | yes |
| `DFT.Scope.ensemble_vrep` | yes |
| `DFT.Scope.strong_hk` | yes |
| `DFT.Scope.isCritical_iff_det` | yes |
| `DFT.lieb_eq_Fe` | yes |
| `DFT.Continuum.subgrad_unique` | yes |
| `DFT.dimH_image_le_of_pointwise_lipschitz` | yes |
| `DFT.dimH_nonUVDens_lattice_fermions_w` | yes |
| `DFT.dimH_nonUVDens_le` | yes |
| `DFT.dimH_zeroSet_add_one_le` | yes |
| `DFT.ens_purify` | yes |
| `DFT.ft_theorem2_counterexample` | yes |
| `DFT.generic_ground_mem_omega` | yes |
| `DFT.generic_ground_mem_omega_spin` | yes |
| `DFT.generic_hk_lattice_fermions_w` | yes |
| `DFT.generic_hk_spin` | yes |
| `DFT.generic_hk_spin_field` | yes |
| `DFT.goodOn_unique` | yes |
| `DFT.groundState_field_shift` | yes |
| `DFT.hubbard_triplet_frozen` | yes |
| `DFT.hubbard_triplet_not_mem_omega` | yes |
| `DFT.kfb_sq_w` | yes |
| `DFT.ks_potential_exists` | yes |
| `DFT.ks_potential_exists_interior` | yes |
| `DFT.ks_potential_generic_unique` | yes |
| `DFT.lattice_myksoda` | yes |
| `DFT.NonUVDens` | yes |
| `DFT.not_mem_omega_of_frozen` | yes |
| `DFT.square_kMat_degenerate` | yes |
| `DFT.square_not_mem_omega` | yes |
| `DFT.T` | yes |
| `DFT.td_existence` | yes |
| `DFT.td_global` | yes |
| `DFT.td_kohn_sham` | yes |
| `DFT.td_kohn_sham_ensemble` | yes |
| `DFT.td_spin_existence` | yes |
| `DFT.td_spin_uniqueness` | yes |
| `DFT.td_uniqueness` | yes |
| `DFT.van_leeuwen` | yes |
| `DFT.van_leeuwen_ens` | yes |
| `DFT.van_leeuwen_unique` | yes |
