# Verification record — pentagon_code_v006

Generated from local execution records. This is not a manually signed assertion or a formal proof certificate.

**OCaml:** COMPLETE (77/77 required jobs).

**Wolfram supplementary checks:** PASS.

**Manuscript association:** MATCH.

**Combined confirmation:** COMPLETE.

OCaml component inventory SHA-256: `56eedc1efc7d3afcb2bfc4f74b55c9d4bc4d301bfe2bc928fb3be8117152a7cc`.

Revalidate this record after moving or modifying files: `python3 confirm.py --check`.

The required OCaml set consists of all proof jobs plus unit, extended, contact-sign, and geometric MITM contract tests. Optional diagnostics do not replace proof jobs.

| Job | Verified status | Seconds |
|---|---|---:|
| `unit` | PASS | 1.318 |
| `extended` | PASS | 1.318 |
| `squeeze_sign_tests` | PASS | 1.316 |
| `pinwheel1237` | PASS | 1.886 |
| `lj1237` | PASS | 1.615 |
| `tj1237` | PASS | 1.602 |
| `pint1237` | PASS | 1.316 |
| `onedeltajmin` | PASS | 1.35 |
| `pinwheel17215` | PASS | 1.349 |
| `lj17215` | PASS | 1.356 |
| `tj17215` | PASS | 1.337 |
| `pint17215` | PASS | 1.363 |
| `dimer_group1` | PASS | 2.401 |
| `dimer_group2` | PASS | 85.992 |
| `dimer_group3` | PASS | 108.179 |
| `dimer_group4` | PASS | 97.964 |
| `squeeze_sign_BA_BC` | PASS | 3.629 |
| `squeeze_sign_BA_CB` | PASS | 1.87 |
| `squeeze_sign_AB_BC` | PASS | 2.124 |
| `squeeze_sign_AB_CB` | PASS | 1.35 |
| `squeeze` | PASS | 3.205 |
| `autodiff_twist_lj1` | PASS | 1.34 |
| `autodiff_twist_lj2` | PASS | 1.34 |
| `autodiff_path_0_0` | PASS | 1.341 |
| `autodiff_path_0_1` | PASS | 1.358 |
| `autodiff_path_0_2` | PASS | 1.369 |
| `autodiff_path_0_3` | PASS | 1.366 |
| `autodiff_path_0_4` | PASS | 1.365 |
| `autodiff_path_1_0` | PASS | 1.348 |
| `autodiff_path_1_1` | PASS | 1.345 |
| `autodiff_path_1_2` | PASS | 1.621 |
| `autodiff_path_1_3` | PASS | 1.361 |
| `autodiff_path_1_4` | PASS | 1.346 |
| `autodiff_path_2_0` | PASS | 1.351 |
| `autodiff_path_2_1` | PASS | 1.341 |
| `autodiff_path_2_2` | PASS | 1.348 |
| `autodiff_path_2_3` | PASS | 1.335 |
| `autodiff_path_2_4` | PASS | 1.331 |
| `autodiff_path_3_0` | PASS | 1.33 |
| `autodiff_path_3_1` | PASS | 1.334 |
| `autodiff_path_3_2` | PASS | 1.337 |
| `autodiff_path_3_3` | PASS | 1.337 |
| `autodiff_path_3_4` | PASS | 1.331 |
| `autodiff_path_4_0` | PASS | 1.331 |
| `autodiff_path_4_1` | PASS | 1.344 |
| `autodiff_path_4_2` | PASS | 1.342 |
| `autodiff_path_4_3` | PASS | 1.329 |
| `autodiff_path_4_4` | PASS | 1.336 |
| `mitm_precluster1_case0` | PASS | 1434.225 |
| `mitm_precluster1_case1` | PASS | 42.984 |
| `mitm_precluster1_case2` | PASS | 219.127 |
| `mitm_precluster2_case0` | PASS | 2495.668 |
| `mitm_precluster2_case1` | PASS | 364.071 |
| `mitm_precluster2_case2` | PASS | 488.775 |
| `mitm_precluster4_case0_experimental` | PASS | 3960.466 |
| `mitm_precluster4_case1_experimental` | PASS | 6971.658 |
| `mitm_precluster6_case1` | PASS | 1183.011 |
| `mitm_precluster6_case2` | PASS | 3289.565 |
| `mitm_precluster6_case3` | PASS | 1474.064 |
| `mitm_precluster6_case4` | PASS | 1215.377 |
| `mitm_precluster6_case5` | PASS | 2759.598 |
| `mitm_precluster6_case6` | PASS | 1570.893 |
| `mitm_calc_pent2_postcluster_case0` | PASS | 773.05 |
| `mitm_calc_pent2_postcluster_case1` | PASS | 103.061 |
| `mitm_calc_pent2_postcluster_case2` | PASS | 138.579 |
| `mitm_calc_pent2_postcluster_case3` | PASS | 67.021 |
| `mitm_calc_pent2_postcluster_case4` | PASS | 156.057 |
| `mitm_calc_pent3_6D_postcluster` | PASS | 24646.423 |
| `mitm_calc_pent3AB_postcluster` | PASS | 6130.054 |
| `mitm_calc_pent3BC_postcluster` | PASS | 2429.198 |
| `mitm_calc_pent3AC_postcluster` | PASS | 1513.091 |
| `mitm_calc_pent4_6D_postcluster` | PASS | 5138.937 |
| `mitm_dimer_isosceles_precluster` | PASS | 1328.773 |
| `mitm_geometric_control` | PASS | 1.317 |
| `pintab_area` | PASS | 1.329 |
| `small3C_area` | PASS | 8.332 |
| `face_lj1` | PASS | 1.315 |

Wolfram evidence mode: `APPROVED_LEGACY_EQUIVALENCE`.

The imported Wolfram JSON is unchanged. Its earlier test program is covered by the explicit mathematical-equivalence record; it is not a new execution of this reporting wrapper.

## Interpretation

A completed finite search establishes its encoded exclusion under the documented coordinate and interval contracts. Function tests and symbolic checks have distinct roles. Compiler, library, and source identities accompany the run reports.
Prior timing summaries in evidence/ supply no passes. The only accepted earlier computation records are those covered by the explicit compatibility contract, with intact logs, original fingerprints, and unchanged calculation inputs. No timeout, failure, interruption, or absent log counts as a pass.
