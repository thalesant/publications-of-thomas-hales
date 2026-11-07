# Paper-to-code index — code v003 / manuscript v005

**Context:** commands below are for Linux/Ubuntu-WSL Bash, at the extracted package root containing `run.py`. Append `--list` to preview without executing.

The selected jobs establish their encoded terminal exclusions. The paper supplies the reductions and earlier lemmas; a claim selection is not the entire transitive mathematical proof. Use `--all` for the complete proof-job set. Source-specific completion is generated in `verification/CONFIRMATION.md`.

## Lemma 4.7 — Delta-junction area

Source code: `QBQQTVY`; paper label: `lemma:delta`.

A 3C triangle of type Delta is excluded from the subcritical case; the stated area bound is greater than 1.5.

**Assumptions / reductions:** The paper’s P-triangle / contact-type conventions and the geometric classification. Code uses outdomfn_delta and deltajedge on the initial Delta coordinate box; the area predicate is areamin_acute.

**Interpretation:** The Delta contact chart is tested at cutoff 1.5. This excludes that contact type from the subcritical cases.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `onedeltajmin` | `(List.assoc "onedeltajmin" !calcs) ()` | `ocaml/pent.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim lemma:delta --list
python3 run.py --claim lemma:delta
```

## Lemma 4.9 — Longest edge of a subcritical triangle

Source code: `BVICHFW`; paper label: `lemma:172`.

If every edge is at most 1.72, the P-triangle is not subcritical.

**Assumptions / reductions:** The paper reduces the nonobtuse short-edge case to the classified 3C configurations. Use the four non-Delta contact types plus the separate Delta exclusion.

**Interpretation:** The code uses the stronger longest-edge cutoff 1.7215. Four non-Delta types and the Delta exclusion exhaust the classified terminal contact patterns.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `onedeltajmin` | `(List.assoc "onedeltajmin" !calcs) ()` | `ocaml/pent.ml` | proof |
| `pinwheel17215` | `(List.assoc "pinwheel17215" !calcs) ()` | `ocaml/pent.ml` | proof |
| `lj17215` | `(List.assoc "lj17215" !calcs) ()` | `ocaml/pent.ml` | proof |
| `tj17215` | `(List.assoc "tj17215" !calcs) ()` | `ocaml/pent.ml` | proof |
| `pint17215` | `(List.assoc "pint17215" !calcs) ()` | `ocaml/pent.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim lemma:172 --list
python3 run.py --claim lemma:172
```

## Lemma 4.11 — Minimum nonobtuse triangle area

Source code: `QGPVOYX`; paper label: `lemma:a0`.

Every nonobtuse P-triangle has area greater than a_min.

**Assumptions / reductions:** The paper first reduces to 3C contact; amin is 1.237 in the code. The Delta type is covered separately by onedeltajmin.

**Interpretation:** The four non-Delta contact charts use the exact rational cutoff 1237/1000; the Delta case is handled at the stronger cutoff 1.5.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `pinwheel1237` | `(List.assoc "pinwheel1237" !calcs) ()` | `ocaml/pent.ml` | proof |
| `lj1237` | `(List.assoc "lj1237" !calcs) ()` | `ocaml/pent.ml` | proof |
| `tj1237` | `(List.assoc "tj1237" !calcs) ()` | `ocaml/pent.ml` | proof |
| `pint1237` | `(List.assoc "pint1237" !calcs) ()` | `ocaml/pent.ml` | proof |
| `onedeltajmin` | `(List.assoc "onedeltajmin" !calcs) ()` | `ocaml/pent.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim lemma:a0 --list
python3 run.py --claim lemma:a0
```

## Lemma 5.1 — Pseudo-dimer shared edge

Source code: `NKQNXUN`; paper label: `calc:pseudo1`.

The edge shared by T1 and T0 has length less than 1.8, including the stated relaxation allowing a longest-edge tie.

**Assumptions / reductions:** (T1,T0) in Psi D; also the precise weakening of the third defining condition stated in the lemma. Preparation assumes total area <=2*a_crit and reduces the central configuration to double contact or the stated midpointer/slider endpoint.

**Interpretation:** The three central terminal patterns are double contact, midpointer at a length boundary, and slider at a length boundary. Peripheral data retain a longest shared edge. Closed ranges retain the tied-arrow boundary.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `mitm_precluster1_case0` | `precluster1_case0 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_precluster1_case1` | `precluster1_case1 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_precluster1_case2` | `precluster1_case2 ()` | `ocaml/mitm-calcs.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim calc:pseudo1 --list
python3 run.py --claim calc:pseudo1
```

## Lemma 5.2 — Pseudo-dimer egressive edge

Source code: `RWWHLQT`; paper label: `calc:pseudo2`.

The longest (egressive) edge of T0 has length greater than 1.8, including the stated longest-edge-tie relaxation.

**Assumptions / reductions:** (T1,T0) in Psi D or the specified tied relaxation; terminal domains from sec:pseudo2. The counterexample has all central edges <=1.8 and total area <=2*a_crit.

**Interpretation:** The central equality filter retains all three equalities and either nonshared length equal to 1.8. In the midpointer and slider code labels, AB is shared and AC is the contact edge. The peripheral is O2C, subcritical, and shared-longest.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `mitm_precluster2_case0` | `precluster2_case0 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_precluster2_case1` | `precluster2_case1 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_precluster2_case2` | `precluster2_case2 ()` | `ocaml/mitm-calcs.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim calc:pseudo2 --list
python3 run.py --claim calc:pseudo2
```

## Lemma 5.4 — Pseudo-dimer pair area

Source code: `BXZBPJW`; paper label: `calc:pseudo-area`.

area{T0,T1} > 2*a_crit - epsilon_M.

**Assumptions / reductions:** (T1,T0) in Psi D. Preparation produces two isosceles-peripheral cases or a 3C+3C terminal case.

**Interpretation:** Two isosceles-peripheral cases and the triple-contact type exclusions establish the pair bound. The triple-contact calculation uses the stronger allowance 0.007; the other cases use epsilon_M=0.008.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `dimer_group2` | `List.concat (Dimer.run_group2 ())` | `ocaml/dimer.ml` | proof |
| `dimer_group4` | `Dimer.run_group4 ()` | `ocaml/dimer.ml` | proof |
| `mitm_precluster4_case0_experimental` | `precluster4_case0_experimental ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_precluster4_case1_experimental` | `precluster4_case1_experimental ()` | `ocaml/mitm-calcs.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim calc:pseudo-area --list
python3 run.py --claim calc:pseudo-area
```

## Lemma 5.5 — Pseudo-dimer plus egressive neighbor

Source code: `JQMRXTH`; paper label: `calc:pseudo-area3`.

area{T0,T1,T_minus} > 3*a_crit + epsilon_M.

**Assumptions / reductions:** (T1,T0) in Psi D; T0 attaches to T_minus; T_minus is nonobtuse (explicit current hypothesis). Preparation reduces both peripherals to O2C and gives six assignments of incoming and egressive central edges.

**Interpretation:** All six ordered incoming/egressive edge assignments are checked. The outgoing peripheral cap is acrit+2 epsilon_M, obtained by subtracting the strict pair bound from the assumed triple-area bound.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `mitm_precluster6_case1` | `precluster6_case1 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_precluster6_case2` | `precluster6_case2 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_precluster6_case3` | `precluster6_case3 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_precluster6_case4` | `precluster6_case4 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_precluster6_case5` | `precluster6_case5 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_precluster6_case6` | `precluster6_case6 ()` | `ocaml/mitm-calcs.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim calc:pseudo-area3 --list
python3 run.py --claim calc:pseudo-area3
```

## Lemma 5.10 — No long-isosceles O2C peripheral in a dimer

Source code: `KUGAKIK`; paper label: `calc:dimer-isosc`.

In a dimer pair, T1 cannot be both O2C and long isosceles.

**Assumptions / reductions:** (T1,T0) in DP. Negate the conclusion, reduce T0 to O2C, then run the isosceles peripheral case.

**Interpretation:** The shared-edge glue matches an O2C long-isosceles peripheral to an O2C central triangle at pair cutoff 2 acrit.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `mitm_dimer_isosceles_precluster` | `dimer_isosceles_precluster ()` | `ocaml/mitm-calcs.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim calc:dimer-isosc --list
python3 run.py --claim calc:dimer-isosc
```

## Lemma 5.11 — Three-triangle cluster bound

Source code: `HUQEJAT`; paper label: `calc:pent3`.

area{T0,T1^0,T1^1} > 3*a_crit + epsilon_M.

**Assumptions / reductions:** Three distinct nonobtuse P-triangles; each peripheral attaches to T0 and has area <=a_crit. The two sequential peripheral motions stop at a central contact or a long-isosceles peripheral.

**Interpretation:** Three contact-central charts distinguish the nonshared edge. The fourth chart is the general six-dimensional center with two isosceles peripherals. All four are required; their central cap is acrit+2 epsilon_N+epsilon_M.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `mitm_calc_pent3_6D_postcluster` | `calc_pent3_6D_postcluster ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_calc_pent3AB_postcluster` | `calc_pent3AB_postcluster ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_calc_pent3BC_postcluster` | `calc_pent3BC_postcluster ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_calc_pent3AC_postcluster` | `calc_pent3AC_postcluster ()` | `ocaml/mitm-calcs.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim calc:pent3 --list
python3 run.py --claim calc:pent3
```

## Lemma 5.12 — Four-triangle cluster bound

Source code: `QPJDYDB`; paper label: `calc:pent4`.

area{T0,T1^0,T1^1,T1^2} > 4*a_crit.

**Assumptions / reductions:** Four distinct nonobtuse P-triangles; three subcritical peripherals attach to T0. Each peripheral is O2C after preparation; central side ordering exploits the stated symmetry.

**Interpretation:** The general six-dimensional central chart has peripheral attachments on all three edges. Its central cap is acrit+3 epsilon_N. Strict symmetry exclusions retain equal sides.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `mitm_calc_pent4_6D_postcluster` | `calc_pent4_6D_postcluster ()` | `ocaml/mitm-calcs.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim calc:pent4 --list
python3 run.py --claim calc:pent4
```

## Lemma 5.14 — Non-large-angle two-triangle estimate

Source code: `FHBGHHY`; paper label: `calc:large`.

area{T0,T1} > 2*a_crit + epsilon_M under the non-large-angle and nonshared-edge assumptions.

**Assumptions / reductions:** Both P-triangles nonobtuse, area(T1)<=a_crit, T1 attaches to T0. A nonshared edge e of T0 has length >1.8 and the angle along (T0,e) is not large.

**Interpretation:** The paper excludes right triangles by the shared-leg area estimate. The remaining cases are double contact or one contact together with a nonshared length of 1.8.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `mitm_calc_pent2_postcluster_case0` | `calc_pent2_postcluster_case0 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_calc_pent2_postcluster_case1` | `calc_pent2_postcluster_case1 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_calc_pent2_postcluster_case2` | `calc_pent2_postcluster_case2 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_calc_pent2_postcluster_case3` | `calc_pent2_postcluster_case3 ()` | `ocaml/mitm-calcs.ml` | proof |
| `mitm_calc_pent2_postcluster_case4` | `calc_pent2_postcluster_case4 ()` | `ocaml/mitm-calcs.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim calc:large --list
python3 run.py --claim calc:large
```

## Section 6.2 — Long-isosceles terminal exclusions (stage 2)

Source code: `GAIMXAD`; paper label: `sec:O2C`.

Terminal exclusions named iso_2C and iso_2C' in the paper’s stage-2 calculation.

**Assumptions / reductions:** Use the acute, subcritical long-isosceles terminal configurations and contact alternatives actually listed in the paper.

**Interpretation:** The two long-isosceles exclusions are evaluated together with four shared-contact coordinate restrictions by dimer_group1. Result labels follow the returned list, not the evaluation order.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `dimer_group1` | `Dimer.run_group1 ()` | `ocaml/dimer.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim sec:O2C --list
python3 run.py --claim sec:O2C
```

## Lemma 6.5 — Squeezing area inequality (stage 3)

Source code: `LZMJIZU`; paper label: `lemma:squeeze-area`.

The specified squeezing deformation decreases area for the stated nonobtuse double-contact configuration of area <=a_crit+epsilon_N.

**Assumptions / reductions:** The geometric motion, signs of slopes, and contact branches are fixed by the local proof. Code uses the mk2Ce representation, shared-length range [2*kappa,2.32], and area cutoff aK+epsN_I.

**Interpretation:** Four contact-sign calculations establish positive finite slopes and the supporting-side assertions. The separate squeeze calculation proves the reciprocal-slope area inequality on that branch. All five proof jobs are required.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `squeeze_sign_BA_BC` | `SqueezeSign.verify_case "BA_BC"` | `ocaml/squeeze_sign.ml` | proof |
| `squeeze_sign_BA_CB` | `SqueezeSign.verify_case "BA_CB"` | `ocaml/squeeze_sign.ml` | proof |
| `squeeze_sign_AB_BC` | `SqueezeSign.verify_case "AB_BC"` | `ocaml/squeeze_sign.ml` | proof |
| `squeeze_sign_AB_CB` | `SqueezeSign.verify_case "AB_CB"` | `ocaml/squeeze_sign.ml` | proof |
| `squeeze` | `Dimer.squeeze_calc ()` | `ocaml/dimer.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim lemma:squeeze-area --list
python3 run.py --claim lemma:squeeze-area
```

## Section 6.4 — Exclusion outside the ice-ray neighborhood (stage 4)

Source code: `DSKKWND`; paper label: `sec:nbd`.

Reduce candidate 3C+3C dimers to the case-dependent neighborhood U with |x_i|<0.01.

**Assumptions / reductions:** Dimer area and common-longest-edge constraints; eight shared-edge contact charts per triangle. The code uses alphaB, betaB-pi/5, xbetaB-sigma, alphaD as the neighborhood quantities.

**Interpretation:** Group 2 excludes 48 distinct ordered contact pairs (64 retained calls). Group 3 treats the other sixteen pairs; four allow the stated pseudo-dimer alternative as well as the 0.01 neighborhood.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `dimer_group2` | `List.concat (Dimer.run_group2 ())` | `ocaml/dimer.ml` | proof |
| `dimer_group3` | `Dimer.run_group3 ()` | `ocaml/dimer.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim sec:nbd --list
python3 run.py --claim sec:nbd
```

## Section 6.6 — Descent to the shear curve (stage 6)

Source code: `LPEYXGH`; paper label: `sec:curve`.

Area decreases along the stated shared-edge paths from U to Gamma.

**Assumptions / reductions:** The source’s top/bottom chart selections and derivatives must match the paper’s specified paths. 25 first-derivative pair checks plus two auxiliary twist checks.

**Interpretation:** Two twist exclusions and 25 first-derivative combinations justify descent to the shear curve. These are distinct from the exact final shear-area argument.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `autodiff_twist_lj1` | `Autodiff.twist_claim_lj1 ()` | `ocaml/autodiff.ml` | proof |
| `autodiff_twist_lj2` | `Autodiff.twist_claim_lj2 ()` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_0_0` | `Autodiff.recurseD 0 0` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_0_1` | `Autodiff.recurseD 0 1` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_0_2` | `Autodiff.recurseD 0 2` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_0_3` | `Autodiff.recurseD 0 3` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_0_4` | `Autodiff.recurseD 0 4` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_1_0` | `Autodiff.recurseD 1 0` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_1_1` | `Autodiff.recurseD 1 1` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_1_2` | `Autodiff.recurseD 1 2` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_1_3` | `Autodiff.recurseD 1 3` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_1_4` | `Autodiff.recurseD 1 4` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_2_0` | `Autodiff.recurseD 2 0` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_2_1` | `Autodiff.recurseD 2 1` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_2_2` | `Autodiff.recurseD 2 2` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_2_3` | `Autodiff.recurseD 2 3` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_2_4` | `Autodiff.recurseD 2 4` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_3_0` | `Autodiff.recurseD 3 0` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_3_1` | `Autodiff.recurseD 3 1` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_3_2` | `Autodiff.recurseD 3 2` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_3_3` | `Autodiff.recurseD 3 3` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_3_4` | `Autodiff.recurseD 3 4` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_4_0` | `Autodiff.recurseD 4 0` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_4_1` | `Autodiff.recurseD 4 1` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_4_2` | `Autodiff.recurseD 4 2` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_4_3` | `Autodiff.recurseD 4 3` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_4_4` | `Autodiff.recurseD 4 4` | `ocaml/autodiff.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim sec:curve --list
python3 run.py --claim sec:curve
```

## Section 6.5 — Exact area formula along Gamma

Source code: `BKUSHRZ`; paper label: `sec:gamma`.

The paper needs positive second derivative along Gamma for |t|<0.01.

**Assumptions / reductions:** The paper defines t=bar x_beta-sigma; the shared-edge parameter has an absolute contact-length interpretation.

**Interpretation:** The paper proves area=2 acrit+sigma t^2 by a diagonal determinant. The numerical second-derivative calculation is supplementary; it uses the absolute contact parameter sigma+t, not t.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `gamma_convexity` | `Autodiff.gamma_convexity_diagnostic ()` | `ocaml/autodiff.ml` | diagnostic |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim sec:gamma --list
python3 run.py --claim sec:gamma
```

## Section A.7 — Shared-edge chart restrictions

Source code: `SMPXAOD`; paper label: `sec:shared`.

Restrictions used to select valid/stable shared-edge charts: pin-T longest edge, pinwheel contact length, LJ beta, TJ beta.

**Assumptions / reductions:** The paper’s relevant area cap is a_crit+epsilon_N; parameters retain their raw chart meanings.

**Interpretation:** The contact-chart restrictions establish the side/orientation alternatives used before differentiating the shared-edge coordinate formulas.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `dimer_group1` | `Dimer.run_group1 ()` | `ocaml/dimer.ml` | proof |
| `autodiff_twist_lj1` | `Autodiff.twist_claim_lj1 ()` | `ocaml/autodiff.ml` | proof |
| `autodiff_twist_lj2` | `Autodiff.twist_claim_lj2 ()` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_0_0` | `Autodiff.recurseD 0 0` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_0_1` | `Autodiff.recurseD 0 1` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_0_2` | `Autodiff.recurseD 0 2` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_0_3` | `Autodiff.recurseD 0 3` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_0_4` | `Autodiff.recurseD 0 4` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_1_0` | `Autodiff.recurseD 1 0` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_1_1` | `Autodiff.recurseD 1 1` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_1_2` | `Autodiff.recurseD 1 2` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_1_3` | `Autodiff.recurseD 1 3` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_1_4` | `Autodiff.recurseD 1 4` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_2_0` | `Autodiff.recurseD 2 0` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_2_1` | `Autodiff.recurseD 2 1` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_2_2` | `Autodiff.recurseD 2 2` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_2_3` | `Autodiff.recurseD 2 3` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_2_4` | `Autodiff.recurseD 2 4` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_3_0` | `Autodiff.recurseD 3 0` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_3_1` | `Autodiff.recurseD 3 1` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_3_2` | `Autodiff.recurseD 3 2` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_3_3` | `Autodiff.recurseD 3 3` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_3_4` | `Autodiff.recurseD 3 4` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_4_0` | `Autodiff.recurseD 4 0` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_4_1` | `Autodiff.recurseD 4 1` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_4_2` | `Autodiff.recurseD 4 2` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_4_3` | `Autodiff.recurseD 4 3` | `ocaml/autodiff.ml` | proof |
| `autodiff_path_4_4` | `Autodiff.recurseD 4 4` | `ocaml/autodiff.ml` | proof |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --claim sec:shared --list
python3 run.py --claim sec:shared
```

## MITM central-triangle diagnostic (name contains 1237)

Source code: `diagnostic:central-1237`; paper label: `(diagnostic)`.

This function uses a 1.2 debug cutoff, despite its name.

**Assumptions / reductions:** The existing central five-dimensional chart and code-defined side ranges.

**Interpretation:** This diagnostic deliberately uses the cutoff 1.2 despite the historical identifier. It does not establish the 1.237 theorem; the primary jobs are listed separately.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `mitm_test1_centralpent_1237` | `test1_centralpent_1237 ()` | `ocaml/mitm-calcs.ml` | diagnostic |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --job mitm_test1_centralpent_1237 --list
python3 run.py --job mitm_test1_centralpent_1237
```

## MITM central-triangle short-edge diagnostic

Source code: `diagnostic:central-172`; paper label: `(diagnostic)`.

Checks the central chart with every side in [2*kappa,1.72] against aK.

**Assumptions / reductions:** No peripheral data; code-defined five-dimensional chart.

**Interpretation:** An additional central-chart diagnostic with all sides at most 1.72. It supplements, rather than replaces, the primary classified contact calculations.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `mitm_test1_centralpent_172` | `test1_centralpent_172 ()` | `ocaml/mitm-calcs.ml` | diagnostic |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --job mitm_test1_centralpent_172 --list
python3 run.py --job mitm_test1_centralpent_172
```

## Historical isosceles 1.27 check

Source code: `historical:one127`; paper label: `(diagnostic)`.

The source describes a 1.27 area lower-bound check on subcritical isosceles triangles and says it may no longer be needed.

**Assumptions / reductions:** Four sign choices and the existing domain2C, with shared length in [1.72,1.79].

**Interpretation:** Optional check of the original subcritical isosceles domain at area cutoff 1.27. It is not a premise of the published proof.

| Job | Mathematical call | Source | Role |
|---|---|---|---|
| `historical_one127` | `Dimer.recursesgn Dimer.one127 Dimer.domain2C` | `ocaml/dimer.ml` | diagnostic |

**Bash at PACKAGE_ROOT:**
```bash
python3 run.py --job historical_one127 --list
python3 run.py --job historical_one127
```

## Complete job catalogue

This includes supporting stages and optional diagnostics, not only the eight principal lemmas.

| Job | Role | Paper | Mathematical task |
|---|---|---|---|
| `unit` | test | tests:function-contracts | Deterministic boundary, geometry, derivative and finite-MITM checks |
| `extended` | test | tests:function-contracts | All unit checks plus deterministic generated geometric and key-cover cases |
| `squeeze_sign_tests` | test | tests:squeeze-contracts | 71 checks of contact construction, sign predicates, strict overlap and subdivision coverage |
| `pinwheel1237` | proof | Lemma 4.11 [lemma:a0] | Exclude nonobtuse pinwheel triangles of area at most 1.237. |
| `lj1237` | proof | Lemma 4.11 [lemma:a0] | Exclude nonobtuse L-junction triangles of area at most 1.237. |
| `tj1237` | proof | Lemma 4.11 [lemma:a0] | Exclude nonobtuse T-junction triangles of area at most 1.237. |
| `pint1237` | proof | Lemma 4.11 [lemma:a0] | Exclude nonobtuse pin-T junction triangles of area at most 1.237. |
| `onedeltajmin` | proof | Lemma 4.7 [lemma:delta], Lemma 4.11 [lemma:a0], Lemma 4.9 [lemma:172] | Exclude Delta-contact triangles of area at most 1.5 on the classified domain. |
| `pinwheel17215` | proof | Lemma 4.9 [lemma:172] | Exclude subcritical pinwheel triangles with every side at most 1.7215 (stronger than the paper’s 1.72 bound). |
| `lj17215` | proof | Lemma 4.9 [lemma:172] | Exclude subcritical L-junction triangles with every side at most 1.7215 (stronger than the paper’s 1.72 bound). |
| `tj17215` | proof | Lemma 4.9 [lemma:172] | Exclude subcritical T-junction triangles with every side at most 1.7215 (stronger than the paper’s 1.72 bound). |
| `pint17215` | proof | Lemma 4.9 [lemma:172] | Exclude subcritical pin-T junction triangles with every side at most 1.7215 (stronger than the paper’s 1.72 bound). |
| `dimer_group1` | proof | Section 6.2 [sec:O2C], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Two isosceles exclusions and four contact-chart restrictions |
| `dimer_group2` | proof | Section 6.4 [sec:nbd], Lemma 5.4 [calc:pseudo-area], Theorem 6.1 [thm:dimer-area] | 64 original calls, 48 distinct ordered contact pairs |
| `dimer_group3` | proof | Section 6.4 [sec:nbd], Theorem 6.1 [thm:dimer-area] | 12 ordinary and 4 pseudo-relaxed neighborhood checks |
| `dimer_group4` | proof | Lemma 5.4 [calc:pseudo-area], Theorem 6.1 [thm:dimer-area] | Four 3C+3C bounds at the stronger 0.007 allowance |
| `squeeze_sign_BA_BC` | proof | Lemma 6.5 [lemma:squeeze-area], Section 6.3 [sec:squeeze], Theorem 6.1 [thm:dimer-area] | B points to A and C: both contact signs and supporting-side conditions on the full four-parameter domain |
| `squeeze_sign_BA_CB` | proof | Lemma 6.5 [lemma:squeeze-area], Section 6.3 [sec:squeeze], Theorem 6.1 [thm:dimer-area] | B points to A; C points to B: both contact signs and supporting-side conditions on the full four-parameter domain |
| `squeeze_sign_AB_BC` | proof | Lemma 6.5 [lemma:squeeze-area], Section 6.3 [sec:squeeze], Theorem 6.1 [thm:dimer-area] | A points to B; B points to C: both contact signs and supporting-side conditions on the full four-parameter domain |
| `squeeze_sign_AB_CB` | proof | Lemma 6.5 [lemma:squeeze-area], Section 6.3 [sec:squeeze], Theorem 6.1 [thm:dimer-area] | A and C point to B: both contact signs and supporting-side conditions on the full four-parameter domain |
| `squeeze` | proof | Lemma 6.5 [lemma:squeeze-area], Section 6.3 [sec:squeeze], Theorem 6.1 [thm:dimer-area] | Certify the reciprocal-slope area-decrease inequality, using the three-way sufficient test; combine with all four contact-sign jobs. |
| `historical_one127` | diagnostic | diagnostic:one127 | Historical 1.27 isosceles checks; not a current proof dependency |
| `autodiff_twist_lj1` | proof | Section A.7 [sec:shared], Section 6.6 [sec:curve], Theorem 6.1 [thm:dimer-area] | Certify the local twist reduction for lj1 contact. |
| `autodiff_twist_lj2` | proof | Section A.7 [sec:shared], Section 6.6 [sec:curve], Theorem 6.1 [thm:dimer-area] | Certify the local twist reduction for lj2 contact. |
| `autodiff_path_0_0` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (0,0) on its prescribed neighborhood and path. |
| `autodiff_path_0_1` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (0,1) on its prescribed neighborhood and path. |
| `autodiff_path_0_2` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (0,2) on its prescribed neighborhood and path. |
| `autodiff_path_0_3` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (0,3) on its prescribed neighborhood and path. |
| `autodiff_path_0_4` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (0,4) on its prescribed neighborhood and path. |
| `autodiff_path_1_0` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (1,0) on its prescribed neighborhood and path. |
| `autodiff_path_1_1` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (1,1) on its prescribed neighborhood and path. |
| `autodiff_path_1_2` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (1,2) on its prescribed neighborhood and path. |
| `autodiff_path_1_3` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (1,3) on its prescribed neighborhood and path. |
| `autodiff_path_1_4` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (1,4) on its prescribed neighborhood and path. |
| `autodiff_path_2_0` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (2,0) on its prescribed neighborhood and path. |
| `autodiff_path_2_1` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (2,1) on its prescribed neighborhood and path. |
| `autodiff_path_2_2` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (2,2) on its prescribed neighborhood and path. |
| `autodiff_path_2_3` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (2,3) on its prescribed neighborhood and path. |
| `autodiff_path_2_4` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (2,4) on its prescribed neighborhood and path. |
| `autodiff_path_3_0` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (3,0) on its prescribed neighborhood and path. |
| `autodiff_path_3_1` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (3,1) on its prescribed neighborhood and path. |
| `autodiff_path_3_2` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (3,2) on its prescribed neighborhood and path. |
| `autodiff_path_3_3` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (3,3) on its prescribed neighborhood and path. |
| `autodiff_path_3_4` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (3,4) on its prescribed neighborhood and path. |
| `autodiff_path_4_0` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (4,0) on its prescribed neighborhood and path. |
| `autodiff_path_4_1` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (4,1) on its prescribed neighborhood and path. |
| `autodiff_path_4_2` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (4,2) on its prescribed neighborhood and path. |
| `autodiff_path_4_3` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (4,3) on its prescribed neighborhood and path. |
| `autodiff_path_4_4` | proof | Section 6.6 [sec:curve], Section A.7 [sec:shared], Theorem 6.1 [thm:dimer-area] | Certify strict area decrease for shared-edge contact-chart pair (4,4) on its prescribed neighborhood and path. |
| `gamma_convexity` | diagnostic | Section 6.5 [sec:gamma] | Recentered optional numerical check; exact formula proves the paper claim |
| `mitm_precluster1_case0` | proof | Lemma 5.1 [calc:pseudo1] | Shared-edge bound: outside-double-contact central triangle, total cutoff 2 a_crit. |
| `mitm_precluster1_case1` | proof | Lemma 5.1 [calc:pseudo1] | Shared-edge bound: midpoint contact at the nonshared length-1.8 endpoint, total cutoff 2 a_crit. |
| `mitm_precluster1_case2` | proof | Lemma 5.1 [calc:pseudo1] | Shared-edge bound: slider contact with either nonshared length 1.8, total cutoff 2 a_crit. |
| `mitm_precluster2_case0` | proof | Lemma 5.2 [calc:pseudo2] | Egressive-edge bound: outside-double-contact central triangle with sides at most 1.8, total cutoff 2 a_crit. |
| `mitm_precluster2_case1` | proof | Lemma 5.2 [calc:pseudo2] | Egressive-edge bound: midpoint contact on a shared-edge tie or nonshared length-1.8 boundary, retaining all three equalities. |
| `mitm_precluster2_case2` | proof | Lemma 5.2 [calc:pseudo2] | Egressive-edge bound: slider contact on a shared-edge tie or nonshared length-1.8 boundary, retaining all three equalities. |
| `mitm_precluster4_case0_experimental` | proof | Lemma 5.4 [calc:pseudo-area] | Pseudo-dimer pair-area bound 2 a_crit - epsilon_M; outside-double-contact peripheral with local AB=AC. |
| `mitm_precluster4_case1_experimental` | proof | Lemma 5.4 [calc:pseudo-area] | Pseudo-dimer pair-area bound 2 a_crit - epsilon_M; outside-double-contact peripheral with local BC=AC. |
| `mitm_precluster6_case1` | proof | Lemma 5.5 [calc:pseudo-area3] | Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge AB, outgoing edge BC; exceptional peripheral cap a_crit + 2 epsilon_M. |
| `mitm_precluster6_case2` | proof | Lemma 5.5 [calc:pseudo-area3] | Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge AB, outgoing edge AC; exceptional peripheral cap a_crit + 2 epsilon_M. |
| `mitm_precluster6_case3` | proof | Lemma 5.5 [calc:pseudo-area3] | Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge BC, outgoing edge AB; exceptional peripheral cap a_crit + 2 epsilon_M. |
| `mitm_precluster6_case4` | proof | Lemma 5.5 [calc:pseudo-area3] | Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge BC, outgoing edge AC; exceptional peripheral cap a_crit + 2 epsilon_M. |
| `mitm_precluster6_case5` | proof | Lemma 5.5 [calc:pseudo-area3] | Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge AC, outgoing edge AB; exceptional peripheral cap a_crit + 2 epsilon_M. |
| `mitm_precluster6_case6` | proof | Lemma 5.5 [calc:pseudo-area3] | Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge AC, outgoing edge BC; exceptional peripheral cap a_crit + 2 epsilon_M. |
| `mitm_calc_pent2_postcluster_case0` | proof | Lemma 5.14 [calc:large] | Non-large-angle pair bound 2 a_crit + epsilon_M: outside-double-contact central triangle. |
| `mitm_calc_pent2_postcluster_case1` | proof | Lemma 5.14 [calc:large] | Non-large-angle pair bound 2 a_crit + epsilon_M: shared edge AB, distinguished nonshared edge AC at length 1.8, with central contact. |
| `mitm_calc_pent2_postcluster_case2` | proof | Lemma 5.14 [calc:large] | Non-large-angle pair bound 2 a_crit + epsilon_M: shared edge AB, distinguished nonshared edge BC at length 1.8, with central contact. |
| `mitm_calc_pent2_postcluster_case3` | proof | Lemma 5.14 [calc:large] | Non-large-angle pair bound 2 a_crit + epsilon_M: shared edge BC, distinguished nonshared edge AC at length 1.8, with central contact. |
| `mitm_calc_pent2_postcluster_case4` | proof | Lemma 5.14 [calc:large] | Non-large-angle pair bound 2 a_crit + epsilon_M: shared edge BC, distinguished nonshared edge AB at length 1.8, with central contact. |
| `mitm_calc_pent3_6D_postcluster` | proof | Lemma 5.11 [calc:pent3] | Three-triangle bound 3 a_crit + epsilon_M: unrestricted six-dimensional central chart and two long-isosceles peripherals. |
| `mitm_calc_pent3AB_postcluster` | proof | Lemma 5.11 [calc:pent3] | Three-triangle bound 3 a_crit + epsilon_M: contact-central chart with peripherals on BC and AC; AB is unshared. |
| `mitm_calc_pent3BC_postcluster` | proof | Lemma 5.11 [calc:pent3] | Three-triangle bound 3 a_crit + epsilon_M: contact-central chart with peripherals on AB and AC; BC is unshared. |
| `mitm_calc_pent3AC_postcluster` | proof | Lemma 5.11 [calc:pent3] | Three-triangle bound 3 a_crit + epsilon_M: contact-central chart with peripherals on AB and BC; AC is unshared. |
| `mitm_calc_pent4_6D_postcluster` | proof | Lemma 5.12 [calc:pent4] | Four-triangle bound 4 a_crit: six-dimensional central chart and three subcritical outside-double-contact peripherals. |
| `mitm_dimer_isosceles_precluster` | proof | Lemma 5.10 [calc:dimer-isosc] | Exclude an outside-double-contact long-isosceles subcritical peripheral in a dimer pair with total area at most 2 a_crit. |
| `mitm_test1_centralpent_1237` | diagnostic | diagnostic:central | Existing central-chart diagnostic (1.2 debug cutoff, not 1.237) |
| `mitm_test1_centralpent_172` | diagnostic | diagnostic:central | Existing central-chart diagnostic (1.72 cutoff) |
