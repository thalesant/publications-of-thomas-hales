# Pentagon paper revision guide, 2016 through v009

The [2016–v008 comparison](pentagon_changes_2016v2_to_v008.md) gives the earlier changes in the authors’ order. The table below continues that record. All 168 numbered labels in v008 have the same numbers in v009. Page references in this table are printed pages of the v009 paper as originally released.

| v009 location | What to review |
|---|---|
| Introduction, pp. 2 and 5 | Added the Kallus–Kusner reference on local optimality. The numerical-check paragraph identifies what the supplementary suite checks in Theorem 9.9, including the quadrilateral bounds underlying the Case 1 table. |
| Corollary 2.16, p. 13 | The saturation argument inserts a periodic orbit of an additional pentagon. The proof distinguishes the two outer-edge lengths of the dimer kite and uses the pentagons at the endpoints to determine its neighbor. |
| Lemma 4.8, pp. 21–22 | An exact inequality gives the printed bound 1.72 directly from the squared distance. The catalogue identifies the historical Wolfram ID for the shear identity. The separate OCaml midpoint test uses the bound of this lemma. |
| Theorem 6.1, §6.2, p. 30, condition (5) | Specifies the translation of the outer pentagon with the second contact disregarded. |
| Theorem 6.1, end of §6.7, p. 36 | Kept the geometric proof of the exact area on the shear curve and removed the repeated Heron calculation. |
| Theorem 9.9, Case 4, p. 51 | Corrected the maximum diagonal to 2.9595. The isosceles area decreases and the fixed-circumradius area increases on the range of the common diagonal. The proof explains why opposite endpoints on each of the four equal subintervals give a lower bound for their sum. |
| §A.3, proof on pp. 58–59 | The four contact boundaries give interval sections at fixed pointer inclination. The proof locates the two extrema on a query rectangle, includes the interior stationary curve on a side of constant distance, and explains the outward-rounded comparisons at endpoints. All additional coordinate symbols belong to the proof. |
| §§A.10.3 and A.11.1, pp. 65–66 | The standard-coordinate area exclusions precede the shared-coordinate calculations. They cover the singular end in each case and retain the cutoff itself. |
| §A.12.1, p. 68 | The statement that the indicated edge is longest now has the area hypothesis used by the pin-T job. |
| §B.4.6, p. 75 | The stopping argument uses a sufficiently short descent at a compact minimum. Translation keeps the relative pentagon orientation fixed. |

## OCaml changes and their scope

| Location | Change |
|---|---|
| [Positive contact chart](../ocaml/banana.ml) | Enumerates the four true boundary arcs and the stationary curve from §A.3. The midpoint arc is split at its distance turning point. Arc endpoints, physical corners and rectangle corners are tested separately. Closed interval tests receive outward enclosures. The negative-height case follows by reflection. The inverse diagnostic chart keeps its earlier implementation. |
| [Pseudo-dimer angle guard](../ocaml/mitm-calcs.ml) | The angle must lie strictly between both bounds in Definition 5.13. A representative at the upper end of the period consequently survives. The five affected pseudo-dimer guard searches are the five named mitm_calc_pent2_postcluster_case jobs, numbered 0 through 4. The contact-angle routine has additional callers. |
| [Meet-in-the-middle search](../ocaml/meet-in-middle.ml) | The first cut now replaces the existing key. The reported hash length counts distinct keys. New round logs count additional subdivisions caused by Unstable in the central and peripheral searches separately. |
| [Dimer](../ocaml/dimer.ml) and [autodiff](../ocaml/autodiff.ml) | The neighborhood radius is defined in Dimer and reused by Autodiff. Removed an unused narrower side range in mitm-calcs.ml. The side range selected by the search is unchanged. |
| [Interval commentary](code_commentary.pdf) | Explains why partial-domain square roots and inverse trigonometric functions enclose the physical value at their geometric call sites, and why first- and second-derivative evaluation needs the separate guarded division. |
| [Regression tests](../tests/ocaml/tests.ml) | Tests the upper flush representative, the strict interior and lower endpoint, the midpoint chord outside the chart, forward contacts including chart boundaries and the stationary curve, the Lemma 4.8 bound, and the distinct hash-key count. |

## Verification and the two supplementary questions

The release preserves the Mathematica sources and the original 161-check report byte for byte. The manuscript association is rebuilt for v009. The new OCaml source inventory requires fresh execution. From the extracted package root in Linux or Ubuntu Bash, run

    python3 run.py --all --diagnostics
    python3 confirm.py --check

A separate numerical comparison used 2,400 rectangles and 1,501,614 incidences of forward-constructed contacts. All sampled receptor angles were within the extrema computed by an independent floating-point implementation. The proof for every rectangle is in §A.3. These comparisons do not execute the OCaml jobs.

Lemma 5.12 still asserts its area bound. The reviewers report an empty terminal contact domain in a separate search with both area caps raised. The released theorem and its proof use the weaker assertion. The source of the small round-five count differences in the earlier comparison of precluster6 cases 5 and 6 remains unidentified. The new split counters report the events on the current sources. The original logs do not contain those counters.

## Finding an earlier change in v009

Use the unchanged statement or section number from the [2016–v008 table](pentagon_changes_2016v2_to_v008.md). The following concordance lists the numbered labels whose starting page moved. Figures carry the prefix “Fig.” and appendix subsections retain their printed letters.

| v008 page | v009 page | Numbered locations beginning there |
|---:|---:|---|
| 5 | 6 | Fig. 2.1 |
| 6 | 7 | Fig. 2.4 |
| 7 | 8 | Fig. 2.6 |
| 11 | 12 | 2.12, 2.13 |
| 17 | 18 | Fig. 3.6 |
| 20 | 21 | 4.5 |
| 22 | 23 | Fig. 4.1 |
| 23 | 22 | 4.10 |
| 23 | 24 | §5 |
| 25 | 26 | 5.13 |
| 30 | 31 | §6.3 |
| 31 | 32 | 6.5 |
| 34 | 35 | Fig. 6.2 |
| 53 | 54 | 10.6 |
| 54 | 55 | 10.8 |
| 58 | 59 | §A.4 |
| 59 | 60 | Fig. A.4 |
| 60 | 61 | §A.7 |
| 62 | 63 | A.4, §A.9 |
| 63 | 64 | Fig. A.6 |
| 64 | 65 | Fig. A.7, §A.10.3 |
| 65 | 66 | Fig. A.8, §A.11.1 |
| 66 | 67 | §A.12, Fig. A.9, A.5 |
| 67 | 68 | §A.12.1, §B |
| 68 | 69 | §B.3 |
| 69 | 70 | B.1 |
| 70 | 71 | §B.4, B.2 |
| 71 | 72 | §B.4.1, §B.4.2 |
| 72 | 73 | B.3, §B.4.3 |
| 73 | 74 | §B.4.4, §B.4.5 |
| 74 | 75 | §B.4.6 |
| 75 | 76 | §B.4.8 |
