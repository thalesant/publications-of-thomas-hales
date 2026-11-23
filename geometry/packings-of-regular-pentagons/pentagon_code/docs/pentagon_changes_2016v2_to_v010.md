# Pentagon paper revision guide, 2016 through v010

This guide compares the 60-page arXiv:1602.07220v2 of 13 September 2016 with the 78-page manuscript `pentagon_v010.pdf`. Each reference to the 2016 paper is identified in its own column. Current page references are the page numbers printed in v010.

## The five changes from v009 to v010

Each of these proofs now states what it proves in its opening sentence. All 168 numbered labels agree with v009, including the lemma and equation numbers in Appendix A. The verification code is v006.

| Passage | v009 proof opening | v010 proof opening | Claim identified at the outset |
|---|---:|---:|---|
| Lemma 2.12 | p. 12 | p. 12 | A lower bound $a$ on the cluster averages yields the density bound $\mathrm{area}_P/(2a)$. |
| After Definition 3.9 | p. 18 | p. 18 | Every triple contact is a limit of configurations of one of the five types in which each pointer meets the relative interior of its receptor edge. The proof ends on p. 19. |
| Lemma 5.14 | p. 26 | p. 26 | The interval calculation in §B.4.6 gives the stated strict lower bound on the sum of the two triangle areas. |
| Lemma 9.2 | p. 43 | p. 44 | Under the hypotheses of the lemma, $2\kappa\le d_3'<d_3$ implies $\theta<\pi$ and $2\eta\sin(\theta/2)\le d_2$. |
| §A.3 | p. 58 | p. 59 | For a closed rectangle in the inclination–distance plane, the computed interval contains $\theta$ for every represented contact $B\to A$ with $h\ge 0$. An empty result rules out such a contact. The proof ends on p. 60. |

## Changes introduced in v009, located in v010

| Passage in v010 | Change |
|---|---|
| Introduction, pp. 2 and 5 | Added the Kallus–Kusner reference on local optimality. The paragraph on numerical checks explains what the supplementary Wolfram suite checks for the Case 1 table of Theorem 9.9. |
| Corollary 2.16, p. 13 | Saturation follows by inserting a periodic orbit of an additional pentagon. The edge lengths of the dimer kite and the pentagons at the endpoints determine its neighbor. |
| Lemma 4.8, p. 22 | An exact inequality on the squared distance gives the bound $1.72$. Code v006 has a separate OCaml test for this lemma. The historical Wolfram identifier for the shear identity is explained below. |
| Theorem 6.1, §6.2, p. 30, condition (5) | Specifies the translation of the outer pentagon when its second contact is disregarded. |
| Theorem 6.1, end of §6.7, p. 36 | The determinant calculation gives the exact area along the shear curve. The repeated Heron calculation was removed. |
| Theorem 9.9, Case 4, pp. 51–52 | The maximum diagonal rounds to $2.9595$. On p. 52 the isosceles area decreases and the fixed-circumradius area increases. Evaluating them at opposite endpoints gives a lower bound on each of the four equal intervals. |
| §A.3, pp. 58–60 | At each fixed pointer inclination the nonempty section is an interval. The proof identifies where the extrema can occur, including the stationary point on a side of constant distance, and explains why outward-rounded tests retain a common endpoint. |
| §§A.10.3 and A.11.1, pp. 66–67 | The area exclusions in standard coordinates cover the singular end of each shared chart and retain the cutoff itself. |
| §A.12.1, p. 68 | The assertion that the indicated pin-$T$ edge is longest now carries the area hypothesis used in the calculation. |
| §B.4.6, pp. 75–76 | A short descent at a minimum suffices for the stopping argument. Translation preserves the relative orientation of the pentagons. |

## Where to find the changes since 2016

The rows follow the 2016 paper. The original referee report is `report_Y_on_v2.pdf`. The current column gives v010 pages, including cases where an illustration and the surrounding statement fall on different pages.

| Original location (2016) | Current location (v010) | Change |
|---|---|---|
| Throughout; §§11–12 | Throughout, particularly Appendices A and B | Section-based numbering introduced; former §§11–12 become appendices. |
| §1, pp. 2–3 | §1, pp. 2–3 | Density, periodic approximation, saturation, and degeneracy conventions expanded. |
| End of §2, Theorem 14, p. 10; referee general request | §1, pp. 3–5, and Theorem 2.15, p. 13 | Proof roadmap added; placed in the introduction rather than at the end of §2. |
| §2, constants on p. 3 and modified area on p. 7 | Equations (2.1)–(2.2), p. 5, Figure 2.1, p. 6, and Equation (2.6), p. 10 | Constants collected and recalled; referee change implemented. |
| §2.2, pp. 7–8; general exposition request | §2.2, pp. 6–11, especially Figure 2.8 on p. 10 | New area-transfer illustration; motivation and local explanations expanded. |
| Lemma 10, p. 9 | Lemma 2.11, p. 11 | Proof expanded. |
| Lemma 11, pp. 9–10 | Lemma 2.12 and proof, p. 12 | Periodic-quotient argument clarified. The statement on p. 12 requires $a>0$. |
| Remark 15, p. 10 | Corollary 2.16 and proof, p. 13 | Remark replaced by a corollary with a geometric uniqueness proof. |
| §3.1, pp. 10–11 | §3.1, pp. 13–14 | Angle convention made explicit. |
| Figure 9, p. 12 | Figure 3.2, p. 15 | Contact-type diagrams enlarged and supplemented by distorted inner polygons; referee change implemented. |
| Lemmas 16–18 and Figure 11, pp. 12–13 | Lemmas 3.1–3.3 and Figure 3.4, pp. 16–17 | Separation proofs and degeneracies explained; diagram annotated. |
| Lemmas 22–23, pp. 13–14 | Lemmas 3.7–3.8, pp. 17–18, and the proof after Definition 3.9, pp. 18–19 | Contact-classification proofs expanded. The pin-1 and pin-3 exclusions assume that each pointer meets the relative interior of an edge. The proof of Lemma 3.7 uses the three pointers and the inner vertex. After Definition 3.9 a new proof obtains every triple contact as a limit of contacts of one of the five types. It includes coincident vertices and contact along an edge. The final paragraph on p. 19 proves that the triangle of centers is acute. |
| Lemma 26, p. 15 | Lemma 4.2, p. 20 | Obtuse-edge bound added explicitly. |
| Lemmas 29–30, p. 15 | Lemmas 4.5–4.6 and their proofs, p. 21 | Conclusions and common proof revised to endpoint minimization. |
| Lemma 33 and Figure 14, pp. 16–17 | Lemma 4.9, pp. 22–23, and Figure 4.1, p. 23 | Simultaneous-minimum and slider arguments expanded; figure revised. The pinwheel calculation for this lemma now covers the full angle domain. |
| Lemmas 34–35, p. 17 | Lemmas 4.10–4.11, pp. 23–24 | Double-contact statement and minimum-area proofs revised. The pinwheel calculation for the area bound in Lemma 4.11 uses the same enlarged domain. |
| Lemmas 36–38, pp. 17–18; §§12.4.1–12.4.2, p. 57 | Lemmas 5.1–5.3, p. 24, and §§B.4.1–B.4.2, pp. 72–74 | Tie cases added; terminal reductions and corresponding calculations revised. Referee correction to the dropped attachment condition implemented. The preparation for Lemma 5.1 on pp. 72–73 fixes the shared pentagons and minimizes the height under the side constraint. It rules out a right triangle at the minimum. |
| Lemma 39, p. 18; §12.4.3, pp. 57–58 | Lemma 5.4, p. 24, §6.4, pp. 33–34, and §B.4.3, p. 74 | Bound made strict; preparation revised; omitted pin-T shared-edge case excluded by supplementary calculations. The proof in §B.4.3 specifies when squeezing reaches a tie or a contact. For twelve ordered pairs it uses stage 4 outside $U$ and stages 6–7 inside $U$, including when the shared edge is not longest on $T_0$. The pinwheel part of the small-side calculation now covers the full angle domain. |
| Lemma 40 and Corollary 41, p. 18; §12.4.4, p. 58 | Lemma 5.5 and Corollary 5.6, pp. 24–25, and §B.4.4, pp. 74–75 | Nonobtuseness hypothesis added; bound, citations, squeezing explanation, and peripheral calculation domain revised. Referee changes implemented. The argument for Lemma 5.5 uses the fixed-edge reduction on $T_1$ and Lemma B.2 on $T_-$. It explains why squeezing must reach contact and identifies the two additional cases with contact on the edge shared with $T_1$. |
| Corollary 42, p. 18 | Corollary 5.7 and proof, p. 25 | The target of an $\mathcal M$-pair is nonobtuse, so Corollary 5.6 applies. |
| Definition 44, p. 18 | Definition 5.9, p. 25 | Outside-double-contact definition generalized to adjacent pairs. |
| Lemma 45, p. 18, and §12.4.5 | Lemma 5.10, p. 25, its use on p. 32, and §B.4.5, p. 75 | The calculation keeps the shared edge tied for longest on subcritical $T_1$. It allows either order of the two nonshared edges on $T_0$ and includes the case where $T_0$ is supercritical. |
| Definition 46 and Figure 15, p. 18 | Definition 5.13 and Figure 5.1, p. 26 | Large-angle convention defined for noncontacting pentagons; referee change implemented. |
| Lemma 47, pp. 18–19; §12.4.6, pp. 58–59 | Lemma 5.14, p. 26, and §B.4.6, pp. 75–76 | Nonobtuseness hypothesis added; terminal reduction and right-angle exclusion revised. |
| Lemmas 49–50, p. 19; §§12.4.7–12.4.8, p. 59 | Lemmas 5.11–5.12, p. 25, and §§B.4.7–B.4.8, pp. 76–77 | Lemmas moved earlier; nonobtuseness hypotheses added; preparation expanded. For Lemma 5.11, §B.4.7 keeps a peripheral triangle fixed once it reaches a tie. The motion stops at the first contact in the central triangle or when both peripherals have reached a tie. |
| Theorem 51 and proof outline, pp. 19–20 | Theorem 6.1 and proof outline, pp. 27–28 | Closed-domain minimum framework and strict-descent explanation added. The proof uses the area-decreasing motions as local tests at a pair of least area. |
| §§6.1–6.2, pp. 20–22 | §§6.1–6.2, pp. 28–31 | Deformation constraints and stopping events clarified; referee change implemented. On p. 28 a short descending slide preserves a strict longest-edge inequality. On p. 30 condition (5) requires that the translation decreasing the angle at the center of $A$ does not shorten $d_{AB}$. The text identifies the signed inclination used in each of the two calculations. The last paragraph of §6.2 obtains outside double contact with the shared pentagons fixed and the shared edge still a longest edge. |
| Lemmas 53–54, pp. 21–22 | Lemmas 6.3–6.4 and their proofs, pp. 29–30 | Local-motion proofs revised; no-contact hypothesis added to Lemma 6.4. The two incircles determine the direction of the downhill slide. The midpoint in Lemma 6.4 is a vertex of $A$ on an edge of $B$. |
| §6.3 and Lemma 55, pp. 22–23 | §6.3, pp. 31–33, especially Lemma 6.5, pp. 32–33 | Squeezing construction and proof revised; four contact-sign calculations added. On p. 32 the proof treats the two longest-edge ties separately. A tie on subcritical $T_1$ uses Lemma 5.10 and §B.4.5, including when $T_0$ is supercritical. At a vertex, the end of the proof of Lemma 6.5 follows the two actual contact segments for equal rises in height (p. 33). |
| §6.3, p. 23, unnumbered area observation | Lemma 6.6, Equation (6.7), and the paragraph following the proof, p. 33 | New numbered lemma and proof. After the proof of Lemma 6.6, a height estimate shows that the two outer pentagons stay apart while both areas decrease. |
| §§6.4–6.6, pp. 23–25 | §§6.4–6.6, pp. 33–35, and §A.7, pp. 61–63 | Neighborhood and path conventions clarified; finite-flow and stationary-coordinate cases explained; LJ₁ face calculation added. In §A.7 the pinwheel and $TJ_3$ inequalities give the restrictions on the shared angle (p. 63). The five choices on each side are listed on p. 63, including the cases with a coordinate fixed at zero. |
| §6.7, pp. 25–26 | §6.7, pp. 35–36, and §B.2, pp. 69–70 | Numerical convexity argument replaced by exact geometric area proof. Section B.2 cites the exact area on $\Gamma$, $2a_{\mathrm{crit}}+\sigma t^2$, and identifies its unique minimum at $t=0$. |
| Lemma 56, p. 26 | Lemma 7.1 and proof, p. 37 | Proof expanded and supporting lemmas cited; referee change implemented. |
| Lemmas 59–62, pp. 27–28 | Lemmas 7.4–7.7, pp. 37–39 | Proofs and correction-term arguments clarified. |
| Corollary 66, p. 29 (report calls it “Lemma 66”) | Corollary 8.4, pp. 39–40 | Statement and proof notation corrected; referee change implemented. |
| Lemmas 68–70, pp. 29–30 | Lemma 8.6, Corollary 8.7, and Lemma 8.8, pp. 40–41 | Edge-bound justifications and source-triangle distinctions clarified; referee changes implemented. |
| Proof of Theorem 63, p. 31 | Proof of Theorem 8.1, p. 42 | Unique attachment target explained; notation and supporting citation corrected. Referee changes implemented. The proof treats a third triangle attaching to $T_0$ by Lemma 8.10 if it is nonobtuse and by Lemma 8.6 if it is obtuse. |
| Corollary 74, p. 31 | Between Lemmas 8.11 and 8.12, p. 42 | Corollary deleted. |
| §9 notation and Remark 78, p. 32 | §9 and Remark 9.1, p. 43 | Circumradius-area notation changed; Delaunay explanation expanded. Referee notation request implemented. |
| Lemma 80, p. 33 | Lemmas 9.3–9.4, pp. 44–45 | New monotonicity lemma; deformation and radius-bound explanations supplied. Referee changes implemented. |
| Theorem 82, p. 34; Lemma 87, pp. 35–36 | Theorem 9.6, p. 45, and Lemma 9.11, pp. 46–47 | Cluster-identification and external-transfer proofs expanded. |
| Proof of Theorem 85, Case 1, pp. 36–37 | Proof of Theorem 9.9, Case 1, pp. 48–50 | Quadrilateral deformation, boundary cases, and trapezoid reduction expanded; referee change implemented. |
| Same proof, Cases 2–3, pp. 37–38; Equation (89), p. 37 | Lemma 9.12, p. 47, Cases 2–3 of Theorem 9.9, pp. 50–51, and Equation (9.14), p. 50 | New radius-area lemma; proofs revised; side parameters and asymmetric estimate explained. Referee changes implemented. Case 2 identifies $T_0$ as the central triangle and the triangles attached along its edges as peripheral (p. 50). |
| Same proof, Case 4, pp. 38–39 | Theorem 9.9, Case 4, pp. 51–52 | Relaxed constraints and stopping conditions clarified. |
| Lemma 91, p. 39 | Lemma 10.1, pp. 52–53 | Statement and proof revised to distinguish regular and exceptional peripherals. |
| Lemma 92, pp. 39–40 | Lemma 10.2, p. 53 | False local triangle bound withdrawn; replaced by a structural lemma for exceptional peripherals. |
| Figure 19, p. 40 | Removed (formerly Figure 10.1 in manuscript v005) | Figure supporting the withdrawn lemma removed. |
| Lemma 94, p. 40 | Lemma 10.4, p. 53 | Regularity hypothesis added; proof revised. |
| Lemma 95, pp. 40–41 | Lemma 10.5, p. 54 | Four-triangle proof revised to include the exceptional-peripheral case. |
| Lemma 96, p. 41 | Lemma 10.6, pp. 54–55 | Three-triangle proof revised to include the exceptional-peripheral case. |
| Lemma 97, pp. 41–42 | Lemma 10.7 and proof, pp. 55–56 | Exceptional peripheral excluded for a two-triangle cluster; final counting argument expanded. |
| §§11.2–11.7, pp. 43–48 | §§A.2–A.7, pp. 57–63 | Coordinate conventions, shared-edge identities, and path description corrected or clarified. |
| §11.9.1, pinwheel with a shared edge | §A.9.1, p. 65 | The text gives the area bound for $x_\gamma\ge 0.8$. Cyclic relabeling gives the same cutoff for the other two offsets. |
| §§11.10.3–11.12.1, pp. 50–53; referee comments on pp. 51–53 | §A.10.3, p. 66, §§A.11.1–A.11.2, p. 67, and §A.12.1, p. 68 | Ambiguous ice-ray/shared-edge statements rewritten; coordinate-domain bounds clarified. |
| §12 and §12.1, pp. 53–54 | Appendix B and §B.1, p. 69 | Interval-backend description updated; original timing identified as historical. |
| §12.3, pp. 54–56 | §B.3, pp. 70–71, and the meet-in-the-middle control in code v006 | Geometric positive-control test added (code only). On p. 71 the two inclinations refer to the same ordered endpoints on both sides. The text accounts for endpoint exchange and identifies $A$ as the pointer on the shared edge $AC$ in the five-dimensional coordinates. |
| §12.4 and Lemma 106, pp. 56–57 | §B.4 and Lemma B.2, pp. 71–72 | Nonobtuseness stated; peripheral reduction and proof expanded. Lemma B.2 excludes a right triangle for the exceptional peripheral using its own area bound. The following paragraph treats the subcritical peripherals with the shared edge fixed. The display on p. 72 collects ten side bounds from monotonicity and Heron’s formula. |
| Reference [2], p. 59 | Reference [2], p. 77 | Published bibliographic details supplied; referee change implemented. |
| Bibliography, entries for Dye and Henley, and the references to the companion code | References [4], [5], and [7], p. 77 | The entries identify the publisher of Dye’s 1937 edition, the code and its source fingerprint (now v006), and the full page range of Henley’s paper. |
| Code references and calculation footnotes; referee general request, report pp. 1–2 | Code v006, in `docs/index.html`, `docs/CALCULATIONS.md`, and `docs/code_commentary.pdf` | Code reorganized; statement-to-function navigation, mathematical commentary, tests, and reproduction instructions supplied. |

## Referee follow-up

| Referee request | Location or status in v010 |
|---|---|
| Report p. 2 requests a repository, file, and function locator for each computer-assisted statement. | In code v006, docs/index.html maps the statement number and source label to the computation identifier and code. The mathematical commentary is docs/code_commentary.pdf. The referee requested these locators in the paper itself. |
| Report p. 3 reads “P. 31. Proof of Lemma 72. Lemma 26 is used here but not mentioned.” | Original Lemma 72 is on p. 30. Original p. 31 contains the proof of Theorem 63 and Lemma 73. In v010 their counterparts, the proof of Theorem 8.1 and Lemma 8.11 on p. 42, both cite Lemma 4.2 (original Lemma 26). The literal counterpart of original Lemma 72 is Lemma 8.10 on p. 41. Its proof has no explicit citation to Lemma 4.2. |

## Companion calculations

The following changes were introduced in code v006 alongside manuscript v009. The five v010 edits concern the prose of the paper. Paths in this table are relative to the v006 package root.

| File | Change in code v006 |
|---|---|
| `ocaml/banana.ml` | The positive contact chart enumerates four boundary arcs and the stationary curve in §A.3. The midpoint arc is split at its distance turning point. The routine checks arc endpoints and rectangle corners and uses closed intervals. Reflection gives the negative-height case. |
| `ocaml/mitm-calcs.ml` | The pseudo-dimer test applies both strict bounds in Definition 5.13, $\pi/5<\alpha<2\pi/5$. This retains a flush contact represented at the upper endpoint of the period. Definition 5.13 itself has identical wording in v008, v009 and v010. The guard occurs in the five postcluster jobs numbered 0 through 4. |
| `ocaml/meet-in-middle.ml` | The first cut replaces the existing key, so the reported hash-table length counts distinct keys. Round logs record additional central and peripheral subdivisions caused by Unstable separately. |
| `ocaml/dimer.ml`, `ocaml/autodiff.ml`, `ocaml/mitm-calcs.ml` | Dimer defines the neighborhood radius used by Autodiff. An unused narrower side range was removed from mitm-calcs.ml. |
| docs/code_commentary.pdf | Gives the geometric justification for partial-domain square roots and inverse trigonometric functions, and the denominator check needed for first and second derivatives. |
| `tests/ocaml/tests.ml` | Adds checks for the flush endpoint and strict angle bounds, the midpoint chord outside the chart, forward contacts and chart boundaries, the Lemma 4.8 midpoint distance, and the distinct-key count. |
| `docs/WOLFRAM_CHECKS.md` | The historical ID `contact.midpointer-length` denotes the shear specialization. The OCaml test for the midpoint estimate of Lemma 4.8 is `contact.midpointer-lemma-4.8`. |

The v006 release carries forward the 161-check Mathematica report on the same component. The original assembly association recorded v009. The published assembly identifies v010 and its compiled label map. The 77 required OCaml stages and four optional diagnostics belong to v006. The v010 editorial changes require no additional calculation. For the execution record of a particular run, consult `verification/CONFIRMATION.md` in that copy.

A separate numerical comparison for §A.3 used 2,400 rectangles and 1,501,614 incidences of forward-constructed contacts. All sampled receptor angles lay between the extrema computed by an independent floating-point implementation. The argument for arbitrary rectangles is on pp. 59–60.

Two supplementary questions remain as recorded for v009. Lemma 5.12 uses its area bound. The independent reviewers reported an empty terminal domain when both area caps were raised. The small round-five differences in the earlier comparison of precluster6 cases 5 and 6 have no established explanation in the original logs.

## Page concordance for earlier readers

The table lists numbered locations whose starting page moved between v008, v009 and v010. Each entry refers to the same numbered object in all three versions. The five proof-opening references at the start of this guide give the pages of the proofs themselves.

| v008 | v009 | v010 | Location |
|---:|---:|---:|---|
| 5 | 6 | 6 | Fig. 2.1 |
| 6 | 7 | 7 | Fig. 2.4 |
| 7 | 8 | 8 | Fig. 2.6 |
| 11 | 12 | 12 | Lemma 2.12, (2.13) |
| 17 | 18 | 18 | Fig. 3.6 |
| 19 | 19 | 20 | §4 |
| 20 | 21 | 21 | Lemma 4.5 |
| 21 | 21 | 22 | Lemma 4.8 |
| 22 | 23 | 23 | Fig. 4.1 |
| 23 | 22 | 23 | Lemma 4.10 |
| 23 | 24 | 24 | §5 |
| 24 | 24 | 25 | Cor. 5.7 |
| 25 | 26 | 26 | Def. 5.13 |
| 26 | 26 | 27 | §6, Thm. 6.1 |
| 30 | 31 | 31 | §6.3 |
| 31 | 32 | 32 | Lemma 6.5 |
| 34 | 34 | 35 | §6.6 |
| 34 | 35 | 35 | Fig. 6.2 |
| 36 | 36 | 37 | Lemma 7.1 |
| 37 | 37 | 38 | Cor. 7.5, Lemma 7.6 |
| 38 | 38 | 39 | §8, Thm. 8.1 |
| 39 | 39 | 40 | Lemma 8.5 |
| 40 | 40 | 41 | Lemma 8.8, (8.9) |
| 42 | 42 | 43 | Lemma 8.14 |
| 44 | 44 | 45 | Lemma 9.5 |
| 45 | 45 | 46 | Lemma 9.10 |
| 46 | 46 | 47 | Lemma 9.12 |
| 50 | 50 | 51 | (9.15) |
| 52 | 52 | 53 | Lemma 10.2 |
| 53 | 53 | 54 | Lemma 10.5 |
| 53 | 54 | 54 | Lemma 10.6 |
| 54 | 54 | 55 | Lemma 10.7 |
| 54 | 55 | 55 | (10.8) |
| 56 | 56 | 57 | Fig. A.1, (A.1), §A.2 |
| 57 | 57 | 58 | §A.3 |
| 58 | 58 | 59 | Fig. A.3 |
| 58 | 59 | 60 | §A.4 |
| 59 | 60 | 60 | Fig. A.4 |
| 60 | 61 | 61 | §A.7 |
| 62 | 63 | 63 | (A.4) |
| 62 | 63 | 64 | §A.9 |
| 63 | 63 | 64 | Fig. A.5 |
| 63 | 64 | 64 | Fig. A.6 |
| 64 | 65 | 65 | Fig. A.7 |
| 64 | 65 | 66 | §A.10.3 |
| 65 | 66 | 66 | Fig. A.8 |
| 65 | 66 | 67 | §A.11.1 |
| 66 | 67 | 67 | §A.12 |
| 66 | 67 | 68 | Fig. A.9, Lemma A.5 |
| 67 | 68 | 68 | §A.12.1 |
| 67 | 68 | 69 | §B |
| 68 | 68 | 69 | §B.2 |
| 68 | 69 | 70 | §B.3 |
| 69 | 70 | 71 | (B.1) |
| 70 | 71 | 71 | §B.4 |
| 70 | 71 | 72 | Lemma B.2 |
| 71 | 72 | 72 | §B.4.1 |
| 71 | 72 | 73 | §B.4.2 |
| 72 | 73 | 73 | (B.3) |
| 72 | 73 | 74 | §B.4.3 |
| 73 | 74 | 74 | §B.4.4 |
| 73 | 74 | 75 | §B.4.5 |
| 74 | 75 | 75 | §B.4.6 |
| 75 | 75 | 76 | §B.4.7 |
| 75 | 76 | 77 | §B.4.8 |
