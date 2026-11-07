# Wolfram check catalogue — manuscript v005

Each record below states **what is tested, why, and how it relates to the paper**. The displayed paper reference identifies context; the logical role distinguishes a paper assertion from an auxiliary identity or finite diagnostic. All constants use circumradius-one normalization.

## Notation and scope

`k=κ=cos(π/5)`, `s=σ=sin(π/5)`, `aK=a_crit`, `amin=1237/1000`, `epsN=aK-amin`, `epsM=1/125`. `triangleArea[a,b,c]` is Heron’s formula; `circleArea[a,b,r]` is the specified obtuse branch with short sides a,b and radius r. `positive[u]` means exact algebraic positivity, not a decimal tolerance.

Definitions and references are in `mathematica/PentagonChecks.wl`. The `condition` shown is the actual assertion template from that file; loop indices and selected side assignments are explained in each family. EXACT examples remain finite examples unless the assertion is symbolic or bounds a complete cell by a stated monotonicity argument. Numerical diagnostics use a fixed seed, 80 digits by default, and tolerance 10^-40.

To execute, follow [the package README](../mathematica/README.md). No OCaml run is triggered by this suite. The complete expected set is 161 IDs; a partial section run cannot supply a complete confirmation.

## constants (16 checks)

### `constants.kappa-radical` — Pentagon inradius

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 1 [sec:intro].

**Assertion:** κ = cos(π/5) = (1+√5)/4

**Why:** Identifies the exact constant used by all center-separation bounds.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:69`; navigation code `VNDQIXO`.

```wolfram
exactZero[k-(1+Sqrt[5])/4]
```

### `constants.sigma-radical` — Half side length

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 1 [sec:intro].

**Assertion:** σ = sin(π/5) = √(10−2√5)/4

**Why:** Identifies the exact contact-coordinate length scale.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:70`; navigation code `VNDQIXO`.

```wolfram
exactZero[s-Sqrt[10-2 Sqrt[5]]/4]
```

### `constants.acrit-radical` — Critical triangle area

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 1 [sec:intro].

**Assertion:** a_crit = 3(1+κ)κσ/2 = 3√(5(5+2√5))/16

**Why:** Connects the ice-ray cell area to the radical expression in the introduction.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:71`; navigation code `VNDQIXO`.

```wolfram
exactZero[aK-3 Sqrt[5 (5+2 Sqrt[5])]/16]
```

### `constants.density` — Optimal packing density

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 1 [sec:intro].

**Assertion:** 5κσ / (2a_crit) = (5−√5)/3

**Why:** Divides the area of one pentagon by the area per center in the ice-ray packing.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:72`; navigation code `VNDQIXO`.

```wolfram
exactZero[5 k s/(2 aK)-(5-Sqrt[5])/3]
```

### `constants.pentagon-area` — Area of one pentagon

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section 1 [sec:intro].

**Assertion:** 5κσ = (5/2) sin(2π/5)

**Why:** Checks the decomposition into five isosceles triangles of circumradius one.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:73`; navigation code `VNDQIXO`.

```wolfram
exactZero[5 k s-5 Sin[2 Pi/5]/2]
```

### `constants.pythagorean` — Trigonometric normalization

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section 1 [sec:intro].

**Assertion:** κ² + σ² = 1

**Why:** A basic identity used to simplify the contact formulas.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:74`; navigation code `VNDQIXO`.

```wolfram
exactZero[k^2+s^2-1]
```

### `constants.golden-ratio` — Algebraic normalization

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section 1 [sec:intro].

**Assertion:** 4κ² − 2κ − 1 = 0

**Why:** Checks the quadratic relation used in exact pentagon simplifications.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:75`; navigation code `VNDQIXO`.

```wolfram
exactZero[4 k^2-2 k-1]
```

### `rounding.density` — Density decimal

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 1 [sec:intro].

**Assertion:** |(5−√5)/3 − 0.921311| < 1/(2·10^6)

**Why:** Checks the stated nearest-decimal precision, not equality with a machine float.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:76`; navigation code `VNDQIXO`.

```wolfram
rounded[(5-Sqrt[5])/3,921311/10^6,6]
```

### `rounding.kappa` — Inradius decimal

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 1 [sec:intro].

**Assertion:** |κ − 0.809| < 1/(2·10^3)

**Why:** Checks the stated nearest-decimal precision, not equality with a machine float.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:77`; navigation code `VNDQIXO`.

```wolfram
rounded[k,809/1000,3]
```

### `rounding.sigma` — Half side length decimal

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 1 [sec:intro].

**Assertion:** |σ − 0.5878| < 1/(2·10^4)

**Why:** Checks the stated nearest-decimal precision, not equality with a machine float.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:78`; navigation code `VNDQIXO`.

```wolfram
rounded[s,5878/10000,4]
```

### `rounding.acrit` — Critical area decimal

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 1 [sec:intro].

**Assertion:** |a_crit − 1.29036| < 1/(2·10^5)

**Why:** Checks the stated nearest-decimal precision, not equality with a machine float.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:79`; navigation code `VNDQIXO`.

```wolfram
rounded[aK,129036/100000,5]
```

### `rounding.epsilonN` — Area correction decimal

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Equation 2.1 [eqn:epsN].

**Assertion:** |epsilon_N − 0.05336| < 1/(2·10^5)

**Why:** Checks the stated nearest-decimal precision, not equality with a machine float.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:80`; navigation code `VNDQIXO`.

```wolfram
rounded[epsN,5336/100000,5]
```

### `constants.corrections-ordered` — Order of correction constants

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Equation 2.2 [eqn:epsM].

**Assertion:** epsilon_N > epsilon_M > 0

**Why:** Justifies replacing an epsilon_M charge by the larger epsilon_N charge.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:81`; navigation code `VNDQIXO`.

```wolfram
positive[epsN-epsM]&&positive[epsM]
```

### `constants.midpointer-rounded` — Midpointer threshold decimal

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 4.8 [lemma:mid-172].

**Assertion:** |√(4κ²+σ²)−1.72149| < 0.000005

**Why:** Checks the numerical value used to compare a midpoint contact with 1.72.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:82`; navigation code `VNDQIXO`.

```wolfram
rounded[Sqrt[4 k^2+s^2],172149/100000,5]
```

### `constants.sqrt8-kappa-rounded` — Right-triangle threshold decimal

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 4.2 [lemma:right].

**Assertion:** |√8 κ−2.288| < 0.0005

**Why:** Checks the printed circumradius/side threshold.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:83`; navigation code `VNDQIXO`.

```wolfram
rounded[Sqrt[8] k,2288/1000,3]
```

### `constants.rational-inputs` — Exact rational constants

**Role:** Implementation check. **Method:** EXACT. **Paper:** Equation 2.2 [eqn:epsM].

**Assertion:** a_min=1237/1000 and epsilon_M=1/125 are exact Rational objects

**Why:** Prevents accidental introduction of machine-precision thresholds in the symbolic suite.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:84`; navigation code `VNDQIXO`.

```wolfram
Head[amin]===Rational&&Head[epsM]===Rational
```

## triangle-bounds (45 checks)

### `bound.lemma21` — Upper side bound for a subcritical triangle

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 4.1 [lemma:21].

**Assertion:** area(2.1,2κ,2κ) > a_crit

**Why:** Together with area monotonicity, excludes a side of length at least 2.1.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:87`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[21/10,2 k,2 k]-aK]
```

### `bound.right-gap` — Comparison with the right-triangle threshold

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 4.2 [lemma:right].

**Assertion:** κ√8 > 2.1

**Why:** The side bound makes a nonobtuse subcritical triangle acute.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:88`; navigation code `VNDQIXO`.

```wolfram
positive[k Sqrt[8]-21/10]
```

### `bound.midpointer` — Midpointer distance exceeds the short-edge bound

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 4.8 [lemma:mid-172].

**Assertion:** √(4κ²+σ²) > 1.72

**Why:** Excludes midpoint contact in the all-sides-at-most-1.72 reduction.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:89`; navigation code `VNDQIXO`.

```wolfram
positive[Sqrt[4 k^2+s^2]-43/25]
```

### `bound.pseudo3` — Two long sides force excessive area

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 5.3 [calc:pseudo3].

**Assertion:** area(1.72,1.8,1.8) > a_crit+epsilon_N

**Why:** Supplies the last numerical inequality in the third pseudo-dimer length bound.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:90`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[43/25,9/5,9/5]-(aK+epsN)]
```

### `bound.pseudo-table-111` — Three sides at least 1.8

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 8.3 [lemma:pd-nra-dimer].

**Assertion:** area(1.8,1.8,1.8) > a_crit+0.112

**Why:** Checks a row of the area table used in the pseudo-dimer charging argument.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:91`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[9/5,9/5,9/5]-(aK+112/1000)]
```

### `bound.pseudo-table-110` — Two sides at least 1.8 and one at least 1.72

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 8.3 [lemma:pd-nra-dimer].

**Assertion:** area(1.8,1.8,1.72) > a_crit+0.069

**Why:** Checks the corresponding two-large-side row of that table.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:92`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[9/5,9/5,43/25]-(aK+69/1000)]
```

### `bound.pseudo-table-100` — One large and two subcritical shared sides

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 8.3 [lemma:pd-nra-dimer].

**Assertion:** area(1.8,1.72,1.72) > a_crit+3epsilon_M

**Why:** Checks the correction allowance in the one-large-side row.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:93`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[9/5,43/25,43/25]-(aK+3 epsM)]
```

### `bound.pseudo-table-11min` — Two large sides and the center-separation bound

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 8.3 [lemma:pd-nra-dimer].

**Assertion:** area(1.8,1.8,2κ) > a_crit+epsilon_M

**Why:** Checks the weaker third-side row of the area table.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:94`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[9/5,9/5,2 k]-(aK+epsM)]
```

### `bound.obtuse-neighbor` — Neighbor across an obtuse hypotenuse

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 8.13 [lemma:Nb].

**Assertion:** area(κ√8,2κ,1.72) > a_crit+epsilon_N

**Why:** Provides the numerical excess used by the obtuse-neighbor estimate.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:95`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[k Sqrt[8],2 k,43/25]-(aK+epsN)]
```

### `bound.two-nonobtuse` — Charged nonobtuse triangle beside an obtuse one

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** area(κ√8,1.72,1.72) > a_crit+2epsilon_N

**Why:** Checks the stronger lower bound when both other sides are charged.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:96`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[k Sqrt[8],43/25,43/25]-(aK+2 epsN)]
```

### `bound.two-mcorrections` — Two small corrections on a nonobtuse neighbor

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** area(κ√8,1.72,2κ) > a_crit+2epsilon_M

**Why:** Checks an alternative correction budget in the obtuse case analysis.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:97`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[k Sqrt[8],43/25,2 k]-(aK+2 epsM)]
```

### `bound.three-m` — Three small corrections plus one large correction

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** area(1.8,1.8,1.8) > a_crit+3epsilon_M+epsilon_N

**Why:** Checks the total excess for that side pattern.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:98`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[9/5,9/5,9/5]-(aK+3 epsM+epsN)]
```

### `bound.obtuse-adjacent` — Obtuse triangle at circumradius two

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** circleArea(2κ,κ√8,2) > a_crit+2epsilon_N

**Why:** Checks the radius-two endpoint used in the obtuse-cluster proof.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:99`; navigation code `VNDQIXO`.

```wolfram
positive[circleArea[2 k,k Sqrt[8],2]-(aK+2 epsN)]
```

### `bound.obtuse-case1-circle` — Cocircular two-triangle endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** (2κ)³(1−(2κ)²/16)^(3/2) > 2a_crit+4epsilon_N

**Why:** Checks the worst numerical budget of the cyclic quadrilateral endpoint.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:100`; navigation code `VNDQIXO`.

```wolfram
positive[(2 k)^3 (1-(2 k)^2/16)^(3/2)-(2 aK+4 epsN)]
```

### `bound.obtuse-case1-right-boundary` — Right-angle boundary during contraction

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** κ²√8 + circleArea(2κ,2κ,2) > 2a_crit+4epsilon_N

**Why:** Excludes the right angle at a shared vertex while contracting the nonobtuse triangle.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:101`; navigation code `VNDQIXO`.

```wolfram
positive[k^2 Sqrt[8]+circleArea[2 k,2 k,2]-(2 aK+4 epsN)]
```

### `bound.obtuse-case1-shared-chord` — Shared chord at the radius-two boundary

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** 4κ√(1−κ²/4) > 1.72√2

**Why:** Excludes radius two in the second contraction after the other triangle reaches its side bounds.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:102`; navigation code `VNDQIXO`.

```wolfram
positive[4 k Sqrt[1-k^2/4]-(43/25) Sqrt[2]]
```

### `bound.case2-central` — Central triangle in the three-triangle obtuse case

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** area(2κ,κ√8,κ√8) > 1.73

**Why:** Checks the uncharged central lower estimate.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:103`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[2 k,k Sqrt[8],k Sqrt[8]]-173/100]
```

### `bound.case2-central-charged` — Charged central triangle in the same case

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** area(1.72,κ√8,κ√8) > 1.73+epsilon_N

**Why:** Checks the extra allowance for a charged side.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:104`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[43/25,k Sqrt[8],k Sqrt[8]]-(173/100+epsN)]
```

### `bound.case2-small-radius` — Peripheral bound for radius at most 1.7

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** circleArea(2κ,2κ,1.7) > 1.08

**Why:** Checks the endpoint of the small-radius peripheral estimate.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:105`; navigation code `VNDQIXO`.

```wolfram
positive[circleArea[2 k,2 k,17/10]-108/100]
```

### `bound.case2-small-radius-charged` — Charged small-radius peripheral

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** circleArea(2κ,1.72,1.7) > 1.08+2epsilon_N

**Why:** Checks the correction allowance for that peripheral.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:106`; navigation code `VNDQIXO`.

```wolfram
positive[circleArea[2 k,43/25,17/10]-(108/100+2 epsN)]
```

### `bound.case2-total-small` — Total of the small-radius three-triangle estimates

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** 1.73+2·1.08 > 3a_crit

**Why:** Combines the previously checked lower estimates.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:107`; navigation code `VNDQIXO`.

```wolfram
positive[173/100+2 (108/100)-3 aK]
```

### `bound.obtuse-minimum` — Uniform radius-two peripheral estimate

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** circleArea(2κ,2κ,2) > 0.968

**Why:** Supplies a common coarse peripheral bound.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:108`; navigation code `VNDQIXO`.

```wolfram
positive[circleArea[2 k,2 k,2]-968/1000]
```

### `bound.case2-large-radius-central` — Central estimate in the large-radius subcase

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** κ√(4·1.7²−4κ²) > 2.41

**Why:** Evaluates the nonobtuse circumradius bound used in that subcase.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:109`; navigation code `VNDQIXO`.

```wolfram
positive[k Sqrt[4 (17/10)^2-4 k^2]-241/100]
```

### `bound.case2-total-large` — Total of the large-radius three-triangle estimates

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** 2·0.968+2.41 > 3a_crit+5epsilon_N

**Why:** Checks the complete correction budget.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:110`; navigation code `VNDQIXO`.

```wolfram
positive[2 (968/1000)+241/100-(3 aK+5 epsN)]
```

### `bound.case3-equilateral` — Four-triangle central equilateral endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** area(κ√8,κ√8,κ√8) > 2.2668

**Why:** Checks the coarse central area estimate for three obtuse neighbors.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:111`; navigation code `VNDQIXO`.

```wolfram
positive[triangleArea[k Sqrt[8],k Sqrt[8],k Sqrt[8]]-22668/10000]
```

### `bound.case3-large-radius-central` — Four-triangle central circumradius estimate

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** (κ√8/2)√(4·1.7²−8κ²) > 2.6

**Why:** Evaluates the high-radius central lower bound.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:112`; navigation code `VNDQIXO`.

```wolfram
positive[Sqrt[8] k/2 Sqrt[4 (17/10)^2-8 k^2]-26/10]
```

### `bound.case3-total-small` — Four-triangle small-radius total

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** 2.2668+3·1.08 > 4a_crit+6epsilon_N

**Why:** Combines the small-radius central and peripheral bounds.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:113`; navigation code `VNDQIXO`.

```wolfram
positive[22668/10000+3 (108/100)-(4 aK+6 epsN)]
```

### `bound.case3-total-large` — Four-triangle large-radius total

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** 2.6+3·0.968 > 4a_crit+6epsilon_N

**Why:** Combines the high-radius central and peripheral bounds.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:114`; navigation code `VNDQIXO`.

```wolfram
positive[26/10+3 (968/1000)-(4 aK+6 epsN)]
```

### `bound.case5-center` — Obtuse center endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** circleArea(κ√8,κ√8,2) > 2.45

**Why:** Checks the central bound when the center triangle is obtuse.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:115`; navigation code `VNDQIXO`.

```wolfram
positive[circleArea[k Sqrt[8],k Sqrt[8],2]-245/100]
```

### `bound.case5-total` — Obtuse-center total

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** 2.45+2·0.968 > 3a_crit+5epsilon_N

**Why:** Combines the estimates for that cluster.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:116`; navigation code `VNDQIXO`.

```wolfram
positive[245/100+2 (968/1000)-(3 aK+5 epsN)]
```

### `bound.nonobtuse-two` — Two nonobtuse triangles with a large edge

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 10 [sec:nonobtuse].

**Assertion:** a_min+area(1.8,1.8,1.72)−2epsilon_M > 2a_crit

**Why:** Checks the two-triangle correction estimate.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:117`; navigation code `VNDQIXO`.

```wolfram
positive[amin+triangleArea[9/5,9/5,43/25]-2 epsM-2 aK]
```

### `bound.pseudo-area3-right` — Right-angle endpoint of the exceptional peripheral

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section B.4.4 [sec:pseudo-area3].

**Assertion:** 2a_min+1.8κ > 3a_crit+epsilon_M

**Why:** Excludes the right-angle alternative in the exceptional-peripheral reduction.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:118`; navigation code `VNDQIXO`.

```wolfram
positive[2 amin+(9/5) k-(3 aK+epsM)]
```

### `bound.pseudo1-preparation` — Midpointer endpoint in the shared-edge calculation

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section B.4.1 [sec:pseudo1].

**Assertion:** a_min+area(1.8,1.8,1.72) > 2a_crit

**Why:** Eliminates the undesired midpointer length-boundary case.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:119`; navigation code `VNDQIXO`.

```wolfram
positive[amin+triangleArea[9/5,9/5,43/25]-2 aK]
```

### `bound.large-right-exclusion` — Right-angle endpoint in the non-large-angle estimate

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section B.4.6 [sec:large].

**Assertion:** a_min+1.72κ > 2a_crit+epsilon_M

**Why:** Checks the shared-leg exclusion of right triangles.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:120`; navigation code `VNDQIXO`.

```wolfram
positive[amin+(43/25) k-(2 aK+epsM)]
```

### `bound.squeeze-side-cut` — Upper base cut in the squeeze calculation

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 6.5 [lemma:squeeze-area].

**Assertion:** κ√(2.32²−(2κ)²) > a_crit+epsilon_N

**Why:** Justifies the finite shared-side range in the older derivative calculation.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:121`; navigation code `LZMJIZU`.

```wolfram
positive[k Sqrt[(58/25)^2-(2 k)^2]-(aK+epsN)]
```

### `bound.pent3-unshared-cut` — Unshared side bound in a three-triangle cluster

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 5.11 [calc:pent3].

**Assertion:** area(1.72,1.72,2.02) > a_crit+2epsilon_N+epsilon_M

**Why:** Justifies the central chart upper range on the unshared side.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:122`; navigation code `HUQEJAT`.

```wolfram
positive[triangleArea[43/25,43/25,101/50]-(aK+2 epsN+epsM)]
```

### `bound.C013-cap-below-epsN` — Exceptional-peripheral cap lies in the squeezing range

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 5.5 [calc:pseudo-area3].

**Assertion:** 2epsilon_M < epsilon_N

**Why:** Checks that the pair-subtraction cap is below the squeeze-area cap.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:123`; navigation code `JQMRXTH`.

```wolfram
positive[epsN-2 epsM]
```

### `bound.BXZBPJW-stronger-cut` — The triple-contact allowance is stronger

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 5.4 [calc:pseudo-area].

**Assertion:** 2a_crit−0.007 > 2a_crit−epsilon_M

**Why:** Explains why the 0.007 code allowance proves the paper’s 0.008 bound.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:124`; navigation code `BXZBPJW`.

```wolfram
positive[(2 aK-7/1000)-(2 aK-epsM)]
```

### `triangle.pythagorean.3` — Known right-triangle areas

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 4 [sec:area].

**Assertion:** Heron(3,4,5) = 6 = 3·4/2.

**Why:** Checks the exact Heron helper against base×height/2 on four independent fixtures.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:126`; navigation code `VNDQIXO`.

```wolfram
exactZero[triangleArea[aa,bb,cc]-ar]
```

### `triangle.pythagorean.5` — Known right-triangle areas

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 4 [sec:area].

**Assertion:** Heron(5,12,13) = 30 = 5·12/2.

**Why:** Checks the exact Heron helper against base×height/2 on four independent fixtures.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:126`; navigation code `VNDQIXO`.

```wolfram
exactZero[triangleArea[aa,bb,cc]-ar]
```

### `triangle.pythagorean.8` — Known right-triangle areas

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 4 [sec:area].

**Assertion:** Heron(8,15,17) = 60 = 8·15/2.

**Why:** Checks the exact Heron helper against base×height/2 on four independent fixtures.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:126`; navigation code `VNDQIXO`.

```wolfram
exactZero[triangleArea[aa,bb,cc]-ar]
```

### `triangle.pythagorean.7` — Known right-triangle areas

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 4 [sec:area].

**Assertion:** Heron(7,24,25) = 84 = 7·24/2.

**Why:** Checks the exact Heron helper against base×height/2 on four independent fixtures.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:126`; navigation code `VNDQIXO`.

```wolfram
exactZero[triangleArea[aa,bb,cc]-ar]
```

### `triangle.nonobtuse-equilateral` — Equilateral area fixture

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 4 [sec:area].

**Assertion:** area(2,2,2)=√3

**Why:** Checks the Heron helper on an equilateral fixture.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:128`; navigation code `VNDQIXO`.

```wolfram
exactZero[triangleArea[2,2,2]-Sqrt[3]]
```

### `triangle.area-permutations` — Heron symmetry

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 4 [sec:area].

**Assertion:** area(2,3,4) is invariant under all side permutations

**Why:** Checks that the area helper does not privilege a side.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:129`; navigation code `VNDQIXO`.

```wolfram
And@@(exactZero[(triangleArea@@#)-triangleArea[2,3,4]]& /@ Permutations[{2,3,4}])
```

### `triangle.radius345` — Known circumradius

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** 3·4·5/(4area(3,4,5))=5/2

**Why:** Checks the circumradius/area convention.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:130`; navigation code `VNDQIXO`.

```wolfram
exactZero[3 4 5/(4 triangleArea[3,4,5])-5/2]
```

## obtuse-endpoints (27 checks)

### `quadrilateral.cyclic.0` — Cyclic quadrilateral endpoint by charged-edge count

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** For the four boundary sides with exactly 0 entries 1.72 and 4 entries 2κ, sqrt(∏(p−d_i)) > 2a_crit + 0 epsilon_N, where p=(d_1+…+d_4)/2.

**Why:** Checks all five side-multiset budgets, independently of cyclic order.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:136`; navigation code `VNDQIXO`.

```wolfram
positive[cyclic-target]
```

### `quadrilateral.cyclic.1` — Cyclic quadrilateral endpoint by charged-edge count

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** For the four boundary sides with exactly 1 entries 1.72 and 3 entries 2κ, sqrt(∏(p−d_i)) > 2a_crit + 1 epsilon_N, where p=(d_1+…+d_4)/2.

**Why:** Checks all five side-multiset budgets, independently of cyclic order.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:136`; navigation code `VNDQIXO`.

```wolfram
positive[cyclic-target]
```

### `quadrilateral.cyclic.2` — Cyclic quadrilateral endpoint by charged-edge count

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** For the four boundary sides with exactly 2 entries 1.72 and 2 entries 2κ, sqrt(∏(p−d_i)) > 2a_crit + 2 epsilon_N, where p=(d_1+…+d_4)/2.

**Why:** Checks all five side-multiset budgets, independently of cyclic order.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:136`; navigation code `VNDQIXO`.

```wolfram
positive[cyclic-target]
```

### `quadrilateral.cyclic.3` — Cyclic quadrilateral endpoint by charged-edge count

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** For the four boundary sides with exactly 3 entries 1.72 and 1 entries 2κ, sqrt(∏(p−d_i)) > 2a_crit + 3 epsilon_N, where p=(d_1+…+d_4)/2.

**Why:** Checks all five side-multiset budgets, independently of cyclic order.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:136`; navigation code `VNDQIXO`.

```wolfram
positive[cyclic-target]
```

### `quadrilateral.cyclic.4` — Cyclic quadrilateral endpoint by charged-edge count

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** For the four boundary sides with exactly 4 entries 1.72 and 0 entries 2κ, sqrt(∏(p−d_i)) > 2a_crit + 4 epsilon_N, where p=(d_1+…+d_4)/2.

**Why:** Checks all five side-multiset budgets, independently of cyclic order.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:136`; navigation code `VNDQIXO`.

```wolfram
positive[cyclic-target]
```

### `quadrilateral.right-nonempty.0` — Right-endpoint enumeration is nonempty

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** The distinct permutations with 0 sides 1.72 and 4 sides 2κ include an assignment (u,v,w,z) with u²+v²≤w²+z².

**Why:** Checks that the endpoint enumeration for this boundary-side count is nonempty, so a skipped/empty enumeration cannot pass vacuously.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:139`; navigation code `VNDQIXO`.

```wolfram
Length[right]>0
```

### `quadrilateral.right-nonempty.1` — Right-endpoint enumeration is nonempty

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** The distinct permutations with 1 sides 1.72 and 3 sides 2κ include an assignment (u,v,w,z) with u²+v²≤w²+z².

**Why:** Checks that the endpoint enumeration for this boundary-side count is nonempty, so a skipped/empty enumeration cannot pass vacuously.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:139`; navigation code `VNDQIXO`.

```wolfram
Length[right]>0
```

### `quadrilateral.right-nonempty.2` — Right-endpoint enumeration is nonempty

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** The distinct permutations with 2 sides 1.72 and 2 sides 2κ include an assignment (u,v,w,z) with u²+v²≤w²+z².

**Why:** Checks that the endpoint enumeration for this boundary-side count is nonempty, so a skipped/empty enumeration cannot pass vacuously.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:139`; navigation code `VNDQIXO`.

```wolfram
Length[right]>0
```

### `quadrilateral.right-nonempty.3` — Right-endpoint enumeration is nonempty

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** The distinct permutations with 3 sides 1.72 and 1 sides 2κ include an assignment (u,v,w,z) with u²+v²≤w²+z².

**Why:** Checks that the endpoint enumeration for this boundary-side count is nonempty, so a skipped/empty enumeration cannot pass vacuously.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:139`; navigation code `VNDQIXO`.

```wolfram
Length[right]>0
```

### `quadrilateral.right-nonempty.4` — Right-endpoint enumeration is nonempty

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** The distinct permutations with 4 sides 1.72 and 0 sides 2κ include an assignment (u,v,w,z) with u²+v²≤w²+z².

**Why:** Checks that the endpoint enumeration for this boundary-side count is nonempty, so a skipped/empty enumeration cannot pass vacuously.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:139`; navigation code `VNDQIXO`.

```wolfram
Length[right]>0
```

### `quadrilateral.right.0.1` — Right-triangle plus nonobtuse-neighbor endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Assignment 1 in the distinct-permutation set with 0 sides 1.72, restricted by u²+v²≤w²+z²: uv/2 + Heron(w,z,√(u²+v²)) > 2a_crit + 0 epsilon_N.

**Why:** The first two sides are the right triangle’s legs; the other triangle shares its hypotenuse and is nonobtuse. Every retained assignment is checked, independently of cyclic symmetry.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:142`; navigation code `VNDQIXO`.

```wolfram
positive[total-target]
```

### `quadrilateral.right.1.1` — Right-triangle plus nonobtuse-neighbor endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Assignment 1 in the distinct-permutation set with 1 sides 1.72, restricted by u²+v²≤w²+z²: uv/2 + Heron(w,z,√(u²+v²)) > 2a_crit + 1 epsilon_N.

**Why:** The first two sides are the right triangle’s legs; the other triangle shares its hypotenuse and is nonobtuse. Every retained assignment is checked, independently of cyclic symmetry.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:142`; navigation code `VNDQIXO`.

```wolfram
positive[total-target]
```

### `quadrilateral.right.1.2` — Right-triangle plus nonobtuse-neighbor endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Assignment 2 in the distinct-permutation set with 1 sides 1.72, restricted by u²+v²≤w²+z²: uv/2 + Heron(w,z,√(u²+v²)) > 2a_crit + 1 epsilon_N.

**Why:** The first two sides are the right triangle’s legs; the other triangle shares its hypotenuse and is nonobtuse. Every retained assignment is checked, independently of cyclic symmetry.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:142`; navigation code `VNDQIXO`.

```wolfram
positive[total-target]
```

### `quadrilateral.right.2.1` — Right-triangle plus nonobtuse-neighbor endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Assignment 1 in the distinct-permutation set with 2 sides 1.72, restricted by u²+v²≤w²+z²: uv/2 + Heron(w,z,√(u²+v²)) > 2a_crit + 2 epsilon_N.

**Why:** The first two sides are the right triangle’s legs; the other triangle shares its hypotenuse and is nonobtuse. Every retained assignment is checked, independently of cyclic symmetry.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:142`; navigation code `VNDQIXO`.

```wolfram
positive[total-target]
```

### `quadrilateral.right.2.2` — Right-triangle plus nonobtuse-neighbor endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Assignment 2 in the distinct-permutation set with 2 sides 1.72, restricted by u²+v²≤w²+z²: uv/2 + Heron(w,z,√(u²+v²)) > 2a_crit + 2 epsilon_N.

**Why:** The first two sides are the right triangle’s legs; the other triangle shares its hypotenuse and is nonobtuse. Every retained assignment is checked, independently of cyclic symmetry.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:142`; navigation code `VNDQIXO`.

```wolfram
positive[total-target]
```

### `quadrilateral.right.2.3` — Right-triangle plus nonobtuse-neighbor endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Assignment 3 in the distinct-permutation set with 2 sides 1.72, restricted by u²+v²≤w²+z²: uv/2 + Heron(w,z,√(u²+v²)) > 2a_crit + 2 epsilon_N.

**Why:** The first two sides are the right triangle’s legs; the other triangle shares its hypotenuse and is nonobtuse. Every retained assignment is checked, independently of cyclic symmetry.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:142`; navigation code `VNDQIXO`.

```wolfram
positive[total-target]
```

### `quadrilateral.right.2.4` — Right-triangle plus nonobtuse-neighbor endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Assignment 4 in the distinct-permutation set with 2 sides 1.72, restricted by u²+v²≤w²+z²: uv/2 + Heron(w,z,√(u²+v²)) > 2a_crit + 2 epsilon_N.

**Why:** The first two sides are the right triangle’s legs; the other triangle shares its hypotenuse and is nonobtuse. Every retained assignment is checked, independently of cyclic symmetry.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:142`; navigation code `VNDQIXO`.

```wolfram
positive[total-target]
```

### `quadrilateral.right.2.5` — Right-triangle plus nonobtuse-neighbor endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Assignment 5 in the distinct-permutation set with 2 sides 1.72, restricted by u²+v²≤w²+z²: uv/2 + Heron(w,z,√(u²+v²)) > 2a_crit + 2 epsilon_N.

**Why:** The first two sides are the right triangle’s legs; the other triangle shares its hypotenuse and is nonobtuse. Every retained assignment is checked, independently of cyclic symmetry.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:142`; navigation code `VNDQIXO`.

```wolfram
positive[total-target]
```

### `quadrilateral.right.3.1` — Right-triangle plus nonobtuse-neighbor endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Assignment 1 in the distinct-permutation set with 3 sides 1.72, restricted by u²+v²≤w²+z²: uv/2 + Heron(w,z,√(u²+v²)) > 2a_crit + 3 epsilon_N.

**Why:** The first two sides are the right triangle’s legs; the other triangle shares its hypotenuse and is nonobtuse. Every retained assignment is checked, independently of cyclic symmetry.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:142`; navigation code `VNDQIXO`.

```wolfram
positive[total-target]
```

### `quadrilateral.right.3.2` — Right-triangle plus nonobtuse-neighbor endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Assignment 2 in the distinct-permutation set with 3 sides 1.72, restricted by u²+v²≤w²+z²: uv/2 + Heron(w,z,√(u²+v²)) > 2a_crit + 3 epsilon_N.

**Why:** The first two sides are the right triangle’s legs; the other triangle shares its hypotenuse and is nonobtuse. Every retained assignment is checked, independently of cyclic symmetry.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:142`; navigation code `VNDQIXO`.

```wolfram
positive[total-target]
```

### `quadrilateral.right.4.1` — Right-triangle plus nonobtuse-neighbor endpoint

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Assignment 1 in the distinct-permutation set with 4 sides 1.72, restricted by u²+v²≤w²+z²: uv/2 + Heron(w,z,√(u²+v²)) > 2a_crit + 4 epsilon_N.

**Why:** The first two sides are the right triangle’s legs; the other triangle shares its hypotenuse and is nonobtuse. Every retained assignment is checked, independently of cyclic symmetry.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:142`; navigation code `VNDQIXO`.

```wolfram
positive[total-target]
```

### `case4.cell-lower-bound.1` — Uniform four-cell bound in the obtuse proof

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Cell 1: Heron(2κ,2κ,z_1) + CircleArea(2κ,z_0,2) > 2a_crit+4 epsilon_N, with z_i=κ√8+(4κ√(1−κ²/4)−κ√8)i/4.

**Why:** The two summands have opposite monotonicity on the stated interval. Using opposite endpoints produces a bound on the whole cell, not a midpoint sample.

**Scope:** Four exact algebraic endpoint comparisons plus the stated monotonicity argument on [κ√8,4κ√(1−κ²/4)].

**Source:** `mathematica/PentagonChecks.wl:149`; navigation code `VNDQIXO`.

```wolfram
positive[lb-(2 aK+4 epsN)]
```

### `case4.cell-lower-bound.2` — Uniform four-cell bound in the obtuse proof

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Cell 2: Heron(2κ,2κ,z_2) + CircleArea(2κ,z_1,2) > 2a_crit+4 epsilon_N, with z_i=κ√8+(4κ√(1−κ²/4)−κ√8)i/4.

**Why:** The two summands have opposite monotonicity on the stated interval. Using opposite endpoints produces a bound on the whole cell, not a midpoint sample.

**Scope:** Four exact algebraic endpoint comparisons plus the stated monotonicity argument on [κ√8,4κ√(1−κ²/4)].

**Source:** `mathematica/PentagonChecks.wl:149`; navigation code `VNDQIXO`.

```wolfram
positive[lb-(2 aK+4 epsN)]
```

### `case4.cell-lower-bound.3` — Uniform four-cell bound in the obtuse proof

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Cell 3: Heron(2κ,2κ,z_3) + CircleArea(2κ,z_2,2) > 2a_crit+4 epsilon_N, with z_i=κ√8+(4κ√(1−κ²/4)−κ√8)i/4.

**Why:** The two summands have opposite monotonicity on the stated interval. Using opposite endpoints produces a bound on the whole cell, not a midpoint sample.

**Scope:** Four exact algebraic endpoint comparisons plus the stated monotonicity argument on [κ√8,4κ√(1−κ²/4)].

**Source:** `mathematica/PentagonChecks.wl:149`; navigation code `VNDQIXO`.

```wolfram
positive[lb-(2 aK+4 epsN)]
```

### `case4.cell-lower-bound.4` — Uniform four-cell bound in the obtuse proof

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** Cell 4: Heron(2κ,2κ,z_4) + CircleArea(2κ,z_3,2) > 2a_crit+4 epsilon_N, with z_i=κ√8+(4κ√(1−κ²/4)−κ√8)i/4.

**Why:** The two summands have opposite monotonicity on the stated interval. Using opposite endpoints produces a bound on the whole cell, not a midpoint sample.

**Scope:** Four exact algebraic endpoint comparisons plus the stated monotonicity argument on [κ√8,4κ√(1−κ²/4)].

**Source:** `mathematica/PentagonChecks.wl:149`; navigation code `VNDQIXO`.

```wolfram
positive[lb-(2 aK+4 epsN)]
```

### `trapezoid.second-derivative` — Trapezoid area derivative

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** A(t)=(b+t)√(a²−t²); Aʺ(t)=−(ba²+3a²t−2t³)/(a²−t²)^(3/2)

**Why:** Checks the derivative formula used to choose area endpoints; a>0 and −a<t<a.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:150`; navigation code `VNDQIXO`.

```wolfram
TrueQ[FullSimplify[D[(bb+tt) Sqrt[aa^2-tt^2],{tt,2}]+(bb aa^2+3 aa^2 tt-2 tt^3)/(aa^2-tt^2)^(3/2)==0,Assumptions->aa>0&&-aa<tt<aa]]
```

### `trapezoid.radius-derivative` — Trapezoid circumradius derivative

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section 9 [sec:obtuse].

**Assertion:** R²(t)=a²(a²+b²+2bt)/(4(a²−t²)); derivative=a²(b+t)(a²+bt)/(2(a²−t²)²)

**Why:** Checks the rational derivative used with the area endpoint argument.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:152`; navigation code `VNDQIXO`.

```wolfram
TrueQ[FullSimplify[D[aa^2(aa^2+bb^2+2 bb tt)/(4(aa^2-tt^2)),tt]-aa^2(bb+tt)(aa^2+bb tt)/(2(aa^2-tt^2)^2)==0]]
```

## gamma (35 checks)

### `Gamma.diagonal-determinant` — Shear area from the two diagonals

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** det((1+κ,t),(−2σt,6κσ))/2=2a_crit+σt²

**Why:** Checks the exact area formula proved geometrically in the paper.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:157`; navigation code `BKUSHRZ`.

```wolfram
exactZero[Det[{u,v}]/2-GammaArea[t]]
```

### `Gamma.first-triangle` — First triangle in the shear family

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** area(T0)=a_crit+t/4+σt²/2

**Why:** Checks the center-coordinate determinant for one half of the dimer.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:160`; navigation code `BKUSHRZ`.

```wolfram
exactZero[ar1-(aK+t/4+s t^2/2)]
```

### `Gamma.second-triangle` — Second triangle in the shear family

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** area(T1)=a_crit−t/4+σt²/2

**Why:** Checks the reflected half and the sign of its linear term.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:161`; navigation code `BKUSHRZ`.

```wolfram
exactZero[ar2-(aK-t/4+s t^2/2)]
```

### `Gamma.sum` — Sum of the two shear triangles

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** area(T0)+area(T1)=2a_crit+σt²

**Why:** Checks cancellation of the two linear terms.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:162`; navigation code `BKUSHRZ`.

```wolfram
exactZero[ar1+ar2-GammaArea[t]]
```

### `Gamma.stationary` — Stationarity of the ice-ray

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** Aʹ(0)=0

**Why:** Checks the symmetric critical point.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:163`; navigation code `BKUSHRZ`.

```wolfram
exactZero[D[GammaArea[t],t]/.t->0]
```

### `Gamma.second-derivative` — Exact second derivative

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** Aʺ(t)=2σ

**Why:** Checks the constant second derivative without interval differentiation.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:164`; navigation code `BKUSHRZ`.

```wolfram
exactZero[D[GammaArea[t],{t,2}]-2 s]
```

### `Gamma.strict-convexity` — Positive second derivative

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** 2σ>0

**Why:** Completes the exact convexity argument.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:165`; navigation code `BKUSHRZ`.

```wolfram
positive[2 s]
```

### `Gamma.symmetry` — Reflection of the shear parameter

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(t)=A(−t)

**Why:** Checks the symmetry used in the minimization.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:166`; navigation code `BKUSHRZ`.

```wolfram
exactZero[GammaArea[t]-GammaArea[-t]]
```

### `pinwheel.slice-stationary-parameter` — Pinwheel slice stationary parameter

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Lemma 4.11 [lemma:a0].

**Assertion:** Bʹ((1−κ)/(2σ))=0

**Why:** Checks the one-dimensional stationary point mentioned with the numerical minimum. It is not a global optimization over all contact types.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:170`; navigation code `QGPVOYX`.

```wolfram
exactZero[D[bpoly,x]/.x->(1-k)/(2 s)]
```

### `pinwheel.parameter-rounding` — Pinwheel stationary parameter decimal

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 4.11 [lemma:a0].

**Assertion:** |(1−κ)/(2σ)−0.16246|<0.000005

**Why:** Checks the printed parameter value.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:171`; navigation code `QGPVOYX`.

```wolfram
TrueQ[FullSimplify[Abs[(1-k)/(2 s)-16246/100000]<1/200000]]
```

### `pinwheel.slice-area-rounding` — Pinwheel slice minimum decimal

**Role:** Paper assertion. **Method:** EXACT. **Paper:** Lemma 4.11 [lemma:a0].

**Assertion:** |B((1−κ)/(2σ))/2−1.23719|<0.000005

**Why:** Checks the printed sample area, not the universal lower bound.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:172`; navigation code `QGPVOYX`.

```wolfram
TrueQ[FullSimplify[Abs[(bpoly/.x->(1-k)/(2 s))/2-123719/100000]<1/200000]]
```

### `Gamma.Heron-factor` — Independent squared-side identity

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** 16 area²=4 B(x)² for B(x)=σx²+(κ−1)x+σ(4κ+1)

**Why:** Cross-checks the determinant formula against the raw contact side formulas.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:173`; navigation code `BKUSHRZ`.

```wolfram
exactZero[heron-4 bpoly^2]
```

### `Gamma.positive-root-discriminant` — Sign of the single-triangle square root

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** disc(B)=−(13+15√5)/8

**Why:** Together with σ>0, shows B(x)>0 and selects the positive area root.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:174`; navigation code `BKUSHRZ`.

```wolfram
exactZero[Discriminant[bpoly,x]+(13+15 Sqrt[5])/8]
```

### `Gamma.raw-centered-identity` — Absolute versus centered contact coordinates

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section A.7 [sec:shared].

**Assertion:** [B(x)+B(2σ−x)]/2=A(x−σ)

**Why:** Checks the shift x=σ+t and the partner parameter 2σ−x.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:175`; navigation code `SMPXAOD`.

```wolfram
exactZero[(bpoly+(bpoly/.x->2 s-x))/2-GammaArea[x-s]]
```

### `Gamma.unique-minimum.-10` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(-10/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.-9` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(-9/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.-8` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(-8/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.-7` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(-7/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.-6` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(-6/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.-5` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(-5/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.-4` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(-4/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.-3` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(-3/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.-2` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(-2/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.-1` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(-1/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.0` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(0/1000) = 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.1` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(1/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.2` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(2/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.3` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(3/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.4` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(4/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.5` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(5/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.6` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(6/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.7` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(7/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.8` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(8/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.9` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(9/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

### `Gamma.unique-minimum.10` — Exact shear samples about the minimum

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** A(10/1000) > 2a_crit, where A(t)=2a_crit+σt².

**Why:** A regression of the exact identity at 21 rational arguments. The continuum minimum follows from σt², not from these samples.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:176`; navigation code `BKUSHRZ`.

```wolfram
If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]
```

## contact-identities (8 checks)

### `contact.slider-length` — Slider center distance

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section A [sec:coords].

**Assertion:** ell(x,0)²=4κ²+x²

**Why:** Checks the slider specialization of the contact distance.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:179`; navigation code `VNDQIXO`.

```wolfram
exactZero[ellx[x,0]^2-(4 k^2+x^2)]
```

### `contact.midpointer-length` — Shared shear contact distance

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section A [sec:coords].

**Assertion:** ell(x,π/5)²=(1+κ)²+(σ−x)²

**Why:** Checks the contact specialization used by the shear family.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:180`; navigation code `VNDQIXO`.

```wolfram
exactZero[ellx[x,Pi/5]^2-((1+k)^2+(s-x)^2)]
```

### `contact.reflection` — Reflection of pair-contact coordinates

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section A [sec:coords].

**Assertion:** ell(x,α)²=ell(2σ−x,2π/5−α)²

**Why:** Checks the coordinate reflection of Section A.1.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:181`; navigation code `VNDQIXO`.

```wolfram
exactZero[ellx[x,alpha]^2-ellx[2 s-x,2 Pi/5-alpha]^2]
```

### `contact.midpoint-value` — Midpoint of the slider branch

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Lemma 4.8 [lemma:mid-172].

**Assertion:** ell(σ,0)=√(4κ²+σ²)

**Why:** Checks the value used in the 1.72 comparison.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:182`; navigation code `VNDQIXO`.

```wolfram
exactZero[ellx[s,0]-Sqrt[4 k^2+s^2]]
```

### `contact.iceray-short-edge` — Short boundary edge of an ice-ray dimer

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section 6.5 [sec:gamma].

**Assertion:** 4κ²+(σ/(2κ))²=11/4

**Why:** Checks the shorter pair of kite edges.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:183`; navigation code `BKUSHRZ`.

```wolfram
exactZero[4 k^2+(s/(2 k))^2-11/4]
```

### `contact.iceray-unequal-boundary-edges` — The two kite edge lengths differ

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Corollary 2.16 [cor:equal].

**Assertion:** √(4κ²+σ²)>√11/2

**Why:** Distinguishes the kite from a rhombus in the equality case.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:184`; navigation code `VNDQIXO`.

```wolfram
positive[Sqrt[4 k^2+s^2]-Sqrt[11]/2]
```

### `area.squared-sides-Heron` — Squared-side form of Heron

**Role:** Supporting identity. **Method:** EXACT. **Paper:** Section A [sec:coords].

**Assertion:** 16 area(a,b,c)²=(a+b+c)(−a+b+c)(a−b+c)(a+b−c)

**Why:** Checks the polynomial normalization used in interval arithmetic.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:185`; navigation code `VNDQIXO`.

```wolfram
TrueQ[Expand[(16 triangleArea[aa,bb,cc]^2)-(aa+bb+cc)(-aa+bb+cc)(aa-bb+cc)(aa+bb-cc)]===0]
```

### `area.determinant345` — Determinant/Heron cross-check

**Role:** Implementation check. **Method:** EXACT. **Paper:** Section A [sec:coords].

**Assertion:** det((3,0),(0,4))/2=area(3,4,5)

**Why:** Checks the signed determinant orientation against the unsigned area helper.

**Scope:** Exact algebraic evaluation; no floating-point tolerance.

**Source:** `mathematica/PentagonChecks.wl:186`; navigation code `VNDQIXO`.

```wolfram
Det[{{3,0},{0,4}}]/2==triangleArea[3,4,5]
```

## diagnostics (30 checks)

### `diagnostic.area-determinant.1` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.2` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.3` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.4` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.5` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.6` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.7` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.8` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.9` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.10` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.11` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.12` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.13` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.14` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.15` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.16` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.17` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.18` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.19` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.area-determinant.20` — Generated triangle area comparison

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 20 seeded 80-digit triangles: |Heron−absolute determinant/2|<10^−40

**Why:** Uses two independent area expressions on generated examples.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:193`; navigation code `VNDQIXO`.

```wolfram
NumericQ[ar]&&Abs[ar-ref]<10^-40
```

### `diagnostic.rigid-area.1` — Generated rigid-motion invariance

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 10 seeded 80-digit examples: signed determinant area is unchanged by rotation and translation to tolerance 10^−40

**Why:** Tests coordinate conventions under rigid motions.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:199`; navigation code `VNDQIXO`.

```wolfram
Abs[original-ref]<10^-40
```

### `diagnostic.rigid-area.2` — Generated rigid-motion invariance

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 10 seeded 80-digit examples: signed determinant area is unchanged by rotation and translation to tolerance 10^−40

**Why:** Tests coordinate conventions under rigid motions.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:199`; navigation code `VNDQIXO`.

```wolfram
Abs[original-ref]<10^-40
```

### `diagnostic.rigid-area.3` — Generated rigid-motion invariance

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 10 seeded 80-digit examples: signed determinant area is unchanged by rotation and translation to tolerance 10^−40

**Why:** Tests coordinate conventions under rigid motions.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:199`; navigation code `VNDQIXO`.

```wolfram
Abs[original-ref]<10^-40
```

### `diagnostic.rigid-area.4` — Generated rigid-motion invariance

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 10 seeded 80-digit examples: signed determinant area is unchanged by rotation and translation to tolerance 10^−40

**Why:** Tests coordinate conventions under rigid motions.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:199`; navigation code `VNDQIXO`.

```wolfram
Abs[original-ref]<10^-40
```

### `diagnostic.rigid-area.5` — Generated rigid-motion invariance

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 10 seeded 80-digit examples: signed determinant area is unchanged by rotation and translation to tolerance 10^−40

**Why:** Tests coordinate conventions under rigid motions.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:199`; navigation code `VNDQIXO`.

```wolfram
Abs[original-ref]<10^-40
```

### `diagnostic.rigid-area.6` — Generated rigid-motion invariance

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 10 seeded 80-digit examples: signed determinant area is unchanged by rotation and translation to tolerance 10^−40

**Why:** Tests coordinate conventions under rigid motions.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:199`; navigation code `VNDQIXO`.

```wolfram
Abs[original-ref]<10^-40
```

### `diagnostic.rigid-area.7` — Generated rigid-motion invariance

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 10 seeded 80-digit examples: signed determinant area is unchanged by rotation and translation to tolerance 10^−40

**Why:** Tests coordinate conventions under rigid motions.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:199`; navigation code `VNDQIXO`.

```wolfram
Abs[original-ref]<10^-40
```

### `diagnostic.rigid-area.8` — Generated rigid-motion invariance

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 10 seeded 80-digit examples: signed determinant area is unchanged by rotation and translation to tolerance 10^−40

**Why:** Tests coordinate conventions under rigid motions.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:199`; navigation code `VNDQIXO`.

```wolfram
Abs[original-ref]<10^-40
```

### `diagnostic.rigid-area.9` — Generated rigid-motion invariance

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 10 seeded 80-digit examples: signed determinant area is unchanged by rotation and translation to tolerance 10^−40

**Why:** Tests coordinate conventions under rigid motions.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:199`; navigation code `VNDQIXO`.

```wolfram
Abs[original-ref]<10^-40
```

### `diagnostic.rigid-area.10` — Generated rigid-motion invariance

**Role:** Numerical diagnostic. **Method:** NUMERIC. **Paper:** Section A [sec:coords].

**Assertion:** 10 seeded 80-digit examples: signed determinant area is unchanged by rotation and translation to tolerance 10^−40

**Why:** Tests coordinate conventions under rigid motions.

**Scope:** Finite deterministic sample; not a proof over a continuum.

**Source:** `mathematica/PentagonChecks.wl:199`; navigation code `VNDQIXO`.

```wolfram
Abs[original-ref]<10^-40
```
