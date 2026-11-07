# Contact-line signs in the squeezing lemma

## Claim and context for a first-time reader

This calculation supports **Lemma 6.5, `lemma:squeeze-area`, Section 6.3** of
`pentagon_v005.tex`. Pentagon circumradius is one. Put

\[
\kappa=\cos(\pi/5),\quad \sigma=\sin(\pi/5),\quad
 a_{\rm crit}=\frac32(1+\kappa)\kappa\sigma,\quad
 a_{\min}=1.237,\quad \epsilon_N=a_{\rm crit}-a_{\min}.
\]

The input is a nonobtuse triangle of centers of three pentagons with disjoint
interiors, with B contacting A and C, and with area at most
`acrit + epsN` (about 1.34371610). Put A to the left of C on a horizontal
line and B above it. The conclusion is that the A--B contact line has
strictly negative finite slope, the C--B contact line has strictly positive
finite slope, and B lies above both supporting lines while the respective
other center lies below. This excludes horizontal and vertical contact
normals and makes the two contact equations independent.

This is NOT the area-derivative calculation. The separate existing
`squeeze_calc` checks an inequality of the contact slopes; the present result
places those slopes on the positive finite branch required to interpret it.
The target is fixed by the lemma, not adjustable through a command-line
numeric cutoff. In particular, `amin + epsN` would be the WRONG smaller
hypothesis for this lemma.

## Four cases and the four real parameters

For A--B use the coordinates `(x_alpha, alpha)` of Section A.1
(`sec:two`), and for B--C use `(x_gamma, gamma)`, in each case with the
pointer/receptor roles appropriate to that case. Both length coordinates
range over `[0,2*sigma]`, both angle coordinates over `[0,2*pi/5]`.

| Job | Contact A--B | Contact B--C |
|---|---|---|
| `BA_BC` | B points to A | B points to C |
| `BA_CB` | B points to A | C points to B |
| `AB_BC` | A points to B | B points to C |
| `AB_CB` | A points to B | C points to B |

Endpoints are included. Thus edge-to-edge sliders and the limiting
vertex-to-vertex cases are not dropped. A vertex-to-vertex contact is
represented by its specified supporting vertex--edge branch. Where more
than one representation exists, retaining both is conservative.

Fix B at the origin with a vertex at (1,0). Fivefold symmetry lets us
normalize the A attachment. C then has five relative attachment choices,
rotations by `2*pi*m/5`, `m=0,...,4`. These are finite chart alternatives,
not a fifth continuous coordinate.

The manuscript's pointwise uniqueness observation is correct: a contact
side is at most 2, every center distance is at least `2*kappa`, and hence
at a feasible nonobtuse triangle the B angle lies in
`[arc(2,2,2*kappa), pi/2]`, an interval shorter than `2*pi/5`. For completeness,
the cosine rule is decreasing in that angle and its cosine is increasing in
either incident side throughout `[2*kappa,2]`: the relevant numerator is at
least `8*kappa^2-4>0`. Its maximum therefore occurs at incident sides 2,2
and opposite side `2*kappa`.

However, different points in an interval box can admit different rotation
indices. The program therefore tests **all five indices** and never selects
one by rounding the midpoint of an angular interval. This is a harmless
larger computation and avoids a discontinuous chart-selection rule.

## Explicit contact coordinates

Write `delta=pi/5`, `P=2*pi/5`,
`e(theta)=(cos(theta),sin(theta))`, and let J be a positive quarter turn.
All vectors below are bold. The records returned by `contact` contain the
neighbor's center, a unit normal **from B toward that neighbor**, and a
vertex orientation of the neighbor.

For **B pointing to X**, let `h=x-sigma`, `phi=alpha-delta`. Then

\[
 \mathbf n=\mathbf e(\phi),\qquad
 \mathbf c_X=(1,0)+\kappa\mathbf n+hJ\mathbf n,\qquad
 \omega_X=\alpha+3\pi/5.
\]

The pointer is `(1,0)`. The receptor's edge midpoint is displaced by
`h J n` from it; its endpoint called `w` in Section A.1 is displaced by
`x J n`. Thus x is measured from the paper's specified endpoint, not from
the midpoint. The receptor edge is a supporting line of B because
`phi` lies between `-pi/5` and `pi/5`. Both pentagons lie on the proper
opposite sides of this line.

For **X pointing to B**, exchange the roles in the same construction and
rotate so that the receptor B has orientation zero. With `psi=P-alpha`,

\[
 \mathbf n=\mathbf e(\pi/5),\qquad
 \mathbf c_X=\mathbf e(\psi)+\kappa\mathbf n+hJ\mathbf n,\qquad
 \omega_X=\pi+\psi.
\]

This is the same Section A.1 convention with the pointer and receptor
exchanged. It is not an unannounced reflection of alpha. Rotating the
entire record for C through `mP` completes the configuration.

As a cross-check against `Pent.ellx`, the squared center distance in the
first formula is

\[
 1+\kappa^2+h^2+2\kappa\cos\phi-2h\sin\phi.
\]

In `ell_aux`, the length argument is `-h`, and its angle is
`alpha+3*pi/10=phi+pi/2`. Expanding that cosine law gives exactly this
expression. The role-exchanged construction is a rigid rotation of the
negative center difference and has the same distance. The fast OCaml tests
also compare these enclosures at fixed representative parameters.

For subdivision the four normalized coordinates are in the exact unit
cube. The program maps `u` to `x=2*sigma*u` and `v` to `alpha=P*v` by interval
arithmetic. This does not change the geometric parameter range.

## Signed normals instead of tangent divisions

Let the reconstructed neighbor centers be **a**, **c**, put **g**=**c**-**a**,
and let `H=det(a,c)`. The positive triangle orientation is `H>0`. Indeed,
after moving A to the origin and directing AC to the right, B is above AC
exactly when this determinant is positive. Nondegenerate nonobtuse
triangles with all center separations at least `2*kappa` have this
orientation or its reflected representation, which the full charts cover.

Let **n_A**, **n_C** be the normals from B toward A and C in the contact
records, and write

\[
 q_A=\mathbf n_A\cdot\mathbf g,\quad r_A=\det(\mathbf n_A,\mathbf g),\qquad
 q_C=\mathbf n_C\cdot\mathbf g,\quad r_C=\det(\mathbf n_C,\mathbf g).
\]

In the orthonormal frame along AC and upward from AC, the tangent `J n`
has components `(r,q)/|g|`. Therefore the contact line has slope `q/r`.
The inward normal toward B is `-n`, whose upward component is `r/|g|`.
Thus the four strict tests

\[
 -q_A>0,\quad r_A>0,\quad q_C>0,\quad r_C>0
\]

prove both slope signs AND both supporting-side assertions. This also
proves that every relevant component is nonzero. No division by an
uncertain slope and no tangent cutoff appears in this verification.

On this branch the paper's positive quantities are
`sigma_A=-q_A/r_A` and `sigma_C=q_C/r_C`. With A fixed and `ell'=-1`,
the contact equations give

\[
 x_B'=-\frac{\sigma_C}{\sigma_A+\sigma_C},\qquad
 h'=\frac{\sigma_A\sigma_C}{\sigma_A+\sigma_C}>0.
\]

A horizontal change of frame therefore gives precisely the three motion
signs used in the revised proof. The old disjunction in `squeeze_calc`
then implies its reciprocal-slope inequality, since both slopes are
positive. The new calculation supplies this branch assumption; it does
not silently substitute for the old inequality calculation.

## Exclusion order and why it is sound

After eliminating the nonpositive orientation, `classify` tries:

1. `|C-A|^2 < 4*kappa^2`. Nonoverlapping pentagons contain disjoint open
   incircles, so this rules out the input.
2. A negative dot product at A, B, or C. This certifies an obtuse angle;
   equality is retained.
3. `det(A,C)/2 > acrit+epsN`. This violates the area hypothesis.
4. The four strict normal-component inequalities above. This is not an
   exclusion of a feasible triangle: it proves the desired conclusion.
5. Strict overlap of the interiors of A and C. This violates nonoverlap.

If none succeeds, the box is unresolved and is bisected. The order matches
the requested progression from cheap tests to geometric overlap. An
interval operation or unexpected exception is never reclassified as a pass.

## Overlap test from actual pentagon vertices

For a convex pentagon of vertex orientation omega, its five outward edge
normals are `e(omega+pi/5+2*pi*j/5)`. Its own projection along one of
these unit normals is exactly `[-1,kappa]` relative to its center.
For the other pentagon, its projected vertices give

\[
 \mathbf d\cdot\mathbf n+
 \cos(\omega_{\rm other}+2\pi k/5-\arg\mathbf n),\qquad k=0,\ldots,4.
\]

The code computes enclosures of the minimum and maximum of these five
values. To prove interior overlap on an axis, it requires that the
**upper bound on the other minimum** be below `kappa`, and that the
**lower bound on the other maximum** exceed `-1`. The relevant interval
comparison with kappa is also strict and directed outward.

These strict overlaps must hold on all ten edge-normal axes of both
pentagons. The separating-axis criterion for convex polygons then proves
interior overlap. Failure on even one axis is unresolved, not a proof of
nonoverlap. In particular, a touching pair is never discarded as strictly
overlapping just because its intervals share an endpoint.

This elementary vertex test deliberately does not call the older
`Pet.pet` or banana-angle routines. Its complete implementation is short
and independently inspectable.

## What constitutes a completed calculation

The initial queue is the unit four-cube for EACH of the five rotations.
A closed bisection gives children sharing the same stored midpoint, so
no parameter boundary is lost. Each terminal box must have one of the
six recorded reasons (orientation plus the five tests above).

The recursion returns only when the queue is empty. It checks the binary
forest counts `nodes=2*splits+5`, `leaves=splits+5`, and that all five
rotations were actually visited. Each case has its own log and process.
A width limit, diagnostic node limit, timeout, exception or interrupted
process is INCOMPLETE, not a counterexample and not a pass. A passed
sample test is not a substitute for completion of the four full queues.

No claim that a `true` return alone validates the primitive interval
backend is made. The existing CRlibm-backed implementation and its saved
environment remain the numerical foundation, as in the rest of the project.
