# Section 3 literature trust boundary

Verified against the original sources on 2026-09-24. The author explicitly
authorized literature-backed black boxes. `MoireLiterature.lean` therefore
contains **five custom axioms**. Their proofs are external to Lean. No `sorry`
is used, and no axiom asserts a gasket-specific result.

## Sources and declarations

| Lean declaration | Original source | Specialisation used |
| --- | --- | --- |
| `MoireLiterature.planar_ambient_bound` | Corso–Shmerkin, Section 1.2, inequality (1.2); Section 2.2 states rescaling invariance | Compactly supported planar probability measures; upper bound two |
| `MoireLiterature.line_ambient_bound` | Rossi–Shmerkin, Section 1, p. 2, dimension range immediately before (1.1) | Compactly supported probability measures on the real axis; upper bound one |
| `MoireLiterature.line_convolution_bound` | Rossi–Shmerkin, Section 1, equation (1.2) | Compactly supported probability measures on the real axis; use commutativity for both factors |
| `MoireLiterature.corso_shmerkin_line` | Corso–Shmerkin, Corollary 4.2 | Dimension one, contraction 1/2, uniform weights, exponential separation, dimension less than one |
| `MoireLiterature.corso_shmerkin_plane` | Corso–Shmerkin, Corollary 4.2 | Dimension two, contraction 1/2, uniform weights, exponential separation, unsaturation in every direction |

Original sources:

- Emilio Corso and Pablo Shmerkin, *Dynamical self-similarity, Lq-dimensions and
  Furstenberg slicing in Rd*, [arXiv:2409.04608v1](https://arxiv.org/html/2409.04608v1).
  [Section 1.2](https://arxiv.org/html/2409.04608v1#S1.SS2),
  [Section 2.2](https://arxiv.org/html/2409.04608v1#S2.SS2),
  [Corollary 4.2](https://arxiv.org/html/2409.04608v1#S4.SS2).
- Eino Rossi and Pablo Shmerkin, *On measures that improve Lq dimension under
  convolution*, [arXiv:1812.05660v2](https://arxiv.org/pdf/1812.05660v2), printed p. 2.

These are specialised mathematical statements, not claims that the source papers
contain Lean code. The representation identifications below are part of the
explicitly trusted translation of each literature result.

## Representation and hypothesis audit

**Plane and line.** Complex numbers represent the Euclidean plane by real and
imaginary coordinates. The line is represented by imaginary coordinate zero.
Its dyadic squares of nonzero mass are exactly those with imaginary index zero;
their real-coordinate slices are the half-open dyadic intervals. Thus the same
`lqDimension` definition represents line dimension on these measures. Orthogonal
projection coordinates are `Re(conj(direction) * point)` for unit directions;
representing their scalar values on the real axis preserves that coordinate's
dyadic intervals.

**Logarithms.** The papers use base-two logarithms. Lean uses natural logarithms
and divides by `log 2` in `scaleDimension`, giving the same quotient. The
irrelevant level-zero value does not affect the limit inferior.

**Compactness.** All five axioms require an actual compact set of measure one,
expressed by `MoireCompactLaws.CompactlySupported`. The mapped gasket laws and
the difference law satisfy this by proved continuous-image constructions.
The convolution axiom requires both factors to have mass one on the real axis.
This deliberately avoids asserting an uncited generalisation to arbitrary
planar or noncompact measures.

**Self-similarity.** `UniformSelfSimilar` states the measure identity for the
maps `x ↦ (x + vertices i)/2`. In the cited notation, the translation is therefore
`a_i = vertices i / 2`, the contraction is `lambda = 1/2`, and the orthogonal
part is the identity. Positive alphabet cardinality ensures positive uniform
weights. The translated formula is

    log(N * (1/N)^q) / ((q - 1) * log(1/2)) = log(N) / log(2).

This scalar specialisation is included in the declared external theorem; it is
not a new assertion about a gasket.

**Separation.** `cylinderCenter` is the weighted finite sum giving the translation
of a word's composed maps. Its equality with the existing gasket and difference
word centers is proved in `MoireHomogeneousSystem`. The interface requires a
positive rate below one and arbitrarily large natural levels with the separation
bound for every pair of distinct words. Arbitrarily large levels are equivalent
to the increasing sequence of levels used by Corollary 4.2. The rate restriction
only narrows the cited hypothesis.

**Unsaturation.** The one-dimensional interface assumes dimension less than one.
The planar interface quantifies over every unit direction and requires the
projected dimension to exceed the planar dimension minus one. No separation or
unsaturation hypothesis is omitted. The application proves the latter condition
inside its dimension-drop contradiction.

## Completed entry point and audit

`MoireLiterature.inputs` supplies every field of `LiteratureInput`.
`MoireSection3Complete.ae_upper_box_dimension` has **no analytic input parameter**.
It states the actual almost-everywhere upper box bound for gasket intersections.
`ae_full_lq_dimension` similarly states full difference-measure dimension for
almost every angle, simultaneously for every real q > 1.

The main theorem's axiom dependencies are the three standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) and exactly the five declarations
listed above. Section 2 and the paper-specific Section 3 proofs retain their
standard-only dependencies. `audit/CheckAxioms.ps1` checks this separation and
rejects unexpected custom axioms, `sorryAx`, or a missing final entry point.
The completed projection lemma also reports all five dependencies because it
receives the whole `inputs` record; its mathematical argument uses the three
line results. This conservative dependency list is retained in the audit.

Build: `section3-literature-build-2026-09-24.txt`.
Combined audit: `section3-literature-axioms-2026-09-24.txt`.
This is completion **relative to the documented literature black boxes**, not
a claim that those external results have themselves been proved in Lean.
