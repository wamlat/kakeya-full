# Independent review: realization of the sphere-net-tested raw sample

Reviewed the full frozen `formalization/SphereNetSampleRealization.lean` at
SHA-256 `ad372c13817b22b97aa1474638d07d2def201d2c708aaafa29df9a65b67747b8`.
No mathematical or source-scope defect found. This was a read-only review;
the geometry agent owns the separate production source/dependency audit.

The review compared the output with combined.txt lines 1333–1490, especially
Lemma 6.1 (6.7)–(6.11), and inspected the invoked original-cell count,
all-ball, and longitudinal-grid lemmas.

`Output` contains one depth, one original raw outcome, and one `SampleGood`
certificate for the actual whole-sphere net. `of_sample` packages exactly
those supplied fields. There is no second sample, row scaling, changed test
mask, or hidden narrow-density certificate. The imported `SampleGood` uses
only the source full-density band [mu/2,2mu]. Existence of this certificate is
deliberately outside this deterministic realization module and is to be
provided by the root's same-law probability theorem.

`family` maps the selected subtype labels back to the original integer cells
and uses the original `F.tube` without changing any index or axis. Marks use
the same outcome and deterministic high-cell set. Thus separation, bounded
bases, and any additional real-cap bound transfer unchanged. The actual
marks are subsets of actual full rows. The union count is bounded by the
original available support count, and the selected whole-cell union lies
inside the available whole-cell union. The statements correctly avoid
asserting containment of these whole cells in the measurable shading union.

The selected full/marked labels retain positive intersection with their own
original full/marked measurable set, respectively. Physical full-carrier
membership then puts every selected center within
(width+(n+1)/2)*delta of a point on the original individual-length axis.
There is no renormalization to a unit interval. The longitudinal lemma counts
the actual centers lying within that fixed radius of any axis interval
[a,a+delta], using the genuine integer-grid bound; no alignment or count
premise is added.

Physical mass plus the broad density band gives exactly
c0*lambda/(2delta) <= #Y_i <= 2*C0*lambda/delta. The source quarter-total
bound uses the exact original normalized marked mass Wg, not merely its
lower bound xi*lambda*M/delta. The middle inequality
(xi/(8*C0))*sum #Y_i <= Wg/4 follows from the actual full upper counts and
original marked mass, and combines with Wg/4 <= sum #H_i. Its division by
C0 is valid because the original Input proves C0>0.

The full two-ends conclusion controls every center and radius delta<=r<=1.
Finite test coverage is proved by the underlying grid-ball construction;
the density conversion uses mu<=2*#Y_i, which follows from the source lower
half-mean bound alone. The radius enlargement costs 4^alpha, and alpha<=1
gives the dimension-only multiplier 8*ballCoefficient(n) in the final
statement. The source positive-gap range ensures this alpha<=1 hypothesis.
There is no sub-delta two-ends premise and no assumed arbitrary-ball estimate.

`closed_broadness` identifies each actual original marked row with the same
net-tested outcome row, then proves the 1/10 bound for every unit cap center
at exactly theta. Labels outside the available support have empty marked
rows. The entire-sphere net's strict cover already controls closed theta
caps, so the open-cap corollary needs only inclusion and incurs no radius
change. No original-direction-only test or angular re-sampling is substituted.

These statements provide the geometric conclusions of the high alternative
once the actual good sample is supplied. They do not independently assert
the low/high dichotomy, theta's inverse-log lower bound, or probability >3/4;
those are separate proved inputs to the final source wrapper.
