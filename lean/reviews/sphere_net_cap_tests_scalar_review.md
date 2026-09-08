# Independent review: actual sphere-net cap tests

Reviewed `formalization/SphereNetCapTests.lean` at SHA-256
`1a904c253c381ecbf814760a7cad0409c304628d4f3368eb006fafbda8cc06a2`.
Read-only mathematical statement and proof review; no defect found. The parent
owns the independent production source/dependency audit.

The angular masks use every center of the actual entire-sphere net. Its strict
radius-theta cover places every **closed** original theta cap in an **open**
radius-2theta test, including caps centered away from all original directions.
`cap_containment` proves containment on the same arbitrary finite index row;
`all_closed_caps` transfers its cardinality estimate. There is no hypothesis
that the original cap center belongs to the tube family.

`row_cap_card` identifies the actual output row with the cap count for the
same outcome and original tube indices. `sampled_closed_broadness` retains
that row unchanged, proves the 1/10 bound on high cells, and handles low cells
by their actual empty marked row. Its `SampleGood` argument is an explicit
deterministic-transfer premise; this module does not claim the existence or
probability of such an outcome.

The cap expectation is derived by integrating the original almost-everywhere
pointwise incidence inequality on each actual finite-volume grid cell. All
marked sets are measurable; no global finite-volume premise is needed here.
The single almost-everywhere broadness premise quantifies over all original
unit centers and admissible radii, so selecting a net center and radius
2theta preserves the same null-set exception. Open tested caps are included
in the original closed caps using projective-distance symmetry.

`source_cap_test` uses the literal theta choice, its upper bound, and its
factor-1000 budget. The lower-scale condition delta <= 2theta remains an
explicit geometric range condition. `input_cap_test` uses the original
`rawMarked` cell weights and original support; there is no row equalization,
density-ratio loss, new outcome, or probability oracle hidden in this wrapper.
Net size and simultaneous failure probability are separate conclusions to
be supplied by the dedicated budget and probability modules.
