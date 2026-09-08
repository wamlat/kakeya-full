# Actual marked-compatible spatial groups

Three new development modules: `SpatialMarkedPartition`, `ActualSpatialMarked`, and `SpatialMarkedGroups`. They do not edit any frozen module, lakefile, registry or verifier.

The input is one actual measurable angular piece: an original tube family F in ambient k+1, one unit cap center u and angular scale tau≥delta, original Full sets Y_i inside the physical carriers, marked subsets G_i⊆Y_i, original full upper masses 2*lam, total marked mass at least eta*lam*M, and actual marked power broadness at scale tau. The mass variable `lam` in the grouping theorem is a physical per-tube mass; to compose with the anisotropic sampling interface substitute `lambda*delta^k`.

`SpatialMarkedPartition` constructs all labels and injective tube fibers. On each fiber, `Full Y label q` is EXACTLY the corresponding original full set; it is never replaced by an independently chosen shading. `Marks G label C q` keeps the actual original marks only where the full original marked multiplicity is at most 4C times that fiber's marked multiplicity. Its actual row cardinality is proved equal to `SpatialSplitting.restore`. Consequently at least three quarters of total marked mass survives across ALL labels, and marked broadness has the proved factor 4C. Population and total full mass partition exactly; the union of all spatial full unions equals the old full union. There is no selection of one box and no factor involving the number of boxes.

`ActualSpatialMarked` constructs the labels `spatialLabel u tau (F.tube i)` from actual tube bases. The overlap constant is

`C = (2*ceil((k+width+angular)/2)+3)^k`.

The physical carrier/cap geometry proves that at every point at most C different labels are occupied. Thus the full spatial subunions have pointwise overlap at most C and their summed real volumes are at most C times the ORIGINAL full-union volume. Every tube and its original base in label q belong to the SAME genuine parallel box

`parallelBox u tau q (R+1+width) (k+width+angular)`.

This is derived from the actual original base bound and angular localization. No common-box premise or label-count premise is added. Original direction separation, real-cap coefficient and angular containment survive through the injective fiber indexing.

`SpatialMarkedGroups.construct` keeps all labels whose marked mass is at least `(eta/4)*lam*M_q`. It proves:

- each retained fiber is nonempty and has the required actual common-box bases;
- total retained marked mass is at least `eta*lam*M/2`;
- total retained population, summed across all retained boxes, is at least `eta*M/4`;
- each box has marked/full mass fraction at least `eta/8`;
- its literal marks are subsets of its unchanged full sets, with pointwise angular broadness coefficient `K*(4C)`;
- each full union remains inside the SAME original full union.

Dropping insufficient boxes changes no set inside a retained box, so it requires no further broadness restoration. The full-subunion overlap bound for all labels automatically bounds the retained subcollection as well.

## Exact downstream use

For `AnisotropicSamplingInput` or `AnisotropicJointGeometry`, use each q in the literal `SpatialMarkedGroups.good` set, family `SpatialMarkedPartition.family F lab q`, full sets `Full Y lab q`, marks `Marks G lab C q`, and marked fraction parameter `eta/4`. `group_mass` is the precise per-box mass hypothesis after `lam=lambda*delta^k`; `ActualSpatialMarked.common_base_box` is the literal box hypothesis. `family_geometry` provides inherited original separation/cap/local direction geometry. Full measurability, physical carrier inclusion, comparable lower/upper mass and full two ends are inherited by the EXACT original-index equality `full_exact`; no further full-set trimming is necessary.

A refined angular input can take Y to be the existing exact restricted Ref sets from `AngularRestrictedMeasurable`. The generic construction does not itself package that particular P/V substitution or compose the per-box sampling alternatives and their estimates. Those are the remaining integrations; no desired estimate, sampled outcome, or broadness-under-arbitrary-thinning premise has been introduced here.

## Verification

All three modules clean-build to `.olean` with no warnings. Fresh source-prefix audits check all 40 explicit declarations (31 theorems and nine definitions); their only axioms are standard foundations `propext`, `Classical.choice`, `Quot.sound`. Each audit uses the complete final source, with logs `<Module>_full_source_audit.log` in audit_work.

- `SpatialMarkedPartition.lean`: 21 declarations, clean build and exact-source axiom audit PASS; SHA-256 `40aa8a8f084c9be2225768adb54d1585f4c057968c88635d81e4333ad7e52ab9`.
- `ActualSpatialMarked.lean`: 10 declarations, clean build and exact-source axiom audit PASS; SHA-256 `2a43683e945616ac90d72deee325148c49ba4e3d16484160862c07aa1b16d844`.
- `SpatialMarkedGroups.lean`: 9 declarations, clean build and exact-source axiom audit PASS; SHA-256 `7eab7b6987b6774fcafecdd15eead7a31d1a61b57ba5da68de53f261e4470859`.
