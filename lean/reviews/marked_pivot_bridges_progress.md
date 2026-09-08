# Original marks, adjustable pruning, and normalized spatial bounds

The original pivot uses two distinct shadings: full shadings for legal samples and sparse marks for angular broadness and the angle population. An earlier helper applied under a stronger full-row broadness hypothesis. Its statement was correct, but that hypothesis does not follow merely from broadness of the marks.

`MarkedSubsetSamples.lean` closes this interface. It forms the actual marked family with the same original tubes and proves that its transverse angles are a literal subset of the full-family transverse angles. The marked incidence count and single-radius marked broadness give the required I²/(2E) lower bound for the full-family angle set. Full-shading two ends then construct legal samples for this set. Enlarging the angle set preserves every geometric collision argument and its matching angle-count factor; no assertion of full-row broadness is made.

The same explicit parameter infrastructure remains available. Taking kappa = PivotKappa.choice(width,B,theta⁻¹,alpha,1), the proved parameter tests imply 2 kappa ≤ theta, the physical two-ends exclusion and kappa ≤ 1/100. Thus a single original angular radius theta is sufficient. No all-radius marked power-cap bound is required by the new constructor.

`MarkedSpatialPruning.lean` extends the actual base-estimate pruning to any positive deletion budget loss. Its constant K is chosen before the family and before loss. At dyadic depth J it sets eta=loss/(J+1) and the actual threshold

    L=max(1, K E A delta^(d-m-epsilon) eta^(-(p+1)) lambda^(-p)/M).

The original survivor family is unchanged as a construction. Its deleted full incidence satisfies delta R ≤ loss lambda M, while its union has the proved spatial ball bounds. This allows loss to be a small fraction of the original marked density xi; a half-full-incidence budget would not protect arbitrarily sparse marks. The exact inverse-loss factor is loss^(-(p+1))(J+1)^(p+1).

`PrunedScaleTransport.lean` addresses the separate mesh interface. Legal labeled pairs use the common mesh delta/(1+2width), while original spatial pruning is at delta. It proves equality of the actual label tests

    ballCells(E,delta/R,x,r) = ballCells(E,delta,R*x,R*r)

for R>0. Therefore the original all-radius spatial population constant transports exactly to the normalized mesh, on the same original labels. Original tubes are never presumed admissible at the smaller mesh. The pruned-normalized theorem invokes the proved original large-radius extension before applying this identity.

`MarkedPivotSelection.lean` composes this marked/full angle bridge with the actual collision-selected output population. With kappa fixed by width, B, theta and alpha, it constructs both the full sample system S and the actual dyadic selection P. It returns the lower/upper sigma bounds and

    Q ≥ (outputCoefficient/16) kappa^(5(k+1)) lambda^6 I^2
          / (sigma^2 delta^2 pivotLog(delta)^3 E).

Here I is an actual marked incidence lower bound and E bounds the marked-cell set. The original geometric, comparable-full-density, full-two-ends and single-radius marked cap tests remain explicit; the output count, angle count, legal sample system and collision energy are derived. The normalized collision scale is a stated numerical hypothesis.

All four modules compile without diagnostics and pass full-source logical-dependency audits with only standard foundations. The complete pivot implication remains separate downstream work. The companion marked density recovery and pruning assembly modules now construct the recovered configuration; their concrete composition with this selection constructor is later development than this report's checkpoint.
