# Actual transformed angular-piece populations (Section 7)

Three new modules are clean-built and frozen: TransformedGridSupport.lean (14 declarations), AngularPiecePopulation.lean (5), and TransformedSamplingPopulation.lean (2). A fresh combined full-source audit checks all 21 declarations, each depending only on propext, Classical.choice and Quot.sound. No errors, warnings, sorry or custom axioms.

## Missing construction now supplied

The previous AnisotropicGrid module controlled fibers of rounded old centers, hence lower counts for that rounded image. Section 7 also needs the different assertion that ALL new cells meeting the stretched old-cell union number at most a fixed multiple of the old-cell count. The new construction supplies this upper comparison explicitly.

For a finite old cell set S at mesh delta, and an actual map f whose distances expand by at most 1/tau, each new cell at mesh delta/tau meeting f(old cell z) has center within n(delta/tau) of f(center z). One half-cell error comes from the old cell under the map, and one from the new cell. It therefore lies in an explicit integer box of cardinality (2n+3)^n. The finite biUnion of these boxes over S contains every possible touching cell. Filtering it by actual nonempty intersection defines `touched`; `mem_touched` proves the exact intersection iff, and `image_covered` covers the whole exact image. This includes every boundary point actually present under the half-open conventions.

The actual `pieceMap u tau W q` first applies the common width homothety x/W and then the constructed `normalizeBox u tau q`. For W >= 1 and 0 < tau <= 1, its distance upper bound is derived from those maps. Thus `piece_support` assumes no anisotropic geometry oracle. Its touching-cell count is at most (2n+3)^n times #S, independent of delta, tau, W, center direction and translation.

`positive_support_subset` places the literal SamplingSupport support of any full-set restrictions of that image inside touched. `positive_support_card` is the actual positive-sampling-support upper comparison. It neither identifies cell cardinality with transformed volume nor introduces an inverse tau loss.

## Actual sampling and low-cell branches

TransformedSamplingPopulation.sampled_union_card uses the actual SamplingRealization.full family on that positive support. Its literal union count is at most (2n+3)^n #S. The theorem works for every outcome because output incidences are indexed by the actual finite support; no good-event or energy premise is needed for this count.

low_count_or_high uses the literal marked weights volreal(G_i intersection cell)/(delta/tau)^n, with G_i subset Y_i. It constructs the positive low-cell/high-cell dichotomy and proves in the low branch:

    totalMarkedMean/(2 cutoff) <= #positiveLow <= (2n+3)^n #S.

Otherwise the actual high cells carry at least half of the total marked mean. No analytic estimate on a piece is assumed. Equality between total marked mean and global measurable marked mass is the separately proved SamplingMeans interface and is deliberately not asserted without its carrier/support hypotheses here.

## Actual original-piece summation

AngularPiecePopulation derives the exact old group-union inclusion and uses finite incidence double counting with Pieces.kept_overlap to prove:

    sum_kept #((P.family g).unionCells) <= 2 tau^(-beta) #F.unionCells.

It then constructs the transformed-reference inclusion under the common piece map, proves each actual positive support count, and sums the counts using only those ORIGINAL restricted unions. Group directions/translations may vary. No overlap of sampled cubes or their pullbacks is postulated.

## Exact remaining boundary

These theorems close the count comparison Es <= #Q <= C E_j and the geometric population portion of the low-cell branch. They do not establish the marked estimate itself, a four-case estimate oracle, density refinement, or preservation of the marked mass under choosing unit segments. The final full sets must be actual restrictions of the indicated transformed old piece union. AngularPiecePopulation specializes this to AngularSeedRealization.Ref. AngularSeedRealization.Full contains original full shadings on participating indices and does not automatically have the same pointwise overlap as Ref; our theorem does not conflate them. After an actual density/mark refinement supplies restricted full shadings, the generic TransformedGridSupport theorem applies even if the final tube index type has changed.

For one group the fixed original cell set S may be any verified restricted piece union. At the final summation, the angular overlap must belong to those exact old S sets. The stronger intermediate statement that all transformed available supports have a summed population bound does not claim their spatial overlaps are controlled.

## Validation

- transformed_grid_support_compile.log
- angular_piece_population_compile.log
- transformed_sampling_population_compile.log
- transformed_piece_population_full_source_audit.lean and .log (21 declarations)

SHA-256:
- TransformedGridSupport: 22f9fa34410b15b61aa7e6b9163c65056b7e2f0315989fdac8ee0d04c479f153
- AngularPiecePopulation: 24ae11cf2c4dec8d58126b123de70090c3d6b857e47e016ba5003f5563f26379
- TransformedSamplingPopulation: 709a89df92dcdd848f6c2e5aec34bfecd939d2ef9c97b55c80a284ec338e8368
