# Actual discrete-to-measurable assembly

`DiscreteMeasurable.lean` contains 19 theorems and compiles on Lean 4.33.1 with the pinned mathlib. It imports the actual geometry, occupancy selection, density normalization, tube volume and scale-choice modules. There are no `sorry` terms or custom axioms. All printed dependencies are the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`. Full compiler/dependency output: `discrete_measurable_compile.log`; built module: `.lake/build/lib/lean/DiscreteMeasurable.olean`.

## Geometry and normalization are instantiated

An injective restriction of a finite original tube family preserves projective direction separation, bounded bases and every angular-cap count. The cap proof maps each actual selected cap fiber injectively into its original fiber and compares its cardinality.

A `CommonIntegerSelection` is mapped into an actual `TubeFamily` indexed by the selected tube count. Its grid labels are images under the supplied injective list of genuine Euclidean labels. Positive measured tube-cell incidence yields an actual point in the physical tube and half-open cell; the existing geometric theorem then proves center admissibility with the fixed width enlargement `width + k/2`.

The module derives the real bound `number_of_cells ≤ C(k,width)/δ` for every actual admissible tube, where

`C(k,width) = max(1, 4*(2*ceil(width+1)+3)^k)`.

It invokes the proved actual subset trimming in DensityNormalization, preserving all geometric conditions, and constructs a `ShadedConfiguration` with `0<density≤1`. The retained density is at least `δ*K/(2*C)`, where K is the common integer count. The resulting discrete union is compared to actual Lebesgue measure of the original union using the selected occupancy class; it is not identified with an assumed measurable object.

## Actual selection and explicit logarithmic budgets

`positive_incidence_count` derives the cutoff's positive-incidence bound from physical tube containment with no remaining cell-count premise. `actual_occupancy_selection` starts from original measurable shadings in an actual finite grid cover, uses common cell volume `δ^k`, constructs the actual high-occupancy filter, and selects the actual occupancy and tube-mass classes. Its only cutoff budget is the explicit inequality

`lo * δ^k * (C(k,width+k/2)/δ) ≤ base/2`.

It proves that every tube retains at least `base/2`. It also constructs class depths with the explicit bounds

`Jocc+1 ≤ log(1/lo)/log(2)+2`,

`Jtube+1 ≤ log(upper/(base/(4*(Jocc+1))))/log(2)+2`.

These are proved logarithmic ratio bounds, not a claim that arbitrary finite class budgets have uniform growth.

## Conditional measurable inequality

`selection_configuration` constructs the normalized configuration. `selection_measurable_bound` applies a supplied proved discrete bound. `discrete_estimate_measurable` starts with the project's full `DiscreteEstimate` definition and chooses the positive estimate constant **before** the scale, density, cap coefficient, tube family, original measurable shadings and selected classes.

The stronger `selection_measure_class_losses` eliminates the selected occupancy using `0<w≤1` and `p≥1`, and substitutes the actual class-selection count inequalities. Let B=Jocc+1, Bt=Jtube+1, M be the original tube count, V be the common cell volume, C the fixed normalization constant, `base` the original required per-tube mass, and `upper` the original mass upper bound. Assuming cutoff retention at least M*base/2, it proves

`measure(U) ≥ c A^(-1) δ^(m-d+ε) * (δ*base/(16*C*B*V))^p * (M*base/(4*B*Bt*upper)) * V`.

All occupancy variables have disappeared. For V=δ^k and comparable base,upper proportional to λδ^(k-1), this has the intended power δ^(k+m-d+ε) λ^p M and only explicit B^(p+1)Bt class losses, up to fixed constants.

## Small-density branch

`small_density_actual_tube` handles 0<λ≤δ≤1 with p≥1 and d≤p. It uses the proved lower volume of an actual UnitTube, an actual shading-density inequality, an actual shading subset of the union, finite union measure, and the explicit total count M≤C A δ^(-m). It derives the intended bound with no favorable δ^ε factor needed. The dimensional tube-volume constant remains explicit.

## Remaining scope

These theorems do not assert the novel analytic `DiscreteEstimate`; it is an explicit hypothesis in the conversion. The high-density result now constructs its actual finite configurations and proves the measurable inequality with explicit class losses. A final fully uniform measurable theorem still needs the routine parameter specialization `lo` proportional to λ, the identification of base/upper with fixed multiples of λδ^(k-1), and absorption of the displayed logarithmic losses into an arbitrary scale exponent. The existing bounded-grid cover and tube-volume theorems supply the physical application hypotheses; this module accepts their finite covering/required-shading-mass inputs rather than repeating those constructions.
