# Finite sampling assembly: completed

`audit_work/formalization/SamplingApplication.lean` imports the completed `Sampling.lean` probability model and now compiles cleanly. Its **17 exported theorems** all print only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms. No warnings, errors, admitted proofs, custom axioms, or native decision axioms occur. The compiled `.olean` is available in `.lake/build/lib/lean/SamplingApplication.olean`; the log is `audit_work/sampling_application_compile.log`.

## What is constructed and proved

`finite_sampling_assembly` takes finite types of tubes `T`, cells `C`, ball tests `B`, and cap tests `A`. Its probabilities are actual arrays `p(t,c),q(t,c)` with `0≤q≤p≤1`. Ball and cap membership are finite Boolean incidence masks. The random outcome is the single shared three-state product sample on `T×C` from `Sampling.lean`.

The module proves that its masks' expected counts and realized counts equal the corresponding actual row, column, ball, and cap incidence sums. It then defines four tagged families of failure events:

1. every tube's full-count density band;
2. every tube–ball upper-count test;
3. every high cell's marked lower-count test;
4. every high-cell–cap marked upper-count test.

Every probability bound is derived by applying the already proved product-law Chernoff theorems. Their finite sum is checked against the displayed numeric budget. A positive-mass outcome outside all failure events is produced; no simultaneous good event or failure-probability bound is imported as an assumption.

The output full shading `fullShading ω t` and high-cell marked shading `markedShading high ω t` are **actual finite sets of cells** on the same tube index type. The `SampleGood` conclusion contains all of the following:

- every tube has full cardinality between half and twice its expected full count;
- every ball test satisfies its upper cutoff;
- every high cell has at least half its expected marked multiplicity;
- every cap test contains at most one tenth of the actual high-cell marked multiplicity;
- the total retained marked cardinality is at least one quarter of the original total expected marked mass;
- the total full cardinality is at most twice the original total expected full mass;
- marked shadings are subsets of full shadings;
- selected full/marked incidences have respectively positive `p`/`q`.

The quarter-mass claim uses the explicit input that high cells carry at least half the original expected marked mass, as in (6.13). Actual marked-cardinality sums are connected to high-cell column sums by a proved double-counting identity.

## Explicit numeric hypotheses

The genuinely unproved application inputs are plainly exposed:

- `4 * expected_ball_count ≤ ball_cutoff`;
- `1000 * expected_cap_count ≤ expected_marked_cell_count` on high cells;
- high expected marked mass is at least half the total;
- the sum

  `Σ_t 2 exp(−μ_t/12) + Σ_(t,b) exp(−u_tb/4) + Σ_(c high) exp(−μ_c/8) + Σ_(c high,a) exp(−μ_c/8)`

  is less than one.

`failureBudget_le_uniform` further bounds this budget using actual numbers of tubes, balls, high cells and caps and uniform lower bounds `μFull`, `μBall`, `μHigh`:

`2 #T exp(−μFull/12) + #T #B exp(−μBall/4) + #High (1+#A) exp(−μHigh/8)`.

Thus the next large-scale asymptotic argument has a concrete finite bound to use.

## Requested capped-weight specialization

`capped_sampling_assembly` specializes the construction to

`p(t,c)=min(1,alpha*w(t,c))`, `q(t,c)=min(1,beta*w(t,c))`

for `w≥0` and `0≤beta≤alpha`. Valid probabilities and the coupling inequality are proved from these hypotheses. The same realization and all `SampleGood` conclusions follow under the corresponding explicit expected-mass and numeric-budget hypotheses.

## Relation to (6.7), (6.8), and (6.9)

`SampleGood.density_normalization` sets `r=lambda*N`. From `c0*r≤μ_t≤C0*r` and expected marked mass at least `xi*r*#T`, it proves both

`c0*r/2 ≤ #Y_t ≤ 2*C0*r`

and

`xi/(8*C0) * Σ_t #Y_t ≤ Σ_t #H_t`.

These are exactly the finite cardinality conclusions (6.7) and (6.9). `SampleGood.relative_ball_bound` derives a relative two-ends-style bound from a ball cutoff at most a specified nonnegative factor times the expected full tube count and the retained density lower bound. It does not silently assume a geometric two-ends estimate.

## Remaining scope

This completes a substantial **finite probabilistic assembly**, not the entire geometric Lemma 6.1. Remaining interfaces are: deriving `p,q` from actual measurable intersections; deriving the ball/cap expectation inequalities from geometry and pointwise broadness; constructing geometric finite ball/cap nets and controlling their sizes; proving that the explicit probability budget becomes small under the stated `N,lambda,alpha,s` asymptotics; deriving the low-cell alternative when high mass is below half; and translating finite test inequalities to every Euclidean ball/cap with the required constants. The arbitrary finite-label geometry is deliberate and fully visible in the input types and hypotheses.
