# Independent review of the authorized external inputs

Checked 6 September 2026. The user has now authorized custom axioms for published results. This supersedes the earlier no-custom-axioms status in `external_theorem_boundary.md`; it does not authorize treating the manuscript's novel generalized pivot as a published theorem. Root owns `ExternalAxioms.lean`; this review made no edits to it.

## Exact primary-source statements

**Wolff (1995), Theorem 1, printed p. 652.** The operator estimate has input exponent `d=(n+2)/2`, angular output exponent `(n−1)d'`, and every positive scale loss. The page explicitly says the two-dimensional case is already known, while the paper's argument assumes dimension at least three. Thus the combined result is valid for integer `n≥2`. I independently inspected the publisher's scanned page, including the definitions of the exponents and the small-dimensional qualification. [Publisher PDF](https://ems.press/content/serial-article-files/37888?nt=1).

**Katz–Tao (2002), Theorem 1.1 and Section 5.** The verified version is arXiv `math/0102135v1`, 16 February 2001. The maximal theorem uses input `d=(4n+3)/7` and angular output `q=n+3/4=(4n+3)/4=(n−1)d'`. It has every positive scale loss and applies in integer dimensions `n≥2`; Section 5 explains that the lower-dimensional cases follow from Wolff. Equation (30) is its density-sensitive discrete restricted estimate, with factors `λ^((4n+3)/7) N (#T)^(4/7)`, under the section's scale-loss notation. Separately, Definition 6.1 requires saturated shadings. Equation (40) drops family-size saturation only. Theorem 6.2 assumes `0<d<n` and proves `K(n,d), K(d+1,d′) ⇒ K(n,(2n+1+d′)/4)` for that saturated framework. It does not assert the manuscript's arbitrary-density recursion. [Primary PDF](https://arxiv.org/pdf/math/0102135v1).

**Zahl (2021), Theorem 1.5, equation (1.6).** The verified version is arXiv `1908.05314v4`, 12 January 2021. For each integer `n≥2`, the maximal estimate holds at

`d(n)=max_{j∈{2,…,n}} min(n−j+2, (n²+j²+n−j)/(2n))`.

The meaning of “at dimension d” is equation (1.1): the overlap norm has exponent `d/(d−1)`, scale factor `δ^(-(n/d−1+ε))`, and total tube-volume factor to power `(d−1)/d`, for every `ε>0`. The geometric objects are direction-separated open unit cylinders of radius `δ`. This is an endpoint dimension statement with arbitrary positive scale loss. In particular the formula gives `d(6)=4` and `d(8)=21/4`. [Primary PDF](https://arxiv.org/pdf/1908.05314v4).

**Hickman–Rogers–Zhang.** The checked arXiv version of Theorem 1.2 states a strict range in the adjoint exponent: `p>1+min_j max(2n/[n(n−1)+j(j−1)],1/(n−j+1))`. It is consistent with Zahl's benchmarks, but should not be quoted verbatim as an endpoint adjoint-norm theorem. Importing Zahl's explicitly stated endpoint dimension is simpler than silently closing this strict range. [Primary PDF](https://arxiv.org/pdf/1908.05589).

**Wang–Zahl.** In the manuscript's cited version `2502.17655v1`, Lemma 7.8 concerns separated vectors in arbitrary integer dimension and supplies disjoint caps, broad subsets, and logarithmically retained population. Corollary 7.10 is instead a tube/shading statement in `R³`. It does not directly supply the higher-dimensional assignment and transport interfaces. The local angular selection has already been proved, so importing this result would not remove a current need. This citation is a preprint version. [Primary PDF, printed pp. 63–64](https://arxiv.org/pdf/2502.17655v1).

## Proposed Lean boundary and exponent check

The recommended trusted consequence is a normalized restricted-shading bound in integer dimension `n`, for fixed positive separation and bounded-region constants chosen before all configurations. Its conclusion is

`c δ^(2n−1−d+ε) λ^d M ≤ volume(⋃ᵢ Yᵢ)`.

The actual tube shadings are measurable, lie inside their unit tube carriers, and each has measure at least `λ` times the actual carrier volume, with `0<δ≤1`, `0<λ≤1`. Constants are uniform in scale, density, number of tubes, positions, and any auxiliary cap coefficient.

This displayed statement is a **normalized restricted-shading corollary**, not a verbatim operator theorem. The following explanation is an independent mathematical inference, not an assertion that these adapters have all been checked by Lean:

* Writing `S=Σᵢ volume(Tᵢ)`, an adjoint overlap bound at exponent `d/(d−1)` and Hölder give `volume(⋃Yᵢ)≥c λ^d δ^(n−d+ε) S`. Since `S` is comparable to `M δ^(n−1)`, the displayed exponent follows.
* From an angular maximal bound with output `(n−1)d'`, testing the union of shadings first gives a power `s^((d−1)/(n−1))`, where `s=Mδ^(n−1)`. Direction packing bounds `s` by a fixed constant, and `d≤n` allows this power to be bounded below by a fixed multiple of `s`. This yields the same weaker linear-population conclusion.
* Enlarging cylinders, changing between angle and projective chord separation, allowing a fixed separation coefficient, replacing cylinders by closed capsules, extending from sufficiently small scales to `δ≤1`, and comparing volume conventions incur fixed constants. Root explicitly includes these normalization steps in the trust boundary. The existing measurable-to-grid conversion remains a proved adapter.

## Read-only check of `ExternalAxioms.lean`

The three declarations currently have the correct integer range and exponents. `zahlExponent` takes the supremum over exactly the finite integer interval `[2,n]`; its unused `n<2` branch introduces no assertion. `NormalizedShadingBound` chooses `c` before every configuration and omits `A` from the numerical bound. The predicate still quantifies records containing a cap bound, so “cap-independent” refers to the bound and constant rather than the complete absence of a cap hypothesis. This is harmless and weaker than the imported corollary.

The proved `to_measurable` adapter only inserts `A⁻¹≤1`, using nonnegative factors. The subsequent `to_discrete` invokes the already proved actual measurable-to-grid conversion. No real-cap or larger-ambient claim is introduced by either step. The theorem names and module documentation identify the added trust explicitly. I found no statement-fidelity defect in these declarations.

## What these inputs actually replace

They discharge `DiscreteEstimate n (n−1) d d` for the named exponents and certify the published integer-dimensional benchmarks. They can provide the final analytic input after a separately proved projection into that dimension.

They do not directly discharge a lifted interface `DiscreteEstimate (k+3) d d′ q` with nonmaximal or fractional cap parameter `d`, nor the full `RealCapEstimate` recursion. The existing `FractionalSeed` is a proved source for its own real-cap range; the density-sensitive marked pivot, sampling, angular assembly, and two-ends removal retain their own exact proof obligations. In particular, importing the saturated Katz–Tao recurrence under the type of the manuscript's arbitrary-density pivot would be a substantive and unsupported strengthening.

The earlier independent sampling-interface review was saved as `audit_work/sampling_pivot_interface_review.md` before this research task began. No unfinished Lean edit was left by the task change.
