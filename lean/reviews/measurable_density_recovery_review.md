# Independent review of actual measurable density and marked broadness recovery

Read-only review of all356 lines of MeasurableDensityRecovery.lean. No mathematical statement defect found.

Good indices are selected using the actual threshold eta*lam/2 and injectively reindexed through the finite set. The old global retained mass eta*lam*M and per-index upper2*lam yield good total≥eta*lam*M/2 and good count≥eta*M/4. Empty original families remain allowed, while good_card_pos separately requires M>0. The module does not claim positive population from vacuous hypotheses.

The marked set uses the actual original Ref multiplicity, including references for all discarded original indices. Its threshold is (eta/8)*multiplicity(Ref)≤multiplicity(selected O). Outside that set, discarded selected incidence is pointwise at most eta/8 of Ref incidence. Measurability and finite integrability are constructed from the actual sets. Integration gives discarded mass≤eta/8*sum Ref≤eta*lam*M/4≤half good selected mass. Thus the factor1/2 in marked_mass_lower is justified.

Broadness is inherited from Ref, not assumed for O: an actual injective map sends each selected cap population into the old Ref cap population, and the mark gives the population ratio8/eta. The conclusion holds on marked points for the full selected output shading family. It is not a claim of broadness at every point of the selected union or of per-tube mass lower bounds for each marked intersection.

Two-ends uses Full, the actual inclusion O⊆Ref⊆Full, the selected measure threshold, and the old Full upper bound. The measure ratio Full≤(4/eta)*selected gives the exact coefficient4B/eta on the same radius interval delta≤r≤1. It applies to full selected output shadings, which are the appropriate reference shadings for the marked kernel. A subsequent arbitrary per-tube marked intersection would require its own relative-density argument; this module does not claim one.

The cap and separation inheritance lemmas use the true injective reindexing, so removed indices cease contributing to cap counts. The selected finite-cell field is simply inherited as ancillary data; no grid admissibility is inferred from measurable selection. Full need only have finite outer measure in the main recovery statement; this is sufficient for monotonicity against the measurable Ref and O subsets, and no unsupported Full measurability is invoked.
