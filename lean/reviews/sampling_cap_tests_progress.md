# Actual finite angular tests for sampling

SamplingCapTests.lean constructs one test centered at each original tube direction. The index type is exactly Fin M, whose count has the existing actual separated_total_tube_count bound. No angular-net or theta-dependent covering-count hypothesis is used.

For any finite actual marked row and any center v, a nonempty radius-theta cap contains an original row member a. The proved projective triangle inequality places its entire intersection with the row in a's radius-2theta test. Empty intersections and empty rows are handled directly.

sampled_broadness applies this containment to the literal markedShading of SamplingApplication, giving the one-tenth angular bound at every cell and center, including cells outside the high set. Exact identities relate actual row/cap cardinalities to markedCellCount and markedCapCount. The only angular input is the finite tests in SampleGood.

This closes the finite-to-all-centers angular transfer. Measurable cap expectations and the probability threshold remain separate constructions; the module does not by itself prove the sampling lemma or unrestricted pivot.

Verification: clean Lean 4.33.1 build; all 11 local theorem declarations, including generated ones, passed the full-source environment audit with standard foundations only. No diagnostics or proof placeholders. SHA-256 a015db6172d1e1da545e582b08c3b5aa20c1db1ae00ab7df18047ba504c50157. Development after checkpoint 12; not delivered until included in a later full manifest.
