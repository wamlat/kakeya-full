# Weighted angular selection for arbitrary measurable incidence atoms

Two new modules generalize the actual finite angular construction to arbitrary nonnegative real atom weights. Combined with MeasurableIncidenceAtoms, these weights are the exact volumes of the original family's measurable incidence-pattern regions, with no grid approximation and no dependence on the number of atoms in any quantitative constant.

## Proved construction

`WeightedAngularAssignment` proves exact weighted incidence double counting, nonnegative tube/group weights, actual support of every nonzero weight, and actual finite maximizing assignment. The directional support-count bound yields the same inverse overlap retention as before, including zero weights. The original restoration test compares pointwise before/after cardinalities, not weighted cardinalities. A separate weighted bad-mass estimate proves three-quarter restoration retention without dividing by atom weights. Thus original pointwise broadness remains valid and zero-volume regions are treated correctly.

`WeightedAngularSelection.common_scale_pieces` constructs the disjoint broad decomposition for every finite incidence row. It selects one common angular scale by weighted averaging over exactly J+1 scales; the logarithmic depth loss is unchanged. It does not average over atoms, and no atom-count factor is introduced.

`actual_angular_groups` constructs an actual separated projective net, groups each real piece into a containing radius3tau cap, and preserves weighted incidence by exact disjoint finite double counting. Its directional support bound is dimension-only; pointwise group overlap is at most2tau^(-beta).

`actual_angular_assignment` combines both constructions. It outputs actual kept rows, one assigned cap per original tube, row-subset and unique-assignment properties, the actual local-cap property, at least3/[8C(J+1)] of original weighted incidence, pointwise broadness constant4^beta*4C and overlap2tau^(-beta). Here C=packingConstant(k)*3^k; all geometry uses original tube directions only, independent of atom positions, shape, volume and count.

Input: any TubeFamily(k+1)M with M>0; any finite atom type and atom set; arbitrary nonnegative real weights on that set; a nonempty finite row of original indices at each included atom; delta in(0,1] and beta>=0. No cap, sample, selected-piece or output premise is assumed. Shading/admissibility properties are not required by this purely angular theorem. Actual measurable realization and subsequent hairbrush assembly remain separate modules; these two files alone are not the continuous (4.4) theorem.

## Validation

Both production sources compiled without diagnostics, then the unchanged production declaration-audit machinery recompiled their exact bytes and checked all local theorem and non-theorem declarations, source theorem coverage, absence of admission/unsafe/custom-axiom shortcuts and standard-only dependencies.

- WeightedAngularAssignment: `5911fd148595d7a4c0237d6b25652f3a96371f15226e88961b8469a8716a3f07`, 9 all local declarations, 8 theorem declarations, PASS.
- WeightedAngularSelection: `32e4882cd70e10a8f602b4dd2e1b93a48d8743851d4b4ed3dea0bb937ff02597`, 13 all local declarations, 13 theorem declarations, PASS.
