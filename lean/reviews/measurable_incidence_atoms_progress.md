# Exact measurable incidence-pattern atoms

`MeasurableIncidenceAtoms.lean` is frozen and clean compiled. SHA-256: `7d34c48a3f0c680477287f10fb43c87dd0c367708d93ebe770867f0b4e21d2a6`.

The exact-source audit passes all 34 local declarations (30 local theorems; 22 source theorem statements and four definitions), with only the standard foundational axioms. No `sorry`, custom axioms, or diagnostics remain.

For any finite family of measurable sets of finite measure, this module constructs its literal nonempty incidence-pattern atoms. These are pairwise disjoint measurable sets, each lying inside every shading named in its pattern. Their union is exactly the old shading union. Atom measures sum exactly to the old union measure, and the weighted sum of atom measures times incidence cardinality equals exactly the summed per-tube shading measure.

Any finite retained row assigned to each pattern is realized by actual finite unions of these same atoms. Its incidence pattern is exactly the assigned row at every point of the old union and is empty everywhere outside that union. This is a pointwise identity, not an almost-everywhere replacement. A row-subset condition gives each new shading as a subset of its own original shading. Measurability, finite measure, union containment, individual mass, and total incidence mass are proved for the realization.

The number of patterns can be exponential, but no quantitative constant uses that number: every measure identity is exact and enters the angular selection solely through nonnegative atom weights. This supplies the measurable-to-finite bridge for weighted angular assignment. Weighted scale/group selection and continuous all-angle hairbrush summation are subsequent work, not assumptions or conclusions of this module.
