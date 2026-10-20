# `PottsContinuity/Infinite/`

FKG inequality, comparison, domain Markov property, translation and lattice symmetries for the infinite-volume measures.

13 modules, 2,291 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`Bridge`](Bridge.lean) | Bridges from the frozen every-exhaustion limit to the PD box limit. The PD library uses the same finite random-cluster probabilities, after … |
| [`ClopenFKG`](ClopenFKG.lean) | FKG for increasing clopen events under free and wired limits. |
| [`ComparisonStatements`](ComparisonStatements.lean) | Public comparison statements with the frozen every-exhaustion hypothesis. |
| [`FiniteGraphComparison`](FiniteGraphComparison.lean) | Declarations: `latticeGraphRestriction`, `latticeGraphEvent`, `latticeGraphEvent_isCylinder`, `boxVertexEmbedding_of_mem`, … |
| [`FiniteGraphDMP`](FiniteGraphDMP.lean) | Declarations: `finite_induced_pullback_boundary_le_wired`, `embeddedOutsideState`, `embedded_joint_le_boundary_order` |
| [`InducedDMP`](InducedDMP.lean) | Declarations: `inducedDMP_inter_symmDiff_subset_right`, `inducedDMP_measureReal_symmDiff_lt_of_ennreal`, `inducedDMP_abs_measureReal_inter_sub_le`, `mappedEdgeEmbedding_factor`, … |
| [`LocalComparisons`](LocalComparisons.lean) | Local event comparison for free and wired square-box FK laws. |
| [`MeasurableApprox`](MeasurableApprox.lean) | Declarations: `finiteUpperHull`, `finiteUpperHull_isUpperSet`, `finiteUpperHull_isClopen`, `finiteUpperHull_subset`, … |
| [`MeasurableDomination`](MeasurableDomination.lean) | Declarations: `free_infinite_le_wired_infinite_measurable` |
| [`MeasurableFKG`](MeasurableFKG.lean) | Declarations: `probabilityMeasure_fkg_of_clopen_ennreal`, `ennreal_fkg_of_probabilityMeasure_fkg`, `free_infinite_FKG_measurable`, `wired_infinite_FKG_measurable` |
| [`Parameters`](Parameters.lean) | Source-parameter adapter for the reusable finite and infinite FK library. |
| [`Symmetry`](Symmetry.lean) | Lattice symmetry invariance for free and wired infinite-volume limits. |
| [`Translation`](Translation.lean) | Translation invariance for the frozen every-exhaustion limit. |
