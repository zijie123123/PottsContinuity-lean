# `PottsContinuity/Exploration/`

Explorations of random-cluster configurations, stopping sets and their domain Markov property.

17 modules, 2,248 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`BoundaryClusterDMP`](BoundaryClusterDMP.lean) | A finite wired-boundary cluster exploration and its conditional law. |
| [`BoundaryClusterPathSelector`](BoundaryClusterPathSelector.lean) | Declarations: `BoundaryClusterPathWitness`, `boundaryClusterPathCode`, `boundaryClusterPathCodeSet`, `boundaryClusterPathCodeSet_nonempty_iff`, … |
| [`BoundaryClusterStatisticDMP`](BoundaryClusterStatisticDMP.lean) | Declarations: `boundaryClusterStatistic`, `boundaryClusterStatistic_fiber_eq_revealRecordEvent`, `boundaryCluster_statistic_pullback_boundary_discrete`, `finiteStatisticConditionalPMF_boundaryCluster_embeddedIncreasingEvent_le_freeGraph` |
| [`CircuitFiberFreeComparison`](CircuitFiberFreeComparison.lean) | Conditional free law on an attained finite selector fibre. The finite stopping-set DMP is usually written as a PMF filtered on the record … |
| [`ConnectedBoundaryInclusion`](ConnectedBoundaryInclusion.lean) | A connected set of lattice cells is determined in the inclusion order by its boundary bonds and one marked cell. |
| [`ConnectedCellSetCycleEnvelope`](ConnectedCellSetCycleEnvelope.lean) | A finite connected set of lattice cells is contained in a simple cycle whose crossed bonds lie on the cell boundary. |
| [`DependentPairPathDMP`](DependentPairPathDMP.lean) | A sequential pair record can retain a second path chosen from the first record. |
| [`ExtremalPathDMP`](ExtremalPathDMP.lean) | One-sided path-selector DMP interface. If a selected path is unchanged by edits strictly above it, revealing all edges on or below that … |
| [`FiniteEnvelopeMaxSelector`](FiniteEnvelopeMaxSelector.lean) | Declarations: `envelopeCandidateSet`, `envelopeMaxCandidate`, `envelopeMaxCandidate_spec`, `envelopeMaxCandidate_exists_iff`, … |
| [`FiniteFiberComparison`](FiniteFiberComparison.lean) | Declarations: `pmf_event_le_reference_add_bad_of_goodFiberBound` |
| [`FiniteOutermostSelectorDMP`](FiniteOutermostSelectorDMP.lean) | Finite ordered outermost selectors. For a finite family of candidates, recognizability of a candidate from an exterior edge set is … |
| [`FiniteStoppingSetDMP`](FiniteStoppingSetDMP.lean) | Finite stopping-set domain Markov property. The revealed edge set may depend on the configuration. |
| [`FrozenBoundaryFreeInterior`](FrozenBoundaryFreeInterior.lean) | Free induced boundary on an isolated interior. If no revealed open edge is incident to an interior set, and the set is disjoint from the … |
| [`InteriorFreeLaw`](InteriorFreeLaw.lean) | Free FK law on a region after its exterior is frozen. If the revealed edge set is exactly the complement of an embedded finite subgraph … |
| [`RectangleTopFrontierDMP`](RectangleTopFrontierDMP.lean) | Conditional law for the canonical upper rectangle frontier. This is the upper-side exploration of `Thm3.Push.TopFrontierDMP`, re-exported … |
| [`RectangleTopFrontierPathSelector`](RectangleTopFrontierPathSelector.lean) | A deterministic path witness attached to the upper-frontier record. The path is selected by minimizing its explicit … |
| [`SourceTraceFiberOpen`](SourceTraceFiberOpen.lean) | Declarations: `openWalk_transfer_of_edgewise_adjacency` |
