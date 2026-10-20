# `PottsContinuity/DualityExt/`

Planar duality for general finite domains and annuli.

59 modules, 10,147 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`AnnulusBoundaryIdentification`](AnnulusBoundaryIdentification.lean) | Declarations: `annulusHostRectangle_eq_box`, `annulusPrimalBoundaryClasses_union_eq_vertexBoundary`, `annulus_jointWired_p5a_noFullBoxCrossing_ge_div_at_fullVertexBoundary_of_actualDualMapEq` |
| [`AnnulusCandidateBoundaryPartition`](AnnulusCandidateBoundaryPartition.lean) | Declarations: `annulusCandidateInnerBoundaryClass`, `annulusCandidateOuterBoundaryClass`, `annulusCandidateBoundaryClasses_disjoint`, `annulusCandidateActive_twoBlock_partition_iff`, … |
| [`AnnulusCounterexample`](AnnulusCounterexample.lean) | A boundary-condition counterexample for annulus circuit wording. In the radius-one annulus, a closed dual circuit can have nonzero winding … |
| [`AnnulusFullBoxCrossingTransfer`](AnnulusFullBoxCrossingTransfer.lean) | Declarations: `annulusSourceFullBoxCrossingEvent`, `p5aAnnulusPrimalDualJordanEvent_subset_noFullBoxCrossing` |
| [`AnnulusOuterHostGeometry`](AnnulusOuterHostGeometry.lean) | Declarations: `annulusCandidateDualTranslatePlus`, `annulusCandidateDualTranslateMinus`, `annulusCandidateDualTranslatePlus_adj`, `annulusCandidateDualTranslateMinus_adj`, … |
| [`AnnulusOuterHostInnerConnectivity`](AnnulusOuterHostInnerConnectivity.lean) | Declarations: `annulusExpandedHostEmbedding`, `annulusExpandedHostSourceMap_edge_bond_endpoints`, `annulusExpandedHost_innerEndpoint_edge_mem_removed`, `annulusExpandedHost_innerBox_mem_host`, … |
| [`AnnulusOuterHostOuterConnectivity`](AnnulusOuterHostOuterConnectivity.lean) | Declarations: `expandedHostOuterBoundaryCoord`, `expandedHostOuterBoundary`, `annulusExpandedHostPrimalOuterClass`, `expandedHost_rect_mem_outerBox`, … |
| [`AnnulusPlaneEventRestriction`](AnnulusPlaneEventRestriction.lean) | Declarations: `annulusSourcePlaneEmbedding`, `annulusSourcePlaneGraph_map_le_square`, `annulusSourcePlaneConfiguration`, `annulusSourcePlaneConfiguration_adj`, … |
| [`AnnulusRemovedDualEdgeClassification`](AnnulusRemovedDualEdgeClassification.lean) | Declarations: `annulusCandidateDualOuterHostGraph_map_toExpandedHost_eq`, `annulusCandidateRemovedDualEdge_missingAndTwoBlock` |
| [`AnnulusWiredBoxDMP`](AnnulusWiredBoxDMP.lean) | Declarations: `annulusToBoxVertex`, `annulusSourceGraph_map_le_boxGraph`, `annulusSourcePlaneRestriction_eq_boxRestriction` |
| [`CrossingRestriction`](CrossingRestriction.lean) | Local crossing duality inside a larger rectangular volume. The crossing event uses only the edges of its test rectangle. |
| [`GeneralFiniteDuality`](GeneralFiniteDuality.lean) | Rectangular FK duality for all positive cluster weights. The reusable PD random-cluster parameter carrier assumes `q ≥ 1`. |
| [`PositiveAnnulusDualShell`](PositiveAnnulusDualShell.lean) | Declarations: `annulusHostAnchor`, `annulusSourceGraph`, `annulusSourceEmbedding`, `annulusSourceGraph_map_le_host`, … |
| [`PositiveAnnulusDualTransfer`](PositiveAnnulusDualTransfer.lean) | Declarations: `annulus_jointWired_dualSubevent_measure_ge_div_of_doubleDualGeometry` |
| [`PositiveAnnulusPrimalDMP`](PositiveAnnulusPrimalDMP.lean) | Declarations: `annulusPrimalSeparatedBoundary`, `annulusPrimalInnerBoundaryClass`, `annulusPrimalOuterBoundaryClass`, `annulusPrimalInnerOuter_disjoint`, … |
| [`PositiveAnnulusPrimalPartition`](PositiveAnnulusPrimalPartition.lean) | Declarations: `annulusHostPrimalInnerClass`, `annulusHostPrimalOuterClass`, `annulusHostPrimalInnerOuter_disjoint` |
| [`PositiveBoundaryMerge`](PositiveBoundaryMerge.lean) | Exact positive-`q` reweighting when two wired boundary classes are merged. The annular transfer compares separately wired inner and outer … |
| [`PositiveBoundaryMergeDualTransfer`](PositiveBoundaryMergeDualTransfer.lean) | Conditional finite-volume annulus transfer. This module composes a proved FK law duality with a deterministic event identification and the … |
| [`PositiveBoundaryMergePDTransfer`](PositiveBoundaryMergePDTransfer.lean) | PD-measure consumer for the two-block dual transfer. This module exposes the positive-probability two-block transfer in the `PD.FK.measure` … |
| [`PositiveBoundaryReweighting`](PositiveBoundaryReweighting.lean) | Exact event reweighting under a two-class boundary merge. Merging separately wired boundary classes multiplies the unnormalized mass of the … |
| [`PositiveConditionedSubgraphDuality`](PositiveConditionedSubgraphDuality.lean) | Declarations: `rectangleSubgraphDualOpenRemovedState`, `rectangleSubgraphDualRemovedState_map_subset`, `positiveRemainingWeight_subgraph_conditioned`, `rectangleSubgraphDualConditioned_decomposition`, … |
| [`PositiveConnectedBoundaryPartition`](PositiveConnectedBoundaryPartition.lean) | Boundary connectivity criterion for the induced dual partition. The rectangle restriction law produces a boundary partition from the forced … |
| [`PositiveDomainMarkov`](PositiveDomainMarkov.lean) | Finite domain Markov conditioning for every positive cluster weight. The PD conditional-law API is parameterized by `q ≥ 1`. |
| [`PositiveDualOpenAdjState`](PositiveDualOpenAdjState.lean) | Declarations: `embeddedRectangleDualOpenAdj_crossedSourceClosed` |
| [`PositiveDualSubgraphEdgeState`](PositiveDualSubgraphEdgeState.lean) | Declarations: `mem_edgeRestrictionConfigurationEquiv_symm`, `rectangleSubgraphDualEdgeEmbedding`, `rectangleSubgraphDualEdgeEmbedding_crossingBond`, `rectangleSubgraphDualConfigurationEquiv_edgeState` |
| [`PositiveDualSubgraphLaw`](PositiveDualSubgraphLaw.lean) | The induced dual law as a graph law. The remaining-edge law produced by rectangle conditioning is exactly the positive FK law on the … |
| [`PositiveEmbeddedDualEdgeState`](PositiveEmbeddedDualEdgeState.lean) | Declarations: `embeddedRectangleSubgraphDualConfiguration_edgeState` |
| [`PositiveEndpointDualSubgraphLaw`](PositiveEndpointDualSubgraphLaw.lean) | Endpoint-only dual laws for rectangular subgraphs. The rectangle conditioning proof keeps the full host dual vertex carrier. |
| [`PositiveFreeDomainComparison`](PositiveFreeDomainComparison.lean) | Declarations: `measure_toReal_eq_expectation_indicator`, `event_indicator_monotone`, `free_embedded_event_measure_le`, `free_embedded_event_measure_le_of_target_partition`, … |
| [`PositiveGraphRelabeling`](PositiveGraphRelabeling.lean) | Relabeling finite positive-`q` FK laws. Transporting a finite graph by a vertex equivalence transports its boundary partition and its … |
| [`PositiveInducedSourceBoundaryLaw`](PositiveInducedSourceBoundaryLaw.lean) | Declarations: `embeddedSubgraphInducedDualBoundary`, `positive_embedded_subgraph_induced_duality_law_of_sourcePartition`, `positive_embedded_subgraph_induced_duality_law_PD_of_sourcePartition` |
| [`PositiveInducedWiredDuality`](PositiveInducedWiredDuality.lean) | Wired-side duality with the boundary partition induced by rectangle restriction. When a dual subgraph is embedded in a rectangular host … |
| [`PositiveIsolatedBoundaryLaw`](PositiveIsolatedBoundaryLaw.lean) | Isolated-vertex carrier changes for positive-`q` FK laws. When a graph is embedded into a larger vertex carrier and the added vertices are … |
| [`PositiveP5aAnnulusActualDual`](PositiveP5aAnnulusActualDual.lean) | Declarations: `p5aAnnulusFaceBaseEmbeddingActual`, `p5a_annulus_vertex_not_mem_dualFaceBox`, `p5aAnnulusFaceGraph_map_le_annulusSourceDualGraph`, `p5aAnnulusFaceGraphActual_map_le_annulusSourceDualGraph` |
| [`PositiveP5aAnnulusActualDualJordan`](PositiveP5aAnnulusActualDualJordan.lean) | Declarations: `p5aAnnulusSourceFaceBaseEmbeddingActual`, `p5a_annulus_sourceFaceGraph_map_le_actualDual`, `p5aAnnulusSourceActualDualJordanEvent`, `p5a_annulus_sourceJordan_restriction_subset_actualDual`, … |
| [`PositiveP5aAnnulusActualDualLaw`](PositiveP5aAnnulusActualDualLaw.lean) | Declarations: `p5aAnnulusActiveDualJordanEvent`, `annulusPrimalToActiveDualConfigurationEquiv`, `p5aAnnulusPrimalDualJordanEvent` |
| [`PositiveP5aAnnulusDualMapBridge`](PositiveP5aAnnulusDualMapBridge.lean) | Declarations: `p5aAnnulusMergeActualDual_eventInterfaces_of_configurationMapEq`, `p5aAnnulusMergeActualDual_sourceEvent_eq_of_configurationMapEq`, `annulus_jointWired_p5aJordan_measure_ge_div_of_actualDualMapEq`, `annulus_jointWired_p5a_noFullBoxCrossing_ge_div_of_actualDualMapEq` |
| [`PositiveP5aAnnulusFit`](PositiveP5aAnnulusFit.lean) | Declarations: `dualFaceBox`, `mem_dualFaceBox`, `p5aAnnulusVertexSet`, `dualFaceAnnulusShell`, … |
| [`PositiveP5aAnnulusInnerClass`](PositiveP5aAnnulusInnerClass.lean) | Declarations: `p5a_polygon_vertex_not_mem_box`, `p5aVertexBoxEmbedding`, `p5aBoxGraphHom`, `p5a_polygon_domain_contains_vertexBox` |
| [`PositiveP5aAnnulusMapByEdge`](PositiveP5aAnnulusMapByEdge.lean) | Declarations: `p5aCandidateToActualDualEdgeEquiv`, `p5aActiveDoubleDualToSourceEdgeEquiv`, `p5aSourceToActualDualEdgeEquiv`, `p5aAnnulusCompositeDualMap_eq_of_edgeLabelAgreement` |
| [`PositiveP5aAnnulusMergeActualDual`](PositiveP5aAnnulusMergeActualDual.lean) | Declarations: `positiveFKLaw_map_cast_of_graph_eq`, `annulusCandidateToActualDualConfigurationEquiv`, `annulusCandidate_freeLaw_map_eq_actualDual_freeLaw` |
| [`PositiveP5aAnnulusNoOpenCrossing`](PositiveP5aAnnulusNoOpenCrossing.lean) | Declarations: `p5aAnnulusWalk_edge_mem_step`, `p5aAnnulusMappedWalk_edge_mem_step`, `annulusPrimalOpenGraphToSquare`, `annulusPrimalOuterBoundaryClass_mem_outerBoundary`, … |
| [`PositiveP5aJordanAnnulusTransfer`](PositiveP5aJordanAnnulusTransfer.lean) | Declarations: `p5aAnnulusVertexSet_eq_source` |
| [`PositiveP5aPolygonPDWalk`](PositiveP5aPolygonPDWalk.lean) | Declarations: `p5aPolygonToPD`, `p5aForwardPolygonCycle_isCycle`, `p5aPolygonCyclePD`, `p5aPolygonCyclePD_isCycle`, … |
| [`PositiveP5aRayIndexBarrier`](PositiveP5aRayIndexBarrier.lean) | Declarations: `primalWalk_rayIndex_eq_of_crossedEdges_avoided`, `no_primalWalk_of_distinct_rayIndex_and_crossedEdges_avoided` |
| [`PositiveP5aSourceAnnulusTransfer`](PositiveP5aSourceAnnulusTransfer.lean) | Declarations: `p5aAnnulusSourceFaceGraph`, `p5aAnnulusSourceJordanCircuitEvent`, `p5aAnnulusSourceJordanCircuitEvent_upper`, `p5aAnnulusProbability_eq_sourceFaceMeasure` |
| [`PositivePDLawBridge`](PositivePDLawBridge.lean) | Bridge the positive-parameter law to the PD finite FK law. For `q ≥ 1`, both APIs normalize the same finite FK weights. |
| [`PositivePolygonCycleDomain`](PositivePolygonCycleDomain.lean) | Declarations: `p5aForwardCycle`, `p5aCyclicWalk_getVert`, `p5aCyclicWalk_length`, `p5aForwardCycle_length`, … |
| [`PositivePolygonCycleEdgeIndex`](PositivePolygonCycleEdgeIndex.lean) | Declarations: `polygonCyclicList_chain_local`, `polygonCyclicWalk_length_index`, `polygonCyclicWalk_getVert_index`, `polygonLastIndex_succ_local`, … |
| [`PositivePolygonLatticeCycle`](PositivePolygonLatticeCycle.lean) | Declarations: `polygonCyclicList`, `polygonLastIndex`, `polygonCyclicWalk`, `polygonCyclicList_head`, … |
| [`PositivePolygonRayIndex`](PositivePolygonRayIndex.lean) | Declarations: `polygonRay_interiorCell_adjacent_index`, `polygonRay_domain_vertex_index_ne_zero`, `polygon_domain_avoids_outerBoundary_of_faceBox` |
| [`PositiveRectangleSubgraphDuality`](PositiveRectangleSubgraphDuality.lean) | Positive-`q` dual transport for edge subgraphs of a rectangle. The dual carrier of a rectangle subgraph is represented as the rectangle … |
| [`PositiveSubgraphCrossingTransfer`](PositiveSubgraphCrossingTransfer.lean) | Probability transfer for a subgraph crossing and its forced-open dual. The deterministic crossing-complement theorem applies to a bond … |
| [`PositiveSubgraphDualEdgeEquiv`](PositiveSubgraphDualEdgeEquiv.lean) | Declarations: `rectangleSubgraphDualEdgeEquiv`, `rectangleSubgraphDualEdgeEquiv_crossingBond` |
| [`PositiveTwoBlockPullback`](PositiveTwoBlockPullback.lean) | Pullback of a separately wired boundary partition. The two-block partition is preserved by an injective carrier map when its classes are … |
| [`PositiveWiredArcInducedLaw`](PositiveWiredArcInducedLaw.lean) | Declarations: `positive_embedded_wiredArc_induced_duality_law_PD_at_selfDualParameter_of_sourcePartition` |
| [`PositiveWiredDualEdgeState`](PositiveWiredDualEdgeState.lean) | Declarations: `positiveActiveEdgeToGraphEquiv`, `configurationCast_setEq_eq_edgeMap`, `positiveActiveConfigurationEquiv_apply_edgeMap`, `positiveActiveConfigurationEquiv_edgeState`, … |
| [`PositiveWiredDualSubgraphLaw`](PositiveWiredDualSubgraphLaw.lean) | Wired laws from a free law on the dual subgraph. Applying the proved rectangle free-subgraph duality to a rectangle containing the source … |
| [`RectangleResults`](RectangleResults.lean) | Source-facing finite planar duality interfaces. The finite graph interface below records an arbitrary finite square-lattice subgraph by its … |
