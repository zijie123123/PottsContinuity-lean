# `PottsContinuity/PlanarMixed/`

Mixed boundary conditions and the crossing estimate (3) on squares (`Square/`), the corrected connector events of Lemma 4 (`Lemma4Connectors/`, `Lemma4StoppingRecords/`, `Lemma4RecordCarrier/`), local selectors for Lemma 2 (`StripRSWSelectors/`), the half-height bound of Lemma 6 (`TiltedHalfHeight/`, `TiltedHalfHeightConsumers/`) and the side factor of Theorem 4 (`Thm4SideFactor/`).

259 modules, 24,838 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`ActiveBandWindows`](ActiveBandWindows.lean) | Declarations: `bandWindowEmbedding`, `bandWindow_rank_edges`, `bandWindow_active_map_le` |
| [`AuxiliaryArcRealization`](AuxiliaryArcRealization.lean) | Declarations: `auxiliaryArc_source_partition_eq` |
| [`BandActiveComparisonGeometry`](BandActiveComparisonGeometry.lean) | Declarations: `bandActive_map_le`, `band_active_reference_partition_le`, `band_active_reference_crossing_restricts` |
| [`BandComparisonGeometry`](BandComparisonGeometry.lean) | Declarations: `band_reference_partition_le`, `band_restriction_open_adj`, `band_reference_crossing_restricts` |
| [`BoundaryMergeCost`](BoundaryMergeCost.lean) | Boundary merge costs with an arbitrary pre-existing boundary partition. DCST, proof of eq. (5), TeX lines 1309-1320; BD12 Lemma … |
| [`CanonicalCutBonds`](CanonicalCutBonds.lean) | Canonical bond carriers for the two one-sided cut exteriors and for prewired bonds inside the two marked arcs. |
| [`CanonicalCutCarrier`](CanonicalCutCarrier.lean) | The union of the two closed exterior reveals is exactly the complement of the induced band with all minimally prewired arc bonds removed. |
| [`ClippedCutCarrier`](ClippedCutCarrier.lean) | Exact clipping of an active reference band to a source graph. |
| [`ComplementaryConditioning`](ComplementaryConditioning.lean) | Exact conditioning transport for complementary finite edge bijections. |
| [`CrosscutBand`](CrosscutBand.lean) | The induced band between actual ordered square-crossing walks. |
| [`CrosscutBottomOrder`](CrosscutBottomOrder.lean) | Bottom-boundary order of disjoint top crossings. Uses the interlaced-walk theorem … |
| [`CrosscutOpenWalks`](CrosscutOpenWalks.lean) | The actual frozen-open crosscuts induce the necessary arc wiring. |
| [`CrosscutOrderedPair`](CrosscutOrderedPair.lean) | Construct the ordered-cut interface from actual square-crossing walks. |
| [`CrosscutSeparation`](CrosscutSeparation.lean) | Walk separation by disjoint ordered bottom-to-top square crossings. |
| [`CutExteriorReveals`](CutExteriorReveals.lean) | Canonical one-sided reveals depend only on their own cut and reference side. |
| [`CutRegionCollapse`](CutRegionCollapse.lean) | Cut-avoiding reachability under collapse of connected vertex fibres. |
| [`EmbeddedActiveLaw`](EmbeddedActiveLaw.lean) | Exact active-carrier law from a literal remaining graph. The source reveals the entire complement of the embedded active graph. |
| [`EmbeddedBoundaryLower`](EmbeddedBoundaryLower.lean) | Declarations: `mixedEmbedded_indicator_expectation`, `embedded_measure_lower_of_boundary_domination` |
| [`EmbeddedOpenRestriction`](EmbeddedOpenRestriction.lean) | Actual open paths under literal embedded restriction and active transport. |
| [`ExteriorPartition`](ExteriorPartition.lean) | Finite deterministic certificates for the extremal boundary comparison. The universal quantifier over exterior configurations is equivalent … |
| [`FiniteSlit/ActiveCarrier`](FiniteSlit/ActiveCarrier.lean) | The finite active carrier after alpha/beta prewiring. |
| [`FiniteSlit/ActiveDualEquiv`](FiniteSlit/ActiveDualEquiv.lean) | Actual finite active crossing-edge and complementary-state bijections. |
| [`FiniteSlit/ActiveMarginal`](FiniteSlit/ActiveMarginal.lean) | Exact marginal and canonical complementary map of the original finite source law. |
| [`FiniteSlit/ArcConnectivity`](FiniteSlit/ArcConnectivity.lean) | Actual auxiliary paths along finite wired arcs. |
| [`FiniteSlit/BarrierEdges`](FiniteSlit/BarrierEdges.lean) | Declarations: `slitBarrierEdges`, `slitBarrier_crossing_touches_trace`, `rayIndex_eq_of_slitBarrier` |
| [`FiniteSlit/BoundaryIsolation`](FiniteSlit/BoundaryIsolation.lean) | Exact isolated faces of the reflected finite carrier. |
| [`FiniteSlit/BoundaryPartition`](FiniteSlit/BoundaryPartition.lean) | Separate outer-arc wiring realized by explicit auxiliary OPEN bonds. |
| [`FiniteSlit/BoundaryPaths`](FiniteSlit/BoundaryPaths.lean) | Literal horizontal and vertical auxiliary paths in the finite outer arcs. |
| [`FiniteSlit/CanonicalContactIndex`](FiniteSlit/CanonicalContactIndex.lean) | Declarations: `firstContactIndex`, `isFirstContact_firstContactIndex` |
| [`FiniteSlit/CanonicalSourceArms`](FiniteSlit/CanonicalSourceArms.lean) | Declarations: `disjoint_openSourceSquare_firstContact_exists`, `nativeSourceArmsOfWalks` |
| [`FiniteSlit/ClampedDualSample`](FiniteSlit/ClampedDualSample.lean) | The augmented source sample has the exact frozen exterior record. |
| [`FiniteSlit/ClippedReveals`](FiniteSlit/ClippedReveals.lean) | Literal one-sided source reveals, with the missing slit bonds and the host exterior included separately. |
| [`FiniteSlit/ClosedBandIdentification`](FiniteSlit/ClosedBandIdentification.lean) | Declarations: `first_support_not_beta` |
| [`FiniteSlit/Comparison`](FiniteSlit/Comparison.lean) | The finite dual-to-primal comparison, independently of the remaining finite duality identification. |
| [`FiniteSlit/Configurations`](FiniteSlit/Configurations.lean) | Canonical finite complementary configurations on the actual active reflected graph. |
| [`FiniteSlit/Corners`](FiniteSlit/Corners.lean) | Exact finite slit corners and the excluded terminal crossing bond. |
| [`FiniteSlit/CrosscutActive`](FiniteSlit/CrosscutActive.lean) | Declarations: `firstStartBand`, `secondStartBand`, `arcs_nonempty` |
| [`FiniteSlit/CrosscutBand`](FiniteSlit/CrosscutBand.lean) | Declarations: `CrosscutData`, `orderedCuts`, `rank`, `rank_first_iff`, … |
| [`FiniteSlit/CrosscutSeparation`](FiniteSlit/CrosscutSeparation.lean) | Declarations: `toLattice`, `orderedCutPair_of_slit_crosscuts` |
| [`FiniteSlit/CrossingExtraction`](FiniteSlit/CrossingExtraction.lean) | Finite crossing extraction by removing only fixed slit-internal bonds. |
| [`FiniteSlit/Domain`](FiniteSlit/Domain.lean) | The balanced finite truncated slit box for the revised Case 2 route. |
| [`FiniteSlit/DualEmbedding`](FiniteSlit/DualEmbedding.lean) | The finite reflected graph as actual cells in the original rectangle dual. |
| [`FiniteSlit/DualProbabilityComparison`](FiniteSlit/DualProbabilityComparison.lean) | The canonical finite complementary image is dominated by the explicitly joined dual FK law. |
| [`FiniteSlit/DualSampledCarrier`](FiniteSlit/DualSampledCarrier.lean) | The exact sampled dual graph after conditioning the balanced rectangle. |
| [`FiniteSlit/ExteriorBoundaryEdges`](FiniteSlit/ExteriorBoundaryEdges.lean) | Declarations: `left_exterior_neighbor_portal`, `right_exterior_neighbor_portal`, `opposite_exteriors_not_adj`, `exteriorProjection_map_source_adj_iff` |
| [`FiniteSlit/ExteriorFibres`](FiniteSlit/ExteriorFibres.lean) | Declarations: `left_exterior_to_top`, `right_exterior_to_top`, `exteriorProjection_connected_fibres` |
| [`FiniteSlit/ExteriorGraphIdentity`](FiniteSlit/ExteriorGraphIdentity.lean) | Declarations: `exteriorProjection_map_left_adj_iff`, `exteriorProjection_map_right_adj_iff`, `exteriorProjection_map_no_exterior_adj`, `exteriorProjection_map_eq_sourceExteriorGraph` |
| [`FiniteSlit/ExteriorPortalNeighbors`](FiniteSlit/ExteriorPortalNeighbors.lean) | Declarations: `left_portal_has_exterior_neighbor`, `right_portal_has_exterior_neighbor` |
| [`FiniteSlit/ExteriorProjection`](FiniteSlit/ExteriorProjection.lean) | Collapse of the two geometric reference exteriors. |
| [`FiniteSlit/ExteriorSeeds`](FiniteSlit/ExteriorSeeds.lean) | Declarations: `sourceAlpha`, `sourceBeta`, `exteriorProjection_image_alpha`, `exteriorProjection_image_beta` |
| [`FiniteSlit/ExteriorTopPaths`](FiniteSlit/ExteriorTopPaths.lean) | Declarations: `leftTop`, `rightTop`, `outside_source_iff`, `outside_walk_to_top` |
| [`FiniteSlit/FirstContactCrop`](FiniteSlit/FirstContactCrop.lean) | Declarations: `IsFirstContact`, `IsFirstContact.unique`, `isFirstContact_mapLe_iff`, `sourceSquare_exists_crosscutData_at_firstContact` |
| [`FiniteSlit/FixedPrefixRecord`](FiniteSlit/FixedPrefixRecord.lean) | Declarations: `RetainedRectanglePathGeometry` |
| [`FiniteSlit/ForcedDualState`](FiniteSlit/ForcedDualState.lean) | Exact forced-open dual states in the balanced rectangle. |
| [`FiniteSlit/HorizontalPaths`](FiniteSlit/HorizontalPaths.lean) | Declarations: `horizontal_walk` |
| [`FiniteSlit/HostAugmentation`](FiniteSlit/HostAugmentation.lean) | Rectangular augmentation of an actual finite slit sample. |
| [`FiniteSlit/InducedBoundaryUpper`](FiniteSlit/InducedBoundaryUpper.lean) | The finite induced dual boundary is dominated by the canonical joined B'-K' wiring, up to the proved irrelevant isolated exterior faces. |
| [`FiniteSlit/InducedDualLaw`](FiniteSlit/InducedDualLaw.lean) | The finite active FK law maps to the actual induced reflected dual law. |
| [`FiniteSlit/IntersectingSourceRecord`](FiniteSlit/IntersectingSourceRecord.lean) | The intersecting-arm alternative for the literal source restriction. |
| [`FiniteSlit/IsolatedWiring`](FiniteSlit/IsolatedWiring.lean) | Removing the irrelevant exterior wiring on isolated reflected vertices. |
| [`FiniteSlit/LeftBarrierLoop`](FiniteSlit/LeftBarrierLoop.lean) | Declarations: `exists_left_slit_barrier` |
| [`FiniteSlit/NativeSourceArms`](FiniteSlit/NativeSourceArms.lean) | Declarations: `SourceWalkPair`, `NativeSourceArms`, `croppedTrace`, `tipTrace` |
| [`FiniteSlit/OmegaComparison`](FiniteSlit/OmegaComparison.lean) | The finite Omega comparison from its two deterministic geometry facts. |
| [`FiniteSlit/OpenRectangleCrosscuts`](FiniteSlit/OpenRectangleCrosscuts.lean) | Declarations: `openSourceRectangle_exists_crosscutData` |
| [`FiniteSlit/OpenSourceCrosscuts`](FiniteSlit/OpenSourceCrosscuts.lean) | Declarations: `openSourceSquare_exists_crosscutData_at_firstContact` |
| [`FiniteSlit/OpenSourceTip`](FiniteSlit/OpenSourceTip.lean) | Declarations: `disjoint_openSourceSquare_tip_pos`, `coordinateTrace_eq_of_support_map` |
| [`FiniteSlit/PrefixGeometricCompletion`](FiniteSlit/PrefixGeometricCompletion.lean) | Declarations: `leftContact_geometric_completion`, `leftContact_prefix_first_markedRay_approaches_left`, `disjoint_leftContact_prefix_tip_pos`, `disjoint_leftContact_prefix_avoids_markedRay` |
| [`FiniteSlit/Prewiring`](FiniteSlit/Prewiring.lean) | Exact finite outer-arc prewiring. |
| [`FiniteSlit/RectangleClipping`](FiniteSlit/RectangleClipping.lean) | The source rectangle clipped from the balanced slit reference. |
| [`FiniteSlit/RectangleConditioning`](FiniteSlit/RectangleConditioning.lean) | Exact finite slit conditioning in the surrounding free rectangle. |
| [`FiniteSlit/RectangleContactExistence`](FiniteSlit/RectangleContactExistence.lean) | Declarations: `disjoint_openSourceRectangle_firstContact_exists` |
| [`FiniteSlit/RectanglePrefixCrosscuts`](FiniteSlit/RectanglePrefixCrosscuts.lean) | Declarations: `sourceRectangle_crosscutData_of_leftContactPrefix` |
| [`FiniteSlit/RectangleSeparatePathBound`](FiniteSlit/RectangleSeparatePathBound.lean) | Declarations: `RetainedRectanglePathGeometry.supports_disjoint`, `sourceSeparatePathBoundary` |
| [`FiniteSlit/RectangleSourceArms`](FiniteSlit/RectangleSourceArms.lean) | Declarations: `RectangleSourceArms`, `column_le`, `firstContact_exists`, `cropIndex` |
| [`FiniteSlit/ReferenceBound`](FiniteSlit/ReferenceBound.lean) | The uniform finite truncated-slit mixed estimate. |
| [`FiniteSlit/ReferenceConsumers`](FiniteSlit/ReferenceConsumers.lean) | Finite Case 2 consumers with the reference estimate fully discharged. |
| [`FiniteSlit/RightBarrierLoop`](FiniteSlit/RightBarrierLoop.lean) | Declarations: `exists_right_slit_barrier` |
| [`FiniteSlit/SourceActiveCarrier`](FiniteSlit/SourceActiveCarrier.lean) | Declarations: `sourceRectangle_active_graph_eq` |
| [`FiniteSlit/SourceBandRecord`](FiniteSlit/SourceBandRecord.lean) | Declarations: `sourceInternalBonds_mono`, `sourcePathArcBonds_subset_exterior`, `source_recorded_open_bond` |
| [`FiniteSlit/SourceClosedPathGraph`](FiniteSlit/SourceClosedPathGraph.lean) | Declarations: `sourcePathArcBonds`, `sourceClosedPathGraph`, `sourceClosedPathGraph_le_rectangle` |
| [`FiniteSlit/SourceCrosscuts`](FiniteSlit/SourceCrosscuts.lean) | Declarations: `sourceSquare_exists_crosscutData` |
| [`FiniteSlit/SourceExteriorGraph`](FiniteSlit/SourceExteriorGraph.lean) | Intrinsic source geometry with two auxiliary exterior vertices. |
| [`FiniteSlit/SourceExteriorRegions`](FiniteSlit/SourceExteriorRegions.lean) | Declarations: `sourceLeftExterior`, `sourceRightExterior`, `source_cutReachRegion_iff`, `source_closedCutExterior_iff`, … |
| [`FiniteSlit/SourceExteriorReveals`](FiniteSlit/SourceExteriorReveals.lean) | Declarations: `sourceCoordinateTrace`, `sourceCoordinateTrace_image_eq`, `sourceExteriorReveal`, `sourceExteriorHostReveal`, … |
| [`FiniteSlit/SourcePaths`](FiniteSlit/SourcePaths.lean) | Declarations: `composed_map_le`, `active_map_le` |
| [`FiniteSlit/SourceRecordGeometry`](FiniteSlit/SourceRecordGeometry.lean) | Literal source geometry for a revealed carrier and its frozen open state. |
| [`FiniteSlit/SourceRectangleEmbedding`](FiniteSlit/SourceRectangleEmbedding.lean) | Declarations: `band_subset_sourceRectangle`, `sourceRectangleEmbedding`, `sourceRectangleEmbedding_map_le` |
| [`FiniteSlit/SourceRectanglePadding`](FiniteSlit/SourceRectanglePadding.lean) | Declarations: `rectangle_subset_paddedSquare`, `rectangleToPaddedSquare`, `paddedRectangleReference`, `paddedSquare_reference_comp` |
| [`FiniteSlit/SupportRecordWalks`](FiniteSlit/SupportRecordWalks.lean) | Declarations: `recordedSourceOpenWalk`, `recordedSourceOpenWalk_support`, `sourceSupportWalk_bond_exposed` |
| [`FiniteSlit/VerticalPaths`](FiniteSlit/VerticalPaths.lean) | Declarations: `vertical_walk` |
| [`FixedOpenWalk`](FixedOpenWalk.lean) | Declarations: `fixedOpenWalk`, `fixedOpenWalk_support` |
| [`GlobalCrosscutSideLabels`](GlobalCrosscutSideLabels.lean) | Declarations: `originSquare_row_walk`, `rank_le_one_of_x_le_first`, `three_le_rank_of_second_x_le` |
| [`HorizontalCrosscutGeometry`](HorizontalCrosscutGeometry.lean) | Declarations: `horizontalSquareNormalizationIso`, `horizontalSquareNormalizationIso_val`, `HorizontalSquareCrosscutData`, `normalized`, … |
| [`InducedEndpointMixedBound`](InducedEndpointMixedBound.lean) | Declarations: `inducedEndpointDualCarrierIso` |
| [`IntersectingCrosscuts`](IntersectingCrosscuts.lean) | The intersecting-crosscut branch of the source conditioned estimate. |
| [`Lemma4Connectors/ConfinementProduct`](Lemma4Connectors/ConfinementProduct.lean) | Declarations: `fullCoreConfined`, `confinedAnnulusPairEvent`, `confinedAnnulusPair_probability_le_local_product`, `lemma4_confined_annulus_pair_probability_le_square` |
| [`Lemma4Connectors/GlobalTraceLoop`](Lemma4Connectors/GlobalTraceLoop.lean) | Declarations: `exists_betweenTraceLoop`, `closedTraceLoop_component_strip`, `exterior_column_crossed_bond_absent`, `betweenTraceLoop_closed` |
| [`Lemma4Connectors/HullBoundaryCircuit`](Lemma4Connectors/HullBoundaryCircuit.lean) | Declarations: `cell_false_center`, `cell_true_center`, `cellBoundary_walk_avoids_internal_bond` |
| [`Lemma4Connectors/PrimalWindow`](Lemma4Connectors/PrimalWindow.lean) | Declarations: `primalWindowCrossing`, `primalWindowNoncrossing`, `primalWindowCrossing_isUpperSet`, `primalWindowNoncrossing_isLowerSet`, … |
| [`Lemma4Connectors/SourceConfinement`](Lemma4Connectors/SourceConfinement.lean) | Declarations: `lemma4PrimalNoncrossings`, `lemma4_core_rectangles_of_noncrossings_and_strip`, `lemma4_confined_boxes_of_noncrossings_and_strip` |
| [`Lemma4Connectors/SourceRecordedConnectors`](Lemma4Connectors/SourceRecordedConnectors.lean) | Declarations: `lemma4RecordedCoreGeometryEvent` |
| [`Lemma4Connectors/SourceSlitRecordSurgery`](Lemma4Connectors/SourceSlitRecordSurgery.lean) | Declarations: `SlitSourceScreenCropWitness` |
| [`Lemma4Connectors/SourceTraceStrip`](Lemma4Connectors/SourceTraceStrip.lean) | Declarations: `lemma4_closed_trace_pair_core_strip` |
| [`Lemma4Connectors/TraceIndexScreen`](Lemma4Connectors/TraceIndexScreen.lean) | Declarations: `traceIndexRegion`, `lemma4_strip_in_traceIndexRegion`, `lemma4_confined_boxes_of_traceIndex_noncrossings`, `lemma4TraceNoncrossingAnnulusEvent`, … |
| [`Lemma4RecordCarrier/ActiveRetainedPaths`](Lemma4RecordCarrier/ActiveRetainedPaths.lean) | Declarations: `active_restriction_connection_of_retained_walk` |
| [`Lemma4RecordCarrier/ActiveWindowLowerBound`](Lemma4RecordCarrier/ActiveWindowLowerBound.lean) | Declarations: `lemma4ActiveNativeWindowHorizontalCrossing`, `lemma4ActiveNativeWindowHorizontalCrossing_isUpperSet`, `lemma4_active_window_crossing_implies_reference_crossing`, `lemma4_active_native_window_noncrossing_lower` |
| [`Lemma4RecordCarrier/ActualNativePrimalLaw`](Lemma4RecordCarrier/ActualNativePrimalLaw.lean) | Declarations: `nativeUnqueriedRead`, `nativeUnqueriedRead_original_edges`, `actual_record_native_primal_law`, `lemma4_actual_record_native_primal_law`, … |
| [`Lemma4RecordCarrier/ActualResidualProbabilityChain`](Lemma4RecordCarrier/ActualResidualProbabilityChain.lean) | Declarations: `lemma4_native_primal_connectors_lower_of_nativeWindowBounds`, `lemma4_actual_residual_chain_of_nativeWindowBounds`, `lemma4_band_to_square_bound_of_nativeWindowBounds` |
| [`Lemma4RecordCarrier/ActualResidualRecordEvents`](Lemma4RecordCarrier/ActualResidualRecordEvents.lean) | Declarations: `lemma4ActualResidualConnectorAnnulusEvent`, `lemma4NativePrimalConnectors`, `lemma4_actual_residual_event_on_record`, `lemma4_actual_residual_record_probability_ge_native`, … |
| [`Lemma4RecordCarrier/ActualResidualSourceUpper`](Lemma4RecordCarrier/ActualResidualSourceUpper.lean) | Declarations: `lemma4_actual_residual_connectors_imply_core_geometry`, `lemma4_actual_residual_connector_annulus_subset_trace`, `lemma4_actual_residual_connector_annulus_probability_le_square` |
| [`Lemma4RecordCarrier/ActualResidualTransport`](Lemma4RecordCarrier/ActualResidualTransport.lean) | Declarations: `lemma4_primal_window_crossing_has_native_residual_crossing`, `lemma4_actual_residual_connectors_imply_trace_noncrossings` |
| [`Lemma4RecordCarrier/AnnulusWindowBoundary`](Lemma4RecordCarrier/AnnulusWindowBoundary.lean) | Declarations: `lemma4_annulus_query_in_window_boundary` |
| [`Lemma4RecordCarrier/ClosedQueryStar`](Lemma4RecordCarrier/ClosedQueryStar.lean) | Declarations: `closedClusterReveal_closed_edge_endpoints_reached`, `closedClusterReveal_closed_edge_incident_query` |
| [`Lemma4RecordCarrier/ComplementaryQueryStar`](Lemma4RecordCarrier/ComplementaryQueryStar.lean) | Declarations: `rectangle_auxiliary_edge_original_pair`, `rectangle_auxiliary_pair_of_original_edge`, `complementary_raw_open_query_incident_query` |
| [`Lemma4RecordCarrier/DecreasingEmbeddedComparison`](Lemma4RecordCarrier/DecreasingEmbeddedComparison.lean) | Declarations: `finite_decreasing_boundary_comparison`, `embedded_decreasing_comparison_of_frozen_partition`, `frozen_free_partition_le_wired_of_endpoint_attachment` |
| [`Lemma4RecordCarrier/DecreasingFKG`](Lemma4RecordCarrier/DecreasingFKG.lean) | Declarations: `finiteLaw_lower_event_association`, `finiteLaw_lower_event_product`, `finiteLaw_three_lower_events_of_local_bounds` |
| [`Lemma4RecordCarrier/HorizontalSeedQueries`](Lemma4RecordCarrier/HorizontalSeedQueries.lean) | Declarations: `original_vertical_edge_represented_at_row`, `complementary_raw_query_of_original_seed_endpoint`, `top_raw_query_contains_vertical_boundary_bond`, `bottom_raw_query_contains_vertical_boundary_bond` |
| [`Lemma4RecordCarrier/IncidentVertexLaw`](Lemma4RecordCarrier/IncidentVertexLaw.lean) | Declarations: `incidentVertexSet`, `incidentVertexEmbedding`, `incidentVertexGraph_map`, `incidentVertexConfigurationRead`, … |
| [`Lemma4RecordCarrier/InteriorOriginalEdges`](Lemma4RecordCarrier/InteriorOriginalEdges.lean) | Declarations: `dualBond_endpoints_mem_of_original_interior`, `original_edge_represented_of_interior_endpoint`, `complementary_raw_query_no_open_attachment_at_native_interior` |
| [`Lemma4RecordCarrier/NativeWindowCarrier`](Lemma4RecordCarrier/NativeWindowCarrier.lean) | Declarations: `lemma4NativeWindowVertices`, `lemma4NativeWindowGraph`, `lemma4NativeWindowGraph_le`, `lemma4_native_window_incident_vertex_coordinates`, … |
| [`Lemma4RecordCarrier/NativeWindowEventTransport`](Lemma4RecordCarrier/NativeWindowEventTransport.lean) | Declarations: `lemma4_native_window_crossing_restricts_to_active`, `lemma4_active_noncrossing_implies_native_noncrossing` |
| [`Lemma4RecordCarrier/NativeWindowPartition`](Lemma4RecordCarrier/NativeWindowPartition.lean) | Declarations: `lemma4ActiveNativeWindowVertex`, `lemma4ActiveNativeWindowGraph`, `lemma4ActiveNativeWindowEmbedding`, `lemma4ActiveNativeWindowSides`, … |
| [`Lemma4RecordCarrier/NativeWindowReferenceEmbedding`](Lemma4RecordCarrier/NativeWindowReferenceEmbedding.lean) | Declarations: `lemma4ReferenceCoreVertex`, `lemma4ReferenceCoreGraph`, `lemma4ActiveWindowCoreVertex`, `lemma4ActiveWindowCoreEmbedding`, … |
| [`Lemma4RecordCarrier/OriginalQueryPorts`](Lemma4RecordCarrier/OriginalQueryPorts.lean) | Declarations: `rectangleDualTopPorts_mem_iff_coordinates`, `rectangleDualBottomPorts_mem_iff_coordinates`, `complementary_raw_open_query_endpoint_reached`, `top_raw_open_query_endpoint_above_bottom`, … |
| [`Lemma4RecordCarrier/RawQueryOriginalIndex`](Lemma4RecordCarrier/RawQueryOriginalIndex.lean) | Declarations: `raw_dual_query_original_endpoint_index`, `complementary_raw_query_original_endpoint_index`, `finite_closed_trace_rectangle_read_open`, `complementary_raw_query_endpoint_index_of_closed_trace`, … |
| [`Lemma4RecordCarrier/ReferenceCoreAdjacency`](Lemma4RecordCarrier/ReferenceCoreAdjacency.lean) | Declarations: `referenceDualCore_adj_of_lattice_adj` |
| [`Lemma4RecordCarrier/ReferenceWindowNoncrossing`](Lemma4RecordCarrier/ReferenceWindowNoncrossing.lean) | Declarations: `squareVerticalCrossing_excludes_dualHorizontal`, `referenceDualCoreHorizontalCrossing`, `referenceDualCore_noncrossing_lower` |
| [`Lemma4RecordCarrier/ResidualPrimalWindows`](Lemma4RecordCarrier/ResidualPrimalWindows.lean) | Declarations: `residualPrimalWindowNoncrossing`, `nativePrimalWindowNoncrossing`, `nativePrimalWindowNoncrossing_isLowerSet`, `lemma4ActualResidualConnectors` |
| [`Lemma4RecordCarrier/SourceBandClosedLoop`](Lemma4RecordCarrier/SourceBandClosedLoop.lean) | Declarations: `finiteClosedDualWalk_crossed_edge_absent`, `lemma4_source_band_exists_closed_core_loop` |
| [`Lemma4RecordCarrier/SourceBandQueryAvoidance`](Lemma4RecordCarrier/SourceBandQueryAvoidance.lean) | Declarations: `lemma4_source_lower_query_original_endpoint_zero`, `lemma4_source_band_queries_avoid_component` |
| [`Lemma4RecordCarrier/SourceEq15`](Lemma4RecordCarrier/SourceEq15.lean) | Declarations: `lemma4_actual_native_window_noncrossing_lower`, `lemma4_band_to_square_bound` |
| [`Lemma4RecordCarrier/SourceNativeAttachment`](Lemma4RecordCarrier/SourceNativeAttachment.lean) | Declarations: `lemma4_upper_query_no_native_window_attachment`, `lemma4_lower_query_no_native_window_attachment`, `lemma4_annulus_query_no_interior_window_endpoint`, `lemma4_joint_query_no_open_native_window_attachment` |
| [`Lemma4RecordCarrier/SourceUpperQueryAvoidance`](Lemma4RecordCarrier/SourceUpperQueryAvoidance.lean) | Declarations: `rectangleTopFrontierReveal_eq_raw_of_crossing`, `lemma4_source_upper_query_original_endpoint_zero`, `lemma4_source_upper_query_avoids_core_component` |
| [`Lemma4RecordCarrier/SourceWindowBoundary`](Lemma4RecordCarrier/SourceWindowBoundary.lean) | Declarations: `lemma4_upper_window_exit_queried`, `lemma4_lower_window_exit_queried`, `lemma4_unqueried_edge_preserves_window_height` |
| [`Lemma4RecordCarrier/StrictWindowSubwalk`](Lemma4RecordCarrier/StrictWindowSubwalk.lean) | Declarations: `walk_subwalk_between_levels_no_boundary_edges` |
| [`Lemma4RecordCarrier/VerticalReflectionQueries`](Lemma4RecordCarrier/VerticalReflectionQueries.lean) | Declarations: `rectangle_verticalReflection_auxiliary_closed`, `rectangle_verticalReflection_dual_edge_commutes`, `rectangle_verticalReflection_bottom_ports_map`, `rectangle_verticalReflection_reached_iff`, … |
| [`Lemma4StoppingRecords/ActualNativeDualLaw`](Lemma4StoppingRecords/ActualNativeDualLaw.lean) | Declarations: `subgraphRemovedEdges_edgeRestriction_eq` |
| [`Lemma4StoppingRecords/ComplementaryStoppingRead`](Lemma4StoppingRecords/ComplementaryStoppingRead.lean) | Declarations: `complementaryEdgeRead`, `mem_complementaryEdgeRead`, `complementaryRevealPullback`, `mem_complementaryRevealPullback`, … |
| [`Lemma4StoppingRecords/OriginalClosedDualRead`](Lemma4StoppingRecords/OriginalClosedDualRead.lean) | Declarations: `originalEdgeOfBond`, `originalEdgeOfBond_eq_some_iff`, `rectangleDualOriginalEdge`, `originalClosedDualRectangleRead`, … |
| [`Lemma4StoppingRecords/ReflectedBottomReveal`](Lemma4StoppingRecords/ReflectedBottomReveal.lean) | Declarations: `horizontalCrossing_verticalReflection_iff`, `rectangleBottomFrontierReveal`, `rectangleBottomFrontierReveal_stable`, `horizontalCrossing_readFrom_bottomFrontier` |
| [`Lemma4StoppingRecords/SourceAnnulusReveal`](Lemma4StoppingRecords/SourceAnnulusReveal.lean) | Declarations: `lemma4AnnulusBondReveal`, `lemma4AnnulusPairEvent_read_from_annulusBonds` |
| [`Lemma4StoppingRecords/SourceBandStoppingRecords`](Lemma4StoppingRecords/SourceBandStoppingRecords.lean) | Declarations: `lemma4SourceBandBase`, `lemma4SourceDualBandRead`, `lemma4SourceDualBandFrontierReveal`, `lemma4SourceBandReveal`, … |
| [`Lemma4StoppingRecords/SourceCrossingFrontierRead`](Lemma4StoppingRecords/SourceCrossingFrontierRead.lean) | Declarations: `originalClosedDualGraph_le_square`, `source_closedDualRectangle_crossing_iff_read`, `horizontalCrossing_readFrom_topFrontier` |
| [`OmegaConditional`](OmegaConditional.lean) | Conditional mixed-square transfer to the extremal-path domain Omega. DCST TeX L1229-L1235. |
| [`OmegaInterfaces`](OmegaInterfaces.lean) | Explicit interfaces for the conditioned extremal-path domain. These are predicates on actual finite graph data, not assertions that … |
| [`OrderedCutActive`](OrderedCutActive.lean) | Ordered-cut estimates after removing exposed path bonds. Removed bonds have endpoints in a single separately wired arc. |
| [`OrderedCutBands`](OrderedCutBands.lean) | Constructing band labels from ordered cuts. Labels are the five exhaustive geometric classes: left accessible region (0), first cut (1) … |
| [`OrderedCutConsumers`](OrderedCutConsumers.lean) | Ordered-cut estimates on actual conditional and remaining FK laws. The only topology input is the three deterministic walk-separation … |
| [`OrderedCutRegions`](OrderedCutRegions.lean) | Reachability regions of two ordered vertex cuts. The three hypotheses are ordinary deterministic walk-separation facts. |
| [`RankedBand`](RankedBand.lean) | An induced domain between two ordered graph cuts. Vertices have integer labels: the first marked cut has label 1, the middle has label 2 … |
| [`RankedBandGeometry`](RankedBandGeometry.lean) | Declarations: `rankedBand_exterior_partition_le`, `rankedBand_arcs_connection_restricts` |
| [`RankedBandPaths`](RankedBandPaths.lean) | Actual crossing restriction to a ranked band. The private prefix argument adapts `PlanarTopology.walk_prefix_at_level`: it uses only an … |
| [`RecordedArcBonds`](RecordedArcBonds.lean) | Exposed original arc bonds retain their actual open states in the complete stopping record. |
| [`RetainedWalk`](RetainedWalk.lean) | Declarations: `retainedWalk`, `retainedWalk_support`, `retainedWalk_edges` |
| [`SlitActiveReflection`](SlitActiveReflection.lean) | The repaired domain inclusion after freezing all boundary-internal primal arc bonds OPEN, so their crossing dual bonds are closed and … |
| [`SlitGlobalOpenGraph`](SlitGlobalOpenGraph.lean) | The actual unbounded slit graph and its exact sampled finite restrictions. |
| [`SlitReflectedBonds`](SlitReflectedBonds.lean) | The corrected reflection on actual crossing bonds. |
| [`SlitReflectedCarrier`](SlitReflectedCarrier.lean) | Exact unbounded sampled-bond carriers before and after corrected reflected duality. |
| [`SourceActiveCrosscutComparison`](SourceActiveCrosscutComparison.lean) | Declarations: `active_reference_partition_le`, `active_reference_crossing_restricts`, `active_reference_partition_le_frozen`, `active_extremalBoundaryComparison`, … |
| [`SourceActiveCrosscutReplay`](SourceActiveCrosscutReplay.lean) | Declarations: `embeddedSampleOpenHom`, `active_residual_restored_starts_connected` |
| [`SourceCrosscutComparison`](SourceCrosscutComparison.lean) | Declarations: `extremalBoundaryComparison`, `squareCrossingRestrictsToArcs`, `conditional_arc_lower_bound_of_fiberLaw` |
| [`SourceCrosscutShapes`](SourceCrosscutShapes.lean) | Declarations: `verticalCrosscutData_of_separated_traces`, `lemma4CrosscutSquareBase`, `generalCCrosscutData` |
| [`SourceGlobalWindows`](SourceGlobalWindows.lean) | Declarations: `lemma4GlobalWindow`, `lemma4GlobalWindow_map_le`, `lemma4GlobalWindow_bottom_rank`, `lemma4GlobalWindow_top_rank`, … |
| [`Square/Consumers`](Square/Consumers.lean) | Translated, rotated and odd-side dual-label square wired-arc estimates. All squares here are genuine induced nearest-neighbour graphs. |
| [`Square/DualSwap`](Square/DualSwap.lean) | Actual primal/dual coordinate swap on squares. Adapted from the edge-labelled reflection proof in … |
| [`Square/Extras`](Square/Extras.lean) | Declarations: `rectangleBottomSide`, `rectangleTopSide`, `rectangleVertexEmbedding`, `rectangleGraph_map_rectangleVertexEmbedding`, … |
| [`Square/FrozenBoundaryRetraction`](Square/FrozenBoundaryRetraction.lean) | Declarations: `componentSetoid_comap_le_of_retraction`, `isolatedExtensionPullback_frozenBoundary_partition_eq_of_retraction` |
| [`Square/GeneralRectangleBottomCollar`](Square/GeneralRectangleBottomCollar.lean) | Declarations: `rectangleArbitraryBottomCollarInnerGraph`, `rectangleArbitraryBottomCollarOuterGraph`, `rectangleArbitraryBottomCollarInnerVertex`, `rectangleArbitraryBottomCollarOuterVertex`, … |
| [`Square/GeneralRectangleDualBottomCollar`](Square/GeneralRectangleDualBottomCollar.lean) | Declarations: `generalRectangleDualBottomCollarInnerGraph`, `generalRectangleDualBottomCollarOuterGraph`, `generalRectangleDualBottomCollarInnerVertex`, `generalRectangleDualBottomCollarOuterVertex`, … |
| [`Square/GeneralRectangleDualBottomCollarBoundary`](Square/GeneralRectangleDualBottomCollarBoundary.lean) | Declarations: `generalRectangleDualBottomCollarInnerThreeSides`, `generalRectangleDualBottomCollar_boundary_mem`, `generalRectangleDualBottomCollar_outerBoundaryCondition_pullback` |
| [`Square/GeneralRectangleDualBottomCollarConfiguration`](Square/GeneralRectangleDualBottomCollarConfiguration.lean) | Declarations: `generalRectangleDualBottomCollar_primalMap_le`, `generalRectangleDualBottomCollar_dualMap_le`, `generalRectanglePrimalDualConfiguration_eq_carrier`, `generalRectangleDualBottomCollar_primalDual_restriction_square`, … |
| [`Square/GeneralRectangleDualBottomCollarRestriction`](Square/GeneralRectangleDualBottomCollarRestriction.lean) | Declarations: `generalRectangleDualBottomCollarInnerPrimalEdges`, `mem_generalRectangleDualBottomCollarInnerPrimalEdges`, `generalRectangleDualBottomCollarInnerPrimalEdges_mem_iff`, `generalRectangleDualBottomCollarInnerPrimalEdges_mem_iff_embedding`, … |
| [`Square/GeneralRectangleDualBottomLeaves`](Square/GeneralRectangleDualBottomLeaves.lean) | Declarations: `generalRectangleDualBottomCoreVertex`, `generalRectangleDualBottomCoreVertexEquiv`, `generalRectangleDualBottomCoreGraph`, `generalRectangleDualBottomCoreGraph_le_rectangle`, … |
| [`Square/PMFConditioningEquiv`](Square/PMFConditioningEquiv.lean) | Declarations: `pmf_map_equiv_filter_witness`, `pmf_filter_map_equiv` |
| [`Square/RectangleCrossingSymmetry`](Square/RectangleCrossingSymmetry.lean) | Declarations: `latticeCoordinateSwap`, `latticeCoordinateSwap_swap`, `squareLattice_adj_coordinateSwap_iff`, `rectangleVertexCoordinateSwapEquiv`, … |
| [`Square/RectangleDoubleCollar`](Square/RectangleDoubleCollar.lean) | Declarations: `rectangleDoubleCollarInnerGraph`, `rectangleDoubleCollarOuterGraph`, `rectangleDoubleCollarInnerVertex`, `rectangleDoubleCollarOuterVertex`, … |
| [`Square/RectangleDoubleCollarDualBoundary`](Square/RectangleDoubleCollarDualBoundary.lean) | Declarations: `rectangleDoubleCollarDualInnerVertex`, `rectangleDoubleCollarDualOuterVertex`, `rectangleDoubleCollarDualInnerVerticalSides`, `rectangleDoubleCollarDual_vertex_subset`, … |
| [`Square/RectangleDoubleCollarDualConfiguration`](Square/RectangleDoubleCollarDualConfiguration.lean) | Declarations: `rectangleDoubleCollarInnerPrimalConfigurationCarrier`, `rectangleDoubleCollarPrimalDualConfiguration_eq_carrier`, `rectangleDoubleCollarInnerPrimalEdges_mem_iff_graph`, `rectangleDoubleCollar_primalDual_restriction_square`, … |
| [`Square/RectangleDoubleCollarDualEdges`](Square/RectangleDoubleCollarDualEdges.lean) | Declarations: `rectangleDoubleCollarDualInnerGraph`, `rectangleDoubleCollarDualOuterGraph`, `rectangleDoubleCollarPrimalEdgeEmbedding`, `rectangleDoubleCollar_primalBond_eq`, … |
| [`Square/RectangleDoubleCollarDualLaw`](Square/RectangleDoubleCollarDualLaw.lean) | Declarations: `rectangleDoubleCollarDual_edgeRestriction_injective`, `rectangleDoubleCollarRemovedDualEdges_eq_subgraphRemoved`, `rectangleDoubleCollar_dualConditional_map` |
| [`Square/RectangleDoubleCollarDualRemaining`](Square/RectangleDoubleCollarDualRemaining.lean) | Declarations: `rectangleDoubleCollarInnerPrimalEdges`, `mem_rectangleDoubleCollarInnerPrimalEdges`, `rectangleDoubleCollarInnerPrimalEdges_mem_iff_embedding`, `rectanglePrimalDualEdgeEquiv_apply_primalEdge_double`, … |
| [`Square/RectangleDoubleCollarLaw`](Square/RectangleDoubleCollarLaw.lean) | Declarations: `rectangleDoubleCollar_conditional_law_map` |
| [`Square/RectangleDoubleCollarPartition`](Square/RectangleDoubleCollarPartition.lean) | Declarations: `rectangleDoubleCollar_frozen_pullback_partition_eq_twoBlocks` |
| [`Square/RectangleDoubleCollarPartitionUpper`](Square/RectangleDoubleCollarPartitionUpper.lean) | Declarations: `rectangleDoubleCollarInnerBottom`, `rectangleDoubleCollarInnerTop`, `rectangleDoubleCollarOuterLowerBand`, `rectangleDoubleCollarOuterUpperBand`, … |
| [`Square/RectangleDoubleCollarRowConnectivity`](Square/RectangleDoubleCollarRowConnectivity.lean) | Declarations: `rectangleDoubleCollarRowVertex`, `rectangleDoubleCollarRowVertex_val`, `rectangleDoubleCollar_row_adj`, `rectangleDoubleCollar_adj_removed_of_not_image`, … |
| [`Square/RectangleDualCornerBoundary`](Square/RectangleDualCornerBoundary.lean) | Declarations: `rectangleDualCornerSideColumns`, `rectangleDualCornerClamp_mem_sideColumns`, `rectangleDualCorner_frozenPartition_le_sideColumns` |
| [`Square/RectangleDualCornerClamp`](Square/RectangleDualCornerClamp.lean) | Declarations: `rectangleDualCornerClamp`, `rectangleDualCornerClamp_val`, `rectangleDualCornerClamp_section`, `rectangleDualCornerClamp_embedding_of_mem_corner`, … |
| [`Square/RectangleDualCornerConnectivity`](Square/RectangleDualCornerConnectivity.lean) | Declarations: `rectangleDualCornerClamp_openAdj`, `rectangleDualCornerClamp_actualConnected` |
| [`Square/RectangleDualCornerCore`](Square/RectangleDualCornerCore.lean) | Declarations: `rectangleDualCornerCoreEmbedding`, `rectangleDualCornerCoreGraph`, `rectangleDualCornerCoreGraph_map_le_dual`, `rectangleDualCornerCoreGraph_le_rectangle`, … |
| [`Square/RectangleDualCornerMarginal`](Square/RectangleDualCornerMarginal.lean) | Declarations: `rectangleDualCorner_marginal_bound` |
| [`Square/RectangleDualHorizontalCore`](Square/RectangleDualHorizontalCore.lean) | Declarations: `rectangleDualHorizontalCoreVertex`, `rectangleDualHorizontalCoreGraph`, `rectangleDualHorizontalCoreInclusion`, `rectangleDualHorizontalCoreRetraction`, … |
| [`Square/RectangleDualHorizontalCoreLaw`](Square/RectangleDualHorizontalCoreLaw.lean) | Declarations: `rectangleDualHorizontalCoreGraph_map_le`, `rectangleDualHorizontalCoreGraph_law_map` |
| [`Square/RectangleDualTopLeaves`](Square/RectangleDualTopLeaves.lean) | Declarations: `rectangleDualTopRow_reflect_bottom`, `rectangleDualTopRow_adj_neighbor` |
| [`Square/RectangleDualVerticalReflection`](Square/RectangleDualVerticalReflection.lean) | Declarations: `rectangleDualVerticalReflectionVertexEquiv`, `rectangleDualVerticalReflectionVertexEquiv_val`, `dualBond_reflection_commute`, `rectangleReflectPrimalBond_toSym2`, … |
| [`Square/RectangleMixedCoordinateSwap`](Square/RectangleMixedCoordinateSwap.lean) | Declarations: `boundaryConditionIso_twoBlock_image` |
| [`Square/RectangleMixedCrossingAlternative`](Square/RectangleMixedCrossingAlternative.lean) | Declarations: `rectangleDoubleCollar_mixedLaw_measure_preimage` |
| [`Square/RectangleMixedDuality`](Square/RectangleMixedDuality.lean) | Declarations: `rectangleDoubleCollar_mixedDuality_law_map` |
| [`Square/RectangleTranslation`](Square/RectangleTranslation.lean) | Declarations: `boundaryConditionIso_wired_image`, `rectangleVertexTranslationEquiv`, `rectangleVertexTranslationEquiv_val`, `rectangleGraphTranslationIso`, … |
| [`Square/RectangleVerticalReflection`](Square/RectangleVerticalReflection.lean) | Declarations: `rectangleVerticalReflectionVertexEquiv`, `rectangleVerticalReflectionVertexEquiv_val`, `rectangleGraphVerticalReflectionIso`, `rectangleVerticalReflectionTopSet`, … |
| [`Square/SubgraphIncreasingEventComparison`](Square/SubgraphIncreasingEventComparison.lean) | Declarations: `event_toReal_eq_expectation`, `event_indicator_nonneg`, `event_indicator_mono`, `subgraph_increasing_event_measure_toReal_le`, … |
| [`Square/VerticalAlternative`](Square/VerticalAlternative.lean) | Vertical primal noncrossing and actual horizontal dual crossing on squares. The direction of the event changes while the bottom/top … |
| [`Square/WiredArcSquare`](Square/WiredArcSquare.lean) | The square mixed estimate in the actual WIRED-ARC direction, all q >= 1. The parameter is explicitly sqrt(q)/(1+sqrt(q)). |
| [`Square/WiredComparison`](Square/WiredComparison.lean) | Actual wired-direction corner comparison. The corner restriction and graph comparison proof patterns are adapted from … |
| [`SquareCrosscutData`](SquareCrosscutData.lean) | Concrete open square-crosscut data, shared by finite-host consumers. |
| [`StripRSWSelectors/ActualPrefixQueryContainment`](StripRSWSelectors/ActualPrefixQueryContainment.lean) | Declarations: `actual_confined_prefix_raw_query_endpoint_left`, `actual_confined_prefix_query_subset_stoppedReveal` |
| [`StripRSWSelectors/CrosscutLeftClosure`](StripRSWSelectors/CrosscutLeftClosure.lean) | Declarations: `crosscut_left_barrier_indices_with_support` |
| [`StripRSWSelectors/LeftSlitClosure`](StripRSWSelectors/LeftSlitClosure.lean) | Declarations: `exists_left_slit_barrier_with_support` |
| [`StripRSWSelectors/LeftSlitPortIndices`](StripRSWSelectors/LeftSlitPortIndices.lean) | Declarations: `slitBarrier_left_row_index_eq_boundary`, `leftSlitBarrier_interval_left_ports_index_one` |
| [`StripRSWSelectors/PaddedArm`](StripRSWSelectors/PaddedArm.lean) | Declarations: `prefixPaddingOpenHom`, `prefixAuxRay_connected_top`, `prefixAuxCompletion_arm_of_confined_connection` |
| [`StripRSWSelectors/PaddedBarrierOpen`](StripRSWSelectors/PaddedBarrierOpen.lean) | Declarations: `prefixAux_barrier_trace_open` |
| [`StripRSWSelectors/PaddedCompletion`](StripRSWSelectors/PaddedCompletion.lean) | Declarations: `PrefixSourceVertex`, `PrefixAuxVertex`, `prefixAuxGraph`, `prefix_padding_rectangle_subset`, … |
| [`StripRSWSelectors/PaddedDecode`](StripRSWSelectors/PaddedDecode.lean) | Declarations: `prefixPaddingRetraction`, `prefixPaddingRetraction_embedding`, `prefixPaddingRetraction_mem_target_iff`, `first_contact_no_target_edge`, … |
| [`StripRSWSelectors/PaddedExtremalSelector`](StripRSWSelectors/PaddedExtremalSelector.lean) | Declarations: `prefixAuxExtremalTrace`, `prefixAuxExtremalTrace_search`, `prefixAuxExtremalTrace_firstContact`, `paddedExtremalConfinedPrefixSelector` |
| [`StripRSWSelectors/PaddedQueryLocality`](StripRSWSelectors/PaddedQueryLocality.lean) | Declarations: `maskedSourceQuery`, `maskedCompletion`, `maskedCompletion_agreement`, `paddedPrefixSourceQueryReveal`, … |
| [`StripRSWSelectors/PrefixBarrierIndices`](StripRSWSelectors/PrefixBarrierIndices.lean) | Declarations: `internalArc_walk_beta_support`, `sourceBeta_cutReach_index_of_slitBarrier` |
| [`StripRSWSelectors/RawLeftQueryContainment`](StripRSWSelectors/RawLeftQueryContainment.lean) | Declarations: `raw_left_source_query_endpoints_of_barrier` |
| [`StripRSWSelectors/RoundedLocalSelector`](StripRSWSelectors/RoundedLocalSelector.lean) | Declarations: `paddedExtremalConfinedPrefixSelector_isLocal`, `roundedLocalConfinedPrefixSelectorExists` |
| [`StripRSWSelectors/UpperRayExterior`](StripRSWSelectors/UpperRayExterior.lean) | Declarations: `source_upper_ray_mem_leftExterior` |
| [`Thm4SideFactor/DirectSideAverage`](Thm4SideFactor/DirectSideAverage.lean) | Declarations: `slitRightResidualCrossingProbability`, `slitLeftResidualCrossingProbability`, `slitScreen_right_factor_of_residual_bounds`, `slitScreen_left_factor_of_residual_bounds` |
| [`Thm4SideFactor/FixedRevealAverage`](Thm4SideFactor/FixedRevealAverage.lean) | Declarations: `fixedReveal_joint_lower_of_remaining_bounds` |
| [`Thm4SideFactor/NativePush`](Thm4SideFactor/NativePush.lean) | Declarations: `floor_nat_mul`, `nativeSide_symmetric_reference_eq`, `nativeSide_reference_le`, `nativeSide_crossing_uniform_pos` |
| [`Thm4SideFactor/NativePushBridge`](Thm4SideFactor/NativePushBridge.lean) | Declarations: `nativeSideCrossingProbability_eq_rectangleBand` |
| [`Thm4SideFactor/NativePushDefinitions`](Thm4SideFactor/NativePushDefinitions.lean) | Declarations: `nativeSideRectangle`, `nativeSideBoundary`, `nativeSideCrossingEvent`, `nativeSideCrossingProbability` |
| [`Thm4SideFactor/NativePushPaths`](Thm4SideFactor/NativePushPaths.lean) | Declarations: `nativeSideReducedCrossingEvent_confined_walk` |
| [`Thm4SideFactor/NativePushReduced`](Thm4SideFactor/NativePushReduced.lean) | Declarations: `nativeSideWiredEdges_prewired`, `nativeSideWiredEdges_band_internal`, `nativeSideCrossing_sdiff_wiredEdges`, `nativeSideReducedCrossingEvent_isUpperSet`, … |
| [`Thm4SideFactor/NativePushReducedDefinitions`](Thm4SideFactor/NativePushReducedDefinitions.lean) | Declarations: `NativeSideVertex`, `nativeSideFullGraph`, `nativeSideFullBoundary`, `nativeSideWiredEdges`, … |
| [`Thm4SideFactor/OuterBond`](Thm4SideFactor/OuterBond.lean) | Declarations: `side_outer_dual_bond_open` |
| [`Thm4SideFactor/OuterSupport`](Thm4SideFactor/OuterSupport.lean) | Declarations: `auxiliary_open_endpoint_mem_original`, `right_removed_open_endpoint_mem_original`, `sideHost_mapped_endpoint_original` |
| [`Thm4SideFactor/RightBoundaryComparison`](Thm4SideFactor/RightBoundaryComparison.lean) | Declarations: `right_native_boundary_le_induced`, `right_native_further_boundary_le` |
| [`Thm4SideFactor/RightCrossingTransport`](Thm4SideFactor/RightCrossingTransport.lean) | Declarations: `RightRetainedDualGraph`, `rightNativeRemainingRead`, `sideBondToFKC`, `sideBondToFKC_pair`, … |
| [`Thm4SideFactor/RightEmbeddingGeometry`](Thm4SideFactor/RightEmbeddingGeometry.lean) | Declarations: `rightNativeToHostDual`, `rightNativeDualBond`, `rightNativeDualBond_pair`, `rightNative_primal_supported` |
| [`Thm4SideFactor/RightOuterRoutes`](Thm4SideFactor/RightOuterRoutes.lean) | Declarations: `SideDualVertex`, `sideDualGraph`, `rightDualExterior`, `right_outer_step`, … |
| [`Thm4SideFactor/RightProbability`](Thm4SideFactor/RightProbability.lean) | Declarations: `rightNativeHostGraph`, `rightNativeHostBoundary`, `nativeSideReduced_probability_le_rightResidual_of_boundary_and_surgery` |
| [`Thm4SideFactor/RightProbabilityFinal`](Thm4SideFactor/RightProbabilityFinal.lean) | Declarations: `nativeSideReduced_probability_le_rightResidual`, `rightResidual_crossing_uniform_pos` |
| [`Thm4SideFactor/RightReducedEmbedding`](Thm4SideFactor/RightReducedEmbedding.lean) | Declarations: `rightNativeReduced_supported_bond`, `rightNativeReduced_map_le_hostDual` |
| [`Thm4SideFactor/RightSourceBonds`](Thm4SideFactor/RightSourceBonds.lean) | Declarations: `rightSourceBondVertex`, `rightSourceBondEdge`, `rightSourceBondEdge_not_revealed`, `right_retained_dual_edge_of_supported_primal` |
| [`Thm4SideFactor/RightStateTransport`](Thm4SideFactor/RightStateTransport.lean) | Declarations: `rightHostDual_edgeState` |
| [`Thm4SideFactor/SideFactor`](Thm4SideFactor/SideFactor.lean) | Declarations: `slitScreen_sideFactor` |
| [`Thm4SideFactor/SideReflection`](Thm4SideFactor/SideReflection.lean) | Declarations: `slitSideConfigurationReflection`, `slitSideDualReflection`, `slitSideDualBondReflection`, `slitSideDualReflection_involutive`, … |
| [`Thm4SideFactor/SideReflectionLaw`](Thm4SideFactor/SideReflectionLaw.lean) | Declarations: `slitSide_law_reflection`, `slitSide_rightReveal_reflection`, `fixedRemaining_reconstructed_probability_eq_filtered`, `slitLeftResidualCrossingProbability_reflection`, … |
| [`Thm4SideFactor/UniformSideAverage`](Thm4SideFactor/UniformSideAverage.lean) | Declarations: `slitScreenSideFactor_of_uniform_residual_bounds` |
| [`TiltedHalfHeight/AlmostSureOpenColumns`](TiltedHalfHeight/AlmostSureOpenColumns.lean) | Declarations: `openColumnFailureFactor_bounds`, `ae_exists_fullyOpenColumn_right`, `ae_exists_fullyOpenColumn_left`, `ae_exists_fullyOpenColumns_both_sides` |
| [`TiltedHalfHeight/ColumnEvents`](TiltedHalfHeight/ColumnEvents.lean) | Declarations: `verticalColumnIndices`, `verticalColumnBond`, `verticalColumnBonds`, `verticalColumnEdges`, … |
| [`TiltedHalfHeight/ContractedCircuitGeometry`](TiltedHalfHeight/ContractedCircuitGeometry.lean) | Declarations: `closedWalk_meets_central_upper_ray`, `closedWalk_meets_central_lower_ray`, `cellBoundary_height_le_of_hull_not_top` |
| [`TiltedHalfHeight/FiniteContractedAlternative`](TiltedHalfHeight/FiniteContractedAlternative.lean) | Declarations: `hullBoundary_walk_to_native_top`, `halfHeight_or_native_dual_of_open_columns_nonpositive` |
| [`TiltedHalfHeight/FiniteOpenBlockEnergy`](TiltedHalfHeight/FiniteOpenBlockEnergy.lean) | Declarations: `openEnergy_lt_one`, `finite_open_edge_energy`, `finite_open_block_energy`, `finite_notOpenBlock_probability_le`, … |
| [`TiltedHalfHeight/FiniteReadEnergy`](TiltedHalfHeight/FiniteReadEnergy.lean) | Declarations: `blockPullback`, `blockPullback_card_le`, `blockPullback_disjoint`, `noOpenBlocks_read_iff`, … |
| [`TiltedHalfHeight/HalfHeight`](TiltedHalfHeight/HalfHeight.lean) | Declarations: `ae_halfHeight_or_native_dual_nonpositive`, `selfDualTiltedHalfHeight_nonpositive_ge_half_of_reducedMarginal`, `selfDualTiltedHalfHeight_ge_half` |
| [`TiltedHalfHeight/HullBoundaryCrosscut`](TiltedHalfHeight/HullBoundaryCrosscut.lean) | Declarations: `cellHullAvoidanceHom`, `finite_connected_hull_boundary_central_crosscut` |
| [`TiltedHalfHeight/LowerHullCells`](TiltedHalfHeight/LowerHullCells.lean) | Declarations: `lowerHull_coe_mem_iff`, `lowerHull_mem_strip`, `lowerHull_core_mem`, `lowerHull_points_not_top`, … |
| [`TiltedHalfHeight/LowerHullConfinement`](TiltedHalfHeight/LowerHullConfinement.lean) | Declarations: `LowerStripHull`, `lowerStripHull_has_no_top`, `lowerStripHull_avoids_openColumn`, `strip_open_horizontal_step`, … |
| [`TiltedHalfHeight/NativeDualBoundaryStep`](TiltedHalfHeight/NativeDualBoundaryStep.lean) | Declarations: `reducedDualVertex_height_nonpositive`, `reducedDualVertex_adj`, `hullBoundary_step_to_native_dual` |
| [`TiltedHalfHeight/OpenColumnGeometry`](TiltedHalfHeight/OpenColumnGeometry.lean) | Declarations: `fullyOpenColumn_adj`, `fullyOpenColumn_connectedToTop` |
| [`TiltedHalfHeight/OpenColumnTail`](TiltedHalfHeight/OpenColumnTail.lean) | Declarations: `noOpenBlockCylinder`, `isClopen_noOpenBlockCylinder`, `tiltedWindowStripRead_at`, `tiltedStrip_noOpenBlockCylinder_probability_le`, … |
| [`TiltedHalfHeight/ReducedCarrierHalfHeight`](TiltedHalfHeight/ReducedCarrierHalfHeight.lean) | Declarations: `tiltedBondEdge_surjective`, `normalizedStripEdge`, `normalizedStripEdge_eq`, `reducedCarrierLift`, … |
| [`TiltedHalfHeight/TopErasure`](TiltedHalfHeight/TopErasure.lean) | Declarations: `WiredTopEdge`, `topErasedConfiguration`, `topErasedOpenGraph_le`, `walk_reaches_top_after_top_erasure`, … |
| [`TiltedHalfHeightConsumers/AlmostSureConsumer`](TiltedHalfHeightConsumers/AlmostSureConsumer.lean) | Declarations: `probability_ge_half_of_ae_cover_and_map` |
| [`TiltedHalfHeightConsumers/ProbabilityConsumer`](TiltedHalfHeightConsumers/ProbabilityConsumer.lean) | Declarations: `measurableSet_tiltedHalfHeight` |
| [`VerticalCrosscutGeometry`](VerticalCrosscutGeometry.lean) | Declarations: `verticalSquareNormalizationIso`, `verticalSquareNormalizationIso_val`, `VerticalSquareCrosscutData`, `normalized`, … |
