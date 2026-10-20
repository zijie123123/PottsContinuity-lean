# `PottsContinuity/Thm4Plane/`

Theorem 4 in the plane via slit-domain screens, and the derivation of Theorems 1 and 2 from Theorem 4 and Theorem 3.

41 modules, 4,882 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`ExplicitLimit`](ExplicitLimit.lean) | Declarations: `exists_self_dual_free_limit` |
| [`FinalRootRoutes`](FinalRootRoutes.lean) | Declarations: `corrected_touch_lower_bound`, `theorem_2_of_sideFactor`, `theorem_1_of_sideFactor` |
| [`GeneralEScreen`](GeneralEScreen.lean) | Declarations: `generalEScreenRadius`, `generalEScreenEvent`, `generalEScreenEvent_sixteen_eq` |
| [`GeneralScreenArchResidualDomain`](GeneralScreenArchResidualDomain.lean) | Declarations: `generalScreenArchCapDomainGraph` |
| [`GeneralScreenSetup`](GeneralScreenSetup.lean) | Rounded all-scale screen geometry. The dual face center associated with a face base `(x,y)` is `(x+1/2,y+1/2)`. |
| [`LogarithmicLimit`](LogarithmicLimit.lean) | Declarations: `boxBoundary_logarithmic_rate_zero_of_polynomial_lower_bound` |
| [`LogarithmicLimit16`](LogarithmicLimit16.lean) | Declarations: `boxBoundary_logarithmic_rate_zero_of_sixteen_scale_polynomial_lower_bound` |
| [`PlaneFiniteComparison`](PlaneFiniteComparison.lean) | Declarations: `finite_free_embedded_event_le_centered_box_boundary_probability_of_event_inclusion` |
| [`PlaneTranslation`](PlaneTranslation.lean) | Declarations: `centeredBoxBoundaryConnectionEvent`, `translatedBoxBoundaryConnectionEvent`, `translatedBoxBoundaryConnectionEvent_eq_preimage`, `translatedBoxBoundaryConnection_probability_eq` |
| [`ScreenActiveConnectorDualConfig`](ScreenActiveConnectorDualConfig.lean) | Declarations: `SlitRStarGraph`, `SlitRStarVertex`, `SlitRStarEdgeBridge`, `slitRStarEdgeBridge`, … |
| [`ScreenActiveConnectorFactor`](ScreenActiveConnectorFactor.lean) | Declarations: `slitScreenRStarActiveGraph`, `slitScreenRStarActiveArcs`, `SlitActiveConnectorRecordInput` |
| [`ScreenActiveConnectorSourcePaths`](ScreenActiveConnectorSourcePaths.lean) | Declarations: `SlitScreenRStarSourcePathPair`, `SlitScreenRStarSourcePathPair.crosscutData`, `SlitActiveConnectorSourcePathRecordInput` |
| [`ScreenArchCrossedCut`](ScreenArchCrossedCut.lean) | Declarations: `screenArchCrossedBondConfiguration`, `screenArchCrossedBondConfiguration_mem_closed`, `crossedPrimalBond_in_targetBox_of_capInternalEdge`, `screenArchCrossedBondConfiguration_avoids_capInternalEdge_of_exteriorSupport` |
| [`ScreenArchPath`](ScreenArchPath.lean) | Declarations: `generalScreenArchFaceBases`, `generalScreenArchFaceCenters_outside_translatedTargetBox`, `generalScreenActualClosedDualGraph_mono`, `walk_support_pair_reachable`, … |
| [`ScreenBoundaryClusterCap`](ScreenBoundaryClusterCap.lean) | Declarations: `screenTargetCap_subset_boundaryClusterInterior_of_sourceScreen_and_connector` |
| [`ScreenBoundaryClusterConditional`](ScreenBoundaryClusterConditional.lean) | Declarations: `screenCapEmptyRestriction_eq_induce`, `screenBoundaryClusterCapConnectionEvent`, `screenBoundaryClusterCapConnectionEvent_isUpperSet`, `screenBoundaryClusterRestriction_openAdj`, … |
| [`ScreenBoundaryClusterFiber`](ScreenBoundaryClusterFiber.lean) | Declarations: `screenOpenAdj_iff_bond_mem`, `screenBoundaryTouchCluster_subset_of_record_agreement`, `screenBoundaryTouchCluster_reverse_of_record_agreement`, `boundaryClusterInterior_eq_of_boundaryClusterStatistic_eq`, … |
| [`ScreenCanonicalPlaneSourceRecords`](ScreenCanonicalPlaneSourceRecords.lean) | Declarations: `ScreenSlitConfiguration`, `slitScreenPlaneJointSourceEvent`, `SlitScreenPlaneSourceArch`, `slitScreenPlaneSourceCut`, … |
| [`ScreenCapComplementFreeLaw`](ScreenCapComplementFreeLaw.lean) | Declarations: `screenCapEdgeDeletedFullCarrierGraph`, `screenCapEdgeDeletedFullCarrierGraph_le_slitBox`, `screenArchWalk_support_mem_archCarrier`, `generalScreenArchWalk_support_outsideTargetBox` |
| [`ScreenCapDomainPlaneEvent`](ScreenCapDomainPlaneEvent.lean) | Declarations: `screenCapDomainVertexEmbedding`, `screenCapEdgeDeletedDomainGraph`, `screenCapEdgeDeletedDomainGraph_map_to_PD`, `screenCapBoundaryConnectionEvent`, … |
| [`ScreenCapFreeLaw`](ScreenCapFreeLaw.lean) | Declarations: `pdParameters_eq_criticalParameters_of_selfDualValue` |
| [`ScreenCapFullCarrierEvent`](ScreenCapFullCarrierEvent.lean) | Declarations: `screenCapFullCarrierBoundaryConnectionEvent`, `screenCapComplementRevealFullCarrierDecoder` |
| [`ScreenCapResidualConfiguration`](ScreenCapResidualConfiguration.lean) | Declarations: `screenCapDomainVertexEmbeddingToSlitBox`, `screenCapEdgeDeletedDomainGraph_map_to_slitBox`, `screenCapComplementReveal`, `screenCapResidualConfiguration`, … |
| [`ScreenChainRule`](ScreenChainRule.lean) | Declarations: `three_event_probability_chain_lower_bound` |
| [`ScreenConnector`](ScreenConnector.lean) | Declarations: `slitScreenConnectorEvent`, `walk_support_pair_reachable` |
| [`ScreenDominatedBallReveal`](ScreenDominatedBallReveal.lean) | Declarations: `slitScreenBallRevealEdges`, `slitScreenBallReveal`, `openAdj_transferred_of_ball_agreement`, `screenWalk_transferred_of_ball_agreement`, … |
| [`ScreenFactorAssembly`](ScreenFactorAssembly.lean) | Declarations: `slitScreenFiniteMeasure`, `slitScreenFourFactor_probability_lower_bound_of_crossing_factors` |
| [`ScreenFreeComponent`](ScreenFreeComponent.lean) | Declarations: `screenCap_open_adj_le_edgeRestriction_of_closedCut`, `screenTargetCap_openConnectionToWiredArc_false_of_crosscut` |
| [`ScreenMixedFactor`](ScreenMixedFactor.lean) | Declarations: `slitScreenRStarBase`, `slitScreenRStarSide` |
| [`ScreenPlaneAssembly`](ScreenPlaneAssembly.lean) | Declarations: `theorem_four_at_self_dual_of_screen_factors_and_plane_transfer`, `theorem_four_at_self_dual_of_source_screen_interfaces` |
| [`ScreenRecordAssembly`](ScreenRecordAssembly.lean) | Declarations: `SlitConnectorRecordInput`, `SlitPlaneRecordInput` |
| [`ScreenSelectedArchResidual`](ScreenSelectedArchResidual.lean) | Declarations: `screenActualDualWalk_support_mem_carrier`, `generalEScreenEvent_fixedDualWalk_componentResidualConnection` |
| [`ScreenSideFactor`](ScreenSideFactor.lean) | The two side screens from recordwise rotated crossing estimates. Each record input describes one application of Lemma 3 in a finite … |
| [`ScreenTargetCap`](ScreenTargetCap.lean) | Declarations: `screenTargetCap`, `screenTargetRadius`, `screenTargetCap_y_lower`, `max_le_add_one`, … |
| [`ScreenTargetCapComponent`](ScreenTargetCapComponent.lean) | Declarations: `screenTargetCapEdgeDeletedComponent`, `screenTargetCap_subset_edgeDeletedComponent_of_no_internal_removal`, `screenTargetCapEdgeDeletedComponent_boundaryEdge_mem_removed` |
| [`ScreenTargetCapGraphConnectivity`](ScreenTargetCapGraphConnectivity.lean) | Declarations: `screenTargetCapInternalEdge`, `screenTargetCapRectangleVertex`, `screenTargetCapRectToCap`, `screenTargetCapRectToCap_val`, … |
| [`ScreenTargetCapInducedPath`](ScreenTargetCapInducedPath.lean) | Declarations: `screenTargetCap_bottomCenter_mem`, `generalEScreenEvent_has_path_in_any_induced_cap_domain` |
| [`ScreenTargetCapPlaneEvent`](ScreenTargetCapPlaneEvent.lean) | Declarations: `screenSlitVertexEmbedding`, `screenSlitGraph_map_to_PD` |
| [`ScreenTargetExterior`](ScreenTargetExterior.lean) | Declarations: `screenTargetFaceCenterInBox`, `screenTargetPrimalBondInBox`, `dualBond_has_faceCenter_in_target_of_crossingBond_in_target`, `dualBond_crossingBond_not_in_target_of_faceCenters_outside`, … |
| [`SlitScreenEvent`](SlitScreenEvent.lean) | Declarations: `slitScreenEvent`, `int_abs_succ_bounds`, `int_abs_adj_bounds`, `shiftedRadius`, … |
| [`TheoremFourOfSideFactor`](TheoremFourOfSideFactor.lean) | Declarations: `theorem_four_at_self_dual_of_sideFactor` |
