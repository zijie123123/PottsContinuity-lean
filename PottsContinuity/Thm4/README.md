# `PottsContinuity/Thm4/`

Lemma 8 and the proof of Theorem 4 from the parafermionic observable (Section 4 of the paper).

95 modules, 13,110 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`BoundaryLowerFour`](BoundaryLowerFour.lean) | Declarations: `connectedExteriorVertices_expected_card`, `cover_boundary_connection_sum_lower_bound_four` |
| [`BoundaryPhase`](BoundaryPhase.lean) | Declarations: `parafermionicBoundarySpin`, `parafermionicBoundarySpin_bounds`, `parafermionicBoundaryPhase`, `parafermionicBoundaryCoefficient`, … |
| [`CanonicalSeed`](CanonicalSeed.lean) | Canonical seed for a queried edge. The incoming source-tip port is uniquely determined by its actual lifted edge. |
| [`ContourBoundary`](ContourBoundary.lean) | Declarations: `parafermionicCoverFinitePortOtherEndpointInBox`, `parafermionicCoverFinitePortEdgeEndpointsInBox_iff`, `parafermionicCoverPortVertex_otherEndpoint_adj`, `parafermionicCoverExposedCornerOccurrence`, … |
| [`CoverConfiguration`](CoverConfiguration.lean) | Declarations: `ParafermionicAmbientVertex`, `ParafermionicAmbientGraph`, `parafermionicCoverBoxVertexEmbedding`, `parafermionicCoverBoxGraph_map_le`, … |
| [`CoverGraph`](CoverGraph.lean) | Declarations: `frozen_squareLattice_adj_iff`, `ParafermionicCoverVertex`, `parafermionicCoverSheetShift`, `parafermionicCoverAdjCases`, … |
| [`CoverMeasureBridge`](CoverMeasureBridge.lean) | Declarations: `coverOriginConnectionProbability`, `coverExteriorBoundary_image`, `fkc_coverOriginConnectionWeight_eq`, `fkc_boundary_connection_sum_eq` |
| [`CoverPorts`](CoverPorts.lean) | Declarations: `ParafermionicCoverPort`, `parafermionicCoverPortVertex`, `parafermionicCoverPortSourceSheet`, `parafermionicCoverPortOtherVertex`, … |
| [`CoverToggle`](CoverToggle.lean) | Declarations: `parafermionicCoverFiniteEdgeEmbedding`, `parafermionicCoverConfigurationExtensionState_toggle_at_image`, `parafermionicCoverConfigurationExtensionState_toggle`, `parafermionicCoverPortBondState_toggle`, … |
| [`CoverTurn`](CoverTurn.lean) | Declarations: `parafermionicCoverMedialTurnPositive`, `parafermionicCoverMedialTurnExponent` |
| [`CriticalEdgeToggle`](CriticalEdgeToggle.lean) | Declarations: `toggleEdgeConfiguration`, `toggleEdgeConfiguration_mem`, `toggleEdgeConfiguration_mem_of_ne`, `toggleEdgeConfiguration_involutive`, … |
| [`DirectedPath`](DirectedPath.lean) | Declarations: `parafermionicCoverFinitePairingForward_orientation_change`, `parafermionicCoverFinitePairingForward_predecessor_unique`, `parafermionicCoverFiniteWalkForward_of_incoming`, `parafermionicCoverFiniteOrigin_no_incoming`, … |
| [`EdgeCutDirectedPaths`](EdgeCutDirectedPaths.lean) | Declarations: `edgeCutWalkDirected_of_incoming`, `edgeCutWalkDirected_of_no_incoming`, `edgeCutWalkDirected_last`, `edgeCutBackward_adj_or`, … |
| [`EdgeCutGraph`](EdgeCutGraph.lean) | Declarations: `parafermionicCoverFiniteEdgeCutGraph`, `parafermionicCoverFiniteEdgeCutGraph_adj_iff`, `parafermionicCoverFiniteEdgeCutGraph_adj_false_false`, `parafermionicCoverFiniteEdgeCutGraph_adj_false_true`, … |
| [`EdgeCutOrientation`](EdgeCutOrientation.lean) | Declarations: `parafermionicCoverFiniteEdgeCutForward`, `parafermionicCoverFiniteEdgeCut_adj_or_forward`, `coverCutCorner_eq_corner_of_ne`, `parafermionicCoverFiniteEdgeCutForward_not_both`, … |
| [`EdgeCutPartner`](EdgeCutPartner.lean) | Declarations: `parafermionicCoverFiniteEdgeCutTerminals`, `parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne`, `parafermionicCoverFiniteEdgeCutTerminals_card`, `ParafermionicCoverFiniteEdgeCutTerminal`, … |
| [`EdgeCutPathSystem`](EdgeCutPathSystem.lean) | Declarations: `parafermionicCoverFiniteEdgeCutSourcePath`, `parafermionicCoverFiniteEdgeCutSourcePath_isPath`, `parafermionicCoverFiniteEdgeCutSourcePath_unique`, `parafermionicCoverFiniteEdgeCutSourcePath_end_eq_sinkLabel`, … |
| [`EdgeCutReconnection`](EdgeCutReconnection.lean) | Declarations: `parafermionicCoverFiniteEdgeCutPort_state_eq_mem`, `parafermionicCoverFiniteEdgeCutPort_localPair_eq_state`, `parafermionicCoverOpenPair_closedPair_commute`, `parafermionicCoverFiniteEdgeCutSeed_localPair_eq`, … |
| [`EdgeCutReconnectionTurn`](EdgeCutReconnectionTurn.lean) | Declarations: `medialTurnPositive_eq_incoming_xor_state`, `parafermionicCoverFiniteEdgeCutSinkTurnExponent`, `edgeCutTurn_sink_one_point`, `edgeCutTurn_sink_two_point`, … |
| [`EdgeCutRoutingWalk`](EdgeCutRoutingWalk.lean) | Declarations: `parafermionicCoverFiniteEdgeCutRoutingSuccessor`, `parafermionicCoverFiniteEdgeCutRoutingLength`, `parafermionicCoverFiniteEdgeCutSourcePath_cornerCut`, `parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath`, … |
| [`EdgeCutSourceSinkCount`](EdgeCutSourceSinkCount.lean) | Declarations: `ParafermionicCoverFiniteEdgeCutSources`, `ParafermionicCoverFiniteEdgeCutSinks`, `parafermionicCoverFiniteEdgeCutSourceSinkEquiv`, `parafermionicCoverFiniteEdgeCutSources_card`, … |
| [`EdgeCutTerminalLabels`](EdgeCutTerminalLabels.lean) | Declarations: `parafermionicCoverFiniteEdgeCutSeedPort`, `parafermionicCoverFiniteEdgeCutSeedPort_spec`, `ParafermionicCoverFiniteEdgeCutSeedOrbit`, `parafermionicCoverFiniteEdgeCutSeedOrbit_nonempty`, … |
| [`EdgeCutTerminalPermutation`](EdgeCutTerminalPermutation.lean) | Declarations: `parafermionicCoverFiniteEdgeCutTerminalPermutation`, `parafermionicCoverFiniteEdgeCutTerminalPermutation_sinkLabel`, `parafermionicCoverFiniteEdgeCutTerminalPermutation_reachable`, `parafermionicCoverFiniteEdgeCutSourceSinkEquiv_toggle_eq`, … |
| [`EdgeCutTerminals`](EdgeCutTerminals.lean) | Declarations: `parafermionicCoverFiniteEdgeCutQueriedPorts`, `parafermionicCoverFiniteEdgeCutDegreeOneVertices`, `parafermionicCoverFiniteEdgeCutCornerTerminals`, `parafermionicCoverFiniteEdgeCutDegreeOne_true_iff`, … |
| [`EdgePorts`](EdgePorts.lean) | Declarations: `parafermionicCoverPortEdge_eq_iff_four`, `parafermionicCoverPort_four_pairwise_ne`, `parafermionicCoverPort_four_mem_finite` |
| [`EndpointDefect`](EndpointDefect.lean) | The actual local winding defect at q = 4. This is the signed internal-port sum in one actual finite edge fiber, before averaging over the … |
| [`EndpointPassage`](EndpointPassage.lean) | Declarations: `continuous_le_at_four`, `fkc_event_upper_bound_at_four` |
| [`Exploration`](Exploration.lean) | Declarations: `parafermionicCoverFiniteOriginCornerPort`, `parafermionicCoverFiniteOriginCornerPort_val`, `parafermionicCoverFiniteCornerPairPerm_origin`, `parafermionicCoverFiniteCornerPairPerm_origin_ne`, … |
| [`ExplorationOrientation`](ExplorationOrientation.lean) | Declarations: `parafermionicCoverFinitePairingForward`, `parafermionicCoverFiniteCornerCutPairingGraph_adj_iff`, `parafermionicCoverFinitePairingForward_implies_adj`, `parafermionicCoverFiniteCutCorner_eq_corner_of_ne`, … |
| [`ExplorationPath`](ExplorationPath.lean) | Declarations: `parafermionicCoverFiniteCornerCutPairingGraph_le`, `parafermionicCoverFiniteOriginExplorationPath`, `parafermionicCoverFiniteOriginExplorationPath_isPath`, `parafermionicCoverFiniteOriginExplorationPath_support_actualConnected` |
| [`ExplorationProbability`](ExplorationProbability.lean) | Declarations: `parafermionicCoverOriginExplorationVisitEvent`, `parafermionicCoverFiniteOriginCornerPortPrimalVertex_eq_boxOrigin`, `parafermionicCoverOriginExplorationVisitEvent_subset_actualConnection`, `parafermionicCoverOriginExplorationVisit_probability_le_connection` |
| [`ExteriorConnectionCount`](ExteriorConnectionCount.lean) | Declarations: `coverExteriorBoundary`, `connectedExteriorVertices`, `exteriorIncomingVisit_vertex_mem`, `exteriorIncomingVisits_card_le_three_connected` |
| [`ExteriorDirections`](ExteriorDirections.lean) | Declarations: `vertical_port_internal`, `incoming_port_side_eq`, `exterior_incoming_ports_at_vertex_card_le_three` |
| [`ExteriorWinding`](ExteriorWinding.lean) | Declarations: `exteriorPort_state_false`, `exteriorPort_localPair_otherVertex`, `exteriorPort_localPair_iff`, `medialTurnPositive_closed_eq_flag`, … |
| [`ExtremalConnectionMass`](ExtremalConnectionMass.lean) | Declarations: `coverOriginConnectionProbability_le_exp_extremal`, `coverExtremalConnectionMass`, `coverExtremalConnectionMass_le`, `tendsto_coverExtremalConnectionMass` |
| [`FKCExplorationBridge`](FKCExplorationBridge.lean) | Declarations: `explorationVertexEquiv`, `cutCornerPair_eq`, `explorationGraphIso`, `exploration_support_eq`, … |
| [`FKCGraphBridge`](FKCGraphBridge.lean) | Declarations: `fkc_coverGraph_eq`, `fkc_ambientGraph_eq`, `fkcEdgeEquiv`, `fkcConfiguration`, … |
| [`FKCPortBridge`](FKCPortBridge.lean) | Declarations: `axisEquiv`, `bondEquiv`, `portEquiv`, `coverPortEquiv`, … |
| [`FKCProbabilityBridge`](FKCProbabilityBridge.lean) | Declarations: `fkcBoundaryToPD`, `fkcBoundaryToPD_free`, `fkcBoundaryToPD_wired`, `fkc_measure_eq` |
| [`FKCTurnBridge`](FKCTurnBridge.lean) | Declarations: `turnExponent_eq`, `stepTurn_eq`, `walkTurn_map`, `exploration_turn_eq_four` |
| [`FKCVisitBridge`](FKCVisitBridge.lean) | Declarations: `sourceFlag`, `sinkFlag`, `falseVisits_card_twoSegments`, `finiteEdgeEmbedding_eq`, … |
| [`FarLayerEndpoint`](FarLayerEndpoint.lean) | Declarations: `cover_connection_four_le_exp_positive`, `cover_connection_four_le_exp_negative` |
| [`FiniteEdgePort`](FiniteEdgePort.lean) | Declarations: `parafermionicCoverPort_exists_for_edge`, `parafermionicCoverFiniteEdgeEmbedding_endpoints_mem`, `parafermionicCoverFinitePort_exists_for_edge` |
| [`FinitePairSum`](FinitePairSum.lean) | Declarations: `sum_signed_eq_incoming_pairs` |
| [`FiniteParameterContinuity`](FiniteParameterContinuity.lean) | Declarations: `continuous_selfDual_edgeProbability`, `continuous_selfDual_weight`, `continuous_selfDual_partitionFunction`, `continuous_selfDual_configurationProbability`, … |
| [`FinitePorts`](FinitePorts.lean) | Declarations: `ParafermionicCoverFinitePort`, `parafermionicCoverFinitePortCoordinatesEmbedding`, `parafermionicCoverFinitePortFintype`, `parafermionicCoverLocalPair_preservesFinitePort`, … |
| [`FiniteWitnessEndpoint`](FiniteWitnessEndpoint.lean) | Declarations: `continuous_finite_witness_at_four` |
| [`LatticePorts`](LatticePorts.lean) | Actual square-lattice bonds and medial ports. A bond is a horizontal or vertical unit lattice segment, normalized by its left or lower … |
| [`LocalWinding`](LocalWinding.lean) | Additive local winding across a restored queried edge. Unlike an exponential phase, the winding difference across a visited local pairing … |
| [`MedialPortTurn`](MedialPortTurn.lean) | Declarations: `medialTurnPositive` |
| [`ModifiedContourIdentity`](ModifiedContourIdentity.lean) | Declarations: `contourIdentityValue_corner_eq`, `contourIdentitySign_corner`, `contourIdentity_origin_internal`, `contourIdentity_originPartner_internal`, … |
| [`ModifiedObservableSum`](ModifiedObservableSum.lean) | Declarations: `modifiedPathExpectation_eq_configuration_sum`, `modifiedPathExpectation_four_eq_winding_sum`, `modifiedPathExpectation_four_edge_defect_zero` |
| [`OriginCorner`](OriginCorner.lean) | Declarations: `parafermionicCoverOriginCornerPort`, `parafermionicCoverOriginCornerPortOther`, `parafermionicCoverOriginCornerPort_primalVertex`, `parafermionicCoverOriginCornerPortOther_primalVertex`, … |
| [`PairingGraph`](PairingGraph.lean) | A layered simple graph retaining two pairing identities. Each port has a false-layer vertex and a true-layer vertex, joined vertically. |
| [`PairingPathSupport`](PairingPathSupport.lean) | Declarations: `path_support_closed_under_adj_of_two_terminal_degrees`, `pairingGraph_path_support_closed_under_adj` |
| [`PairingSingleCut`](PairingSingleCut.lean) | Declarations: `pairingSingleCut`, `pairingSingleCut_involutive`, `pairingSingleCutPerm`, `pairingSingleCutPerm_apply`, … |
| [`PathObservable`](PathObservable.lean) | Declarations: `parafermionicCoverPathPhaseExpectation`, `parafermionicCoverPathPhaseExpectation_norm_le_visit`, `parafermionicCoverPathPhaseExpectation_norm_le_connection`, `parafermionicCoverPathPhaseExpectation_target`, … |
| [`PathPhase`](PathPhase.lean) | Declarations: `walk_dropUntil_end_eq_nil`, `parafermionicCoverPathPhaseAtom`, `parafermionicCoverPathPhaseAtom_norm`, `parafermionicCoverPathPhaseAtom_source`, … |
| [`PathTerminals`](PathTerminals.lean) | Declarations: `degree_one_vertex_mem_path_support_endpoints` |
| [`PhaseAlgebra`](PhaseAlgebra.lean) | Declarations: `loopWeight`, `loopWeight_sq`, `loopWeight_pos`, `one_le_loopWeight`, … |
| [`PhaseRecurrence`](PhaseRecurrence.lean) | Declarations: `dart_snd_mem_support_of_mem_darts`, `phaseOfWalk_darts_recurrence`, `parafermionicCoverPathPhaseAtom_darts_recurrence` |
| [`PortCoordinates`](PortCoordinates.lean) | Declarations: `endpoint_portBaseFromPrimalVertex`, `latticePortPrimalVertexCoordinatesEquiv` |
| [`PortOrientation`](PortOrientation.lean) | Declarations: `medialIncomingPrimalLeft`, `medialIncomingPrimalLeft_openPair`, `medialIncomingPrimalLeft_closedPair`, `medialIncomingPrimalLeft_cornerPair`, … |
| [`PrimalConnectivity`](PrimalConnectivity.lean) | Declarations: `parafermionicCoverFinitePortPrimalVertex`, `parafermionicCoverFiniteLocalPair_open_adj`, `parafermionicCoverFiniteLocalPair_actualConnected`, `parafermionicCoverFiniteCornerPair_actualConnected`, … |
| [`RoutingPortVisits`](RoutingPortVisits.lean) | Declarations: `parafermionicCoverFiniteEdgeFalseVisits`, `cornerCutSourcePath_support_eq`, `queried_visit_in_cutPath_endpoints`, `queried_visit_iff_cutPath_endpoint`, … |
| [`SelfDualParameters`](SelfDualParameters.lean) | The explicit self-dual finite FK parameter. The parameter is the formula sqrt(q)/(1+sqrt(q)), with real q >= 1. |
| [`SideBoundary`](SideBoundary.lean) | Declarations: `coverSideBoundary`, `coverSideBoundary_image`, `coverSideBoundary_card_le`, `cover_boundary_connection_sum_le_side_add_extremal` |
| [`SidePositive`](SidePositive.lean) | Declarations: `coverPositiveVerticalVertex`, `coverPositiveVerticalVertex_mem`, `coverPositiveVerticalVertex_probability_pos` |
| [`SideWitness`](SideWitness.lean) | Declarations: `cover_side_connection_sum_eventually_lower`, `cover_side_connection_eventual_polynomial_witness` |
| [`SideWitnessAllScales`](SideWitnessAllScales.lean) | Declarations: `cover_side_connection_polynomial_witness` |
| [`SlitBottomWitness`](SlitBottomWitness.lean) | Declarations: `slit_bottom_center_probability_pos_one`, `slit_bottom_arc_polynomial_witness` |
| [`SlitCenterLowerBound`](SlitCenterLowerBound.lean) | Declarations: `slit_center_arc_polynomial_lower_bound`, `slit_box_center_arc_polynomial_lower_bound` |
| [`SlitCenterPairComparison`](SlitCenterPairComparison.lean) | Declarations: `slit_center_probability_ge_pair_strict`, `slit_center_probability_ge_pair` |
| [`SlitComparison`](SlitComparison.lean) | Declarations: `slitArcConnectionProbability`, `continuous_slitArcConnectionProbability`, `cover_side_to_slit_strict`, `cover_side_to_slit_four`, … |
| [`SlitPairedWitness`](SlitPairedWitness.lean) | Declarations: `slit_paired_bottom_polynomial_witness` |
| [`SlitReflection`](SlitReflection.lean) | Declarations: `continuous_le_on_closed_range`, `slitPairConnectionProbability`, `continuous_slitPairConnectionProbability`, `slitArcConnectionProbability_reflection`, … |
| [`SourceNormalization`](SourceNormalization.lean) | Declarations: `pathWindingAtom_source` |
| [`TerminalPairing`](TerminalPairing.lean) | A finite graph component containing a degree-one vertex has another degree-one vertex when the ambient graph has maximum degree two. |
| [`ThreeReturnConnection`](ThreeReturnConnection.lean) | Declarations: `edgeCutSourcePath_actualConnected`, `fin3_eq_one_of_ne_zero_ne_two`, `fin3_eq_two_of_ne_zero_ne_one`, `fin3_eq_zero_of_ne_one_ne_two`, … |
| [`ThreeTerminalRouting`](ThreeTerminalRouting.lean) | Declarations: `ThreeTerminal`, `threeTerminalSwap`, `openRoutingSuccessor`, `firstPositiveReturnLength`, … |
| [`TotalWinding`](TotalWinding.lean) | Declarations: `total_signed_winding_sum` |
| [`TwoReturnNonconnection`](TwoReturnNonconnection.lean) | Declarations: `closedTwoReturn_not_actualConnected`, `twoReturn_selfDual_free_probability` |
| [`TwoTerminalGraph`](TwoTerminalGraph.lean) | The unique open path in a finite two-terminal graph. A finite simple graph with two distinct vertices of degree one and every other vertex … |
| [`UniformBoundaryLower`](UniformBoundaryLower.lean) | Declarations: `cover_boundary_connection_sum_uniform_lower` |
| [`WalkTurn`](WalkTurn.lean) | Declarations: `parafermionicCoverFinitePairingStepTurn`, `parafermionicCoverFinitePairingWalkTurn`, `parafermionicCoverFinitePairingWalkTurn_append` |
| [`WindingBulk`](WindingBulk.lean) | Declarations: `internalPortEdge`, `internalPortEdge_projection`, `windingEdgePorts_mem_iff_internal_edge`, `sum_windingEdgePorts_eq_internal_sum`, … |
| [`WindingCancellation`](WindingCancellation.lean) | Declarations: `windingAtomicDefect_two_return_probability_pair_four`, `windingAtomicDefect_closed_probability_pair_four`, `windingAtomicDefect_probability_pair_cancel_four`, `windingAtomicDefect_configuration_sum_four` |
| [`WindingDefectVisits`](WindingDefectVisits.lean) | Declarations: `windingEdgePorts_eq_queriedPorts`, `windingAtomicDefect_eq_four_ports`, `windingIncomingVisitCount`, `windingAtomicDefect_eq_signed_visit_count` |
| [`WindingRecurrence`](WindingRecurrence.lean) | Declarations: `windingOfWalk`, `dart_snd_mem_support_of_mem_darts`, `windingOfWalk_darts_recurrence`, `parafermionicCoverPathWindingAtom_darts_recurrence` |
| [`WindingRoutingCounts`](WindingRoutingCounts.lean) | Declarations: `fin3_nonzero_cases`, `fin3_distinct_nonzero_cases`, `incomingPort_ne_sourceLabel`, `queried_mem_visits_iff`, … |
| [`WindingToggle`](WindingToggle.lean) | Declarations: `openRouting_of_two_return`, `openRouting_of_three_return`, `closed_routing_successors`, `windingAtomicDefect_closed_two_return_values`, … |
| [`WindingVisitMass`](WindingVisitMass.lean) | Declarations: `coverFreeFourMass`, `pathWindingMean`, `exteriorIncomingVisits`, `pathWindingMean_eq_re`, … |
| [`ZeroReturnPermutation`](ZeroReturnPermutation.lean) | Declarations: `sourceLabel_zero_vertex`, `sinkLabel_zero_vertex`, `terminalPermutation_zero_iff_edgeCutZeroReturn`, `windingAtomicDefect_permutation_zero_probability_pair` |
| [`ZeroReturnWinding`](ZeroReturnWinding.lean) | Winding cancellation for the actual zero-return event. The event is literal reachability of the original two corner terminals after cutting … |
| [`ZeroTurn`](ZeroTurn.lean) | Declarations: `finiteCornerCut_support_adj`, `finiteCornerCut_vertical_support_iff`, `finitePath_vertical_successor_dart`, `finitePath_vertical_predecessor_dart`, … |
