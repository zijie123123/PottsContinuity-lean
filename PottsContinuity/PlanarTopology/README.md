# `PottsContinuity/PlanarTopology/`

Discrete planar topology: Jordan-type separation, circuits and crossings, planar non-coexistence, crossing corridors.

220 modules, 17,853 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`AdjacentProbabilityBalance`](AdjacentProbabilityBalance.lean) | Declarations: `exists_adjacent_above_threshold`, `exists_adjacent_above_threshold_of_tendsto` |
| [`AffinePathIntersection`](AffinePathIntersection.lean) | Declarations: `clamp_eq_of_strict_interior`, `affine_paths_intersect` |
| [`AffineWalkBounds`](AffineWalkBounds.lean) | Declarations: `latticeWalkPath_mem_of_convex`, `latticeWalkPath_affine_band_bounds` |
| [`AlphaConnectorEndpoints`](AlphaConnectorEndpoints.lean) | Declarations: `unit_center_coordinates`, `alpha_clamp_coordinates`, `alpha_clamped_left_endpoint`, `alpha_clamped_right_endpoint` |
| [`AlphaCoreBottomChain`](AlphaCoreBottomChain.lean) | Declarations: `alpha_core_bottom_grid_covers`, `alpha_core_512_bottom_connections_glue` |
| [`AlphaCoreBottomEvent`](AlphaCoreBottomEvent.lean) | Declarations: `alphaCoreBottomArc`, `alphaCoreBottomFactor`, `alpha_core_bottom_arc_long_gluing` |
| [`AlphaCoreBottomGluing`](AlphaCoreBottomGluing.lean) | Declarations: `alpha_core_to_bottom_long_gluing` |
| [`AlphaCoreBridgeWitness`](AlphaCoreBridgeWitness.lean) | Declarations: `alpha_core_bridge_walk_witness` |
| [`AlphaCoreCoverGluing`](AlphaCoreCoverGluing.lean) | Declarations: `alpha_core_cover_piece_gluing` |
| [`AlphaCoreFiniteCover`](AlphaCoreFiniteCover.lean) | Declarations: `alpha_core_bridge_finite_cover`, `kst_arm_complement_dual_finite_cover` |
| [`AlphaCoreFiveCover`](AlphaCoreFiveCover.lean) | Declarations: `alphaCoreCoverPiece`, `alphaCoreCoverPiece_isCylinder`, `alphaCoreCoverPiece_isUpperSet`, `alpha_core_bridge_five_cover` |
| [`AlphaCoreRectangleFactors`](AlphaCoreRectangleFactors.lean) | Declarations: `alphaCoreRectangle`, `alpha_core_horizontal_factor_witness`, `alpha_core_vertical_factor_witness` |
| [`AlphaCoreRectangleGluing`](AlphaCoreRectangleGluing.lean) | Declarations: `alphaCoreRectangleFactor`, `alpha_core_rectangle_long_gluing` |
| [`AlphaCoreReflections`](AlphaCoreReflections.lean) | Declarations: `alphaCoreReflectionXIso`, `alphaCoreReflectionYIso`, `alphaCoreReflectionXIso_box`, `alphaCoreReflectionYIso_box`, … |
| [`AlphaCoreSymmetries`](AlphaCoreSymmetries.lean) | Declarations: `alphaCoreReflectionBothIso`, `alphaCoreReflectionBothIso_box`, `alphaCoreReflectionXIso_symm_apply`, `alphaCoreLeftTargets_x_map`, … |
| [`AlphaCoreTargets`](AlphaCoreTargets.lean) | Declarations: `alphaCoreLeftTargets`, `alphaCoreRightTargets`, `alpha_left_port_core_target`, `alpha_right_port_core_target` |
| [`AlphaCoreToBottom`](AlphaCoreToBottom.lean) | Declarations: `alphaCoreToBottom`, `alphaCoreToBottom_isUpperSet`, `alphaCoreToBottom_isCylinder`, `alpha_core_to_bottom_reflected_glue` |
| [`AlphaTargetAlternative`](AlphaTargetAlternative.lean) | Declarations: `alphaTargetPrimalCrossing`, `alphaTargetDualCrossing`, `alpha_target_crossings_exclusive`, `alpha_target_crossing_iff_not_dual` |
| [`AlphaTargetDualPorts`](AlphaTargetDualPorts.lean) | Declarations: `alphaTargetRectangle_next_val`, `alphaTargetRectangle_boundaryBond`, `alphaTargetRectangle_cell_center_iff`, `alphaTargetRectangle_outsideSide`, … |
| [`AlphaTargetDuality`](AlphaTargetDuality.lean) | Declarations: `alpha_target_dual_exists` |
| [`AlphaTargetGraphBridge`](AlphaTargetGraphBridge.lean) | Declarations: `alphaTargetRectangle_vertex_mem_iff`, `alphaTargetRectangle_graph_adj_iff`, `alphaTargetRectangleGraphIso`, `alphaTargetRectangleGraphIso_val`, … |
| [`AlphaTargetRectangle`](AlphaTargetRectangle.lean) | Declarations: `alphaTargetRectanglePolygon`, `alphaTargetRectanglePolygon_domain`, `alphaTargetRectangle_index_val`, `alphaTargetRectangle_bottom_vertex`, … |
| [`ArchRayIndex`](ArchRayIndex.lean) | Declarations: `rayIndex_telescope_of_left_horizontal`, `boundary_attached_arch_rayIndex` |
| [`AssociationReversal`](AssociationReversal.lean) | Declarations: `lowerSet_FKG_of_upperSet_FKG`, `upperSet_FKG_map_of_antitone` |
| [`BalancedBottomEnlargement`](BalancedBottomEnlargement.lean) | Declarations: `balanced_bottom_connection_enlarges_to_vertical` |
| [`BalancedCellBottomEscape`](BalancedCellBottomEscape.lean) | Declarations: `balanced_cells_eventually_far_bottom`, `balanced_cells_eventually_far_left_bottom` |
| [`BalancedCellBulkEscape`](BalancedCellBulkEscape.lean) | Declarations: `balanced_cells_eventually_far_top`, `balanced_cells_eventually_far_all_sides` |
| [`BalancedCellFiniteWitness`](BalancedCellFiniteWitness.lean) | Declarations: `translated_finite_set_subset_rectangle_of_anchor_margins`, `measure_finiteLocalUniquenessEvent_translate_ge`, `finiteLocalUniquenessEvent_connects_in_domain`, `balanced_cells_uniform_local_uniqueness` |
| [`BalancedCellInteriorWitness`](BalancedCellInteriorWitness.lean) | Declarations: `translated_finite_set_strict_rectangle_interior`, `balanced_cells_uniform_interior_local_uniqueness` |
| [`BalancedCellLeftBound`](BalancedCellLeftBound.lean) | Declarations: `balanced_cell_near_left_core_probability_le_four_arms_of_three_comparisons`, `balanced_cell_near_left_core_probability_le_four_arms` |
| [`BalancedCellLeftEscape`](BalancedCellLeftEscape.lean) | Declarations: `latticeTranslate_image_box_zero`, `measure_infiniteHit_latticeBox_translate`, `balanced_cells_eventually_far_left_of_positive_core`, `balanced_cells_eventually_far_left` |
| [`BalancedCellRightEscape`](BalancedCellRightEscape.lean) | Declarations: `balanced_cells_eventually_far_right` |
| [`BalancedCellTranspose`](BalancedCellTranspose.lean) | Declarations: `transposeLaw_rectangleSeedConnectionEvent`, `transposeLaw_rectangleSeedLeftProbability`, `transposeLaw_rectangleSeedRightProbability`, `transposeLaw_rectangleSeedBottomProbability`, … |
| [`BalancedSeedCell`](BalancedSeedCell.lean) | Declarations: `rectangleSeedLeftProbability`, `rectangleSeedRightProbability`, `rectangleSeedBottomProbability`, `rectangleSeedTopProbability`, … |
| [`BalancedSeedDominantBound`](BalancedSeedDominantBound.lean) | Declarations: `rectangleSeed_subset_rectangle`, `balanced_seed_dominant_complement_pow_four` |
| [`BalancedSeedDominantLimit`](BalancedSeedDominantLimit.lean) | Declarations: `balanced_seed_dominant_probability_eventually_gt` |
| [`BalancedSeedReflection`](BalancedSeedReflection.lean) | Declarations: `rectangleSeedReflectXAnchor`, `reflectionXLaw_rectangleSeedConnectionEvent`, `reflectionXLaw_rectangleSeedLeftProbability`, `reflectionXLaw_rectangleSeedRightProbability`, … |
| [`BandCrossingChain`](BandCrossingChain.lean) | Declarations: `kst_band_horizontal_chain_width` |
| [`BandCrossingGluing`](BandCrossingGluing.lean) | Declarations: `kst_band_walks_glue`, `kst_band_horizontal_chain` |
| [`BottomArchSeparation`](BottomArchSeparation.lean) | Declarations: `rayIndex_telescope_of_high_column_absent` |
| [`BottomSpan`](BottomSpan.lean) | Declarations: `band_interlaced_walks_intersect` |
| [`BottomSpanThrough`](BottomSpanThrough.lean) | Declarations: `exists_kst_maximal_bottom_span_through`, `kst_maximal_bottom_span_through_no_right_straddle`, `kst_maximal_bottom_span_through_no_left_straddle` |
| [`BoundaryExtension`](BoundaryExtension.lean) | Declarations: `left_boundary_extension`, `right_boundary_extension` |
| [`BoundaryWalkClipping`](BoundaryWalkClipping.lean) | Declarations: `walk_subwalk_between_sets` |
| [`BoundedOpenGeometry`](BoundedOpenGeometry.lean) | Declarations: `coordinate_le_on_closure_of_frontier`, `subset_open_of_preconnected_frontier_disjoint`, `coordinate_lt_on_open_of_frontier`, `complexOpenRectangle`, … |
| [`BoxSampledDualScreen`](BoxSampledDualScreen.lean) | Declarations: `latticeRectangle_neg_eq_box`, `boxRectangleGraphIso`, `boxRectangleGraphIso_val` |
| [`CentralConnectorEndpoints`](CentralConnectorEndpoints.lean) | Declarations: `unit_center_coordinates`, `central_clamp_coordinates`, `central_clamped_left_endpoint`, `central_clamped_right_endpoint` |
| [`CentralTargetDualPorts`](CentralTargetDualPorts.lean) | Declarations: `centralTargetRectangle_next_val`, `centralTargetRectangle_boundaryBond`, `int_half_between_iff`, `centralTargetRectangle_cell_center_iff`, … |
| [`CentralTargetDuality`](CentralTargetDuality.lean) | Declarations: `central_target_dual_exists` |
| [`CentralTargetRectangle`](CentralTargetRectangle.lean) | Declarations: `centralTargetRectanglePolygon`, `centralTargetRectanglePolygon_domain`, `centralTargetRectangle_index_val`, `centralTargetRectangle_bottom_vertex`, … |
| [`ClampedDualConnector`](ClampedDualConnector.lean) | Declarations: `clampedRectangleDualCurve`, `clampedRectangleDualCurve_mem`, `clamped_trace_dualCurve_disjoint`, `central_dual_ports_ne`, … |
| [`CommonCoreBoundaryBound`](CommonCoreBoundaryBound.lean) | Declarations: `infiniteHit_subset_rectangle_four_seed_union`, `infiniteHit_real_le_rectangle_four_seed_sum` |
| [`ConfinedWalkCylinders`](ConfinedWalkCylinders.lean) | Declarations: `walk_edge_lift_domain`, `kstPathOpen_congr_on_domain` |
| [`ContinuousBoundaryExtension`](ContinuousBoundaryExtension.lean) | Declarations: `pair_segment_parameter`, `pair_segment_box`, `continuous_left_boundary_extension`, `continuous_right_boundary_extension` |
| [`ContinuousThreeArc`](ContinuousThreeArc.lean) | Declarations: `segment_fixed_fst`, `continuous_three_arc_paths_intersect` |
| [`ContinuousVerticalWallBarrier`](ContinuousVerticalWallBarrier.lean) | Declarations: `continuous_vertical_wall_barrier` |
| [`ContinuousWallBarrier`](ContinuousWallBarrier.lean) | Declarations: `continuous_wall_barrier` |
| [`DRTActualHeightSelector`](DRTActualHeightSelector.lean) | Declarations: `verticalRectangle_antitone_height`, `verticalRectangle_zero_height_eq_univ`, `exists_actual_balanced_height_tendsto_atTop` |
| [`DRTCrossingContradiction`](DRTCrossingContradiction.lean) | Declarations: `balanced_crossing_max_eq`, `drt_crossing_contradiction_of_crossingLimits` |
| [`DRTCrossingMinimum`](DRTCrossingMinimum.lean) | Declarations: `drt_crossing_min_eventually_lt`, `drt_crossing_min_tendsto_zero` |
| [`DRTFixedEnlargementMaximum`](DRTFixedEnlargementMaximum.lean) | Declarations: `drt_fixed_enlargement_crossing_max_eventually_gt`, `drt_fixed_enlargement_crossing_max_tendsto_one` |
| [`DRTFixedSideDecay`](DRTFixedSideDecay.lean) | Declarations: `horizontalRectangle_fixed_height_probability_tendsto_zero`, `verticalRectangle_fixed_width_probability_tendsto_zero` |
| [`DRTHeightSelector`](DRTHeightSelector.lean) | Declarations: `exists_balanced_consecutive_height`, `exists_balanced_height_tendsto_atTop_of_fixedHeightLimits` |
| [`DRTHorizontalFixedWidth`](DRTHorizontalFixedWidth.lean) | Declarations: `horizontalRectangle_fixed_width_real_probability_tendsto_one` |
| [`DRTVerticalFixedHeight`](DRTVerticalFixedHeight.lean) | Declarations: `verticalRectangle_fixed_height_real_probability_tendsto_one`, `horizontalRectangle_fixed_height_real_probability_tendsto_zero`, `verticalRectangle_fixed_width_real_probability_tendsto_zero` |
| [`DisjointRayIndex`](DisjointRayIndex.lean) | Disjoint lattice supports avoid the dual interpretation of a lattice loop. The dual bond crossing a primal bond has the primal source among … |
| [`DobrushinDualProjection`](DobrushinDualProjection.lean) | Declarations: `domainClosedDualGraph`, `domain_localPair_dual_reachable`, `dobrushin_geometry_faceBase_of_interior`, `dobrushin_edge_dual_reachable_of_interior_geometry`, … |
| [`DobrushinExteriorExtraction`](DobrushinExteriorExtraction.lean) | Declarations: `domainClosedDualGraph_antitone`, `dobrushin_geometry_not_interior`, `dobrushin_exterior_dual_connection_of_classification` |
| [`DobrushinPrimalProjection`](DobrushinPrimalProjection.lean) | Actual primal connectivity beside the Dobrushin interface. |
| [`DualConfigurationTranslation`](DualConfigurationTranslation.lean) | Declarations: `latticeConfigurationBondState_translate`, `wholePlaneDualConfiguration_translate`, `wholePlaneDualLaw_translation_invariant` |
| [`DualLawAssociation`](DualLawAssociation.lean) | Declarations: `wholePlaneDualConfiguration_antitone`, `wholePlaneDualLaw_FKG` |
| [`DualPairCurve`](DualPairCurve.lean) | Declarations: `dualPairCurve`, `complex_segment_box`, `dualPairCurve_bounds`, `latticePairCurve_dualPairCurve_disjoint` |
| [`DualRoleExchange`](DualRoleExchange.lean) | Declarations: `wholePlaneDualConfiguration_twice`, `wholePlaneDualLaw_twice` |
| [`DualWalkCurves`](DualWalkCurves.lean) | Label-preserving dual walk interpolation. The interpolation and edge-label lemmas below are adapted from the private helpers in … |
| [`ExteriorBottomExtension`](ExteriorBottomExtension.lean) | Declarations: `vertical_walk_between`, `left_boundary_to_lower_line`, `right_boundary_to_lower_line` |
| [`FiniteClusterArmLimit`](FiniteClusterArmLimit.lean) | Declarations: `sampledGraphArmEvent`, `sampledGraphArmEvent_measurableSet`, `sampledGraphArmEvent_probability_tendsto_zero` |
| [`FiniteConnectionHull`](FiniteConnectionHull.lean) | Declarations: `exists_finite_connection_hull`, `exists_finite_local_uniqueness` |
| [`FourCyclePorts`](FourCyclePorts.lean) | Declarations: `fourCyclePort`, `fourCycle_ports_connected_of_adjacent`, `fourCyclePort_cyclic` |
| [`GridSignBalance`](GridSignBalance.lean) | Declarations: `grid_two_signs_balanced_cell` |
| [`HalfPlaneArchAvoidance`](HalfPlaneArchAvoidance.lean) | Declarations: `open_bond_dual_not_mem_walk`, `halfplane_open_edge_avoids_arch_closure` |
| [`HalfPlaneArchScreen`](HalfPlaneArchScreen.lean) | Declarations: `boundary_attached_dual_arch_finite_halfplane_cluster`, `boundary_attached_dual_arch_screens_unit_segment` |
| [`HalfPlaneArmLimit`](HalfPlaneArmLimit.lean) | Declarations: `halfPlane_arm_probability_tendsto_zero`, `halfPlane_arm_real_probability_tendsto_zero` |
| [`HalfPlaneBalancedExits`](HalfPlaneBalancedExits.lean) | Declarations: `halfPlaneExitEvent_opposite_translated_balancing` |
| [`HalfPlaneBoundaryFiniteness`](HalfPlaneBoundaryFiniteness.lean) | Declarations: `wholePlaneDualLaw_ae_iff`, `halfPlane_finite_unit_ae` |
| [`HalfPlaneClusterEvents`](HalfPlaneClusterEvents.lean) | Declarations: `sampledGraph_infinite_iff_escape`, `measurableSet_sampledGraph_infiniteAt`, `halfPlaneInfiniteAt`, `halfPlaneInfiniteAt_measurableSet`, … |
| [`HalfPlaneEvents`](HalfPlaneEvents.lean) | Declarations: `measurableSet_domain_open_reachable`, `halfPlaneBoundaryEvent`, `halfPlaneBoundaryEvent_measurableSet` |
| [`HalfPlaneExitArch`](HalfPlaneExitArch.lean) | Declarations: `opposite_halfplane_first_exits_give_arch`, `opposite_dual_first_exits_screen_unit_segment` |
| [`HalfPlaneExitBalance`](HalfPlaneExitBalance.lean) | Declarations: `halfPlaneExitEvent_adjacent_balancing` |
| [`HalfPlaneExitBoundary`](HalfPlaneExitBoundary.lean) | Declarations: `exterior_terminal_walk_has_boundary_connection` |
| [`HalfPlaneExitEvents`](HalfPlaneExitEvents.lean) | Declarations: `halfPlaneExitDomain`, `halfPlaneExitEvent`, `halfPlaneExitEvent_measurableSet`, `halfPlaneExitEvent_isUpperSet`, … |
| [`HalfPlaneExitFKG`](HalfPlaneExitFKG.lean) | Declarations: `halfPlaneExitEvent_of_original_walk`, `infiniteHit_opposite_subset_halfPlaneExit`, `halfPlaneExitEvent_ge_infiniteHit_product`, `halfPlaneExitEvent_ge_infiniteHit_square_of_translate` |
| [`HalfPlaneExitTargetLimits`](HalfPlaneExitTargetLimits.lean) | Declarations: `halfPlaneExitEvent_mono`, `halfPlaneExitEvent_lower_target_probability_tendsto`, `halfPlaneExitEvent_upper_target_probability_tendsto`, `halfPlaneExitEvent_lower_target_real_probability_tendsto`, … |
| [`HalfPlaneExitTranslation`](HalfPlaneExitTranslation.lean) | Declarations: `halfPlaneExitEvent_translate_vertical`, `halfPlaneExitEvent_vertical_preimage`, `measure_halfPlaneExitEvent_vertical_translate` |
| [`HalfPlaneExitUniformBound`](HalfPlaneExitUniformBound.lean) | Declarations: `halfPlaneExitEvent_translated_box_lower_bound` |
| [`HalfPlaneFKG`](HalfPlaneFKG.lean) | Declarations: `infiniteHit_translate_preimage`, `measure_infiniteHit_translate` |
| [`HalfPlaneFirstExit`](HalfPlaneFirstExit.lean) | Declarations: `open_connection_has_first_exterior_exit` |
| [`HalfPlaneLeftmostRoot`](HalfPlaneLeftmostRoot.lean) | Declarations: `halfPlane_infinite_has_translated_boundary_root` |
| [`HalfPlaneLocalProbability`](HalfPlaneLocalProbability.lean) | Declarations: `halfPlaneLocalUniquenessEvent_ge_finite_witness`, `halfPlaneLocalUniquenessEvent_probability_tendsto_one` |
| [`HalfPlaneLocalUniqueness`](HalfPlaneLocalUniqueness.lean) | Declarations: `halfPlaneLocalUniquenessEvent`, `halfPlane_singleton_boundary_reachable`, `halfPlaneLocalUniquenessEvent_measurableSet`, `finite_local_unique_subset_halfplane` |
| [`HalfPlaneNonpercolation`](HalfPlaneNonpercolation.lean) | Declarations: `halfPlane_no_infinite_cluster_ae` |
| [`HalfPlaneScreenAlmostSure`](HalfPlaneScreenAlmostSure.lean) | Declarations: `halfPlane_finite_unit_probability_one_of_dualLaw`, `halfPlane_finite_unit_ae_of_dualLaw` |
| [`HalfPlaneScreenBulkLimit`](HalfPlaneScreenBulkLimit.lean) | Declarations: `halfPlane_screen_lower_bound_of_dualLaw` |
| [`HalfPlaneScreenProbability`](HalfPlaneScreenProbability.lean) | Declarations: `halfPlane_screen_probability_lower_bound_of_dualLaw` |
| [`HorizontalWalks`](HorizontalWalks.lean) | Declarations: `horizontal_interval_walk`, `horizontal_walk_between` |
| [`InfiniteClusterIsometry`](InfiniteClusterIsometry.lean) | Declarations: `rcOpenConfigurationIso`, `rcOpenConfigurationIso_apply`, `graphIso_infinite_component_iff`, `infiniteAt_configurationIso_iff`, … |
| [`InfiniteHitProbability`](InfiniteHitProbability.lean) | Declarations: `infiniteHit_box_probability_tendsto_one` |
| [`IntegerCoreClamp`](IntegerCoreClamp.lean) | Declarations: `integerIntervalClamp`, `integerIntervalClamp_mem`, `integerIntervalClamp_fixed`, `integerIntervalClamp_consecutive` |
| [`InterlacedPaths`](InterlacedPaths.lean) | Interlaced paths on a half-plane boundary must share an original vertex. |
| [`IsometricEvents`](IsometricEvents.lean) | Declarations: `latticeConfigurationIsoHomeomorph_trans_apply`, `isCylinder_iso_preimage`, `isUpperSet_iso_preimage`, `latticeBox_iso_trans`, … |
| [`IsometricGluing`](IsometricGluing.lean) | Declarations: `isometric_gluing_pad`, `isometric_gluing_iso_preimage` |
| [`KSTArmCoreBridge`](KSTArmCoreBridge.lean) | Declarations: `alphaCoreBridge`, `alpha_dual_ports_subset_core_bridge`, `kstArm_compl_subset_dual_core_bridge` |
| [`KSTArmDualCertificate`](KSTArmDualCertificate.lean) | Declarations: `alphaCoreLongRectangle`, `alpha_core_dual_long_crossing_excludes_short`, `kst_arm_dual_cover_certificate` |
| [`KSTArmDuality`](KSTArmDuality.lean) | Declarations: `alphaDualPortEvent`, `alphaDualPortEvent_dual_iff`, `kstArm_compl_eq_dualPortEvent` |
| [`KSTArmRectangleBridge`](KSTArmRectangleBridge.lean) | Declarations: `kstArm_iff_alpha_target_primal` |
| [`KSTArmTranslation`](KSTArmTranslation.lean) | Declarations: `kstPathOpen_translate_from_preimage`, `kst_translated_arm_witness`, `kst_translated_arm_mpath` |
| [`KSTAspectFactors`](KSTAspectFactors.lean) | Declarations: `kstHorizontalFactorIso`, `kstVerticalFactorIso`, `kst_horizontal_factor_witness`, `kst_vertical_factor_witness` |
| [`KSTAspectRatio`](KSTAspectRatio.lean) | Declarations: `kstAspectFactor`, `kst_aspect_ratio_gluing` |
| [`KSTBetaBottomChain`](KSTBetaBottomChain.lean) | Declarations: `kst_beta_bottom_grid_covers`, `kst_96_beta_bottom_connections_glue` |
| [`KSTBetaBottomEvent`](KSTBetaBottomEvent.lean) | Declarations: `kstBetaBottomArc`, `kstBetaBottomArcFactor`, `kst_beta_bottom_arc_long_gluing` |
| [`KSTBridgeBottomEvent`](KSTBridgeBottomEvent.lean) | Declarations: `kstReflectionXIso`, `kstBridgeToBottom`, `kstBridgeToBottom_isUpperSet`, `kstBridgeToBottom_isCylinder`, … |
| [`KSTBridgeBottomGluing`](KSTBridgeBottomGluing.lean) | Declarations: `kst_bridge_to_bottom_long_gluing` |
| [`KSTBridgeCoverGluing`](KSTBridgeCoverGluing.lean) | Declarations: `kst_bridge_cover_piece_gluing` |
| [`KSTBridgeFiniteCover`](KSTBridgeFiniteCover.lean) | Declarations: `kst_bridge_finite_cover_multiple12`, `kst_bridge_finite_cover` |
| [`KSTBridgeFiveCover`](KSTBridgeFiveCover.lean) | Declarations: `kstBridgeCoverPiece`, `kstBridgeCoverPiece_isCylinder`, `kstBridgeCoverPiece_isUpperSet`, `kst_bridge_five_cover` |
| [`KSTBridgeIntersection`](KSTBridgeIntersection.lean) | Declarations: `kst_mpath_bridge_intersect` |
| [`KSTBridgeSymmetries`](KSTBridgeSymmetries.lean) | Declarations: `kstReflectionYIso`, `kstReflectionBothIso`, `latticeTransposeIso_box`, `kstReflectionYIso_box`, … |
| [`KSTCascadeConnections`](KSTCascadeConnections.lean) | Declarations: `kst_wall_contact_connection`, `kst_left_connection_translated_bridge`, `kst_right_connection_translated_bridge` |
| [`KSTCascadeInclusion`](KSTCascadeInclusion.lean) | Declarations: `kst_corridor_bridge_inclusion` |
| [`KSTClosing`](KSTClosing.lean) | Declarations: `takeUntil_subwalk`, `kst_bridge_of_band_crossing`, `kst_quasi_closing` |
| [`KSTCorridor`](KSTCorridor.lean) | Declarations: `latticePairCurve_of_pathIn`, `kst_corridor` |
| [`KSTCorridorAttachment`](KSTCorridorAttachment.lean) | Declarations: `isSubwalk_reverse_walk`, `kst_contained_mpath_reverse`, `kst_attached_of_corridor_cases` |
| [`KSTCorridorTranspose`](KSTCorridorTranspose.lean) | Declarations: `latticeTransposeIso`, `transposeWalk`, `transposeWalk_twice`, `mem_transposeWalk_support` |
| [`KSTCurveIntersection`](KSTCurveIntersection.lean) | Declarations: `complexCoordinates`, `continuous_complexCoordinates`, `latticePairCurve`, `latticePairCurve_bounds`, … |
| [`KSTDownwardAttachment`](KSTDownwardAttachment.lean) | Declarations: `kst_mpath_attached_of_downward_funnel` |
| [`KSTDownwardFunnel`](KSTDownwardFunnel.lean) | Declarations: `kst_funnel_extract_downward` |
| [`KSTFunnel`](KSTFunnel.lean) | Declarations: `kst_funnel_extract` |
| [`KSTFunnelAttachment`](KSTFunnelAttachment.lean) | Declarations: `kst_mpath_integral_pathIn`, `kst_mpath_attached_of_funnel` |
| [`KSTLowerArmConstruction`](KSTLowerArmConstruction.lean) | Declarations: `kst_three_arms_bottom_attachment` |
| [`KSTPartition`](KSTPartition.lean) | The deterministic partition in the KST cascade argument, with original connectors transported to contiguous smaller paths in either … |
| [`KSTQuasiConstruction`](KSTQuasiConstruction.lean) | Declarations: `kst_quasi_construction_multiple192`, `kst_quasi_construction` |
| [`KSTQuasiFromWalls`](KSTQuasiFromWalls.lean) | Declarations: `kst_quasi_of_vertical_walls` |
| [`KSTRectangleFactors`](KSTRectangleFactors.lean) | Declarations: `kst_horizontal_rectangle_factor_witness`, `kst_vertical_rectangle_factor_witness` |
| [`KSTRectangleRealization`](KSTRectangleRealization.lean) | Declarations: `kstPathOpen_map_iso_inverse`, `rectangle_connected_of_kst_open_walk`, `horizontalRectangle_of_kst_open_walk` |
| [`KSTRectangleWitness`](KSTRectangleWitness.lean) | Declarations: `kstPathOpen_of_rectangle_walk`, `kst_horizontal_crossing_witness` |
| [`KSTSideBridge`](KSTSideBridge.lean) | Declarations: `kstPathOpen_map_iso`, `kstPathOpen_translate`, `kst_bridge_of_walk_bounds`, `kst_bridge_of_left_side_to_target`, … |
| [`KSTSkinnyGluing`](KSTSkinnyGluing.lean) | Declarations: `kstSkinnyFactor`, `kst_skinny_rectangle_gluing` |
| [`KSTUpperArmConstruction`](KSTUpperArmConstruction.lean) | Declarations: `kst_three_arms_top_attachment` |
| [`KSTVerticalCorridor`](KSTVerticalCorridor.lean) | Declarations: `kst_corridor_vertical_attachments` |
| [`LatticeEdges`](LatticeEdges.lean) | Euclidean intersections of square-lattice unit edges. An embedded lattice vertex on a nearest-neighbor edge is an endpoint. |
| [`LocalUniquenessEvents`](LocalUniquenessEvents.lean) | Declarations: `finiteLocalUniquenessEvent`, `measurableSet_induced_open_reachable`, `measurableSet_reaches_outside`, `finiteLocalUniquenessEvent_measurableSet`, … |
| [`LocalUniquenessExhaustion`](LocalUniquenessExhaustion.lean) | Declarations: `finiteLocalUniquenessEvent_mono`, `unique_cluster_eventually_local_unique`, `finiteLocalUniquenessEvent_box_monotone` |
| [`LocalUniquenessProbability`](LocalUniquenessProbability.lean) | Declarations: `local_uniqueness_probability_tendsto_one`, `local_uniqueness_real_probability_tendsto_one` |
| [`LocalUniquenessTranslation`](LocalUniquenessTranslation.lean) | Declarations: `finiteLocalUniquenessEvent_translate` |
| [`LowerBoundaryArcExtension`](LowerBoundaryArcExtension.lean) | Declarations: `segment_parameter`, `lower_left_boundary_extension`, `lower_boundary_arc_extension` |
| [`MeasurableReachability`](MeasurableReachability.lean) | Declarations: `sampledGraphChain`, `sampledGraph_reachable_iff_chain`, `measurableSet_sampledGraph_reachable` |
| [`Noncoexistence`](Noncoexistence.lean) | Declarations: `planar_noncoexistence` |
| [`OccurrenceDualHalfSegments`](OccurrenceDualHalfSegments.lean) | Declarations: `bond_midpoint_eq_dual_midpoint` |
| [`OpenArchRayIndex`](OpenArchRayIndex.lean) | Declarations: `open_arch_rayIndex_eq_of_avoiding_adj`, `rayIndex_telescope_of_low_column_absent` |
| [`OpenGraphMonotonicity`](OpenGraphMonotonicity.lean) | Declarations: `rcOpenGraph_monotone`, `infiniteAt_isUpperSet`, `infiniteHit`, `infiniteHit_isUpperSet`, … |
| [`OpenWalkEmbedding`](OpenWalkEmbedding.lean) | Declarations: `rcOpenGraph_le_squareLattice`, `kstPathOpen_of_rcOpen_walk` |
| [`OpposedBottomPaths`](OpposedBottomPaths.lean) | Declarations: `opposed_boundary_bottom_walks_intersect` |
| [`OrdinaryRectangleDuality`](OrdinaryRectangleDuality.lean) | Declarations: `kst_vertical_crossing_witness`, `horizontalRectangle_compl_eq_dual_vertical`, `verticalRectangle_compl_eq_dual_horizontal` |
| [`OrdinaryRectangleDualityLaw`](OrdinaryRectangleDualityLaw.lean) | Declarations: `dualLaw_verticalRectangle_eq_one_sub_horizontal`, `dualLaw_horizontalRectangle_eq_one_sub_vertical` |
| [`PolygonFourArcExistence`](PolygonFourArcExistence.lean) | Declarations: `polygonBoundaryVertices`, `polygonExteriorFaces`, `retainedPort_exterior_label`, `boundaryCapVertexIndex_val_cases`, … |
| [`RectangleBoundaryArcExclusion`](RectangleBoundaryArcExclusion.lean) | Declarations: `rectangle_boundary_arc_dual_excludes_primal` |
| [`RectangleBoundaryArcIntersection`](RectangleBoundaryArcIntersection.lean) | Declarations: `rectangle_boundary_arc_paths_intersect` |
| [`RectangleBoundaryExit`](RectangleBoundaryExit.lean) | Declarations: `walk_reaches_inner_boundary`, `latticeRectangle_exit_on_side`, `infiniteHit_subset_rectangle_side_union` |
| [`RectangleClamp`](RectangleClamp.lean) | Declarations: `unitLatticeMesh`, `rectangleClamp`, `continuous_rectangleClamp`, `rectangleClamp_mem`, … |
| [`RectangleConnectionEvents`](RectangleConnectionEvents.lean) | Declarations: `rectangleConnectionEvent`, `rectangleConnectionEvent_isCylinder`, `rectangleConnectionEvent_measurableSet`, `rectangleConnectionEvent_isUpperSet`, … |
| [`RectangleConnectionImages`](RectangleConnectionImages.lean) | Declarations: `latticeTranslate_injective`, `measure_rectangleConnectionEvent_translate_image`, `rectangleConnectionEvent_bottom_top` |
| [`RectangleConnectionReflection`](RectangleConnectionReflection.lean) | Declarations: `rectangleOpenReflectionXHom`, `rectangleReflectionConfiguration_twice`, `rectangleConnectionEvent_reflectionX_iff`, `reflectionXLaw_rectangleConnectionEvent` |
| [`RectangleConnectionTransport`](RectangleConnectionTransport.lean) | Declarations: `rectangleConnectionEvent_transpose_iff`, `rectangleConnectionEvent_transpose_preimage`, `transposeLaw_rectangleConnectionEvent`, `rectangleConnectionEvent_translate_iff`, … |
| [`RectangleCoreClamp`](RectangleCoreClamp.lean) | Declarations: `rectangleCoreClamp`, `rectangleCoreClamp_bounds`, `rectangleCoreClamp_face_pair` |
| [`RectangleCurveExclusion`](RectangleCurveExclusion.lean) | Declarations: `rectangle_open_walk_trace_subset`, `clamped_dualCurve_disjoint_of_trace_subset` |
| [`RectangleDualBoundaryArcs`](RectangleDualBoundaryArcs.lean) | Declarations: `rectangleLowerDualArc`, `rectangleUpperDualArc`, `rectangle_lower_upper_dual_arcs_disjoint`, `rectangle_lower_dual_arc_clamped`, … |
| [`RectangleDualCoreGeometry`](RectangleDualCoreGeometry.lean) | Declarations: `rectangle_primal_bond_endpoints_mem`, `rectangleDualCoreClamp_step`, `rectangleCoreClamp_mem_interior` |
| [`RectangleDualCoreReachability`](RectangleDualCoreReachability.lean) | Declarations: `rectangleDualRestrictionToInfiniteOpenHom`, `rectangle_dual_reachable_core`, `rectangleDualInterior_eq_rectangle` |
| [`RectangleDualGraphBridge`](RectangleDualGraphBridge.lean) | Declarations: `pdBondOfFKC`, `pdBondOfFKC_toSym2`, `pdBondOfFKC_faceBase`, `pd_rectanglePrimalEdgeBond_toSym2`, … |
| [`RectangleEventTranslation`](RectangleEventTranslation.lean) | Declarations: `latticeRectangle_mem_translate_iff`, `rectangleOpenTranslationHom`, `verticalRectangle_translate`, `horizontalRectangle_translate`, … |
| [`RectangleExit`](RectangleExit.lean) | Declarations: `walk_prefix_to_three_sides` |
| [`RectangleGluingProbability`](RectangleGluingProbability.lean) | Declarations: `probability_inter_two_lower`, `probability_inter_three_lower`, `rectangle_connection_transfer_probability_lower`, `rectangle_connection_glue_probability_lower` |
| [`RectangleGraphBridge`](RectangleGraphBridge.lean) | Declarations: `rectangleDomainGraphIso`, `rectangleDomainGraphIso_val`, `domainGraphIsoOfEq`, `domainGraphIsoOfEq_val`, … |
| [`RectangleGridSignBalance`](RectangleGridSignBalance.lean) | Declarations: `rectangle_grid_two_signs_balanced_cell` |
| [`RectangleHalfPlaneArmBound`](RectangleHalfPlaneArmBound.lean) | Declarations: `halfPlaneVerticalOpenTranslationHom`, `rectangleConnectionEvent_subset_translated_halfPlaneArm`, `rectangleConnectionEvent_le_halfPlaneArm`, `rectangleConnectionEvent_real_le_halfPlaneArm` |
| [`RectangleHalfPlaneArms`](RectangleHalfPlaneArms.lean) | Declarations: `halfPlaneRectangleSeeds`, `mem_halfPlaneRectangleSeeds`, `rectangleToHalfPlaneOpenHom`, `horizontalRectangle_subset_halfPlaneArm`, … |
| [`RectangleIntersection`](RectangleIntersection.lean) | Opposite-side lattice walks in a rectangle share a vertex of their original supports. |
| [`RectangleLocalGluing`](RectangleLocalGluing.lean) | Declarations: `rectangleConnectionEvent_transfer_of_finiteLocalUniqueness`, `rectangleConnectionEvent_glue_of_finiteLocalUniqueness` |
| [`RectanglePolygon`](RectanglePolygon.lean) | Declarations: `rectanglePolygonVertex`, `rectangleLatticePolygon`, `mem_rectanglePolygon_vertices_iff` |
| [`RectanglePolygonDomain`](RectanglePolygonDomain.lean) | Declarations: `rectangle_boundary_adj_common_side`, `rectangle_boundary_segment_subset`, `rectangleLatticePolygon_carrier_subset`, `rectangleLatticePolygon_domain`, … |
| [`RectangleProbabilityBalance`](RectangleProbabilityBalance.lean) | Declarations: `rectangle_probability_profiles_balanced_cell` |
| [`RectangleSampledClosedDual`](RectangleSampledClosedDual.lean) | Declarations: `rectangleSampledClosedDualGraph`, `rectangleSampledClosedDualGraph_adj_mem`, `rectangleSampledClosedDualGraph_adj_finite`, `rectangleSampledClosedDualGraph_walk_finite`, … |
| [`RectangleSeedBalance`](RectangleSeedBalance.lean) | Declarations: `rectangleSeedConnectionEvent`, `rectangle_seed_connection_balanced_cell` |
| [`RectangleTrace`](RectangleTrace.lean) | Declarations: `rectangleTraceConfiguration`, `mem_rectangleTraceConfiguration`, `rectangleTraceOpenHom`, `rectangle_trace_walk_edges_subset`, … |
| [`RectangleTranspose`](RectangleTranspose.lean) | Declarations: `rectangleOpenTransposeHom`, `verticalRectangle_transpose`, `horizontalRectangle_transpose`, `horizontalRectangle_transpose_preimage`, … |
| [`ReflectionConfiguration`](ReflectionConfiguration.lean) | Declarations: `reflectionXLatticeBond`, `latticeConfigurationBondState_reflectionX`, `wholePlaneDualConfiguration_reflectionX`, `reflectionXConfiguration_twice`, … |
| [`ReflectionLaw`](ReflectionLaw.lean) | Declarations: `latticeConfigurationIso_translation`, `atMostOneInfiniteCluster_translate_iff`, `infiniteClusterEvent_translate_iff`, `reflectionXLaw_translation_invariant`, … |
| [`RotatedPolygon`](RotatedPolygon.lean) | Declarations: `rotateLatticePolygon`, `rotateLatticePolygon_carrier`, `rotateLatticePolygon_domain` |
| [`SampledBoundaryStarScreen`](SampledBoundaryStarScreen.lean) | Declarations: `rectangle_closed_star_has_both_axes`, `rectangle_closed_boundary_star_ports_connected`, `rectangle_disconnected_of_closed_boundary_star_and_dual_arms` |
| [`SampledClosedRowsScreen`](SampledClosedRowsScreen.lean) | Declarations: `rectangleSampledBondClosed`, `sampled_closed_horizontal_row_dual_adj`, `sampled_closed_vertical_column_dual_adj`, `sampled_closed_rows_nat`, … |
| [`SampledDualScreenSeparation`](SampledDualScreenSeparation.lean) | Declarations: `rectangle_dual_arc_mem_expanded`, `rectangle_sampled_dual_screen_excludes_primal`, `rectangle_disconnected_of_sampled_dual_arms_and_connector` |
| [`SampledStarActualPorts`](SampledStarActualPorts.lean) | Declarations: `rectangle_sampled_star_actual_ports_connected` |
| [`SampledStarPortRealization`](SampledStarPortRealization.lean) | Declarations: `latticeBond_incident_cases`, `rectangle_closed_star_bond_face_is_actual_port`, `rectangle_closed_star_incident_bond_faces_connected` |
| [`SeedShiftMarkedBox`](SeedShiftMarkedBox.lean) | Declarations: `seed_vertical_shift_subset_translated_marked_box`, `seed_subset_translated_marked_box`, `balanced_cell_core_subset_top_seed` |
| [`SeedSquareCore`](SeedSquareCore.lean) | Declarations: `latticeBox_core_subset_nearby_seed`, `latticeBox_core_subset_seed` |
| [`SeedWiring`](SeedWiring.lean) | Declarations: `seed_connection_union_iff`, `forwardArc_seed_connection_union_iff`, `dobrushin_walk_original_seed_connection` |
| [`SlitArchIndexInvariance`](SlitArchIndexInvariance.lean) | Declarations: `pdBondOfFKC_dual_toSym2`, `slit_arch_index_eq_of_residual_adj`, `slit_arch_index_eq_of_residual_walk` |
| [`SlitArchSampledGeometry`](SlitArchSampledGeometry.lean) | Declarations: `slitScreenDualToIndexLattice`, `slitScreenDualToIndexLattice_walk_edges`, `slitScreenDualToIndexLattice_walk_support`, `slitScreen_arch_column_bounds`, … |
| [`SlitScreenCrosscut`](SlitScreenCrosscut.lean) | Declarations: `slitScreen_crossedDualWalk_separatesCapFromWiredArc` |
| [`SlitScreenSeparatingArch`](SlitScreenSeparatingArch.lean) | Declarations: `generalCEvent_exists_separating_arch` |
| [`SubpathExtraction`](SubpathExtraction.lean) | Contiguous extraction from the given walk, without loop erasure or rerouting. |
| [`ThreeArcIntersection`](ThreeArcIntersection.lean) | Declarations: `rectangle_three_arc_paths_intersect` |
| [`TraceChronology`](TraceChronology.lean) | Declarations: `path_trace_iso_vertex`, `path_trace_rank_step`, `path_trace_rank_endpoints`, `isSubwalk_map_hom`, … |
| [`TransposeConfiguration`](TransposeConfiguration.lean) | Declarations: `transposeLatticeBond`, `latticeConfigurationBondState_transpose`, `wholePlaneDualConfiguration_transpose`, `transposeConfiguration_twice`, … |
| [`TransposeLaw`](TransposeLaw.lean) | Declarations: `configurationIsoLaw_ae_iff`, `transposeLaw_translation_invariant`, `transposeLaw_FKG`, `configurationIsoLaw_unique`, … |
| [`UniqueClusterLocalization`](UniqueClusterLocalization.lean) | Declarations: `unique_cluster_has_finite_local_witness` |
| [`UpperBoundaryArcExtension`](UpperBoundaryArcExtension.lean) | Declarations: `upper_boundary_arc_extension` |
| [`VerticalShiftGluing`](VerticalShiftGluing.lean) | Declarations: `vertical_shift_gluing_probability_lower` |
| [`WalkIntersection`](WalkIntersection.lean) | Declarations: `latticePoint_in_walkSegment_endpoint_support`, `walkSegments_point_intersection_common_support`, `latticeWalkPaths_intersection_common_support` |
| [`WholePlaneRectangleExclusion`](WholePlaneRectangleExclusion.lean) | Declarations: `wholePlane_rectangle_crossings_exclusive` |
| [`WholePlaneWalkExclusion`](WholePlaneWalkExclusion.lean) | Declarations: `wholePlane_open_dual_curves_disjoint` |
