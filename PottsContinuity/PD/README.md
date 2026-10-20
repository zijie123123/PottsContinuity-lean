# `PottsContinuity/PD/`

Finite and infinite-volume FK measures, FKG and comparison inequalities, finite energy and planar duality on rectangles, adapted from the PottsDiscontinuity formalization; 26 of the 44 modules of `RCInfinite/` (Burton–Keane uniqueness) come from the development version of PottsDiscontinuity, not from its public repository.

190 modules, 25,597 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`CorrLength/ConnectionEvents`](CorrLength/ConnectionEvents.lean) | Finite witnesses for infinite-lattice connection events. Connection is expressed as the existence of a finite set of open edges that … |
| [`CorrLength/CorrelationRate`](CorrLength/CorrelationRate.lean) | Existence of the correlation-length rate. The finite-distance connection probabilities are positive and supermultiplicative. |
| [`CorrLength/Positivity`](CorrLength/Positivity.lean) | Positive probability of finite-distance connection. Every pair of square-lattice vertices has a deterministic finite path. |
| [`CorrLength/RotatedLattice`](CorrLength/RotatedLattice.lean) | The rotated lattice and its square-lattice coordinates. The carrier `rotatedVertex` is the even-coordinate-sum sublattice of `ℤ²`. |
| [`CorrLength/SubadditiveRate`](CorrLength/SubadditiveRate.lean) | Fekete's lemma for connection probabilities. This module isolates the analytic step used once the finite-distance connection probabilities … |
| [`Defs/Box`](Defs/Box.lean) | `box` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted … |
| [`Defs/DiagonalSite`](Defs/DiagonalSite.lean) | `diagonalSite` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused here by … |
| [`Defs/IsPottsInfiniteVolumeLimit`](Defs/IsPottsInfiniteVolumeLimit.lean) | `IsPottsInfiniteVolumeLimit` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is … |
| [`Defs/IsRCInfiniteVolumeLimit`](Defs/IsRCInfiniteVolumeLimit.lean) | `IsRCInfiniteVolumeLimit` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused … |
| [`Defs/IsTranslationErgodic`](Defs/IsTranslationErgodic.lean) | `IsTranslationErgodic` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused … |
| [`Defs/PottsHamiltonian`](Defs/PottsHamiltonian.lean) | `pottsHamiltonian` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused here … |
| [`Defs/PottsProb`](Defs/PottsProb.lean) | `pottsProb` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused here by the … |
| [`Defs/RCCriticalParameter`](Defs/RCCriticalParameter.lean) | `rcCriticalParameter` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused … |
| [`Defs/RCFreeClusterCount`](Defs/RCFreeClusterCount.lean) | `rcFreeClusterCount` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused here … |
| [`Defs/RCInfiniteOpenGraph`](Defs/RCInfiniteOpenGraph.lean) | `rcInfiniteOpenGraph` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused … |
| [`Defs/RCOpenGraph`](Defs/RCOpenGraph.lean) | `rcOpenGraph` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused here by the … |
| [`Defs/RCProb`](Defs/RCProb.lean) | `rcProb` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused here by the … |
| [`Defs/RCWeight`](Defs/RCWeight.lean) | `rcWeight` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused here by the … |
| [`Defs/RCWiredClusterCount`](Defs/RCWiredClusterCount.lean) | `rcWiredClusterCount` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused … |
| [`Defs/SquareLattice`](Defs/SquareLattice.lean) | `squareLattice` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused here by … |
| [`Defs/VertexBoundary`](Defs/VertexBoundary.lean) | `vertexBoundary` from the PottsDiscontinuity formalization. A definition of the formalization of arXiv:1611.09877v2 that is reused here by … |
| [`Duality/BondStates`](Duality/BondStates.lean) | Declarations: `latticeBondEdge`, `latticeConfigurationBondState`, `latticeConfigurationBondState_eq`, `wholePlaneOpenPrimalGraph`, … |
| [`Duality/BoxDihedral`](Duality/BoxDihedral.lean) | Declarations: `latticeQuarterTurn`, `latticeQuarterTurnInv`, `latticeReflection`, `latticeQuarterTurnInv_quarterTurn`, … |
| [`Duality/CircuitEnclosure`](Duality/CircuitEnclosure.lean) | Discrete enclosure of the marked vertex by a genuine closed dual simple circuit. |
| [`Duality/ConnectionEvents`](Duality/ConnectionEvents.lean) | Finite actual-path witnesses for whole-plane connectivity. |
| [`Duality/ConnectionSymmetry`](Duality/ConnectionSymmetry.lean) | Isometry and translation covariance of the actual free two-point function. |
| [`Duality/CrossingDuality`](Duality/CrossingDuality.lean) | Declarations: `rectangleDualBottomTopCrossingEvent`, `rectangleHorizontalNoncrossing_subset_dualBottomTopCrossing_preimage`, `rectangleHorizontalComplement_eq_dualBottomTop_preimage`, `rectangle_crossing_duality` |
| [`Duality/Decay`](Duality/Decay.lean) | Exponential two-point decay excludes an infinite origin cluster. The hypothesis below uses the integer lattice's ℓ¹ distance, explicitly … |
| [`Duality/DiagonalComparison`](Duality/DiagonalComparison.lean) | FKG and the actual free-limit symmetries compare every direction with the exact frozen diagonal sequence. |
| [`Duality/DiagonalRate`](Duality/DiagonalRate.lean) | A positive logarithmic rate gives a diagonal exponential bound. The index here is exactly the frozen index: `diagonalSite n = … |
| [`Duality/DualConfigurationBridge`](Duality/DualConfigurationBridge.lean) | Edge-by-edge bridge between finite complementary duality and the actual whole-plane configuration homeomorphism. |
| [`Duality/DualCylinderLaw`](Duality/DualCylinderLaw.lean) | Exact duality on cylinders supported on true finite dual edges. |
| [`Duality/FiniteClusterBoundary`](Duality/FiniteClusterBoundary.lean) | Actual finite-cluster dual boundary and simple cycles. |
| [`Duality/FiniteDuality`](Duality/FiniteDuality.lean) | Declarations: `partition_mul_left`, `pmf_map_equiv_of_common_factor`, `rectanglePrimalDualConfigurationEquiv`, `rectanglePrimalDualConfigurationEquiv_apply`, … |
| [`Duality/FiniteEvenEdgeCycle`](Duality/FiniteEvenEdgeCycle.lean) | Declarations: `edge_mem_some_isCycle_of_even_degree` |
| [`Duality/FiniteGraphBoundaryParity`](Duality/FiniteGraphBoundaryParity.lean) | Declarations: `exists_reachable_between_of_odd_degree_sum` |
| [`Duality/FiniteSupportEvenEdgeCycle`](Duality/FiniteSupportEvenEdgeCycle.lean) | Declarations: `edge_mem_some_isCycle_of_even_degree_of_finite_edgeSet` |
| [`Duality/FreeAssociation`](Duality/FreeAssociation.lean) | Positive association for actual, unbounded free connectivity events. |
| [`Duality/FreeBoxDihedral`](Duality/FreeBoxDihedral.lean) | Declarations: `freeBoxLimit_latticeIso_invariant` |
| [`Duality/InfiniteDuality`](Duality/InfiniteDuality.lean) | Infinite-volume free/wired duality for the actual frozen box limits. |
| [`Duality/LatticeCellBoundary`](Duality/LatticeCellBoundary.lean) | Declarations: `mem_cellBoundaryBonds_faceBase`, `latticeCellBoundaryBonds`, `mem_latticeCellBoundaryBonds`, `latticeCellBoundaryBonds_finite`, … |
| [`Duality/LatticeCellBoundaryFiniteEdges`](Duality/LatticeCellBoundaryFiniteEdges.lean) | Declarations: `latticeCellBoundaryGraph_edgeSet_eq_image`, `latticeCellBoundaryGraph_edgeSet_finite` |
| [`Duality/LatticeCellBoundaryParity`](Duality/LatticeCellBoundaryParity.lean) | Declarations: `boundaryAdj_right`, `boundaryAdj_up`, `boundaryAdj_left`, `boundaryAdj_down`, … |
| [`Duality/LatticeEmbedding`](Duality/LatticeEmbedding.lean) | The positive-mesh square lattice in the complex plane. The vertex `(x,y)` is embedded as `δ*x + I*δ*y` for a strictly positive real mesh … |
| [`Duality/LatticePorts`](Duality/LatticePorts.lean) | Actual square-lattice bonds and medial ports. A bond is a horizontal or vertical unit lattice segment, normalized by its left or lower … |
| [`Duality/LatticeWalkInterpolation`](Duality/LatticeWalkInterpolation.lean) | Declarations: `latticeWalkPath`, `latticeWalkPath_range_subset_segments` |
| [`Duality/NormalizedPotentialSpace`](Duality/NormalizedPotentialSpace.lean) | Declarations: `componentPotentialEvaluation`, `normalizedComponentPotentials`, `componentPotentialEvaluation_surjective`, `componentPotentialEvaluation_range_eq_top`, … |
| [`Duality/Parameters`](Duality/Parameters.lean) | Dual edge parameter. This module proves the algebra of planar FK duality, including the fixed point. |
| [`Duality/PrimalDualSegments`](Duality/PrimalDualSegments.lean) | Declarations: `LatticeBond.midpoint_mem_segment`, `dualFaceCenter`, `primalBondSegment`, `dualBondSegment`, … |
| [`Duality/RayIndex`](Duality/RayIndex.lean) | Signed intersections with the horizontal ray from a primal vertex. |
| [`Duality/RayIndexSeparation`](Duality/RayIndexSeparation.lean) | Finiteness of the nonzero-index region and the jump across a simple circuit. |
| [`Duality/ReachabilityLabels`](Duality/ReachabilityLabels.lean) | Declarations: `actualReachabilityLabel`, `actualReachabilityLabel_eq_true_iff`, `actualReachabilityLabel_eq_true_of_mem`, `actualReachabilityLabel_eq_of_actualConnected`, … |
| [`Duality/Rectangle`](Duality/Rectangle.lean) | Declarations: `latticeRectangle`, `mem_latticeRectangle`, `card_latticeRectangle`, `RectangleVertex`, … |
| [`Duality/RectangleCrossingExclusion`](Duality/RectangleCrossingExclusion.lean) | Declarations: `rectangleComplementDualVerticalCrossingEvent`, `exclusionMesh`, `exclusionOffset`, `rectangleDualOpenGraphToSquare`, … |
| [`Duality/RectangleCurl`](Duality/RectangleCurl.lean) | Declarations: `RectangleExteriorPotential`, `rectangleExtendedPotential`, `rectangleExtendedPotential_of_mem`, `rectangleExtendedPotential_of_not_mem`, … |
| [`Duality/RectangleCurlLinearEquiv`](Duality/RectangleCurlLinearEquiv.lean) | Declarations: `rectangleExteriorPotentialSubmodule`, `rectanglePotentialAsExterior`, `rectanglePrimalFlowDivergence_add`, `rectanglePrimalFlowDivergence_smul`, … |
| [`Duality/RectangleDualAmbient`](Duality/RectangleDualAmbient.lean) | Declarations: `rectangleDualAmbientGraph`, `rectangleDualAmbientGraph_adj_iff`, `primalBondOfDual_endpoints_mem_of_interior_endpoint`, `rectangleDualAmbient_adj_actual_of_left_interior`, … |
| [`Duality/RectangleDualAmbientMarginal`](Duality/RectangleDualAmbientMarginal.lean) | Declarations: `rectangleDualAmbient_law_restrict_to_dual` |
| [`Duality/RectangleDualBoundaryParity`](Duality/RectangleDualBoundaryParity.lean) | Declarations: `rectangleDualBottomPortVertex`, `rectangleDualTopPortVertex`, `rectangleDualBottomPorts`, `rectangleDualTopPorts`, … |
| [`Duality/RectangleDualCarrier`](Duality/RectangleDualCarrier.lean) | Declarations: `rectangleDualExpanded`, `rectangleDualInterior`, `rectangleDualBoundary`, `rectangleDualInterior_eq_empty_width_zero`, … |
| [`Duality/RectangleDualConfiguration`](Duality/RectangleDualConfiguration.lean) | Declarations: `rectangleDualConfigurationEquiv`, `rectangleDualConfigurationEquiv_apply`, `rectangleDualConfigurationEquiv_card`, `rectangleDualConfiguration_card_add`, … |
| [`Duality/RectangleDualCrossing`](Duality/RectangleDualCrossing.lean) | Declarations: `rectangleDual_mem_expanded_iff`, `bottomPort_mem_of_coords`, `topPort_mem_of_coords`, `exists_reachable_between_of_odd_ncard_neighbor_sum`, … |
| [`Duality/RectangleDualCutParity`](Duality/RectangleDualCutParity.lean) | Declarations: `rectangleCutDualAdj_iff_of_faceBase`, `rectangleCutFace_east_adj_iff`, `rectangleCutFace_north_adj_iff`, `rectangleCutFace_west_adj_iff`, … |
| [`Duality/RectangleDualPotential`](Duality/RectangleDualPotential.lean) | Declarations: `rectangleDualConfiguration`, `mem_rectangleDualConfiguration`, `mem_rectangleDualConfiguration_iff`, `rectangleDualOpen_adj_iff`, … |
| [`Duality/RectangleEuler`](Duality/RectangleEuler.lean) | Declarations: `rectangleDualCurlKernelOpenLinearEquiv`, `rectangleDualPotentialCurlKernelSignedKernelEquiv`, `rectangleDualComponentCount_eq_potentialFinrank_add_one`, `rectangleEuler_additive_config` |
| [`Duality/RectangleEvents`](Duality/RectangleEvents.lean) | Declarations: `rectangleHorizontalCrossingEvent` |
| [`Duality/RectangleFlowDimension`](Duality/RectangleFlowDimension.lean) | Declarations: `rectanglePrimalEdgeBond_endpoints_mem_public`, `rectanglePrimalEdgeBond_toSym2_public`, `rectanglePrimalBondToEdge`, `rectanglePrimalEdgeBondEquiv`, … |
| [`Duality/RectangleFlowIntegration`](Duality/RectangleFlowIntegration.lean) | Declarations: `RectanglePrimalFlow`, `rectangleExtendedPrimalFlow`, `rectanglePrimalFlowDivergence`, `rectangleFlowH`, … |
| [`Duality/RectangleLabelCut`](Duality/RectangleLabelCut.lean) | Declarations: `rectangleLabelCutEndpointStates`, `rectangleLabelCutEdgeCarrier`, `mem_rectangleLabelCutEdgeCarrier`, `rectangleLabelCutDualConfiguration`, … |
| [`Duality/RectangleLabelCutIncidence`](Duality/RectangleLabelCutIncidence.lean) | Declarations: `rectangleCutDualEdgeOfBond`, `rectangleCutEdgeOfBond_mem_cut_iff`, `rectangleCutDualEdgeOfBond_adj_iff`, `rectangleCutDualEdgeOfBond_crossingBond`, … |
| [`Duality/RectangleOpenFlow`](Duality/RectangleOpenFlow.lean) | Declarations: `rectangleOpenFlowZeroExtend`, `rectangleOpenFlowZeroExtend_onOpen`, `rectangleOpenFlowZeroExtend_onClosed`, `rectangleOpenFlowSubmodule`, … |
| [`Duality/RectanglePathIntersection`](Duality/RectanglePathIntersection.lean) | Declarations: `unitClamp`, `unitClamp_mem`, `unitClamp_eq_zero_iff`, `unitClamp_eq_one_iff`, … |
| [`Duality/RectangleWalks`](Duality/RectangleWalks.lean) | Declarations: `rectangleOpenGraphToSquare`, `complex_segment_coordinate_bounds`, `latticeWalkPath_coordinate_bounds`, `rectangleOpenWalk_mapped_support_preimage` |
| [`Duality/ReverseInfiniteDuality`](Duality/ReverseInfiniteDuality.lean) | Applying the planar dual transform twice translates face-base coordinates. |
| [`Duality/ScreenBridge`](Duality/ScreenBridge.lean) | The copied whole-plane geometry uses the exact frozen open graph. |
| [`Duality/SignedFlowDimension`](Duality/SignedFlowDimension.lean) | Declarations: `OpenEdgeIndex`, `SignedFlowOrientation`, `signedIncidenceMatrix`, `signedGradient`, … |
| [`Duality/WholePlaneDualConfiguration`](Duality/WholePlaneDualConfiguration.lean) | Declarations: `wholePlaneBondEdgeEquiv`, `wholePlaneDualCrossingEdgeEquiv`, `boolComplementEquiv`, `boolComplementHomeomorph`, … |
| [`Duality/WholePlaneDualGraph`](Duality/WholePlaneDualGraph.lean) | Declarations: `dualBondOfPrimal`, `primalBondOfDual`, `primalBondOfDual_dualBondOfPrimal`, `dualBondOfPrimal_primalBondOfDual`, … |
| [`Duality/WiredDomainComparison`](Duality/WiredDomainComparison.lean) | Wired domain monotonicity on arbitrary finite induced lattice domains. |
| [`Duality/WiredDomainLimit`](Duality/WiredDomainLimit.lean) | Wired limits along finite domains squeezed between consecutive square boxes. |
| [`Duality/WiredPotentialSpace`](Duality/WiredPotentialSpace.lean) | Declarations: `componentConstantFunctions`, `componentPotentialLocalPredicate`, `componentConstant_iff_local`, `componentConstantQuotientEquiv`, … |
| [`FK/AntitoneCylinderConvergence`](FK/AntitoneCylinderConvergence.lean) | Declarations: `probabilityMeasures_tendsto_of_antitone_allOpen` |
| [`FK/BoundaryComparison`](FK/BoundaryComparison.lean) | Comparison under coarser boundary wiring. The cross lattice condition is proved from the same actual component-merging calculation for two … |
| [`FK/BoundaryPartitionLaw`](FK/BoundaryPartitionLaw.lean) | Declarations: `law_eq_of_boundary_partition_eq` |
| [`FK/BoxCompactness`](FK/BoxCompactness.lean) | Subsequence compactness for the actual finite-box configuration laws. The whole-lattice edge-state space is a countable product of the … |
| [`FK/BoxComparison`](FK/BoxComparison.lean) | Monotonicity of free box all-open cylinder probabilities. The comparison is on the actual induced graphs. |
| [`FK/BoxCylinders`](FK/BoxCylinders.lean) | Actual finite all-open cylinders. The events refer to finitely many original whole-lattice edges. |
| [`FK/BoxExhaustion`](FK/BoxExhaustion.lean) | Cofinality of increasing lattice boxes. Nested exhaustive sequences of finite lattice boxes eventually contain each fixed finite lattice … |
| [`FK/BoxLaw`](FK/BoxLaw.lean) | The actual finite-box FK laws on the whole-lattice configuration carrier. Every finite box is its genuine induced square-lattice graph. |
| [`FK/BoxLimits`](FK/BoxLimits.lean) | Declarations: `latticeBox_origin_eq_box`, `frozenExtendedProbabilityMeasure_free`, `frozenExtendedProbabilityMeasure_wired`, `isRCInfiniteVolumeLimit_of_freeBox_tendsto`, … |
| [`FK/BoxTranslation`](FK/BoxTranslation.lean) | Declarations: `boxVertexTranslationIso`, `latticeConfigurationTranslationHomeomorph`, `latticeConfigurationTranslate`, `latticeConfigurationTranslate_measurable`, … |
| [`FK/ComponentBoundarySupport`](FK/ComponentBoundarySupport.lean) | Declarations: `componentSetoid_le_wired_union_of_edge_endpoints` |
| [`FK/ComponentMerge`](FK/ComponentMerge.lean) | Opening an edge between distinct wired components. The new quotient is explicitly identified with the old component quotient with one class … |
| [`FK/ComponentSupermodular`](FK/ComponentSupermodular.lean) | Supermodularity of the actual wired component count. Opening one edge merges two components precisely when its endpoints are not already … |
| [`FK/ConditionalEmbeddedBoundaryUpper`](FK/ConditionalEmbeddedBoundaryUpper.lean) | Declarations: `filteredConditionalEmbeddedEvent_measure_le_boundary` |
| [`FK/ConditionalEmbeddedLaw`](FK/ConditionalEmbeddedLaw.lean) | Declarations: `law_filter_frozen_map_embeddedRestriction` |
| [`FK/ConditionalLaw`](FK/ConditionalLaw.lean) | The spatial Markov identity as actual PMF conditioning. The existing finite FK law is filtered on the event fixing every edge in R. Its … |
| [`FK/ConfigurationBridge`](FK/ConfigurationBridge.lean) | Boolean configurations and finite open-edge sets. These equivalences preserve the actual open graph and both edge counts. |
| [`FK/CylinderConvergence`](FK/CylinderConvergence.lean) | Weak convergence from monotone finite cylinders. On the compact whole-lattice configuration space, monotonicity of every finite all-open … |
| [`FK/CylinderDetermination`](FK/CylinderDetermination.lean) | Determination by finite all-open cylinders. On the natural product measurable space of whole-lattice edge states, the probability of every … |
| [`FK/Disintegration`](FK/Disintegration.lean) | Exact decomposition over frozen edge states. The marginal of the original frozen edges and the induced conditional FK law reconstruct the … |
| [`FK/DomainMarkov`](FK/DomainMarkov.lean) | Wiring induced by a frozen subset of original edges. The induced partition is exactly original wiring joined with connectivity in the … |
| [`FK/EdgeConditional`](FK/EdgeConditional.lean) | The exact law of an edge within a wired component. Fix all edges except one original graph edge, whose endpoints are already in the same … |
| [`FK/EdgeRestriction`](FK/EdgeRestriction.lean) | The same-vertex graph obtained by deleting the nonsampled edges. Deleting edges retains the entire original vertex type. |
| [`FK/EmbeddedBoundaryUpper`](FK/EmbeddedBoundaryUpper.lean) | Declarations: `fkLaw_measure_toReal_eq_expectation`, `embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition` |
| [`FK/EmbeddedClosedInteriorOuterBoundary`](FK/EmbeddedClosedInteriorOuterBoundary.lean) | Declarations: `removedEdge_endpoint_not_image_compl_general`, `isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior` |
| [`FK/EmbeddedClosedInteriorOuterComparison`](FK/EmbeddedClosedInteriorOuterComparison.lean) | Declarations: `embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior` |
| [`FK/EmbeddedMarginalLaw`](FK/EmbeddedMarginalLaw.lean) | Declarations: `embeddedConfigurationRestriction_union_subgraphRemoved`, `remainingLaw_map_embeddedRestriction`, `law_embeddedConfigurationRestriction_eq_bind_frozenMarginal` |
| [`FK/EndpointLimits`](FK/EndpointLimits.lean) | The random-cluster limits at the two edge-parameter endpoints. For every positive cluster weight and either boundary condition, the frozen … |
| [`FK/Events`](FK/Events.lean) | Finite FK events and actual open connectivity. Every configuration has positive mass. |
| [`FK/Expectation`](FK/Expectation.lean) | Real expectations of finite probability mass functions. These are the literal finite weighted sums. |
| [`FK/FiniteEnergy`](FK/FiniteEnergy.lean) | Declarations: `configurationEdgeStateEquiv_symm_apply_false`, `configurationEdgeStateEquiv_symm_apply_true`, `configurationProbability_edgeState_sum`, `configurationProbability_edge_finite_energy`, … |
| [`FK/FreeBoxLimit`](FK/FreeBoxLimit.lean) | Declarations: `allOpen_mono_nnreal`, `freeBoxLimit_existsUnique` |
| [`FK/FreeBoxLimitV1`](FK/FreeBoxLimitV1.lean) | Declarations: `freeBoxLimit_existsUnique` |
| [`FK/FreeBoxPositiveAssociation`](FK/FreeBoxPositiveAssociation.lean) | Declarations: `boxConfiguration_mono`, `boxProbabilityMeasure_apply_preimage`, `boxProbabilityMeasure_finite_positive_association`, `freeBoxLimit_clopen_positive_association` |
| [`FK/FreeBoxTranslation`](FK/FreeBoxTranslation.lean) | Declarations: `freeBoxLimit_translation_invariant` |
| [`FK/FrozenBridge`](FK/FrozenBridge.lean) | Exact finite-volume bridge to the frozen random-cluster probabilities. The graph is the frozen induced graph. |
| [`FK/FrozenLimitBridge`](FK/FrozenLimitBridge.lean) | Declarations: `frozenEdgeEmbedding`, `patternCylinder`, `patternCylinder_isClopen`, `frozenExtendedProbabilityMeasure`, … |
| [`FK/Graph`](FK/Graph.lean) | Finite FK graphs, actual paths, and boundary identifications. The components counted in the finite FK law are classes of **all** vertices … |
| [`FK/IncreasingEvents`](FK/IncreasingEvents.lean) | FKG and wiring comparison for actual increasing events. The finite sums are identified with the real-valued probabilities of the existing … |
| [`FK/IsolatedBoundaryComponents`](FK/IsolatedBoundaryComponents.lean) | Declarations: `isolatedExtensionPullbackBoundary`, `isolatedExtensionExteriorBoundaryClasses`, `isolatedBoundaryLabel_of_hit`, `isolatedBoundaryLabel_of_no_hit`, … |
| [`FK/IsolatedBoundaryLaw`](FK/IsolatedBoundaryLaw.lean) | Declarations: `weight_isolatedExtension_boundary_pullback`, `partitionFunction_isolatedExtension_boundary_pullback`, `configurationProbability_isolatedExtension_boundary_pullback`, `law_isolatedExtension_map_boundary_pullback` |
| [`FK/IsolatedExtension`](FK/IsolatedExtension.lean) | Extending a finite free FK graph by isolated vertices. An injective vertex map transports every original edge and adds no edges at the … |
| [`FK/Isomorphism`](FK/Isomorphism.lean) | Declarations: `boundaryConditionIso`, `configurationIsoEdgeEquiv`, `configurationIso`, `configurationIso_val`, … |
| [`FK/Lattice`](FK/Lattice.lean) | The square lattice and its finite closed boxes. |
| [`FK/LimitTranslation`](FK/LimitTranslation.lean) | Translation invariance on the exact frozen carrier. Uniqueness of the frozen cylinder characterization transfers the invariance of the … |
| [`FK/Marginal`](FK/Marginal.lean) | The exact marginal after removing prewired edges. This proves the sampling equivalence on page 5 of the paper. |
| [`FK/Model`](FK/Model.lean) | The finite random-cluster probability law. The finite FK law `p^{o(A)} (1-p)^{c(A)} q^{k_ξ(A)} / Z`, including every isolated vertex in the … |
| [`FK/Parameters`](FK/Parameters.lean) | Independent finite random-cluster parameters. |
| [`FK/PositiveAssociation`](FK/PositiveAssociation.lean) | Positive association of the actual finite FK law. The component count is the original wired quotient count, including isolated vertices. |
| [`FK/Probability`](FK/Probability.lean) | Normalizing strictly positive weights on a finite configuration space. This module supplies the elementary normalization used in the finite … |
| [`FK/ProbabilityProduct`](FK/ProbabilityProduct.lean) | Products and changes of carrier for finite normalized weights. The product PMF is constructed by independently sampling the two given PMFs … |
| [`FK/RemainingComparison`](FK/RemainingComparison.lean) | FKG and boundary comparison for the actual remaining-edge law. The exact configuration order isomorphism transports the complete finite FK … |
| [`FK/SingleEdgeLaw`](FK/SingleEdgeLaw.lean) | Exact one-edge FK conditional probabilities. With every other edge fixed, the open probability is p if the endpoints are already connected … |
| [`FK/SubgraphComparison`](FK/SubgraphComparison.lean) | Free FK comparison under actual finite graph inclusions. Configurations are transported along injective maps of original unordered edges. |
| [`FK/VolumeComparison`](FK/VolumeComparison.lean) | Comparison of the original FK marginal with a graph with edges deleted. Conditioning on the deleted edges induces a coarser partition than … |
| [`FK/WiredBoxComparison`](FK/WiredBoxComparison.lean) | Wired box laws decrease on increasing cylinder events as the domain grows. |
| [`FK/WiredBoxLaw`](FK/WiredBoxLaw.lean) | Wired finite-box FK laws on the common whole-lattice carrier. |
| [`FK/WiredBoxLimits`](FK/WiredBoxLimits.lean) | A common weak limit of wired FK laws along every nested exhaustive box sequence. |
| [`FK/WiredBoxTranslation`](FK/WiredBoxTranslation.lean) | Declarations: `mem_vertexBoundary_latticeBox_translate_iff`, `boundaryConditionIso_wired_box_partition`, `wiredBoxConfiguration_translation_commute`, `pmf_map_commute`, … |
| [`FK/WiredComponentBridge`](FK/WiredComponentBridge.lean) | Counting components after wiring a vertex boundary. The quotient definition of finite FK components agrees with the description that counts … |
| [`FK/WiredLimitTranslation`](FK/WiredLimitTranslation.lean) | Declarations: `wiredBoxLimit_translation_invariant` |
| [`FK/WiredRemoval`](FK/WiredRemoval.lean) | Removing finitely many prewired edges. For a finite set `R` of original graph edges, configurations split uniquely into the open edges … |
| [`FK/Wiring`](FK/Wiring.lean) | Opening edges and boundary wiring. Opening additional edges can merge components but cannot split them. |
| [`Infra/CylinderUniqueness`](Infra/CylinderUniqueness.lean) | Uniqueness of cylinder limits. A finite measure on a product of countable discrete spaces is determined by its values on the cylinder atoms … |
| [`Infra/RCWeightBasic`](Infra/RCWeightBasic.lean) | Basic facts about the finite-volume random-cluster weights. On the source parameter range `p ∈ [0, 1]`, `q > 0`, every weight is … |
| [`RCInfinite/BoxConnector`](RCInfinite/BoxConnector.lean) | Declarations: `boxVertex_bounds`, `box_mem_of_bounds`, `box_horizontal_up`, `box_vertical_up`, … |
| [`RCInfinite/BoxExhaustion`](RCInfinite/BoxExhaustion.lean) | Declarations: `free_box_exhaustion`, `wired_box_exhaustion`, `translation_invariant` |
| [`RCInfinite/BurtonKeane`](RCInfinite/BurtonKeane.lean) | Declarations: `exists_positive_trifurcation_of_positive_three_clusters`, `isRCInfiniteVolumeLimit_atLeastThree_probability_zero`, `isRCInfiniteVolumeLimit_atMostOneInfiniteCluster` |
| [`RCInfinite/ClusterEvents`](RCInfinite/ClusterEvents.lean) | Declarations: `cluster`, `infiniteAt`, `infiniteClusterEvent`, `atMostOneInfiniteCluster`, … |
| [`RCInfinite/ClusterThresholds`](RCInfinite/ClusterThresholds.lean) | Declarations: `atLeastInfiniteClusters`, `measurableSet_atLeastInfiniteClusters`, `atLeastInfiniteClusters_zero`, `atLeastInfiniteClusters_antitone`, … |
| [`RCInfinite/ComponentCounting`](RCInfinite/ComponentCounting.lean) | Declarations: `componentPart`, `componentPartSubtype`, `componentPartSubtype_card`, `sum_componentPart_card` |
| [`RCInfinite/ComponentSeparators`](RCInfinite/ComponentSeparators.lean) | Declarations: `component_separator_part_le`, `finite_graph_terminal_separator_card_le` |
| [`RCInfinite/ConnectorEmbedding`](RCInfinite/ConnectorEmbedding.lean) | Declarations: `boxExitCarrierVertex`, `boxExitTripleCell_outside_injective`, `boxExitCarrierEmbedding`, `boxExitConnector_adj_lattice`, … |
| [`RCInfinite/ConnectorGraph`](RCInfinite/ConnectorGraph.lean) | Declarations: `BoxExitCarrier`, `boxExitConnectorGraph`, `boxExitConnector_adj_inl_inl`, `boxExitConnector_adj_inl_inr`, … |
| [`RCInfinite/CylinderApproximation`](RCInfinite/CylinderApproximation.lean) | Declarations: `SupportedCylinder`, `SupportedCylinder.isCylinder`, `SupportedCylinder.dependsOn`, `SupportedCylinder.compl`, … |
| [`RCInfinite/Cylinders`](RCInfinite/Cylinders.lean) | Declarations: `Edge`, `DependsOn`, `IsCylinder`, `DependsOn.mono`, … |
| [`RCInfinite/EdgeErgodicity`](RCInfinite/EdgeErgodicity.lean) | Declarations: `edgeTranslate`, `edgeTranslate_measurable`, `edgeTranslate_zero`, `edgeTranslate_add`, … |
| [`RCInfinite/ErgodicLimits`](RCInfinite/ErgodicLimits.lean) | Declarations: `invariant_allOpen_independent`, `invariant_restrict_eq_smul`, `isRCInfiniteVolumeLimit_interior_edge_ergodic`, `dirac_constant_edge_ergodic`, … |
| [`RCInfinite/ExteriorBranches`](RCInfinite/ExteriorBranches.lean) | Declarations: `squareLattice_neighborSet_finite`, `infinite_component_has_infinite_deleted_neighbor`, `exteriorInfiniteAt_has_deleted_neighbor` |
| [`RCInfinite/ExteriorClusters`](RCInfinite/ExteriorClusters.lean) | Declarations: `exteriorOpenGraph`, `exteriorOpenGraph_adj`, `exteriorOpenGraph_le`, `lattice_adj_box_succ`, … |
| [`RCInfinite/FiniteBoxCounting`](RCInfinite/FiniteBoxCounting.lean) | Declarations: `walk_prefix_to_boundary`, `trifurcation_branch_reaches_boundary`, `boxOpenGraph`, `boxBoundaryVertices`, … |
| [`RCInfinite/FiniteClusterExclusion`](RCInfinite/FiniteClusterExclusion.lean) | Declarations: `infiniteClusterWitnesses`, `measurableSet_infiniteClusterWitnesses`, `witnesses_exhaust`, `opening_witnesses_unique`, … |
| [`RCInfinite/FiniteConditioning`](RCInfinite/FiniteConditioning.lean) | Declarations: `pmf_eq_bind_fiber_filter`, `pmf_measureReal_eq_expectation`, `pmf_joint_fiber_sum`, `pmf_joint_le_of_fiber_le`, … |
| [`RCInfinite/FiniteEnergy`](RCInfinite/FiniteEnergy.lean) | Declarations: `openEnergy`, `openEnergy_pos`, `energyBound`, `energyBound_pos`, … |
| [`RCInfinite/FiniteModification`](RCInfinite/FiniteModification.lean) | Declarations: `setEdge`, `setEdge_self`, `setEdge_setEdge`, `setEdge_eq_self`, … |
| [`RCInfinite/FiniteTreeBranches`](RCInfinite/FiniteTreeBranches.lean) | Declarations: `tree_distinct_neighbors_separated_after_delete`, `tree_neighbor_deleted_component_contains_leaf`, `tree_three_leaves_have_separator` |
| [`RCInfinite/GeneratorMixing`](RCInfinite/GeneratorMixing.lean) | Declarations: `covariance`, `covariance_change_right`, `allOpen_cylinder_covariance_tendsto_zero`, `allOpen_measurable_covariance_tendsto_zero`, … |
| [`RCInfinite/GraphModification`](RCInfinite/GraphModification.lean) | Declarations: `infinite_component_contains_old`, `edgeEndpoints`, `opening_new_edge_endpoints`, `opening_infinite_component_contains_old` |
| [`RCInfinite/LimitComparison`](RCInfinite/LimitComparison.lean) | Declarations: `wired_limit_joint_le`, `free_limit_joint_ge`, `abs_covariance_le_of_upper`, `abs_covariance_le_of_lower`, … |
| [`RCInfinite/MappedTree`](RCInfinite/MappedTree.lean) | Declarations: `mappedTreeDeleteIso`, `mapped_tree_delete_reachable_iff` |
| [`RCInfinite/MeasurableBounds`](RCInfinite/MeasurableBounds.lean) | Declarations: `exists_supportedCylinder_real_approx`, `abs_inter_measureReal_sub_le`, `supported_lower_bound_extend`, `openEnergy_le_one`, … |
| [`RCInfinite/Mixing`](RCInfinite/Mixing.lean) | Declarations: `probabilityMeasures_tendsto_of_allOpen_real` |
| [`RCInfinite/OpeningPaths`](RCInfinite/OpeningPaths.lean) | Declarations: `lattice_horizontal_reachable`, `lattice_vertical_reachable`, `squareLattice_reachable`, `rcInfiniteOpenGraph_edgeSet`, … |
| [`RCInfinite/PercolationZeroOne`](RCInfinite/PercolationZeroOne.lean) | Declarations: `infiniteAt_measure_eq_origin`, `infiniteCluster_pos_iff_origin_pos`, `infiniteCluster_zero_one`, `infiniteCluster_eq_one_iff_origin_pos` |
| [`RCInfinite/SpatialComparison`](RCInfinite/SpatialComparison.lean) | Declarations: `boxEdges`, `boxRestriction`, `boxRemovedEdges`, `boxOutsideState`, … |
| [`RCInfinite/SubgraphComparison`](RCInfinite/SubgraphComparison.lean) | Declarations: `finiteLatticeGraph`, `finiteLatticeVertexEmbedding`, `finiteLatticeGraph_map_le`, `finiteSubgraphOpenEvent`, … |
| [`RCInfinite/SubgraphExhaustion`](RCInfinite/SubgraphExhaustion.lean) | Declarations: `subgraphBoxRadius`, `subgraph_subset_boxRadius`, `subgraphBoxRadius_ge_vertex`, `subgraphBoxRadius_tendsto`, … |
| [`RCInfinite/SubgraphProbability`](RCInfinite/SubgraphProbability.lean) | Declarations: `finiteSubgraphConfiguration`, `finiteSubgraphProbabilityMeasure`, `finiteSubgraphConfiguration_open_iff`, `finiteSubgraphProbabilityMeasure_allOpen`, … |
| [`RCInfinite/SurgeryEvents`](RCInfinite/SurgeryEvents.lean) | Declarations: `BoxExit`, `boxExitInside`, `boxExitOutside`, `boxExitEdge`, … |
| [`RCInfinite/SurgeryExterior`](RCInfinite/SurgeryExterior.lean) | Declarations: `exteriorReachable_distinct_endpoints_outside`, `exteriorOpenGraph_le_tree_surgery`, `exteriorOpenGraph_deleted_le_tree_surgery_deleted` |
| [`RCInfinite/TerminalCounting`](RCInfinite/TerminalCounting.lean) | Declarations: `separatingTerminals`, `terminal_separator_card_add_two_le` |
| [`RCInfinite/TerminalSeparation`](RCInfinite/TerminalSeparation.lean) | Declarations: `walk_reachable_deleteIncidenceSet`, `degree_ge_three_of_separated_targets`, `SeparatesThreeTerminals`, `separator_mem_connected_carrier`, … |
| [`RCInfinite/TranslationSupport`](RCInfinite/TranslationSupport.lean) | Declarations: `translatedEdge`, `mem_boxEdges_iff`, `eventually_finset_in_box`, `translatedEdge_not_mem_box`, … |
| [`RCInfinite/TreeCounting`](RCInfinite/TreeCounting.lean) | Declarations: `tree_branch_card_add_two_le_leaf_card`, `tree_branch_card_le_terminals`, `exists_terminal_tree` |
| [`RCInfinite/TreeSurgery`](RCInfinite/TreeSurgery.lean) | Declarations: `boxExitSubembedding`, `boxTreeEdgeState`, `mapped_connector_tree_le_surgery_graph`, `surgery_graph_le_tree_sup_exterior` |
| [`RCInfinite/Trifurcation`](RCInfinite/Trifurcation.lean) | Declarations: `deletedOpenGraph`, `deletedCluster`, `deletedInfiniteAt`, `deletedChain`, … |
| [`RCInfinite/TrifurcationProbability`](RCInfinite/TrifurcationProbability.lean) | Declarations: `trifurcationEvent`, `trifurcationIndicator`, `boxTrifurcationCountReal`, `measurableSet_trifurcationEvent`, … |
| [`RCInfinite/TrifurcationSurgery`](RCInfinite/TrifurcationSurgery.lean) | Declarations: `boxExitTripleCell_surgery_trifurcation` |
| [`RCInfinite/UnionReachability`](RCInfinite/UnionReachability.lean) | Declarations: `reachable_of_sup_of_external_components` |
