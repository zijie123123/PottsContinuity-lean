# `PottsContinuity/Thm3/`

The proof of Theorem 3 (Section 3 of the paper): `Easy/` the easy implications, `RSW/` the renormalisation of Section 3.3 (Lemma 4, Proposition 3), `Push/` Lemmas 2 and 3, `OuterCircuit/` outermost circuits in Lemma 4, `Prop4/` Proposition 4 with Lemma 7, `Touch/` Lemma 6, `StripDual/` self-duality of strips.

1107 modules, 85,721 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`Easy/P1ToP2`](Easy/P1ToP2.lean) | Declarations: `wired_no_infinite_cluster_event`, `wired_all_clusters_finite_ae` |
| [`Easy/P1ToP2Conditional`](Easy/P1ToP2Conditional.lean) | Conditional closure of P1 ⇒ P2 from an outermost-circuit DMP hypothesis. The barrier family and its finite-volume random-domain DMP … |
| [`Easy/P1ToP2DisconnectionBarrier`](Easy/P1ToP2DisconnectionBarrier.lean) | Declarations: `disconnection_openGraph_adj_iff_edge_mem`, `disconnection_revealed_edge_of_cluster`, `disconnection_boundaryTouchCluster_eq_of_agreement`, `disconnection_boundaryClusterRevealMap_stable`, … |
| [`Easy/P2ToP3Conditional`](Easy/P2ToP3Conditional.lean) | Declarations: `oneArmBoundaryEvent`, `reachable_rectangle_to_whole_plane`, `vertical_crossing_has_bottom_one_arm`, `verticalRectangle_subset_bottom_oneArm_union` |
| [`Easy/P2ToP3Summability`](Easy/P2ToP3Summability.lean) | Declarations: `p2p3BoundaryShell`, `p2p3Boundary_latticeBox_max`, `p2p3Boundary_finite`, `p2p3BoundaryShell_injective`, … |
| [`Easy/P2ToP3VerticalRSW`](Easy/P2ToP3VerticalRSW.lean) | Declarations: `weakRSWMapIso`, `weakRSWMapIso_mem_latticeBox`, `horizontalRectangle_subset_preimage_verticalRectangle`, `verticalRectangle_tall_subset_target`, … |
| [`Easy/P2ToP3WeakRSW`](Easy/P2ToP3WeakRSW.lean) | Declarations: `oneArmBoundaryEvent_translation`, `oneArmBoundaryEvent_measurable`, `oneArmBoundaryEvent_real_translation`, `wired_weakRSW_oneArm_lower_bound` |
| [`Easy/P3ToP4`](Easy/P3ToP4.lean) | Declarations: `frozen_limit_to_pd_box_limit`, `corrConnectionEvent_eq_dualityConnectionEvent`, `pairZero_eq_pair`, `frozenConnectionEvent_eq_dualityConnectionEvent`, … |
| [`Easy/P5AnnuliProduct`](Easy/P5AnnuliProduct.lean) | Declarations: `dyadicAnnulusTail`, `dyadicAnnulusTail_isCylinder`, `dyadicAnnulusTail_dependsOn_after`, `wired_dyadic_annulus_product_bound_from`, … |
| [`Easy/P5AnnulusCandidateBoundaryPartition`](Easy/P5AnnulusCandidateBoundaryPartition.lean) | Declarations: `annulusCandidateDoubleDualActiveHostEmbedding`, `annulusCandidateDoubleDualActiveHostGraph_map_eq`, `annulusCandidate_eqvGen_of_hostOpenAdj`, `annulusCandidate_eqvGen_of_hostWalk`, … |
| [`Easy/P5AnnulusCarrierErratum`](Easy/P5AnnulusCarrierErratum.lean) | Declarations: `annulusDualExpandedHostAnchor`, `annulusExpandedHostCarrierEquiv`, `annulusExpandedHostDualCandidateGraph`, `annulusExpandedHostDualCandidateGraph_le_rectangle`, … |
| [`Easy/P5AnnulusCycleBridge`](Easy/P5AnnulusCycleBridge.lean) | Declarations: `polygonCyclicList_nonempty'`, `polygonCyclicList_chain'`, `polygonCyclicWalk_length`, `p5aForwardPolygonCycle_isCycle` |
| [`Easy/P5AnnulusDoubleDualActiveGeometry`](Easy/P5AnnulusDoubleDualActiveGeometry.lean) | Declarations: `annulusVertexSet_of_bounds`, `annulusSourceGraph_edge_incident_first`, `annulusAdj_x_pred`, `annulusAdj_x_succ`, … |
| [`Easy/P5AnnulusDoubleDualCandidate`](Easy/P5AnnulusDoubleDualCandidate.lean) | Declarations: `doubleDualBond_source_shift`, `doubleDualBond_target_shift`, `annulusCandidateDoubleDualEdgeEquiv`, `annulusCandidatePrimalBond`, … |
| [`Easy/P5AnnulusEventProperties`](Easy/P5AnnulusEventProperties.lean) | Declarations: `annulusVertexSet_subset_outerBox`, `annulusOuterBoundary_not_innerBox`, `annulusOpenWalk_transfer`, `annulusOpenWalk_transfer_outside`, … |
| [`Easy/P5AnnulusWiredBoxNoCrossing`](Easy/P5AnnulusWiredBoxNoCrossing.lean) | Declarations: `inducedPullbackBoundary_le_wired_noGap`, `annulus_wired_noCrossing_le_wiredBox_noCrossing_at_touchingBoundary` |
| [`Easy/P5AnnulusWiredBoxTransfer`](Easy/P5AnnulusWiredBoxTransfer.lean) | Declarations: `p5AnnulusInnerWitness`, `p5AnnulusOuterWitness`, `p5a_wiredBoxAnnulusTransfer`, `p5_implies_p1` |
| [`Easy/P5ClosedWalkCycle`](Easy/P5ClosedWalkCycle.lean) | Declarations: `duplicate_dropUntil_facts`, `rayStep_reverse_zero`, `rayIndex_nonzero_length_ge_three`, `closedWalk_exists_simpleNonzeroRayIndex` |
| [`Easy/P5FourFrameConditional`](Easy/P5FourFrameConditional.lean) | Declarations: `p5aAnnulusVertexSet`, `p5VerticalCrossing`, `p5FrameCrossing`, `p5aAnnulusCircuitEvent`, … |
| [`Easy/P5FrameCircuitOfLocation`](Easy/P5FrameCircuitOfLocation.lean) | Declarations: `p5aAnnulusCircuit_of_fourFrameCrossings_of_rayIndexPolygonLocation`, `p5a_uniform_lower_bound_of_p5Aspect16_and_rayIndexPolygonLocation` |
| [`Easy/P5FrameClosedWalk`](Easy/P5FrameClosedWalk.lean) | Declarations: `p5ClosedWalkToSquareLattice`, `walk_between_support_vertices`, `p5_frame_crossings_closedWalk_data`, `p5_frame_crossings_yield_closedWalk_rayIndex_eq_neg_one` |
| [`Easy/P5FrameComparison`](Easy/P5FrameComparison.lean) | Declarations: `p5SquareLattice_adj_iff`, `p5Translate`, `p5QuarterTurn`, `p5ReflectX`, … |
| [`Easy/P5FrameCycleExtract`](Easy/P5FrameCycleExtract.lean) | Declarations: `p5_frame_crossings_yield_simpleClosedWalk_rayIndex_ne_zero` |
| [`Easy/P5FrameCyclePolygonData`](Easy/P5FrameCyclePolygonData.lean) | Declarations: `p5_frame_crossings_yield_openSimplePolygon_rayIndex` |
| [`Easy/P5FrameIntersections`](Easy/P5FrameIntersections.lean) | Declarations: `p5OpenGraphToLattice`, `p5FrameCrossingCorridor`, `P5FrameCrossingWalk`, `p5FrameCrossing_exists_walk`, … |
| [`Easy/P5OneArmAnnuli`](Easy/P5OneArmAnnuli.lean) | Declarations: `walk_first_entry_with_support_subset`, `walk_map_of_support`, `box_boundary_vertex_not_smaller_box`, `annulusInnerSideOpenCrossing`, … |
| [`Easy/P5OneArmArithmetic`](Easy/P5OneArmArithmetic.lean) | Declarations: `dyadicOneArmExponent`, `dyadicOneArmExponent_pos`, `dyadic_factor_after_scale_three_le_power` |
| [`Easy/P5OneArmPower`](Easy/P5OneArmPower.lean) | Declarations: `pdOneArmBoundaryEvent`, `origin_not_boxBoundary`, `origin_adj_edge_mem_boxIncidentEdges`, `pdOneArm_subset_closedStar_compl`, … |
| [`Easy/P5ToP1OfAnnulusTransfer`](Easy/P5ToP1OfAnnulusTransfer.lean) | Declarations: `p5_implies_p1_of_annulusTransfer` |
| [`Easy/P5ToP5a`](Easy/P5ToP5a.lean) | Declarations: `p5_implies_p5a` |
| [`Easy/P5ToP5aConditional`](Easy/P5ToP5aConditional.lean) | Declarations: `p5_implies_p5a_of_rayIndexPolygonLocation` |
| [`OuterCircuit/CandidateEnvelope`](OuterCircuit/CandidateEnvelope.lean) | Declarations: `outerCircuitShapedCandidates_have_envelope` |
| [`OuterCircuit/CyclePolygonRecovery`](OuterCircuit/CyclePolygonRecovery.lean) | Declarations: `interiorCellBases_cast_eq`, `sourcePolygonWalk_envelopePolygon_cast_eq`, `outerCircuitCodePolygon_envelopePolygon_region_eq` |
| [`OuterCircuit/EnvelopeShell`](OuterCircuit/EnvelopeShell.lean) | Declarations: `outerCircuitShellVertex`, `outerCircuitCandidateShape`, `outerCircuitCandidateShape_origin_rayIndex_ne_zero`, `outerCircuitSourceEdge_endpoint_shell`, … |
| [`OuterCircuit/FiniteEnvelopeJoin`](OuterCircuit/FiniteEnvelopeJoin.lean) | Declarations: `outerCircuitSelectorShape`, `outerCircuitSelectorJoinGood`, `outerCircuitSelectorJoinSet`, `outerCircuitSelectorJoinSet_nonempty`, … |
| [`OuterCircuit/FiniteEnvelopeReveal`](OuterCircuit/FiniteEnvelopeReveal.lean) | Declarations: `outerCircuitCandidateSupport_open_of_valid`, `outerCircuitSelectorJoin_valid_of_valid`, `outerCircuitSelectorReveal`, `outerCircuitSelectorReveal_stable` |
| [`OuterCircuit/FinitePolygonFamily`](OuterCircuit/FinitePolygonFamily.lean) | Declarations: `OuterCircuitHostVertex`, `outerCircuitSourceBox_mem_latticeBox`, `outerCircuitHostVertexEquiv`, `outerCircuitHostVertexFintype`, … |
| [`OuterCircuit/FiniteSourceSelector`](OuterCircuit/FiniteSourceSelector.lean) | Declarations: `outerCircuitAmbientEdgeFintype`, `outerCircuitAmbientEdgeDecidableEq`, `outerCircuitHostEdgeToFKC`, `outerCircuitHostEdgeBond`, … |
| [`OuterCircuit/InnerFaceContainment`](OuterCircuit/InnerFaceContainment.lean) | Declarations: `outerCircuitClosedHalfCellBox`, `outerCircuitClosedHalfCellBox_convex`, `outerCircuitLatticeSegment_disjoint_halfCellBox`, `outerCircuitPolygon_carrier_disjoint_halfCellBox`, … |
| [`OuterCircuit/JoinedEnvelopeCode`](OuterCircuit/JoinedEnvelopeCode.lean) | Declarations: `outerCircuitCandidateValid_shape`, `outerCircuitEnvelopeCode_exists`, `outerCircuitCandidateSupport_subset_outside_of_region_subset` |
| [`OuterCircuit/LiftedResidual`](OuterCircuit/LiftedResidual.lean) | Declarations: `outerCircuitLiftedResidualGraph`, `outerCircuitLiftedResidualGraphIso`, `outerCircuitLiftedResidualEmbedding`, `outerCircuitLiftedResidualBoundarySet`, … |
| [`OuterCircuit/PolygonWalkBridge`](OuterCircuit/PolygonWalkBridge.lean) | Declarations: `sourcePolygonToPD`, `sourcePolygonWalk`, `sourcePolygonWalk_eq_p5aPolygonCyclePD`, `sourcePolygonWalk_isCycle`, … |
| [`OuterCircuit/ResidualAnnulusSupport`](OuterCircuit/ResidualAnnulusSupport.lean) | Declarations: `outerCircuitPlusAnnulus_vertex_coordinate_bounds`, `outerCircuitMinusAnnulus_vertex_coordinate_bounds`, `outerCircuitSelectedAnnulusEdge_in_recordedResidual`, `outerCircuitResidualRecordedEdges`, … |
| [`OuterCircuit/ResidualClosure`](OuterCircuit/ResidualClosure.lean) | Declarations: `outerCircuitSelectorReveal_eq_candidateOutside`, `outerCircuitMaximumCandidate_selected_of_outer_event`, `outerCircuitUnrevealedEdge_faceBases_in_candidateInterior`, `outerCircuitFourCellStar_mem_iff_center`, … |
| [`OuterCircuit/ResidualGraph`](OuterCircuit/ResidualGraph.lean) | Declarations: `outerCircuitFourCellStar`, `outerCircuitBond_faceBases_mem_fourCellStar`, `outerCircuitHostEdgeBond_faceBases_mem_fourCellStar`, `outerCircuitUnrevealedAmbientGraph`, … |
| [`OuterCircuit/RootPaths`](OuterCircuit/RootPaths.lean) | Declarations: `outerCircuitSourceWalk_support_in_host`, `outerCircuitOriginHostVertex`, `outerCircuitRootOfIndex`, `outerCircuitSelectedRoot`, … |
| [`OuterCircuit/RootRecords`](OuterCircuit/RootRecords.lean) | Declarations: `outerCircuitSelectedCandidate_of_observation`, `lemma4_outer_open_circuit_root_records`, `selfDual_lemma4_two_annuli_lower` |
| [`OuterCircuit/SelectedRecord`](OuterCircuit/SelectedRecord.lean) | Declarations: `outerCircuitMaximumCandidate`, `outerCircuitSelectedObservationSet`, `lemma4OuterAnnulusEvent_observation_preimage` |
| [`OuterCircuit/SelectorIndex`](OuterCircuit/SelectorIndex.lean) | Declarations: `OuterCircuitSelectorIndex`, `outerCircuitSelectorIndexFintype`, `outerCircuitSelectorIndexDecidableEq`, `outerCircuitSelectorIndexLinearOrder`, … |
| [`OuterCircuit/SourceEventEquivalence`](OuterCircuit/SourceEventEquivalence.lean) | Declarations: `outerCircuitBoundaryEdge_mem_boolConfigurationEquiv_iff_rcAdj`, `outerCircuitCandidateValid_implies_boolAnnulusEvent`, `outerCircuitCandidateValid_exists_of_boolAnnulusEvent`, `lemma4OuterAnnulusEvent_iff_candidate_exists` |
| [`OuterCircuit/SourcePolygonCode`](OuterCircuit/SourcePolygonCode.lean) | Declarations: `outerCircuitPolygon_vertex_mem_host_of_radius`, `outerCircuitPolygon_index_lt_host_card`, `outerCircuitPolygonCodeOfHostPolygon`, `outerCircuitCodePolygon_of_hostPolygon_eq` |
| [`Prop4/ActualStarPortGraph`](Prop4/ActualStarPortGraph.lean) | The connected graph of at most four actual sampled star ports |
| [`Prop4/ActualTubeCrossing`](Prop4/ActualTubeCrossing.lean) | The actual horizontal crossing event in a Euclidean tube. The finite graph retains every tube vertex. |
| [`Prop4/AllSlopeTouch`](Prop4/AllSlopeTouch.lean) | All-slope conditional touch estimate at the explicit self-dual value. The arbitrary-slope reduction is fully proved. |
| [`Prop4/AnalyticSum`](Prop4/AnalyticSum.lean) | The uniform weighted sum in Proposition 4. DCST, TeX lines 1775–1785: the uniform analytic-sum bound in the proof of Proposition 4. |
| [`Prop4/AnnulusArmPolynomialLower`](Prop4/AnnulusArmPolynomialLower.lean) | Declarations: `oneArm_polynomial_lower_of_uniform_annulus` |
| [`Prop4/ArcIsolationEmbedding`](Prop4/ArcIsolationEmbedding.lean) | Exact isolation-event transport when all exterior edges are closed |
| [`Prop4/ArcIsolationLocality`](Prop4/ArcIsolationLocality.lean) | Actual isolation is determined by edges incident to its target |
| [`Prop4/ArcPathLocality`](Prop4/ArcPathLocality.lean) | Locality of actual connection-plus-no-escape events. A connection to the arc can be stopped before leaving the finite target. |
| [`Prop4/ArmMonotone`](Prop4/ArmMonotone.lean) | Monotonicity of the actual infinite-volume arm event |
| [`Prop4/ArmSumShift`](Prop4/ArmSumShift.lean) | The exact two-unit convolution shift in equation (30). Both endpoint arm radii increase by one. |
| [`Prop4/AttachedFaceBoundary`](Prop4/AttachedFaceBoundary.lean) | Mixed primal vertices attach to their own unreached face boundary |
| [`Prop4/BoxComplementaryStarArms`](Prop4/BoxComplementaryStarArms.lean) | The actual complementary star screen on the original source box. All dual steps are genuine sampled closed-original bonds. |
| [`Prop4/BoxConfinedEventIso`](Prop4/BoxConfinedEventIso.lean) | Declarations: `sourceBox_confined_event_iso` |
| [`Prop4/BoxHalfTurn`](Prop4/BoxHalfTurn.lean) | The actual original-box half-turn preserves the free FK law |
| [`Prop4/BoxRawQueryExitTransport`](Prop4/BoxRawQueryExitTransport.lean) | Declarations: `boxMappedQuery_endpoint_preimage`, `sourceBox_lower_raw_query_exit_height_le`, `sourceBox_upper_raw_query_exit_height_ge` |
| [`Prop4/BoxRectangleTubeTransport`](Prop4/BoxRectangleTubeTransport.lean) | Literal tube and cut transport to the sampled rectangle carrier. The vertex map is the coordinate identity. |
| [`Prop4/BoxRectangleWiredLaw`](Prop4/BoxRectangleWiredLaw.lean) | Declarations: `sourceBox_latticeRectangle_eq`, `boxTubeRectangleIso_wired_partition`, `sourceBox_wired_probability_iso` |
| [`Prop4/BoxTraceExcursionTransport`](Prop4/BoxTraceExcursionTransport.lean) | Exact original-box trace transport to the literal sampled rectangle. The trace is read in the inverse source sample, retaining its original … |
| [`Prop4/CapsuleNearestNormal`](Prop4/CapsuleNearestNormal.lean) | A genuine nearest-point normal for a maximal Euclidean excursion. Compactness supplies a nearest segment point. |
| [`Prop4/CapsuleNormalSlopeAlgebra`](Prop4/CapsuleNormalSlopeAlgebra.lean) | Admissible slopes for upper capsule normals. The variational inequality at the point directly below the excursion is a scalar quadratic … |
| [`Prop4/CapsuleSupportingFunctional`](Prop4/CapsuleSupportingFunctional.lean) | A normal supporting the segment also supports its Euclidean capsule. The normal is anchored at a nearest-point variational inequality … |
| [`Prop4/CellBoundaryOneCycle`](Prop4/CellBoundaryOneCycle.lean) | A connected cell region with connected exterior has one boundary cycle |
| [`Prop4/CellRegionIndex`](Prop4/CellRegionIndex.lean) | Index constancy in the two face regions of a cell boundary |
| [`Prop4/CensoredArcBoundary`](Prop4/CensoredArcBoundary.lean) | Boundary control after an arc-censored outside-cluster exploration. All recorded open edges have endpoints in the removed clusters or the … |
| [`Prop4/CensoredArcComparison`](Prop4/CensoredArcComparison.lean) | Direct finite-domain comparison for the source isolation event. Explore exterior clusters in the graph censored at the target wired arc. |
| [`Prop4/CensoredArcConnection`](Prop4/CensoredArcConnection.lean) | First-hit connections surviving the censored outside-cluster exploration. A connection may visit removed clusters after touching the target … |
| [`Prop4/CensoredArcGeometry`](Prop4/CensoredArcGeometry.lean) | Actual paths censored at a prescribed wired arc. The censored graph isolates the arc vertices. |
| [`Prop4/CensoredClusterReveal`](Prop4/CensoredClusterReveal.lean) | A stable exploration of multiple clusters in a fixed censored graph. Clusters are computed using a fixed subgraph H of the ambient graph G … |
| [`Prop4/CensoredComplementLaw`](Prop4/CensoredComplementLaw.lean) | Exact induced-complement law for the actual censored-cluster record |
| [`Prop4/CenteredSquareIso`](Prop4/CenteredSquareIso.lean) | Declarations: `evenSquareToBoxIso`, `squarePairProbability_even_centered` |
| [`Prop4/CentralDualFaceIncidence`](Prop4/CentralDualFaceIncidence.lean) | Genuine sampled incidence of every central physical dual face. The central column contains no isolated expanded-box corner. |
| [`Prop4/ClampedFaceEndpointHeight`](Prop4/ClampedFaceEndpointHeight.lean) | Declarations: `dualFaceCenter_endpoint_coordinate_bounds`, `clamp_coordinate_distance_le`, `rectangleClampedFace_endpoint_height_distance_le` |
| [`Prop4/ClosedConnectorArmSplice`](Prop4/ClosedConnectorArmSplice.lean) | Moving both stopped sampled arms to their original cut roots. All four walks belong to the same restored primal sample. |
| [`Prop4/ClosedConnectorEnergy`](Prop4/ClosedConnectorEnergy.lean) | Closing the retained primal connector bonds under the exact finite law. The uniform closed-edge cost holds for every boundary partition. |
| [`Prop4/ClosedCutEnergy`](Prop4/ClosedCutEnergy.lean) | Uniform conditional closing of a finite cut. The strip side-independence argument needs a closed cut with a positive probability uniform in … |
| [`Prop4/ClosedTubeConnectorWalks`](Prop4/ClosedTubeConnectorWalks.lean) | Retained connectors in a single restored random sample. Closing exactly the retained central rows supplies a genuine sampled walk. |
| [`Prop4/ClosingImage`](Prop4/ClosingImage.lean) | Finite-energy closing surgery on arbitrary events. Unlike an edge-stable conditional event, the source connection event can be destroyed by … |
| [`Prop4/ClusterComplement`](Prop4/ClusterComplement.lean) | Exact all-q FK law on the induced complement of the actual cluster |
| [`Prop4/ClusterConditional`](Prop4/ClusterConditional.lean) | Uniform conditional target bounds after actual-cluster exploration |
| [`Prop4/ClusterConnection`](Prop4/ClusterConnection.lean) | Actual connection witnesses outside an attained seed-cluster record |
| [`Prop4/ClusterFactorization`](Prop4/ClusterFactorization.lean) | Free product bound for genuinely different open clusters. The first root's target event is measurable in its actual cluster record. |
| [`Prop4/ClusterFreeLaw`](Prop4/ClusterFreeLaw.lean) | Free law outside the actual revealed seed cluster. All open recorded edges have both endpoints in the removed cluster. |
| [`Prop4/ClusterReveal`](Prop4/ClusterReveal.lean) | Actual cluster exploration at independent FK parameters. The reveal and its stability are the parameter-independent proved FKC construction. |
| [`Prop4/ComplementComponentConnectivity`](Prop4/ComplementComponentConnectivity.lean) | Removing one component outside a connected explored region |
| [`Prop4/ComponentPocketMarginal`](Prop4/ComponentPocketMarginal.lean) | Exact retained-component marginal with one attached boundary class |
| [`Prop4/ComponentReferenceBoundary`](Prop4/ComponentReferenceBoundary.lean) | Reference exterior partitions on a remaining edge component |
| [`Prop4/Concavity`](Prop4/Concavity.lean) | Quantitative subadditivity defect for the Proposition 4 weights. DCST (15 May 2015), TeX line 1783, the concavity inequality in the proof … |
| [`Prop4/ConfinedTargetComparison`](Prop4/ConfinedTargetComparison.lean) | Embedded wired-target comparison retaining the actual path support. Only one open path is required to stay in the embedded domain. |
| [`Prop4/ContainingDomainTubeConfined`](Prop4/ContainingDomainTubeConfined.lean) | Tube-confined crossings in containing finite domains. The witness retains every visited vertex in the actual tube, even when the sample is … |
| [`Prop4/CorridorAbscissas`](Prop4/CorridorAbscissas.lean) | Capped horizontal positions of the overlapping corridor rectangles. The final stages stay at the rightmost permitted rectangle. |
| [`Prop4/CorridorRectangleContainment`](Prop4/CorridorRectangleContainment.lean) | Every actual corridor rectangle lies in the Euclidean tube. The horizontal and connector carriers include their complete lattice boundaries. |
| [`Prop4/CorridorRectangles`](Prop4/CorridorRectangles.lean) | Actual rectangles forming the digital sloped corridor. Horizontal rectangles have side 2s. |
| [`Prop4/CorridorRows`](Prop4/CorridorRows.lean) | Digital centers of the rectangular corridor. Round the supporting-line height down, then project to the nonempty integer interval leaving s … |
| [`Prop4/CorridorScale`](Prop4/CorridorScale.lean) | A fractional scale for the concrete tube corridor. Rounding the half-radius down gives an integral corridor width. |
| [`Prop4/CorridorTubeContainment`](Prop4/CorridorTubeContainment.lean) | Euclidean tube containment from the actual corridor centers. All distances refer to the original segment in the complex Euclidean plane. |
| [`Prop4/CorridorWiredTubeError`](Prop4/CorridorWiredTubeError.lean) | Quantitative bulk crossings of the actual sloped tube. The finite corridor is contained in the original Euclidean tube. |
| [`Prop4/CutFailure`](Prop4/CutFailure.lean) | Geometric decay for failure of disjoint closed cuts. All probabilities are those of the actual finite FK law. |
| [`Prop4/CutReferenceArmsTouch`](Prop4/CutReferenceArmsTouch.lean) | Actual complementary-arc reference arms at the original cut roots. The stopped touch arms and the retained connector energy are combined in … |
| [`Prop4/CutScanPrefix`](Prop4/CutScanPrefix.lean) | Tested edges precede the actual first successful cut |
| [`Prop4/Decay`](Prop4/Decay.lean) | Parameter choice and quantifier closure for Proposition 4. DCST (15 May 2015), TeX lines 1773 and 1820–1822. |
| [`Prop4/DeletedAmbientDualLaw`](Prop4/DeletedAmbientDualLaw.lean) | Exact ambient marginal after deleting the crossed tube reveal. The expanded induced dual graph may contain extra boundary edges. |
| [`Prop4/DeletedReferenceFirstExit`](Prop4/DeletedReferenceFirstExit.lean) | First physical exit survives restriction to genuine sampled dual edges. The prefix before the first exterior face has every edge incident … |
| [`Prop4/DeletedReferenceInteriorAgreement`](Prop4/DeletedReferenceInteriorAgreement.lean) | Agreement of the actual reference on every edge incident to an interior face. Ambient edges absent from the true sampled dual have both … |
| [`Prop4/DenominatorDescent`](Prop4/DenominatorDescent.lean) | Separate height denominator and horizontal descent radius. The source fixes denominator m. |
| [`Prop4/DenominatorTouch`](Prop4/DenominatorTouch.lean) | Touch averaging with a denominator at most twice the horizontal radius. The actual source descent has radius n*d*m. |
| [`Prop4/DualEscapeTail`](Prop4/DualEscapeTail.lean) | Corrected stretched-exponential bounds for actual dual escapes. The c₀ coefficient is retained. |
| [`Prop4/EmbeddedFreshRestriction`](Prop4/EmbeddedFreshRestriction.lean) | Literal restriction to any embedded graph of fresh original bonds |
| [`Prop4/EndpointInsertion`](Prop4/EndpointInsertion.lean) | Extending an actual finite connection by one original edge. DCST, the odd-square remark following Lemma 7, TeX lines 1761–1767. |
| [`Prop4/EvenRecursion`](Prop4/EvenRecursion.lean) | From the source summation estimate to an attained even recursion. DCST, TeX lines 1775–1785. |
| [`Prop4/EvenSquareDecay`](Prop4/EvenSquareDecay.lean) | The actual-law consumer requiring only Lemma 7's even-square bound. The odd-square remark, exterior-circuit estimate and all numerical … |
| [`Prop4/EvenSquareRawSourceBound`](Prop4/EvenSquareRawSourceBound.lean) | Declarations: `evenSquarePairKernel_of_touch` |
| [`Prop4/EvenSquareSummation`](Prop4/EvenSquareSummation.lean) | Source-compatible odd/even grouping of the exterior-circuit tail. Pair 2m-1 with 2m, so the proved odd-square remark uses the same arm … |
| [`Prop4/ExteriorPartition`](Prop4/ExteriorPartition.lean) | Exact top wiring after a closed-cut exterior exploration. Adapted from FKC/FiniteFK/FrozenBoundaryOutsideRegion.lean. |
| [`Prop4/FKCRectangleDualLift`](Prop4/FKCRectangleDualLift.lean) | Faithful lifting of the finite complementary rectangle dual. The finite dual uses only sampled original bonds. |
| [`Prop4/FKCRectangleOriginalRestriction`](Prop4/FKCRectangleOriginalRestriction.lean) | Literal original-state restriction to the shared finite rectangle. Restriction reads each actual original bond once. |
| [`Prop4/FiniteArmComparison`](Prop4/FiniteArmComparison.lean) | Finite embedded free target events bounded by the actual infinite arm |
| [`Prop4/FiniteArmProduct`](Prop4/FiniteArmProduct.lean) | Actual disconnected endpoint arms bounded by the infinite one-arm product. This is the probabilistic factorization used in Lemma 7. |
| [`Prop4/FiniteComponentWalk`](Prop4/FiniteComponentWalk.lean) | Whole finite component traces with actual walk witnesses. Repeated visits let an original u-v walk cover the whole connected component. |
| [`Prop4/FiniteDistantTarget`](Prop4/FiniteDistantTarget.lean) | Finite target sets beyond the requested arm radius. A path to a distant target first hits the exact frozen box boundary. |
| [`Prop4/FiniteDualArmsCorrelation`](Prop4/FiniteDualArmsCorrelation.lean) | Actual dual-arm correlation in a fresh finite FK law. The two events have a common agreeing extension by the proved meet construction. |
| [`Prop4/FiniteDualSampledWalkMap`](Prop4/FiniteDualSampledWalkMap.lean) | Restored finite dual paths retain actual sampled crossing bonds. The map forgets only the finite face membership proofs. |
| [`Prop4/FiniteEscapeComparison`](Prop4/FiniteEscapeComparison.lean) | Cropping a finite FK connection at a deterministic exterior separator. The existing censored-cluster comparison applies because every … |
| [`Prop4/FiniteFilterEquiv`](Prop4/FiniteFilterEquiv.lean) | Exact finite conditional-law transport under a configuration bijection. The conditioning event is transported together with the full sample … |
| [`Prop4/FiniteSlope`](Prop4/FiniteSlope.lean) | A bounded-denominator slope in the same finite lattice-comparison cell. For a box of radius m, supporting-line comparisons can only change … |
| [`Prop4/FiniteStrictCore`](Prop4/FiniteStrictCore.lean) | A strict affine core crossing in the actual finite wired box. A smaller fractional tube supplies the crossing. |
| [`Prop4/FiniteWiredComparison`](Prop4/FiniteWiredComparison.lean) | Lower-event comparison for a genuine finite wired induced domain. This is the complement of the increasing-event DMP comparison of … |
| [`Prop4/FiniteWiredRectangleError`](Prop4/FiniteWiredRectangleError.lean) | Actual finite wired rectangle error. The finite induced-domain restriction and the original rectangle restriction read the same original … |
| [`Prop4/FirstSeparatorPrefix`](Prop4/FirstSeparatorPrefix.lean) | Actual first-exit prefixes at a deterministic separator. Each retained prefix stays in the cropped domain. |
| [`Prop4/FirstTargetPrefix`](Prop4/FirstTargetPrefix.lean) | A first-target prefix retaining the original sampled edge incidence. Stopping before the first target visit keeps every retained edge … |
| [`Prop4/FourPortInducedConnectivity`](Prop4/FourPortInducedConnectivity.lean) | Nontrivial induced components of a connected four-port graph |
| [`Prop4/FreshStarFaceConnectivity`](Prop4/FreshStarFaceConnectivity.lean) | Fresh incident original edges belong to one unreached face component |
| [`Prop4/FrozenDualRemainingLaw`](Prop4/FrozenDualRemainingLaw.lean) | The exact deleted-dual-graph law of the all-open reference fiber. Crossed revealed bonds are deleted on the dual side. |
| [`Prop4/FrozenFiberDualArms`](Prop4/FrozenFiberDualArms.lean) | Exact fixed-fiber law for reconstructed common dual arms. The normalized original frozen fiber is transported through the proved finite DMP … |
| [`Prop4/FrozenLowerCorrelation`](Prop4/FrozenLowerCorrelation.lean) | Decreasing events in the full restored conditional sample. The exact deleted-graph law correlates arbitrary original lower events after … |
| [`Prop4/FrozenLowerMonotonicity`](Prop4/FrozenLowerMonotonicity.lean) | Monotonicity of decreasing events in the revealed open state. The revealed set stays fixed. |
| [`Prop4/FrozenOriginalConditioning`](Prop4/FrozenOriginalConditioning.lean) | Restoring the entire original sample from its normalized frozen fiber. The exact conditioning event fixes the open and closed states of … |
| [`Prop4/FrozenOriginalDisintegration`](Prop4/FrozenOriginalDisintegration.lean) | Disintegration of the entire original configuration. The fixed revealed-state marginal and its normalized conditional fiber reconstruct the … |
| [`Prop4/FrozenReferenceDualSample`](Prop4/FrozenReferenceDualSample.lean) | The literal deleted dual sample of the all-open primal reference fiber. Restoration opens exactly the prescribed original reveal. |
| [`Prop4/FrozenReplayComparison`](Prop4/FrozenReplayComparison.lean) | Restoring a source reveal after sampling an auxiliary configuration. Only the unrevealed auxiliary edge states are copied. |
| [`Prop4/FrozenSourceLowerBound`](Prop4/FrozenSourceLowerBound.lean) | Averaging a decreasing event over a fixed revealed source event. Any event determined by the revealed edge state admits the same all-open … |
| [`Prop4/GoodCorridorCrossing`](Prop4/GoodCorridorCrossing.lean) | The concrete finite crossing event of the sloped corridor. There are 2n+1 horizontal stages and 2n vertical connectors. |
| [`Prop4/HalfScale`](Prop4/HalfScale.lean) | Corrected half-scale threshold in the all-index recursion. DCST, TeX lines 1787–1791. |
| [`Prop4/InducedConnectionTransport`](Prop4/InducedConnectionTransport.lean) | Exact actual connection transport under closed induced extension |
| [`Prop4/InducedCylinders`](Prop4/InducedCylinders.lean) | Original-edge cylinders under finite induced embeddings. Public generalization of the private restriction argument in … |
| [`Prop4/InfiniteDualArm`](Prop4/InfiniteDualArm.lean) | Whole-plane dual arms for the corrected Proposition 4 proof. The actual complementary-dual transform exchanges the frozen wired and free … |
| [`Prop4/IsoRawRecordProbability`](Prop4/IsoRawRecordProbability.lean) | Declarations: `revealRecordEvent_iso_of_covariance`, `sourceBox_raw_conditional_probability_iso` |
| [`Prop4/LatticeCapsuleSupportingLine`](Prop4/LatticeCapsuleSupportingLine.lean) | An admissible supporting line at a maximal upper Euclidean excursion. The tangent direction is obtained from the genuine nearest-point … |
| [`Prop4/LocalMinimum`](Prop4/LocalMinimum.lean) | Discrete descent for Lemma 6. DCST (15 May 2015), TeX lines 1595–1603, the deterministic local-minimum pigeonhole step. The natural height … |
| [`Prop4/LowerBoundaryComparison`](Prop4/LowerBoundaryComparison.lean) | Decreasing events under boundary wiring. Complementation transports the finite FK boundary comparison to lower events. |
| [`Prop4/LowerDualEndpointColumns`](Prop4/LowerDualEndpointColumns.lean) | Exact column witnesses for a lower-dual reached queried endpoint |
| [`Prop4/LowerDualEndpointSeparation`](Prop4/LowerDualEndpointSeparation.lean) | Lower dual access prevents top access avoiding the primal crossing |
| [`Prop4/LowerTraceHull`](Prop4/LowerTraceHull.lean) | The lower filled region of an arbitrary finite trace. Top access is tested by literal lattice walks inside the original box which avoid the … |
| [`Prop4/LowestHeight`](Prop4/LowestHeight.lean) | The actual lowest top-connected height in each column. DCST, TeX lines 1593–1603 (eq:22 and the local-minimum argument). |
| [`Prop4/MarkedArcAlternativeProved`](Prop4/MarkedArcAlternativeProved.lean) | The exact sampled point-mark complementary-arc alternative |
| [`Prop4/MarkedBoxFrontierTrace`](Prop4/MarkedBoxFrontierTrace.lean) | The concrete marked lower trace on the frozen original-box carrier |
| [`Prop4/MarkedBoxRawAccess`](Prop4/MarkedBoxRawAccess.lean) | Actual raw endpoint access on the original sampled box |
| [`Prop4/MarkedBoxRawReveal`](Prop4/MarkedBoxRawReveal.lean) | The actual raw lower-arc stopping record on the original box |
| [`Prop4/MarkedBoxRawSourceIdentity`](Prop4/MarkedBoxRawSourceIdentity.lean) | The unchanged original box records equal the literal source explorations |
| [`Prop4/MarkedBoxTraceNonempty`](Prop4/MarkedBoxTraceNonempty.lean) | Genuine source connections give both existing concrete marked traces |
| [`Prop4/MarkedCellOutsidePorts`](Prop4/MarkedCellOutsidePorts.lean) | Exterior neighbors of a cell frontier cut at two prescribed marks |
| [`Prop4/MarkedFaceFrontierBridge`](Prop4/MarkedFaceFrontierBridge.lean) | Actual sampled frontiers are the restricted finite cell boundaries |
| [`Prop4/MarkedFaceFrontierConnectivity`](Prop4/MarkedFaceFrontierConnectivity.lean) | Actual marked frontier connectivity from literal complementary arc labels |
| [`Prop4/MarkedHalfTurnRawCovariance`](Prop4/MarkedHalfTurnRawCovariance.lean) | Exact half-turn covariance of raw sampled explorations |
| [`Prop4/MarkedHalfTurnSampledBonds`](Prop4/MarkedHalfTurnSampledBonds.lean) | Exact original-bond labels under the sampled dual half-turn |
| [`Prop4/MarkedIsoComposition`](Prop4/MarkedIsoComposition.lean) | Literal configuration relabeling through composed original graph maps |
| [`Prop4/MarkedJointRawPaths`](Prop4/MarkedJointRawPaths.lean) | Both concrete recorded paths persist in the raw two-sided source record |
| [`Prop4/MarkedJointRawReveal`](Prop4/MarkedJointRawReveal.lean) | The common actual raw record for the two marked traces |
| [`Prop4/MarkedLowerCellLabels`](Prop4/MarkedLowerCellLabels.lean) | Exact exterior labels of the marked lower reached-region cells |
| [`Prop4/MarkedLowerDualReveal`](Prop4/MarkedLowerDualReveal.lean) | The actual closed-dual lower-arc reveal with prescribed marks. The original-state reveal specializes the proved multi-seed cluster … |
| [`Prop4/MarkedLowerExcursionTrace`](Prop4/MarkedLowerExcursionTrace.lean) | The two-mark trace observed by the actual raw lower dual reveal |
| [`Prop4/MarkedLowerExcursionWitnesses`](Prop4/MarkedLowerExcursionWitnesses.lean) | All excursion record fields for the actual marked lower dual reveal. The trace is the actual two-mark connecting frontier trace, including … |
| [`Prop4/MarkedLowerFaceCells`](Prop4/MarkedLowerFaceCells.lean) | Finite cell realization of the actual marked lower raw frontier |
| [`Prop4/MarkedLowerFrontierCrossing`](Prop4/MarkedLowerFrontierCrossing.lean) | The prescribed marked lower frontier in the actual original sample |
| [`Prop4/MarkedLowerRecordedPath`](Prop4/MarkedLowerRecordedPath.lean) | Whole-support recorded paths for the actual lower box trace |
| [`Prop4/MarkedLowerRevealHull`](Prop4/MarkedLowerRevealHull.lean) | Filled-region membership of the actual marked raw query endpoints |
| [`Prop4/MarkedLowerRevealMembers`](Prop4/MarkedLowerRevealMembers.lean) | Actual lower-dual access and columns of every marked revealed bond |
| [`Prop4/MarkedRectangleHalfTurn`](Prop4/MarkedRectangleHalfTurn.lean) | Coordinate-faithful half-turn of rectangles and their sampled faces |
| [`Prop4/MarkedRectangleRawAccess`](Prop4/MarkedRectangleRawAccess.lean) | Actual raw endpoints avoid top access to the concrete marked trace |
| [`Prop4/MarkedUpperBoxTrace`](Prop4/MarkedUpperBoxTrace.lean) | The actual upper trace as inverse half-turn transport of the lower trace |
| [`Prop4/MarkedUpperRawAccess`](Prop4/MarkedUpperRawAccess.lean) | Bottom inaccessibility for actual upper raw query endpoints |
| [`Prop4/MarkedUpperRecordedPath`](Prop4/MarkedUpperRecordedPath.lean) | Whole-support recorded paths for the actual upper box trace |
| [`Prop4/MarkedUpperTraceAccess`](Prop4/MarkedUpperTraceAccess.lean) | Exact upper trace labels for the lower-access half-turn bridge |
| [`Prop4/MaskedConfinedWalk`](Prop4/MaskedConfinedWalk.lean) | Declarations: `masked_walk_of_confined` |
| [`Prop4/MaximalConvolutionCost`](Prop4/MaximalConvolutionCost.lean) | The final n^4 coefficient and exact convolution cutoff. The genuine source-record inequality loses only a parameter-only coefficient. |
| [`Prop4/MaximalExcursionSupportingLine`](Prop4/MaximalExcursionSupportingLine.lean) | The original maximal Euclidean excursion has an admissible upper tangent. The source maximizing event is unchanged. |
| [`Prop4/MaximalRecordSplitBound`](Prop4/MaximalRecordSplitBound.lean) | The maximal source-record split-arm estimate. The upper-arm probability, sampled complementary star screen, surgery and free-cluster … |
| [`Prop4/MaximalRecordUpperArmBound`](Prop4/MaximalRecordUpperArmBound.lean) | The maximal-excursion upper-arm bound on selected actual source records. The complete observation selects the source event. |
| [`Prop4/MaximalRootStarPorts`](Prop4/MaximalRootStarPorts.lean) | Actual sampled star roots at a maximal upper excursion. An original vertex is an actual dual face port except at the unused upper right … |
| [`Prop4/MaximalStripCrop`](Prop4/MaximalStripCrop.lean) | A physical dual crop rooted at an arbitrary lattice face. Translation uses both coordinates of the actual maximal vertex. |
| [`Prop4/MaximalStripCropComparison`](Prop4/MaximalStripCropComparison.lean) | The actual widened-strip touch bound after physical cropping. The actual maximal-root target is outside the physical crop. Every escape … |
| [`Prop4/MaximalStripDeletedEmbedding`](Prop4/MaximalStripDeletedEmbedding.lean) | An actual-root strip avoids all revealed original bonds below its tangent. This comparison permits arbitrary rectangle reveals. |
| [`Prop4/MaximalStripReferenceExit`](Prop4/MaximalStripReferenceExit.lean) | A genuine sampled dual exit above the maximal supporting line. The finite touch lower bound passes through the literal crop, its deleted … |
| [`Prop4/MaximalStripRestoredArm`](Prop4/MaximalStripRestoredArm.lean) | The maximal-root arm in every original conditional sample. Exact dual transport gives the arm in the all-open reference fiber. |
| [`Prop4/MaximalStripSeparation`](Prop4/MaximalStripSeparation.lean) | First exits and wired targets for a strip at an arbitrary physical root. The widened local scale leaves every wired strip vertex outside … |
| [`Prop4/MaximalTouchCost`](Prop4/MaximalTouchCost.lean) | Uniform polynomial cost of the actual maximal-root touch comparison. The widened local scale is bounded by eight times the source scale. |
| [`Prop4/MaximalTraceUpperArm`](Prop4/MaximalTraceUpperArm.lean) | The actual Euclidean maximal event supplies its upper-arm comparison. A columnwise lower reveal lies below the genuine capsule tangent … |
| [`Prop4/MaximalUpperArmLowerBound`](Prop4/MaximalUpperArmLowerBound.lean) | Upper complementary sampled arm at every actual maximal root. A root in the original square either has its own sampled star port or is the … |
| [`Prop4/ObservedBetweenTraceEvent`](Prop4/ObservedBetweenTraceEvent.lean) | Declarations: `betweenTubeTraceEvent_observation_invariant`, `betweenTubeTraceEvent_eq_observation_preimage` |
| [`Prop4/ObservedExcursionConvolution`](Prop4/ObservedExcursionConvolution.lean) | The actual trace excursion bound without a record-cover input. The complete observation determines the trace. |
| [`Prop4/ObservedMaximalExcursion`](Prop4/ObservedMaximalExcursion.lean) | Exact maximal-excursion events on complete path observations. The observed event is the image of the actual maximal event. |
| [`Prop4/ObservedSourceCompletion`](Prop4/ObservedSourceCompletion.lean) | Source completion from observed sample data |
| [`Prop4/OddSquare`](Prop4/OddSquare.lean) | The genuine odd-square comparison in the remark after Lemma 7. DCST, TeX lines 1761–1767. |
| [`Prop4/OneArmRatio`](Prop4/OneArmRatio.lean) | A uniform adjacent-radius bound for the frozen free one-arm probability. The proof uses four whole-face events, translation invariance and … |
| [`Prop4/OpenCorridorChain`](Prop4/OpenCorridorChain.lean) | Finite chains of actual corridor crossings. Each horizontal walk remains unchanged. |
| [`Prop4/OpenCorridorGluing`](Prop4/OpenCorridorGluing.lean) | Original open walks glued inside an arbitrary corridor. The planar intersection step comes from `PlanarTopology`. |
| [`Prop4/PairKernel`](Prop4/PairKernel.lean) | The Lemma-7 square-pair expression and its exact reweighting. DCST, equations (24), (29)–(32), and TeX lines 1775–1782. |
| [`Prop4/PlaneCylinderCriterion`](Prop4/PlaneCylinderCriterion.lean) | Weak convergence from the actual all-open cylinder coordinates |
| [`Prop4/PolynomialDiagonalPenalty`](Prop4/PolynomialDiagonalPenalty.lean) | Declarations: `exists_diagonal_penalty_of_polynomial_lower` |
| [`Prop4/PolynomialPairPackage`](Prop4/PolynomialPairPackage.lean) | Declarations: `evenSquarePairKernel_package_of_polynomial_lower` |
| [`Prop4/PositiveLowerFaceAccess`](Prop4/PositiveLowerFaceAccess.lean) | Nonempty trace-complement access to an incident reached face. Appending the queried bond avoids a zero-length interpolation corner case. |
| [`Prop4/PowerCutoff`](Prop4/PowerCutoff.lean) | The rounded, half-scale power cutoff. The source's even recursion has real lower threshold n^ε. |
| [`Prop4/PrecedingTail`](Prop4/PrecedingTail.lean) | Pairing odd squares with the following even square. The source remark controls side 2m-1 by side 2m, both at arm scale m. |
| [`Prop4/PrimalHalfEdgeAvoidance`](Prop4/PrimalHalfEdgeAvoidance.lean) | Access from a primal edge midpoint to an unvisited endpoint |
| [`Prop4/ProductMaximum`](Prop4/ProductMaximum.lean) | Attainment of product suprema for zero-limit nonnegative sequences. DCST, TeX lines 1780–1791. |
| [`Prop4/RadiusTube`](Prop4/RadiusTube.lean) | Radius-parametrized tubes for the corrected split proof. The source Euclidean tube is retained unchanged. |
| [`Prop4/RadiusTubeSurgery`](Prop4/RadiusTubeSurgery.lean) | Closing costs for the corrected wider tube. The radius-four enlargement restores the source square-arm cutoff while retaining a … |
| [`Prop4/RawBetweenBulk`](Prop4/RawBetweenBulk.lean) | Declarations: `between_trace_bulk_bound_of_touch` |
| [`Prop4/RawBetweenCoreLower`](Prop4/RawBetweenCoreLower.lean) | Declarations: `between_trace_core_probability_mul_le_confined` |
| [`Prop4/RawCentralDomain`](Prop4/RawCentralDomain.lean) | The marked recorded class and all its remaining edge components |
| [`Prop4/RawCentralLaw`](Prop4/RawCentralLaw.lean) | Exact wired law on the whole marked raw retained union |
| [`Prop4/RawCentralReferenceComparison`](Prop4/RawCentralReferenceComparison.lean) | Wired rectangle comparison for the whole marked raw union |
| [`Prop4/RawCentralReplayRetention`](Prop4/RawCentralReplayRetention.lean) | Literal raw replay stays in the edge-defined marked union |
| [`Prop4/RawCentralRestoration`](Prop4/RawCentralRestoration.lean) | Literal fresh-edge restriction and restoration on the marked union |
| [`Prop4/RawCentralRestoredComparison`](Prop4/RawCentralRestoredComparison.lean) | Restored-event comparison under the unchanged raw observation |
| [`Prop4/RawCentralRestoredWalk`](Prop4/RawCentralRestoredWalk.lean) | Confined full raw replay walks survive literal central restoration |
| [`Prop4/RawComponentBoundaryPartition`](Prop4/RawComponentBoundaryPartition.lean) | The exact wired partition on each raw remaining component |
| [`Prop4/RawConfinedReplayComparison`](Prop4/RawConfinedReplayComparison.lean) | Confined full raw replay compared with the genuine stopped source law |
| [`Prop4/RawDualFiniteFit`](Prop4/RawDualFiniteFit.lean) | Literal sampled labels agree with the existing finite raw exploration |
| [`Prop4/RawExploredExterior`](Prop4/RawExploredExterior.lean) | The connected geometric exterior of the raw two-sided exploration |
| [`Prop4/RawFaceBoundaryBounds`](Prop4/RawFaceBoundaryBounds.lean) | Original rectangle bounds for every raw unreached-component boundary |
| [`Prop4/RawFaceBoundaryRetained`](Prop4/RawFaceBoundaryRetained.lean) | Raw unreached-component boundary bonds are recorded open original bonds |
| [`Prop4/RawFaceBoundaryWiring`](Prop4/RawFaceBoundaryWiring.lean) | Actual recorded wiring of each raw unreached face-component boundary |
| [`Prop4/RawFaceComponentCycles`](Prop4/RawFaceComponentCycles.lean) | Single actual boundary cycles of the raw unexplored face components |
| [`Prop4/RawFaceEdgeDomain`](Prop4/RawFaceEdgeDomain.lean) | Raw edge domains of a sampled dual face region |
| [`Prop4/RawLowerFrontierFit`](Prop4/RawLowerFrontierFit.lean) | Source face regions fit the existing marked lower raw frontier exactly |
| [`Prop4/RawMarkedBetweenTransfer`](Prop4/RawMarkedBetweenTransfer.lean) | Averaging actual raw middle transfer over the source between event |
| [`Prop4/RawMarkedMiddleGeometry`](Prop4/RawMarkedMiddleGeometry.lean) | Actual raw trace attachments to the access-defined middle |
| [`Prop4/RawMarkedMiddleLaw`](Prop4/RawMarkedMiddleLaw.lean) | Exact wired middle marginal under the actual raw induced law |
| [`Prop4/RawMarkedStoppedLaw`](Prop4/RawMarkedStoppedLaw.lean) | The exact stopped law for the two uncompleted marked arc explorations |
| [`Prop4/RawMarkedTraceAccess`](Prop4/RawMarkedTraceAccess.lean) | Actual source trace access barriers for the unchanged raw record |
| [`Prop4/RawMaskedBridgeGluing`](Prop4/RawMaskedBridgeGluing.lean) | Declarations: `sourceMarkedRaw_masked_connection_of_query_exit_heights` |
| [`Prop4/RawPhysicalBoundary`](Prop4/RawPhysicalBoundary.lean) | Physical rectangle boundary vertices touch the raw record |
| [`Prop4/RawQueryTubeSides`](Prop4/RawQueryTubeSides.lean) | Raw queried endpoints outside the tube retain their proper source side |
| [`Prop4/RawRecordedFaceRegion`](Prop4/RawRecordedFaceRegion.lean) | Actual raw face regions agree with their recorded face regions |
| [`Prop4/RawRemainingBoundaryWiring`](Prop4/RawRemainingBoundaryWiring.lean) | Actual boundary wiring on each remaining raw primal-edge component |
| [`Prop4/RawRemainingFaceComponents`](Prop4/RawRemainingFaceComponents.lean) | Each remaining primal component has one actual unreached face component |
| [`Prop4/RawReplayDualBridge`](Prop4/RawReplayDualBridge.lean) | Transferring a masked raw-replay dual bridge back to the reference |
| [`Prop4/RawReplayExitHeight`](Prop4/RawReplayExitHeight.lean) | Declarations: `rectangle_mask_omitted_endpoint`, `sampledRawDual_masked_replay_exit_height_le`, `sampledRawDual_masked_replay_exit_height_ge` |
| [`Prop4/RawReplayRegionExit`](Prop4/RawReplayRegionExit.lean) | Declarations: `sampledRawDual_masked_replay_exit` |
| [`Prop4/RawSourceDecay`](Prop4/RawSourceDecay.lean) | Declarations: `dualityQ_corrected_of_touch` |
| [`Prop4/RawSourcePairKernel`](Prop4/RawSourcePairKernel.lean) | Declarations: `source_pair_kernel_of_touch` |
| [`Prop4/RawStoppedComponentLaw`](Prop4/RawStoppedComponentLaw.lean) | Exact wired component laws conditioned on the raw exploration record |
| [`Prop4/RecordedConnectingFrontierTrace`](Prop4/RecordedConnectingFrontierTrace.lean) | The whole frontier trace connecting two prescribed marks. Intersecting the two actual components describes exactly the vertices that can … |
| [`Prop4/RecordedDualFaceFrontier`](Prop4/RecordedDualFaceFrontier.lean) | The original-edge frontier of a recorded closed-dual region. The region consists of actual recorded closed-dual walks from the supplied … |
| [`Prop4/RecordedExcursionConvolution`](Prop4/RecordedExcursionConvolution.lean) | The actual excursion bound from recorded primal and dual walks. The trace is the full support of an actual recorded open path. |
| [`Prop4/RecordedExcursionWitnesses`](Prop4/RecordedExcursionWitnesses.lean) | Primitive recorded-walk data for the excursion branch. This predicate lists only the source reveal, its observed trace, and actual recorded … |
| [`Prop4/RecordedFrontierComponentTrace`](Prop4/RecordedFrontierComponentTrace.lean) | The canonical whole recorded-frontier component trace. The trace is defined by component membership, without choosing a path. |
| [`Prop4/RecordedFrontierTraceArms`](Prop4/RecordedFrontierTraceArms.lean) | Literal recorded lower arms along a frontier walk |
| [`Prop4/RecordedObservationConnectivity`](Prop4/RecordedObservationConnectivity.lean) | Declarations: `actual_connection_of_same_observation`, `observation_preimage_image_eq` |
| [`Prop4/RecordedSampledDualGraph`](Prop4/RecordedSampledDualGraph.lean) | Actual sampled dual bonds fixed closed by a source record. Every edge crosses an original sampled bond in the reveal but outside its … |
| [`Prop4/RecordedWalkConnections`](Prop4/RecordedWalkConnections.lean) | Declarations: `actual_connections_of_recorded_walk` |
| [`Prop4/RecordedWalkPullback`](Prop4/RecordedWalkPullback.lean) | Pullback of actual recorded walks and their whole supports |
| [`Prop4/RectangleComplementaryStarConvolution`](Prop4/RectangleComplementaryStarConvolution.lean) | The sampled complementary-star convolution in the literal rectangle law. The free law is transported by the coordinate identity. |
| [`Prop4/RectangleCutSurvival`](Prop4/RectangleCutSurvival.lean) | Actual endpoint arms surviving any sampled column cut. Adapted from the existing TubeArms proof. |
| [`Prop4/RectangleDeletedReferenceGraph`](Prop4/RectangleDeletedReferenceGraph.lean) | The actual geometry of the deleted all-open reference. The complementary configuration of the whole reveal is exactly the retained dual … |
| [`Prop4/RectangleExteriorConnectivity`](Prop4/RectangleExteriorConnectivity.lean) | Connected exterior face labels of a finite lattice rectangle |
| [`Prop4/RectangleFrozenDuality`](Prop4/RectangleFrozenDuality.lean) | Exact dual law after opening every revealed original bond. The crossing dual bonds are conditioned closed. |
| [`Prop4/RectangleNoncrossingEscape`](Prop4/RectangleNoncrossingEscape.lean) | Rectangle noncrossing forces an actual closed-dual escape. The candidates are the w genuine bottom face ports. |
| [`Prop4/RectangleSampledDualBridge`](Prop4/RectangleSampledDualBridge.lean) | Finite and literal sampled dual walks on the same original edges |
| [`Prop4/RectangleTubeCutRows`](Prop4/RectangleTubeCutRows.lean) | Genuine sampled rows of the transported central tube cut. Every row supplies an original horizontal rectangle bond. |
| [`Prop4/RectangleTubeRevealMembership`](Prop4/RectangleTubeRevealMembership.lean) | Endpoint characterization on the actual rectangle reveal carrier. Coordinate transport retains exactly the tube's internal original bonds … |
| [`Prop4/RectangleWiredCrossing`](Prop4/RectangleWiredCrossing.lean) | Actual wired-plane rectangle crossings from the free arm bound. Finite noncrossing forces a genuine complementary dual arm from one of w … |
| [`Prop4/Recursion`](Prop4/Recursion.lean) | The numeric final induction of Proposition 4. DCST (15 May 2015), TeX lines 1793–1822. |
| [`Prop4/RegionBridgeExtraction`](Prop4/RegionBridgeExtraction.lean) | Removing internal region edges from a bridge between two regions |
| [`Prop4/RetainedCentralRowEdge`](Prop4/RetainedCentralRowEdge.lean) | Every eligible connector row is genuinely sampled and can be closed. The row edge is constructed directly from its two physical endpoints. |
| [`Prop4/RetainedCentralRows`](Prop4/RetainedCentralRows.lean) | Actual retained original connector bonds indexed by central rows. The set contains exactly the still-sampled original horizontal bonds in … |
| [`Prop4/ReweightedKernel`](Prop4/ReweightedKernel.lean) | Extracting the product factor from the source convolution. DCST, TeX lines 1775–1785. |
| [`Prop4/ReweightedSummability`](Prop4/ReweightedSummability.lean) | Actual summability of the reweighted source tails |
| [`Prop4/SafeReferenceArmProbability`](Prop4/SafeReferenceArmProbability.lean) | Actual sampled complementary-arc probability in the primal reference fiber. The literal deleted-dual law and actual safe exit path … |
| [`Prop4/SafeReferenceArmTransport`](Prop4/SafeReferenceArmTransport.lean) | Actual complementary-arc arms from a restored reference exit path. A nontrivial sampled exit supplies its actual incident original bond. |
| [`Prop4/SampledArmCorrelation`](Prop4/SampledArmCorrelation.lean) | Individual dual arms on the actual sampled rectangle carrier. Both arms use the same original sample. |
| [`Prop4/SampledBondAccessGeometry`](Prop4/SampledBondAccessGeometry.lean) | Actual midpoint access for original sampled rectangle bonds |
| [`Prop4/SampledCutClosingProduct`](Prop4/SampledCutClosingProduct.lean) | Closing cost and the full complementary-arc cut product. The original connection may be destroyed by closing the cut. |
| [`Prop4/SampledCutInfiniteProduct`](Prop4/SampledCutInfiniteProduct.lean) | The central cut reference estimate in frozen infinite-volume form. The two entire column target events are compared to their requested … |
| [`Prop4/SampledCutProduct`](Prop4/SampledCutProduct.lean) | Complementary-boundary-arc cut separation and the free product bound. Every arm step crosses a sampled original bond. |
| [`Prop4/SampledCutReferenceProduct`](Prop4/SampledCutReferenceProduct.lean) | The sampled cut product with one all-open reference state. The source connection uses only a prescribed set of revealed edges. |
| [`Prop4/SampledRawDualRegion`](Prop4/SampledRawDualRegion.lean) | The raw sampled closed-dual exploration on an edge-defined domain |
| [`Prop4/SampledRectangleDualArms`](Prop4/SampledRectangleDualArms.lean) | Dual arms retaining a closed sampled original bond at every step. Unlike an agreeing whole-plane completion, this carrier adds no unsampled … |
| [`Prop4/SampledStarPorts`](Prop4/SampledStarPorts.lean) | Actual sampled star ports at every rectangle vertex. Ports are faces of genuine retained incident bonds. |
| [`Prop4/SideArmExtension`](Prop4/SideArmExtension.lean) | One-edge extension of actual side arms |
| [`Prop4/SideArmGeometry`](Prop4/SideArmGeometry.lean) | Four side arms and outward extension. This implements the actual events used for an adjacent-radius finite-energy bound. |
| [`Prop4/SlopeComparison`](Prop4/SlopeComparison.lean) | Exact finite lattice geometry within a slope cell. The same-cell representative preserves every supporting-line comparison in columns … |
| [`Prop4/SlopeProbability`](Prop4/SlopeProbability.lean) | Exact finite-law invariance inside a slope cell. Both the induced vertex carrier and its digital wired arc are unchanged. |
| [`Prop4/SmallScale`](Prop4/SmallScale.lean) | Finite-scale completion of Lemma 7. DCST, TeX line 1759, the final step of the proof of Lemma 7. |
| [`Prop4/SourceBoxRawCoreGluing`](Prop4/SourceBoxRawCoreGluing.lean) | Declarations: `sourceBox_raw_replay_strict_core_gluing` |
| [`Prop4/SourceBoxRawCoreProbability`](Prop4/SourceBoxRawCoreProbability.lean) | Declarations: `sourceBox_raw_record_core_probability_le_confined` |
| [`Prop4/SourceMiddleDomain`](Prop4/SourceMiddleDomain.lean) | The source middle domain defined by access avoiding the two traces. Vertices on either trace are retained. |
| [`Prop4/SourceRevealExtension`](Prop4/SourceRevealExtension.lean) | Completing source records by a deterministic function of the raw record. The extra queried edges can depend on the already recorded set and … |
| [`Prop4/SplitBoundaryArms`](Prop4/SplitBoundaryArms.lean) | Corrected square-boundary arms after splitting at z. These are actual connections in one modified configuration, at square radii whose sum … |
| [`Prop4/SplitRadius`](Prop4/SplitRadius.lean) | The Euclidean/square-radius issue in the split-at-z step. Source lines 1695–1709 infer square-arm cutoffs from Euclidean distance to [u,v]. |
| [`Prop4/SplitScreenBound`](Prop4/SplitScreenBound.lean) | Split-arm convolution from an actual separating screen. Four-edge surgery, simultaneous surviving arms and cluster factorization are proved … |
| [`Prop4/SplitSurgery`](Prop4/SplitSurgery.lean) | The genuine four-edge split surgery. The geometric tube margin gives the exact real cutoff after rounding. |
| [`Prop4/SplitWeight`](Prop4/SplitWeight.lean) | The diagonal and off-diagonal weights in Proposition 4. DCST, TeX lines 1775–1783. |
| [`Prop4/SquareEscape`](Prop4/SquareEscape.lean) | Exact real-radius rounding for square-lattice escape. A real square-radius escape is precisely a hit of the integer ceiling boundary. |
| [`Prop4/StableRecordDualArms`](Prop4/StableRecordDualArms.lean) | Actual dual-arm correlation under a stable exploration record. The law is obtained by conditioning the original finite FK PMF on the … |
| [`Prop4/StableRecordOriginalLaw`](Prop4/StableRecordOriginalLaw.lean) | Exact restoration of the original conditional record law. Restoring the recorded open edges after reading the remaining sample gives the … |
| [`Prop4/StarIsoTransport`](Prop4/StarIsoTransport.lean) | Sampled star surgery under a graph isomorphism. The transported star consists of the same original incident bonds. |
| [`Prop4/StoppedJointLowerBound`](Prop4/StoppedJointLowerBound.lean) | Selected complete records retain their source event in lower-bound averaging. The original conditional law is supported on its exact … |
| [`Prop4/StoppedReferenceArmProbability`](Prop4/StoppedReferenceArmProbability.lean) | Both actual stopped reference roots have complementary-arc arms. A root already on its correct physical arc has a length-zero sampled arm. |
| [`Prop4/StoppedReferenceArmsProduct`](Prop4/StoppedReferenceArmsProduct.lean) | The two actual stopped reference arms occur in the same restored sample. The exact normalized frozen fiber has proved positive correlation … |
| [`Prop4/StretchedSummability`](Prop4/StretchedSummability.lean) | Polynomial weights against stretched exponentials. DCST, the omitted analytic summation in Proposition 4, TeX line 1783. |
| [`Prop4/StrictBandDualExclusion`](Prop4/StrictBandDualExclusion.lean) | Declarations: `strict_affine_band_excludes_sampled_dual_bridge` |
| [`Prop4/SummationDecay`](Prop4/SummationDecay.lean) | The complete numerical summation-to-decay argument. DCST, TeX lines 1775–1822, with the rounded half-scale cutoff and attained maxima. |
| [`Prop4/SupportingLineArmTarget`](Prop4/SupportingLineArmTarget.lean) | A sampled upper-half-plane exit has the correct complementary target. Every nontrivial arm uses the two actual faces of its last sampled … |
| [`Prop4/SupportingLineExteriorArc`](Prop4/SupportingLineExteriorArc.lean) | Exact complementary-arc selection above a supporting line. Both adjacent face labels are used. |
| [`Prop4/TailEnvelope`](Prop4/TailEnvelope.lean) | The genuine tail supremum in Proposition 4. DCST, TeX lines 1791–1821. |
| [`Prop4/TailRecursion`](Prop4/TailRecursion.lean) | Truncating a monotone tail-envelope recursion. DCST (15 May 2015), TeX lines 1793–1821. |
| [`Prop4/TiltedBondReflection`](Prop4/TiltedBondReflection.lean) | Reflection of the actual primal bonds and their adjacent dual faces. The primal normalized bond base and dual face label have different … |
| [`Prop4/TiltedBoundaryLimits`](Prop4/TiltedBoundaryLimits.lean) | Arbitrary admissible lateral partitions share the same tilted weak limit |
| [`Prop4/TiltedCandidates`](Prop4/TiltedCandidates.lean) | Corrected finite candidate set in Lemma 6. DCST, TeX lines 1601–1608. |
| [`Prop4/TiltedClosedExtension`](Prop4/TiltedClosedExtension.lean) | Exact actual strip graph of a closed finite-window extension |
| [`Prop4/TiltedConnectionEvents`](Prop4/TiltedConnectionEvents.lean) | Actual top-connection events in the tilted strip. The source's lowest-height events use paths on the infinite original graph. |
| [`Prop4/TiltedCutScan`](Prop4/TiltedCutScan.lean) | A genuine stopping exploration of tilted cuts. The scan algorithm is reused from FKC's parameter-independent combinatorics. |
| [`Prop4/TiltedCutSeparation`](Prop4/TiltedCutSeparation.lean) | Tilted closed cuts separate actual open paths. The geometric scan bound holds under every finite boundary partition and at every … |
| [`Prop4/TiltedCuts`](Prop4/TiltedCuts.lean) | Actual horizontal edge cuts in tilted windows. A cut between columns k and k+1 consists of precisely the original horizontal edges at … |
| [`Prop4/TiltedCylinderUpper`](Prop4/TiltedCylinderUpper.lean) | Averaging actual stopped cylinders with the geometric scan error |
| [`Prop4/TiltedFrozenInterval`](Prop4/TiltedFrozenInterval.lean) | The exact top-only law between two closed tilted cuts. A genuine frozen state of every non-inner edge is used. |
| [`Prop4/TiltedGeometry`](Prop4/TiltedGeometry.lean) | Digital boundary geometry of the tilted strip. The supporting lines need not contain lattice vertices. |
| [`Prop4/TiltedIncidentEvents`](Prop4/TiltedIncidentEvents.lean) | Finite support and clopenness of tilted-strip isolation. Only the original edges in a one-box collar of the bounded target are needed. |
| [`Prop4/TiltedInterval`](Prop4/TiltedInterval.lean) | The actual induced interval between two tilted closed cuts |
| [`Prop4/TiltedIntervalCylinders`](Prop4/TiltedIntervalCylinders.lean) | Dominating the actual interval cylinders by the top-only strip limit |
| [`Prop4/TiltedIntervalInterior`](Prop4/TiltedIntervalInterior.lean) | Interior geometry for the actual scanned tilted interval |
| [`Prop4/TiltedIsolationClopen`](Prop4/TiltedIsolationClopen.lean) | Clopenness and exact finite-extension preimage of the original A(x) |
| [`Prop4/TiltedIsolationComparison`](Prop4/TiltedIsolationComparison.lean) | The infinite tilted-strip isolation comparison, eq. (23). The exact isolation event is clopen by finite incident-edge locality. |
| [`Prop4/TiltedLaw`](Prop4/TiltedLaw.lean) | Constructing the intrinsic-top tilted law on a common plane carrier. Adapted from the RSW.StripLaw proof: literal closed extension of each … |
| [`Prop4/TiltedLimit`](Prop4/TiltedLimit.lean) | Genuine tilted-strip cylinder-limit construction. Adapted from the RSW.StripLimit proof, preserving actual original edge patterns on … |
| [`Prop4/TiltedMonotone`](Prop4/TiltedMonotone.lean) | Intrinsic-top comparison for tilted box windows. Specializes the RSW.StripMonotone argument to actual tilted windows. |
| [`Prop4/TiltedRecordSuccess`](Prop4/TiltedRecordSuccess.lean) | The complete record fixes success and the surviving interval |
| [`Prop4/TiltedReflection`](Prop4/TiltedReflection.lean) | Actual point reflection of the tilted strip. Reflection through (0,N/2) preserves the original lattice and exchanges its digital top and … |
| [`Prop4/TiltedRemovedCuts`](Prop4/TiltedRemovedCuts.lean) | Every tested exterior cut is among the removed interval edges |
| [`Prop4/TiltedScanFailure`](Prop4/TiltedScanFailure.lean) | Quantitative probability of failed two-sided tilted-cut exploration |
| [`Prop4/TiltedSelfDual`](Prop4/TiltedSelfDual.lean) | The constructed tilted law and explicit self-dual specialization. A law is selected only from proved UNIQUE existence. |
| [`Prop4/TiltedSideComparison`](Prop4/TiltedSideComparison.lean) | The top-only finite tilted law is below the side-wired law |
| [`Prop4/TiltedSideCylinders`](Prop4/TiltedSideCylinders.lean) | Cylinder convergence independent of the artificial side wiring |
| [`Prop4/TiltedStoppedCylinders`](Prop4/TiltedStoppedCylinders.lean) | Actual cylinder comparison on a successful two-sided stopping record |
| [`Prop4/TiltedStoppedInterval`](Prop4/TiltedStoppedInterval.lean) | The exact surviving-interval law on the genuine two-sided scan record |
| [`Prop4/TiltedTwoCutReveal`](Prop4/TiltedTwoCutReveal.lean) | A complete exterior stopping record between two scanned closed cuts. Successful left/right scans retain their surviving interval and reveal … |
| [`Prop4/TiltedWindow`](Prop4/TiltedWindow.lean) | Actual tilted-strip carriers and finite mixed-boundary laws. DCST, TeX lines 1563–1573. |
| [`Prop4/TouchHalfConsumer`](Prop4/TouchHalfConsumer.lean) | Touch consumers after discharging the infinite strip comparison. The explored-strip comparison is discharged by … |
| [`Prop4/TouchIsolation`](Prop4/TouchIsolation.lean) | The actual A(x) event and the deterministic local-minimum implication. DCST, TeX lines 1590–1604. |
| [`Prop4/TouchOnlyAssemblyConsumer`](Prop4/TouchOnlyAssemblyConsumer.lean) | Declarations: `p4toP5RemainingGeometryProvider_of_touch` |
| [`Prop4/TouchOnlyPairDichotomy`](Prop4/TouchOnlyPairDichotomy.lean) | Declarations: `evenSquarePairKernel_package_of_touch` |
| [`Prop4/TouchOnlyPairPackage`](Prop4/TouchOnlyPairPackage.lean) | Declarations: `evenSquarePairKernel_package_of_touch_and_stretchedDecay` |
| [`Prop4/TouchUnion`](Prop4/TouchUnion.lean) | The corrected finite union and averaging step for Lemma 6. DCST, TeX lines 1601–1610. |
| [`Prop4/TraceAccessHalfTurn`](Prop4/TraceAccessHalfTurn.lean) | Exact half-turn transport of trace-avoiding boundary access |
| [`Prop4/TraceEndpointConnector`](Prop4/TraceEndpointConnector.lean) | A sampled crossing-bond connector to an unvisited primal endpoint |
| [`Prop4/TraceHullTubeSide`](Prop4/TraceHullTubeSide.lean) | Filled trace access regions retain the source side outside the tube |
| [`Prop4/TranslatedArcSupport`](Prop4/TranslatedArcSupport.lean) | Literal translated-window boundary support for the direct comparison. Intrinsic top wiring of the ambient strip can enter a lower … |
| [`Prop4/TranslatedContainment`](Prop4/TranslatedContainment.lean) | Explicit ambient containment and the finite source comparison bound |
| [`Prop4/TranslatedInfiniteArm`](Prop4/TranslatedInfiniteArm.lean) | Whole translated arm events under frozen limits. The entire target event is translated at once. |
| [`Prop4/TranslatedWindow`](Prop4/TranslatedWindow.lean) | Translated tilted windows and their actual exit edges. DCST, the event A(x), TeX lines 1590–1604. |
| [`Prop4/TranslatedWindowIso`](Prop4/TranslatedWindowIso.lean) | Actual translated-window graph and wired-target law. Translation identifies the entire target with its nested induced graph once the … |
| [`Prop4/TubeActualReferenceSafeExit`](Prop4/TubeActualReferenceSafeExit.lean) | The safe-exit lower bound in the genuine sampled reference law. Stop the ambient path at its first physical exterior face and use the exact … |
| [`Prop4/TubeBoundaryArms`](Prop4/TubeBoundaryArms.lean) | The n and n-1 endpoint arms in the same cut configuration. This module defines the primal endpoint-arm event `finiteEndpointArmEvent` used … |
| [`Prop4/TubeCentralRetainedBonds`](Prop4/TubeCentralRetainedBonds.lean) | Retained vertical connectors outside the literal central cut. At every physical row outside the cut interval, the horizontal crossed … |
| [`Prop4/TubeColumnConvex`](Prop4/TubeColumnConvex.lean) | Consecutive rows in the literal central tube cut. A Euclidean tube is a thickening of a convex segment. |
| [`Prop4/TubeConfinedExponentialBound`](Prop4/TubeConfinedExponentialBound.lean) | Exponential comparison for the actual tube-confined connection. The cost is uniform over opposite-side endpoints and every positive scale. |
| [`Prop4/TubeConnectionTouchBound`](Prop4/TubeConnectionTouchBound.lean) | A tube-confined connection is bounded by the infinite arm product. Both cuts use the same nonempty interval of central rows. |
| [`Prop4/TubeConnectorArmProbability`](Prop4/TubeConnectorArmProbability.lean) | Paying the retained connector cost in the exact reference fiber. The closed-edge event and both stopped arms occur in one remaining-graph … |
| [`Prop4/TubeConnectorCost`](Prop4/TubeConnectorCost.lean) | Exact count and finite-energy cost of both retained connectors. Only actual remaining original edges are counted. |
| [`Prop4/TubeConnectorHeights`](Prop4/TubeConnectorHeights.lean) | Safe affine connector heights and their true lengths. The endpoints of the actual cut lie within the tube's proved width. |
| [`Prop4/TubeCut`](Prop4/TubeCut.lean) | The literal central cut of the tube. The source cut at x=1/2 consists of the horizontal edges (0,y)--(1,y) whose two endpoints belong to D. … |
| [`Prop4/TubeCutEndpoints`](Prop4/TubeCutEndpoints.lean) | Exact exterior contacts of the central dual cut. At each extremal row of the cut, its outside face is incident to a vertex outside the … |
| [`Prop4/TubeCutNonempty`](Prop4/TubeCutNonempty.lean) | Nonempty central cuts for opposite-face Euclidean tubes. A rounded height at the midpoint belongs to both central columns when the radius … |
| [`Prop4/TubeEventSplit`](Prop4/TubeEventSplit.lean) | Lemma 7's three-event decomposition for finite box traces. The trace arguments are explicit. |
| [`Prop4/TubeExcursion`](Prop4/TubeExcursion.lean) | Farthest-vertex decomposition of a genuine tube excursion. This is the deterministic content of equation (27), valid for any finite path … |
| [`Prop4/TubeExitHeights`](Prop4/TubeExitHeights.lean) | Signed heights of actual tube exit arcs. At slopes of absolute value at most one, an original bond changes the supporting-line deviation by … |
| [`Prop4/TubeExitRegions`](Prop4/TubeExitRegions.lean) | Source-oriented upper and lower exit arcs. The source regions use the integer signed area. |
| [`Prop4/TubeGeometry`](Prop4/TubeGeometry.lean) | The actual Euclidean tube in Lemma 7. Source: DCST, proof of Lemma 7, lines 1645–1660. |
| [`Prop4/TubeHalfPlaneEdges`](Prop4/TubeHalfPlaneEdges.lean) | Affine half-planes outside the actual tube reveal. The original Euclidean tube stays within vertical deviation 2r of its supporting line. |
| [`Prop4/TubeHalfTurn`](Prop4/TubeHalfTurn.lean) | Genuine half-turn geometry for the two excursion cases. Negate the original square and exchange the two endpoints. |
| [`Prop4/TubePartition`](Prop4/TubePartition.lean) | The three genuine regions of Lemma 7. For endpoints on opposite vertical faces, every collinear square vertex lies on the endpoint segment. |
| [`Prop4/TubeRectangleReference`](Prop4/TubeRectangleReference.lean) | The literal tube reference estimate at the source radii. The fixed reveal and cut are coordinate images of the original box objects. |
| [`Prop4/TubeReferenceConnectorWalks`](Prop4/TubeReferenceConnectorWalks.lean) | Genuine sampled vertical connectors of the tube reference. Each step crosses an original physical horizontal bond outside the revealed cut … |
| [`Prop4/TubeReferenceSafeExit`](Prop4/TubeReferenceSafeExit.lean) | The actual reference safe-exit bound from the explicit touch bound. The physical crop has a proved lower exit probability and a proved … |
| [`Prop4/TubeRevealedEdges`](Prop4/TubeRevealedEdges.lean) | Revealing every original edge of the literal Euclidean tube. The revealed set contains exactly the original edges with both endpoints in … |
| [`Prop4/TubeSafeExteriorArcs`](Prop4/TubeSafeExteriorArcs.lean) | Safe affine half-planes meet the correct physical exterior arc. The supporting segment remains inside the source box. |
| [`Prop4/TubeSquaredArmBound`](Prop4/TubeSquaredArmBound.lean) | The actual tube probability has the squared-arm term of Lemma 7. Adjacent-radius insertion converts the n,n-1 product without any radius … |
| [`Prop4/TubeStripCropEmbedding`](Prop4/TubeStripCropEmbedding.lean) | Framing the crop inside the physical dual rectangle. The vertex embedding retains exact original face labels. |
| [`Prop4/TubeStripDeletedEmbedding`](Prop4/TubeStripDeletedEmbedding.lean) | The safe physical crop embeds into the actual deleted reference graph. Both endpoints of every cropped edge lie on the safe side. |
| [`Prop4/TubeStripPhysicalCrop`](Prop4/TubeStripPhysicalCrop.lean) | The literal physical crop of a translated or reflected tilted window. The frame has vertical origin c. |
| [`Prop4/TubeStripPhysicalSeparation`](Prop4/TubeStripPhysicalSeparation.lean) | Physical first exits and the widened tilted-window target. The physical face layer separates every cropped strip walk from its exterior. |
| [`Prop4/TubeSurgery`](Prop4/TubeSurgery.lean) | The actual tube cut and its finite-energy surgery cost. All configurations and boundary conditions live on the original finite box. |
| [`Prop4/TubeTraceHalfTurn`](Prop4/TubeTraceHalfTurn.lean) | Exact half-turn transport of the two actual trace excursion events. The original square is rotated and the endpoint order exchanged. |
| [`Prop4/TubeVerticalOrder`](Prop4/TubeVerticalOrder.lean) | Vertical interpolation towards the supporting segment stays in the tube |
| [`Prop4/TubeWidth`](Prop4/TubeWidth.lean) | A uniform literal width bound for Lemma 7's tube. A coarse factor 2 replaces the source's sharp √2. |
| [`Prop4/TwoExteriorPortsParity`](Prop4/TwoExteriorPortsParity.lean) | An even frontier with exactly two exterior ports joins their marks |
| [`Prop4/TwoMarkedOddFrontier`](Prop4/TwoMarkedOddFrontier.lean) | Two prescribed odd frontier vertices lie in one component |
| [`Prop4/UniformConfinedTube`](Prop4/UniformConfinedTube.lean) | Uniform tube-confined bulk crossings under finite wired laws. The domain may be larger than the tube. |
| [`Prop4/UniformCorridorTube`](Prop4/UniformCorridorTube.lean) | Uniform actual wired-plane tube crossings. The cutoff depends only on the assumed decay parameters and fractional exponent. |
| [`Prop4/UniformExcursionConvolution`](Prop4/UniformExcursionConvolution.lean) | The n^6 excursion convolution from actual selected source records. The source event is covered by the selected maximal records. |
| [`Prop4/UniformMaximalRecordConvolution`](Prop4/UniformMaximalRecordConvolution.lean) | One uniform coefficient for all maximal source-record events. The same coefficient works for every scale, cutoff, endpoints and supplied … |
| [`Prop4/UniformStrictInteriorTube`](Prop4/UniformStrictInteriorTube.lean) | Uniform strict-core crossings from a smaller fractional exponent. The existing bulk theorem is applied at epsilon/2. |
| [`Prop4/UniformTail`](Prop4/UniformTail.lean) | Uniform weighted tail sums. A positive increasing weight converts a summable weighted series into a uniform bound for each weighted tail. |
| [`Prop4/UpperExcursionBoundaryRoot`](Prop4/UpperExcursionBoundaryRoot.lean) | Zero-length exits of the actual upper-excursion root. Inside the original square the physical dual boundary consists only of the top and … |
| [`Prop4/UpperHalfPlaneCrossingBond`](Prop4/UpperHalfPlaneCrossingBond.lean) | Genuine crossed bonds above a supporting line. The two dual face labels are the lower-left corners of their physical cells. |
| [`Prop4/VertexStarArms`](Prop4/VertexStarArms.lean) | Primal arms surviving the split at a genuine path vertex. Closing all original edges incident to the selected vertex retains a prefix from … |
| [`Prop4/VerticalRectangleWiredError`](Prop4/VerticalRectangleWiredError.lean) | Vertical rectangle errors for the corridor construction. Coordinate interchange is applied to the genuine frozen wired law and to the … |
| [`Prop4/WeightedDecay`](Prop4/WeightedDecay.lean) | Stretched-exponential decay after reweighting. DCST (15 May 2015), TeX lines 1770–1793, numeric part of the proof of Proposition 4 that the … |
| [`Prop4/WidenedExcursionExponent`](Prop4/WidenedExcursionExponent.lean) | The widened proof tube is an exact instance of the original tube definition. At every scale at least two, any positive radius is a real … |
| [`Prop4/WidenedStripCropComparison`](Prop4/WidenedStripCropComparison.lean) | The actual widened-strip touch bound after physical cropping. The wired target is genuinely outside the physical crop. Every escape hits … |
| [`Prop4/WidenedTouchPenalty`](Prop4/WidenedTouchPenalty.lean) | Absorbing the cropped-strip touch denominator at scale four n plus two. The larger crop contributes a fixed polynomial penalty, uniformly … |
| [`Prop4/WiredTargetComparison`](Prop4/WiredTargetComparison.lean) | Adding vertices while keeping the same single wired target arc |
| [`Prop4/WiredTargetIso`](Prop4/WiredTargetIso.lean) | Exact wired-target probability under a genuine graph isomorphism |
| [`Push/ActiveFrontierBoundary`](Push/ActiveFrontierBoundary.lean) | Declarations: `active_filledFrontier_not_top`, `active_filledFrontier_boundary_avoid` |
| [`Push/ActiveFrontierCarrier`](Push/ActiveFrontierCarrier.lean) | Declarations: `unexaminedVertices`, `activeUnexaminedGraph`, `edgeRestriction_adj_active`, `activeUnexaminedGraph_map_le`, … |
| [`Push/ActiveFrontierComparison`](Push/ActiveFrontierComparison.lean) | Declarations: `reference_active_restriction_le_frontier_wired`, `activeUnexaminedGraph_map_le_edgeRestriction` |
| [`Push/ActiveFrontierLocality`](Push/ActiveFrontierLocality.lean) | Declarations: `mem_filledTopReveal_iff_cellFaces`, `active_mixed_vertex_mem_frontier_wiring` |
| [`Push/ActiveRestrictionRetention`](Push/ActiveRestrictionRetention.lean) | Declarations: `active_restriction_subset_retains_unexamined`, `nested_crossing_of_active_restriction_domination` |
| [`Push/AllHeightTipRecordSelector`](Push/AllHeightTipRecordSelector.lean) | Declarations: `CaseTwoTipEndpointRecord`, `caseTwoTipEndpointSelector`, `caseTwoTipEndpointSelector_eq_some_iff`, `caseTwoTipEndpointSelector_isSome_iff`, … |
| [`Push/AllHeightTipSourceSplit`](Push/AllHeightTipSourceSplit.lean) | Declarations: `caseTwoTipEndpoint_source_connection_or_native` |
| [`Push/AllScaleTransfer`](Push/AllScaleTransfer.lean) | Declarations: `selfDual_round_down_probability_le`, `selfDual_all_scale_bound_of_divisible_bound` |
| [`Push/ArcInternalEdgeErasure`](Push/ArcInternalEdgeErasure.lean) | Declarations: `arcsConnectionEvent_sdiff_internal_edges` |
| [`Push/AsymmetricRectangleComparison`](Push/AsymmetricRectangleComparison.lean) | Declarations: `asymmetric_neighbor_closed`, `asymmetric_boundary_avoid`, `asymmetric_rectangle_enclosing_comparison` |
| [`Push/AttachmentLabelBoundary`](Push/AttachmentLabelBoundary.lean) | Declarations: `frozenBoundary_le_labelKernel_of_local`, `frozen_pullback_partition_le_of_attachment_labels`, `all_frozen_pullback_partitions_le_of_attachment_labels` |
| [`Push/AugmentedOppositeReach`](Push/AugmentedOppositeReach.lean) | Declarations: `mem_pocketAugmented_of_not_opposite_reachable` |
| [`Push/AuxiliaryIndexInvariance`](Push/AuxiliaryIndexInvariance.lean) | Declarations: `rectangle_same_label_adj_index_eq`, `rectangle_constant_region_index_eq` |
| [`Push/AuxiliaryLabelCut`](Push/AuxiliaryLabelCut.lean) | Declarations: `auxiliaryLabelCut`, `mem_auxiliaryLabelCut_iff`, `auxiliaryClosed_labelCut_adj_preserves`, `auxiliaryClosed_labelCut_reachable_preserves`, … |
| [`Push/BaseCrossingTransport`](Push/BaseCrossingTransport.lean) | Declarations: `baseStripEmbedding_preimage`, `baseRestrictedOpenEmbedding`, `strip_crossing_implies_base_restricted_crossing` |
| [`Push/BaseProbabilityCanonical`](Push/BaseProbabilityCanonical.lean) | Declarations: `selfDual_base_probability_eq_canonical` |
| [`Push/BaseStripComparison`](Push/BaseStripComparison.lean) | Declarations: `stripWindow_crossing_probability_le_base`, `selfDual_strip_probability_le_base_at_three_mul`, `selfDual_base_at_three_mul_of_stripRSW` |
| [`Push/BondFaceIndex`](Push/BondFaceIndex.lean) | Declarations: `faceIndexMark`, `rayIndex_bond_faces_eq_of_not_mem`, `rayIndex_bond_faces_ne_of_mem` |
| [`Push/BoolUpperCylinderUniqueness`](Push/BoolUpperCylinderUniqueness.lean) | Declarations: `boolConstantCylinder_isClopen`, `finite_bool_measure_eq_of_upper_cylinders` |
| [`Push/BottomCapPath`](Push/BottomCapPath.lean) | Declarations: `exists_bottom_cap_path` |
| [`Push/BottomCappedCycle`](Push/BottomCappedCycle.lean) | Declarations: `path_start_not_mem_tail`, `exists_bottom_capped_cycle` |
| [`Push/BottomCoreAmbientLaw`](Push/BottomCoreAmbientLaw.lean) | Declarations: `bottomCoreAmbient_removed_edges_wired`, `bottomCoreAmbient_boundary_pullback`, `bottomCoreAmbient_law_restrict` |
| [`Push/BottomCoreBandProbability`](Push/BottomCoreBandProbability.lean) | Declarations: `bottomCoreBand_probability_ge_rectangleBand` |
| [`Push/BottomCoreBandTransfer`](Push/BottomCoreBandTransfer.lean) | Declarations: `bottomCoreBandEvent`, `bottomCoreBandEvent_of_rectangle_band` |
| [`Push/BottomCoreBoundary`](Push/BottomCoreBoundary.lean) | Declarations: `bottomCoreInclusion`, `bottomCoreRetraction`, `bottomCoreRetraction_val`, `bottomCoreRetraction_inclusion`, … |
| [`Push/BottomCoreErasedPathLift`](Push/BottomCoreErasedPathLift.lean) | Declarations: `bottomCoreAmbient_map_le`, `bottomCoreAmbient_erased_open_adj_pullback`, `bottomCoreErasedOpenHom` |
| [`Push/BottomCoreLaw`](Push/BottomCoreLaw.lean) | Declarations: `bottomCoreGraph_map_le`, `bottomCore_law_map` |
| [`Push/BottomCoreMissingSideBonds`](Push/BottomCoreMissingSideBonds.lean) | Declarations: `bottomCoreAmbient_missing_bond_in_threeSideBonds` |
| [`Push/BoundaryPathCodeWitness`](Push/BoundaryPathCodeWitness.lean) | Declarations: `boundaryPathCodeSelector_hasPath` |
| [`Push/CaseTwoCompleteSourceLinear`](Push/CaseTwoCompleteSourceLinear.lean) | Declarations: `caseTwoCompleteSource_linear_of_prefixLocality_and_sourcePaths` |
| [`Push/CaseTwoDisjointTipLocality`](Push/CaseTwoDisjointTipLocality.lean) | Declarations: `caseTwo_selected_disjoint_tip_pos` |
| [`Push/CaseTwoPrecursorFirstHitPath`](Push/CaseTwoPrecursorFirstHitPath.lean) | Declarations: `caseTwoPrecursorFirstHitSelector_original_path` |
| [`Push/CaseTwoPrecursorFirstHitSelector`](Push/CaseTwoPrecursorFirstHitSelector.lean) | Declarations: `caseTwoPrecursorFirstHitSelector`, `caseTwoPrecursorFirstHitSelector_isSome_iff` |
| [`Push/CaseTwoSelectedNativeCrop`](Push/CaseTwoSelectedNativeCrop.lean) | Declarations: `caseTwoTraceCrop_eq_of_native_arms`, `caseTwo_selected_pair_intersects_or_native_crop` |
| [`Push/CaseTwoTipFirstHitPath`](Push/CaseTwoTipFirstHitPath.lean) | Declarations: `caseTwoTipFirstHitSelector_original_path` |
| [`Push/CaseTwoTipFirstHitSelector`](Push/CaseTwoTipFirstHitSelector.lean) | Declarations: `caseTwoTipFirstHitSelector`, `caseTwoTipFirstHitSelector_isSome_iff` |
| [`Push/CaseTwoTipRawLocality`](Push/CaseTwoTipRawLocality.lean) | Declarations: `caseTwoTipRawReveal`, `caseTwoTipFirstHitSelector_eq_of_raw_agreement`, `caseTwoTipFirstHitSelector_eq_of_raw_reveal_subset` |
| [`Push/CaseTwoTipRawSeparation`](Push/CaseTwoTipRawSeparation.lean) | Declarations: `caseTwoTip_raw_query_off_trace_not_alpha_of_pos_height` |
| [`Push/CaseTwoTraceCrop`](Push/CaseTwoTraceCrop.lean) | Declarations: `caseTwoTipOriginalTrace`, `caseTwoPrecursorOriginalTrace`, `caseTwoTraceCrop`, `caseTwoTraceCrop_eq_of_decoded_firstContact` |
| [`Push/CellBoundaryMixedIncidence`](Push/CellBoundaryMixedIncidence.lean) | Declarations: `cellBoundary_adj_right_iff`, `cellBoundary_no_adj_four_face_labels`, `incident_bond_face_cases`, `cellBoundary_no_adj_incident_face_label`, … |
| [`Push/ClosedClusterFrontier`](Push/ClosedClusterFrontier.lean) | Declarations: `closedClusterReached`, `mem_closedClusterReveal_iff_endpoint`, `closedClusterReached_eq_of_reveal_agreement`, `closedCluster_frontier_primal_open` |
| [`Push/ClosedClusterReveal`](Push/ClosedClusterReveal.lean) | Declarations: `auxiliaryClosedConfiguration`, `mem_auxiliaryClosedConfiguration`, `closedClusterReveal`, `mem_closedClusterReveal`, … |
| [`Push/ClosedDualTraceIndex`](Push/ClosedDualTraceIndex.lean) | Declarations: `rectangle_closed_dual_adj_index_eq_of_open_trace`, `rectangle_closed_dual_walk_index_eq_of_open_trace`, `rectangle_closed_reached_index_of_open_trace`, `rectangle_raw_query_has_seed_index_of_open_trace` |
| [`Push/ClosedPathTransfer`](Push/ClosedPathTransfer.lean) | Declarations: `auxiliaryClosedConfiguration_antitone`, `auxiliaryClosed_path_transfer_below_cut` |
| [`Push/CommonExplorationEvents`](Push/CommonExplorationEvents.lean) | Declarations: `ReadFromReveal`, `readFromReveal_joint_left`, `readFromReveal_joint_inter`, `selectedRevealObservations`, … |
| [`Push/CompletePrefixIntervalBound`](Push/CompletePrefixIntervalBound.lean) | Declarations: `CaseTwoDirectPrefixSourcePaths`, `caseTwoCompleteSource_prefix_interval_lower_bound_of_prefixLocality_and_sourcePaths` |
| [`Push/CompleteSourceEmbedded`](Push/CompleteSourceEmbedded.lean) | Declarations: `embedded_caseTwoCompleteSource_product_of_prefixLocality_and_sourcePaths` |
| [`Push/CompleteSourceIntervalBound`](Push/CompleteSourceIntervalBound.lean) | Declarations: `caseTwoCompleteSource_connection_branch_probability_one_of_prefixLocality`, `caseTwoCompleteSource_interval_lower_bound_of_prefixLocality_and_sourcePaths` |
| [`Push/CompleteSourcePrefixDMP`](Push/CompleteSourcePrefixDMP.lean) | Declarations: `caseTwoCompleteSourceRevealMap`, `caseTwoCompleteSourceRevealMap_eq_of_prefix`, `caseTwoCompleteSource_connection_branch_geometry`, `caseTwoCompleteSourceRevealMap_stable_of_prefixLocality` |
| [`Push/CompleteSourcePrefixSelector`](Push/CompleteSourcePrefixSelector.lean) | Declarations: `caseTwoSourceIntervalConnection`, `caseTwoCompletePrefixSelector`, `caseTwoCompletePrefixSelector_eq_inl_iff`, `caseTwoCompletePrefixSelector_inr_connects`, … |
| [`Push/CompleteSourceStripLimit`](Push/CompleteSourceStripLimit.lean) | Declarations: `stripWindow_caseTwoCompleteSource_product_of_prefixLocality_and_sourcePaths`, `strip_caseTwoCompleteSource_product_of_prefixLocality_and_sourcePaths`, `strip_caseTwoCompleteSource_lower_of_prefixLocality_and_sourcePaths` |
| [`Push/CompletionFreePrefixSelection`](Push/CompletionFreePrefixSelection.lean) | Declarations: `source_prefix_openWalk_on_augmented_fiber` |
| [`Push/ComponentPocketLaw`](Push/ComponentPocketLaw.lean) | Declarations: `componentPocket_frozen_partition`, `componentPocket_law_map`, `componentPocket_frozen_partition_of_no_bridge`, `componentPocket_law_map_of_no_bridge` |
| [`Push/ConfinedPrefixCrosscutGeometry`](Push/ConfinedPrefixCrosscutGeometry.lean) | Declarations: `firstContactTrace_fixed_iff_firstContact_at_length` |
| [`Push/ConfinedPrefixSelector`](Push/ConfinedPrefixSelector.lean) | Declarations: `ConfinedPrefixSelector`, `ConfinedPrefixSelector.IsLocal`, `ConfinedPrefixSelector.toDirectPrefixSystem`, `RoundedLocalConfinedPrefixSelectorExists`, … |
| [`Push/ConfinedPrefixSourceGeometry`](Push/ConfinedPrefixSourceGeometry.lean) | Declarations: `sourceWalkPairUnderlying` |
| [`Push/ConfinedStoppedPrefixGraph`](Push/ConfinedStoppedPrefixGraph.lean) | Declarations: `caseTwoConfinedPrefixGraph`, `caseTwoConfinedPrefixGraph_map_le`, `caseTwoConfinedPrefixConfiguration`, `native_confined_prefix_openWalk_on_augmented_fiber`, … |
| [`Push/CrossingPositivity`](Push/CrossingPositivity.lean) | Declarations: `topWiredCrossing_all_true`, `topWiredCrossing_probability_pos` |
| [`Push/CrossingRestriction`](Push/CrossingRestriction.lean) | Declarations: `bool_embeddedRestriction_state`, `horizontalCrossing_embeddedRestriction_iff` |
| [`Push/CutComponentPockets`](Push/CutComponentPockets.lean) | Declarations: `cutComponent_attachment_mem_cut` |
| [`Push/CutPocketAugmentation`](Push/CutPocketAugmentation.lean) | Declarations: `pocketAugmentedCutExterior` |
| [`Push/DetachedFrontierCycle`](Push/DetachedFrontierCycle.lean) | Declarations: `detached_filledFrontier_has_interior_cycle` |
| [`Push/DetachedFrontierPaths`](Push/DetachedFrontierPaths.lean) | Declarations: `filledCell_reachable_lift_of_no_side_connection` |
| [`Push/DirectPrefixRoundedLocal`](Push/DirectPrefixRoundedLocal.lean) | Declarations: `directPrefixSystem_rounded_local_of_left`, `directPrefixSystem_rounded_local_of_small_horizontal` |
| [`Push/DirectPrefixSystem`](Push/DirectPrefixSystem.lean) | Declarations: `CaseTwoDirectPrefixSystem`, `RoundedDirectPrefixSystem` |
| [`Push/DivisibleHeightInduction`](Push/DivisibleHeightInduction.lean) | Declarations: `selfDual_divisible_push_of_stripRSW` |
| [`Push/DivisibleProduct`](Push/DivisibleProduct.lean) | Declarations: `selfDual_push_product_at_three_mul` |
| [`Push/DivisibleProductEvents`](Push/DivisibleProductEvents.lean) | Declarations: `divisible_reference_bottom_event_eq`, `divisible_reference_upper_event_eq` |
| [`Push/DivisibleReferenceGeometry`](Push/DivisibleReferenceGeometry.lean) | Declarations: `divisible_reference_subset_next`, `divisible_reference_original_sides_wired` |
| [`Push/DualBondLocalization`](Push/DualBondLocalization.lean) | Declarations: `rectangle_dual_edge_face_pair`, `rectangle_dual_step_original_bond`, `rectangle_closed_dual_step_original_bond`, `rectangle_closed_dual_step_of_original_bond`, … |
| [`Push/DualCutCellBoundary`](Push/DualCutCellBoundary.lean) | Declarations: `rectangleLabelFaceCells`, `mem_rectangleLabelFaceCells`, `primalBondOfDual_face_endpoints`, `primalBondOfDual_endpoints_faceIndexMark`, … |
| [`Push/EmbeddedArcErasure`](Push/EmbeddedArcErasure.lean) | Declarations: `embeddedConfigurationRestriction_sdiff`, `embedded_arcsConnection_sdiff_internal_edges` |
| [`Push/EmbeddedFilledDMP`](Push/EmbeddedFilledDMP.lean) | Declarations: `embeddedFilledTopReveal`, `embeddedFilledTopReveal_stable` |
| [`Push/EmbeddedFirstHitSelector`](Push/EmbeddedFirstHitSelector.lean) | Declarations: `embeddedSideFirstHitSelector`, `embeddedSideFirstHitSelector_isSome_iff` |
| [`Push/EmbeddedFixedRecordAgreement`](Push/EmbeddedFixedRecordAgreement.lean) | Declarations: `embedded_fixed_extension_record_agreement` |
| [`Push/EmbeddedFrontierWiring`](Push/EmbeddedFrontierWiring.lean) | Declarations: `actualConnected_embeddedConfiguration`, `embedded_filledFrontier_subset_open_record`, `embedded_frontier_wiring_le_actual_frozen` |
| [`Push/EmbeddedLinearEventBound`](Push/EmbeddedLinearEventBound.lean) | Declarations: `pmf_bind_event_linear_bound`, `embedded_linear_event_bound_of_all_boundaries` |
| [`Push/EmbeddedOpenGraph`](Push/EmbeddedOpenGraph.lean) | Declarations: `embeddedRestriction_open_adj_iff`, `embeddedRestrictionOpenEmbedding` |
| [`Push/EmbeddedRawFirstHit`](Push/EmbeddedRawFirstHit.lean) | Declarations: `embeddedSideRawFirstHitReveal`, `embeddedSideFirstHitSelector_eq_of_raw_agreement` |
| [`Push/EmbeddedRemainingGraph`](Push/EmbeddedRemainingGraph.lean) | Declarations: `edgeRestriction_map_le_embedded`, `activeUnexaminedGraph_map_le_outer_remaining` |
| [`Push/EmbeddedRestrictionStates`](Push/EmbeddedRestrictionStates.lean) | Declarations: `graph_map_le_embedding_trans`, `embeddedConfigurationRestriction_comp`, `embedded_record_agreement_restrict`, `embedded_restriction_restore_remaining` |
| [`Push/EmbeddedReveal`](Push/EmbeddedReveal.lean) | Declarations: `embeddedReveal`, `mem_embeddedReveal_at_edge`, `embeddedReveal_stable` |
| [`Push/EmbeddedUpperBandRecord`](Push/EmbeddedUpperBandRecord.lean) | Declarations: `embedded_upper_band_crossing_record_invariant` |
| [`Push/EnclosingComparison`](Push/EnclosingComparison.lean) | Declarations: `top_wired_enclosing_comparison` |
| [`Push/EnclosingGeometry`](Push/EnclosingGeometry.lean) | Declarations: `topWiredRectangle_enclosing_subset`, `topWiredEnclosing_neighbor_closed`, `topWiredEnclosing_boundary_avoid` |
| [`Push/FilledCellGraphBridge`](Push/FilledCellGraphBridge.lean) | Declarations: `filledTopFrontier_adj_iff_cellBoundary` |
| [`Push/FilledCellNeighborClosure`](Push/FilledCellNeighborClosure.lean) | Declarations: `filledCell_neighbor_mem_rectangle_off_sides` |
| [`Push/FilledFaceBoundaryRows`](Push/FilledFaceBoundaryRows.lean) | Declarations: `cellBoundary_adj_up_iff`, `rectangleFilledFaceCells_top`, `rectangleFilledFaceCells_bottom_not_mem` |
| [`Push/FilledFaceCells`](Push/FilledFaceCells.lean) | Declarations: `rectangleFilledFaceCells`, `mem_rectangleFilledFaceCells`, `mem_filledTopFrontier_iff_cellBoundary` |
| [`Push/FilledFrontierDMP`](Push/FilledFrontierDMP.lean) | Declarations: `auxiliaryRegionReveal`, `mem_auxiliaryRegionReveal`, `rectangleFilledTopReveal`, `rectangleTopReveal_subset_filled`, … |
| [`Push/FilledFrontierFrozenBoundary`](Push/FilledFrontierFrozenBoundary.lean) | Declarations: `filledFrontierWiredVertices`, `filledFrontierWiredVertices_connects_to_side` |
| [`Push/FilledFrontierNoCycles`](Push/FilledFrontierNoCycles.lean) | Declarations: `filled_cut_bond_face_indices_eq`, `filled_frontier_closed_trail_length_zero` |
| [`Push/FilledFrontierSideConnection`](Push/FilledFrontierSideConnection.lean) | Declarations: `filled_frontier_adj_component_meets_side`, `filled_frontier_bond_vertex_connects_to_side` |
| [`Push/FilledRegion`](Push/FilledRegion.lean) | Declarations: `outsideSeedRegion`, `outsideSeedRegion_subset_compl`, `mem_outsideSeedRegion_of_seed`, `outsideSeedRegion_adj_closed`, … |
| [`Push/FilledRegionIndexZero`](Push/FilledRegionIndexZero.lean) | Declarations: `rayIndex_rectangle_bottom_port_zero`, `rayIndex_rectangle_top_port_zero`, `rayIndex_zero_on_top_reached`, `rayIndex_zero_on_bottom_region` |
| [`Push/FiniteContainedRectangleEvent`](Push/FiniteContainedRectangleEvent.lean) | Declarations: `finiteBoolEvent_contained_rectangle`, `nested_rectangle_event_eq_finiteBoolEvent` |
| [`Push/FiniteCrossingClipping`](Push/FiniteCrossingClipping.lean) | Declarations: `horizontalCrossing_clip` |
| [`Push/FiniteIntermediateRectangleEvent`](Push/FiniteIntermediateRectangleEvent.lean) | Declarations: `intermediate_rectangle_event_eq_finiteBoolEvent` |
| [`Push/FiniteRectangleEventBridge`](Push/FiniteRectangleEventBridge.lean) | Declarations: `rectangle_bool_configuration_restriction`, `canonical_rectangle_finiteBoolEvent`, `canonical_rectangle_crossing_probability` |
| [`Push/FirstArrivalDown`](Push/FirstArrivalDown.lean) | Declarations: `walk_first_arrival_down` |
| [`Push/FirstContactPrefix`](Push/FirstContactPrefix.lean) | Declarations: `firstContact_prefix_target_unique` |
| [`Push/FirstContactSuffix`](Push/FirstContactSuffix.lean) | Declarations: `retained_support_append_eq_of_le_length` |
| [`Push/FirstContactTrace`](Push/FirstContactTrace.lean) | Declarations: `firstContactTrace`, `firstContactTrace_eq_support_take`, `support_findIdx_some_iff_firstContact`, `firstContactTrace_exists_prefix` |
| [`Push/ForestComponentLeaves`](Push/ForestComponentLeaves.lean) | Declarations: `forest_component_has_two_original_leaves` |
| [`Push/FrozenConditionalCrossing`](Push/FrozenConditionalCrossing.lean) | Declarations: `frozen_filter_event_eq_deleted_restore_preimage`, `reference_crossing_le_outer_frozen_conditional_crossing` |
| [`Push/HeightComparison`](Push/HeightComparison.lean) | Declarations: `top_wired_height_comparison_parameters`, `top_wired_height_comparison` |
| [`Push/HorizontalBarrierTranslation`](Push/HorizontalBarrierTranslation.lean) | Declarations: `horizontalBarrierTranslationHom`, `rayIndex_horizontalBarrierTranslation`, `slitBarrierEdges_horizontalBarrierTranslation`, `slitBarrierWalk_horizontalBarrierTranslation`, … |
| [`Push/IntervalArmActiveFrozenBoundary`](Push/IntervalArmActiveFrozenBoundary.lean) | Declarations: `intervalArmJoint_active_boundary_le_frozen_record` |
| [`Push/IntervalArmAllAttachments`](Push/IntervalArmAllAttachments.lean) | Declarations: `intervalArmFilledAttachmentVertices`, `intervalArmFilled_attachment_has_frontier_adj`, `intervalArmFilled_attachment_vertices_connected`, `intervalArmFilled_attachment_connects_source` |
| [`Push/IntervalArmBottomEntry`](Push/IntervalArmBottomEntry.lean) | Declarations: `intervalArmFaceLabel_bottom_before`, `intervalArmFaceLabel_bottom_after_of_arm`, `intervalArmFaceLabel_bottom_entry_of_arm` |
| [`Push/IntervalArmCellBridge`](Push/IntervalArmCellBridge.lean) | Declarations: `intervalArmLeftFaceCells`, `mem_intervalArmLeftFaceCells`, `mem_intervalArmLeftFrontier_iff_cellBoundary`, `intervalArmLeftFrontier_adj_iff_cellBoundary`, … |
| [`Push/IntervalArmComponentSource`](Push/IntervalArmComponentSource.lean) | Declarations: `intervalArmFilled_component_contains_source_and_top_leaves` |
| [`Push/IntervalArmConnectionRestoration`](Push/IntervalArmConnectionRestoration.lean) | Declarations: `intervalArmJoint_active_connection_restores_sources`, `intervalArmJoint_remaining_connection_restores_sources` |
| [`Push/IntervalArmCurveIntersection`](Push/IntervalArmCurveIntersection.lean) | Declarations: `interval_arm_complementary_curves_intersect` |
| [`Push/IntervalArmDualPorts`](Push/IntervalArmDualPorts.lean) | Declarations: `intervalArmLeftDualPorts`, `intervalArmRightDualPorts`, `mem_intervalArmLeftDualPorts`, `mem_intervalArmRightDualPorts`, … |
| [`Push/IntervalArmDualSeparation`](Push/IntervalArmDualSeparation.lean) | Declarations: `interval_arm_excludes_complementary_dual_connection` |
| [`Push/IntervalArmEmbeddedCaseOne`](Push/IntervalArmEmbeddedCaseOne.lean) | Declarations: `intervalArmPair_embedded_connection_probability_ge`, `intervalArmPair_embedded_connection_probability_ge_product` |
| [`Push/IntervalArmExteriorComparison`](Push/IntervalArmExteriorComparison.lean) | Declarations: `intervalArmJoint_extremalBoundaryComparison` |
| [`Push/IntervalArmFaceLabel`](Push/IntervalArmFaceLabel.lean) | Declarations: `squareExpandedFaceEquiv`, `intervalArmFaceLabel`, `intervalArmFaceLabel_left`, `intervalArmFaceLabel_right_of_arm` |
| [`Push/IntervalArmFilledActiveLocality`](Push/IntervalArmFilledActiveLocality.lean) | Declarations: `intervalArmFilledLeftFrontier_eq_squareRegionFrontier` |
| [`Push/IntervalArmFilledExploration`](Push/IntervalArmFilledExploration.lean) | Declarations: `intervalArmRightRegion`, `intervalArmFilledLeftFrontier`, `intervalArmFilledLeftReveal`, `intervalArmFilledLeftFrontier_subset_raw`, … |
| [`Push/IntervalArmFilledForest`](Push/IntervalArmFilledForest.lean) | Declarations: `intervalArmFilledLeftFrontier_isAcyclic` |
| [`Push/IntervalArmFilledIndex`](Push/IntervalArmFilledIndex.lean) | Declarations: `rayIndex_square_left_right_bottom_port_zero`, `rayIndex_interval_left_seed_zero`, `rayIndex_interval_right_seed_zero`, `rayIndex_zero_on_interval_left_reached`, … |
| [`Push/IntervalArmFilledNoCycles`](Push/IntervalArmFilledNoCycles.lean) | Declarations: `interval_filled_cut_bond_face_indices_eq`, `interval_filled_frontier_closed_trail_length_zero` |
| [`Push/IntervalArmFilledRecord`](Push/IntervalArmFilledRecord.lean) | Declarations: `intervalArmFilledLeftFrontier_contains_arm`, `intervalArmEvent_readFromFilledLeftReveal` |
| [`Push/IntervalArmFrontierConnected`](Push/IntervalArmFrontierConnected.lean) | Declarations: `intervalArmFilled_frontier_adj_vertices_connected` |
| [`Push/IntervalArmFrontierWitness`](Push/IntervalArmFrontierWitness.lean) | Declarations: `intervalArmLeftFrontier_contains_arm` |
| [`Push/IntervalArmJointRevealDisjoint`](Push/IntervalArmJointRevealDisjoint.lean) | Declarations: `intervalArmJoint_reveal_vertices_disjoint` |
| [`Push/IntervalArmLeafRightPort`](Push/IntervalArmLeafRightPort.lean) | Declarations: `intervalArmFilled_source_leaf_has_right_port` |
| [`Push/IntervalArmLeafRootsUnique`](Push/IntervalArmLeafRootsUnique.lean) | Declarations: `intervalArmFilled_source_leaf_roots_eq` |
| [`Push/IntervalArmLeaves`](Push/IntervalArmLeaves.lean) | Declarations: `intervalArmFilled_region_seed_labels`, `intervalArmFilled_frontier_leaf_mem_source_or_top` |
| [`Push/IntervalArmLeftExploration`](Push/IntervalArmLeftExploration.lean) | Declarations: `intervalArmLeftReveal`, `intervalArmLeftReached`, `intervalArmLeftFrontier`, `intervalArmLeftReached_contains_seed`, … |
| [`Push/IntervalArmLowerCollarIndex`](Push/IntervalArmLowerCollarIndex.lean) | Declarations: `rayIndex_lower_collar_left_seed_zero`, `rayIndex_lower_collar_right_seed_zero`, `lower_collar_closed_trail_avoids_interval_square_bonds` |
| [`Push/IntervalArmOmegaLowerBound`](Push/IntervalArmOmegaLowerBound.lean) | Declarations: `intervalArmJoint_squareCrossingRestrictsToArcs`, `intervalArmJoint_active_wiredArc_lower_bound` |
| [`Push/IntervalArmOppositeRevealAvoidance`](Push/IntervalArmOppositeRevealAvoidance.lean) | Declarations: `intervalArmLeft_path_avoids_right_reveal_incidence`, `intervalArmRight_attachment_avoids_left_reveal_incidence`, `intervalArmLeft_attachment_avoids_right_reveal_incidence` |
| [`Push/IntervalArmPairConnection`](Push/IntervalArmPairConnection.lean) | Declarations: `intervalArmPair_connection_probability_ge` |
| [`Push/IntervalArmPhysicalSideIncidence`](Push/IntervalArmPhysicalSideIncidence.lean) | Declarations: `intervalArmFilledLeft_left_side_incident_reveal`, `intervalArmFilledRight_right_side_incident_reveal` |
| [`Push/IntervalArmRawRightDetermination`](Push/IntervalArmRawRightDetermination.lean) | Declarations: `intervalArmRawRightReveal`, `intervalArmFilledRightReveal_eq_of_raw_agreement`, `intervalArmFilledRightFrontier_eq_of_raw_agreement` |
| [`Push/IntervalArmRecord`](Push/IntervalArmRecord.lean) | Declarations: `intervalArmBottomArc`, `intervalArmEvent`, `intervalArmEvent_on_left_open_record`, `intervalArmEvent_of_left_record_agreement`, … |
| [`Push/IntervalArmRecordLowerBound`](Push/IntervalArmRecordLowerBound.lean) | Declarations: `intervalArmPair_record_connection_lower_bound` |
| [`Push/IntervalArmRegionClosedConnections`](Push/IntervalArmRegionClosedConnections.lean) | Declarations: `intervalArmRightRegion_closed_frontier_connection` |
| [`Push/IntervalArmRemainingLowerBound`](Push/IntervalArmRemainingLowerBound.lean) | Declarations: `intervalArmJoint_remaining_attachment_lower_bound` |
| [`Push/IntervalArmRightAttachments`](Push/IntervalArmRightAttachments.lean) | Declarations: `intervalArmFilledRightAttachmentVertices`, `intervalArmFilledRight_attachment_reflection_iff`, `reflected_success`, `intervalArmFilledRight_attachment_vertices_connected`, … |
| [`Push/IntervalArmRightFrontier`](Push/IntervalArmRightFrontier.lean) | Declarations: `intervalArmFilledRightFrontier`, `intervalArmFilledRightFrontier_subset_open_record`, `intervalArmEvent_on_right_filled_frontier` |
| [`Push/IntervalArmRightFrontierSource`](Push/IntervalArmRightFrontierSource.lean) | Declarations: `reflected_success`, `intervalArmFilledRight_frontier_adj_vertex_connects_source`, `intervalArmFilledRight_bottom_before_reveal_has_frontier_adj` |
| [`Push/IntervalArmRightPathAvoidsLeftReveal`](Push/IntervalArmRightPathAvoidsLeftReveal.lean) | Declarations: `intervalArmRight_path_no_left_frontier_neighbor`, `intervalArmRight_path_avoids_left_reveal_incidence` |
| [`Push/IntervalArmRightRecord`](Push/IntervalArmRightRecord.lean) | Declarations: `intervalArmFilledRightReveal`, `intervalArmFilledRightReveal_stable`, `intervalArmEvent_readFromFilledRightReveal` |
| [`Push/IntervalArmRootRegionBarrier`](Push/IntervalArmRootRegionBarrier.lean) | Declarations: `intervalArmRightRegion_avoids_left_of_frontier_root` |
| [`Push/IntervalArmSeedIndex`](Push/IntervalArmSeedIndex.lean) | Declarations: `rayIndex_left_reached_of_seed_zero`, `rayIndex_right_region_of_seed_zero`, `cut_bond_face_indices_eq_of_seed_zero`, `closed_trail_avoids_interval_square_bonds_of_seed_zero` |
| [`Push/IntervalArmSourceContacts`](Push/IntervalArmSourceContacts.lean) | Declarations: `intervalArmFilled_frontier_source_contacts_eq` |
| [`Push/IntervalArmStripWindowConnection`](Push/IntervalArmStripWindowConnection.lean) | Declarations: `intervalArmStripWindow_connection_mem_local`, `intervalArmStripWindow_connection_probability_le_local` |
| [`Push/IntervalArmStripWindowEmbedding`](Push/IntervalArmStripWindowEmbedding.lean) | Declarations: `intervalArmStripVertex`, `intervalArmStripGraphEmbedding`, `intervalArmStripWindowEmbedding`, `intervalArmStripWindow_map_le` |
| [`Push/IntervalArmStripWindowOpenEdges`](Push/IntervalArmStripWindowOpenEdges.lean) | Declarations: `intervalArmStripWindow_open_adj` |
| [`Push/IntervalArmTopContacts`](Push/IntervalArmTopContacts.lean) | Declarations: `intervalArmFilled_frontier_top_contacts_eq` |
| [`Push/IntervalArmUpperCutExclusion`](Push/IntervalArmUpperCutExclusion.lean) | Declarations: `upper_strip_cut_bond_face_indices_eq`, `upper_strip_closed_trail_avoids_interval_square_bonds` |
| [`Push/IntervalArmUpperIndex`](Push/IntervalArmUpperIndex.lean) | Declarations: `rayIndex_upper_strip_ports_zero`, `rayIndex_upper_strip_left_seed_zero`, `rayIndex_upper_strip_right_seed_zero`, `rayIndex_upper_strip_left_reached_zero`, … |
| [`Push/IsoMixedIncidence`](Push/IsoMixedIncidence.lean) | Declarations: `mixed_incidence_configurationIso_iff` |
| [`Push/IsoStoppingReveal`](Push/IsoStoppingReveal.lean) | Declarations: `configurationIso_inter`, `configurationIso_symm_inter`, `isoStoppingReveal`, `isoStoppingReveal_agreement_pullback`, … |
| [`Push/JointStoppingReveal`](Push/JointStoppingReveal.lean) | Declarations: `jointReveal`, `recorded_agreement_of_subset`, `jointReveal_stable`, `jointReveal_recordEvent` |
| [`Push/LabelCutPathBounds`](Push/LabelCutPathBounds.lean) | Declarations: `rectangleDualBottomPorts_of_coords`, `labelCutDualWalk_support_x_bounds`, `labelCutDual_adj_vertical_step` |
| [`Push/LabelCutPathTrim`](Push/LabelCutPathTrim.lean) | Declarations: `labelCutDual_inner_walk` |
| [`Push/NativeCaseTwoWalks`](Push/NativeCaseTwoWalks.lean) | Declarations: `sourceCaseTwo_native_arms_of_disjoint_walks` |
| [`Push/NativeCompletionFreeSlitPrefix`](Push/NativeCompletionFreeSlitPrefix.lean) | Declarations: `sourceSlitPrefixGraph`, `sourceSlitPrefixGraph_map_le`, `native_prefix_bonds_in_stopped_slit` |
| [`Push/NativeRetainedPathsOnAugmented`](Push/NativeRetainedPathsOnAugmented.lean) | Declarations: `source_tip_openWalk_on_augmented_fiber`, `native_retained_paths_open_on_augmented_fiber` |
| [`Push/NestedFrontierRestoration`](Push/NestedFrontierRestoration.lean) | Declarations: `nested_crossing_after_filled_frontier_restoration`, `nested_crossing_on_filled_record` |
| [`Push/OffTraceFaceIndex`](Push/OffTraceFaceIndex.lean) | Declarations: `rayIndex_incident_face_eq_of_off_support` |
| [`Push/OpenStateEmbedding`](Push/OpenStateEmbedding.lean) | Declarations: `booleanOpenGraph_adj`, `openStateEmbedding` |
| [`Push/OppositeAttachmentDisjointness`](Push/OppositeAttachmentDisjointness.lean) | Declarations: `disjoint_reveals_of_opposite_attachment_avoidance`, `disjoint_reveal_vertices_of_opposite_attachment_avoidance` |
| [`Push/OuterFrontierComparison`](Push/OuterFrontierComparison.lean) | Declarations: `frontier_wired_le_outer_frozen_restriction` |
| [`Push/OuterRestoredCrossing`](Push/OuterRestoredCrossing.lean) | Declarations: `outer_restored_crossing_of_active_reference_witness` |
| [`Push/OuterRestoredCrossingBound`](Push/OuterRestoredCrossingBound.lean) | Declarations: `reference_crossing_le_outer_frozen_restored_crossing` |
| [`Push/OuterWitnessComparison`](Push/OuterWitnessComparison.lean) | Declarations: `reference_event_le_outer_frozen_active_witness` |
| [`Push/PairedIntervalArmRecords`](Push/PairedIntervalArmRecords.lean) | Declarations: `intervalArmJointFilledReveal`, `intervalArmPairEvent`, `intervalArmJointFilledReveal_stable`, `intervalArmPairEvent_readFromJointFilledReveal`, … |
| [`Push/PocketAugmentedSourceReveal`](Push/PocketAugmentedSourceReveal.lean) | Declarations: `pocketAugmentedSourceLeftExterior`, `pocketAugmentedSourceRightExterior`, `pocketAugmentedSourceReveal`, `sourceLeftExterior_subset_pocketAugmented`, … |
| [`Push/PositiveTipOneSidedLocality`](Push/PositiveTipOneSidedLocality.lean) | Declarations: `caseTwoTipRawReveal_subset_right_augmented_of_pos_height`, `caseTwoTipFirstHitSelector_stable_on_right_augmented_of_pos_height` |
| [`Push/PositiveTipPrefixDMP`](Push/PositiveTipPrefixDMP.lean) | Declarations: `caseTwoStoppedPrefixReveal`, `caseTwoTipRightReveal_subset_stoppedPrefixReveal`, `caseTwoPositiveTipPrefixRevealMap`, `caseTwoPositiveTipPrefixRevealMap_stable_of_prefixLocality` |
| [`Push/PositiveTipRecordSelector`](Push/PositiveTipRecordSelector.lean) | Declarations: `CaseTwoPositiveTipRecord`, `caseTwoPositiveTipSelector`, `caseTwoPositiveTipSelector_eq_some_iff`, `caseTwoPositiveTipSelector_oneSidedStable` |
| [`Push/PositiveTipStoppingMap`](Push/PositiveTipStoppingMap.lean) | Declarations: `caseTwoTipRightReveal` |
| [`Push/PrefixExteriorClosure`](Push/PrefixExteriorClosure.lean) | Declarations: `firstContact_prefix_upper_ray_unique` |
| [`Push/PushOfDirectPrefixSystems`](Push/PushOfDirectPrefixSystems.lean) | Declarations: `selfDual_stripRSW_of_directPrefixSystems` |
| [`Push/PushOfLocalConfinedSelectors`](Push/PushOfLocalConfinedSelectors.lean) | Declarations: `selfDual_stripRSW_of_localConfinedPrefixSelectors`, `selfDual_push_of_localConfinedPrefixSelectors` |
| [`Push/PushOfStripRSW`](Push/PushOfStripRSW.lean) | Declarations: `selfDual_push_of_stripRSW` |
| [`Push/PushShiftCrossingTransport`](Push/PushShiftCrossingTransport.lean) | Declarations: `pushShiftRestriction_edge_state`, `pushShiftRestrictedOpenEmbedding`, `shifted_restricted_crossing_implies_upper_band` |
| [`Push/PushShiftGeometry`](Push/PushShiftGeometry.lean) | Declarations: `pushShiftEmbedding`, `pushShiftEmbedding_map_le`, `pushShiftEmbedding_pullback_partition`, `pushShift_restriction_probability_ge` |
| [`Push/PushShiftUpperProbability`](Push/PushShiftUpperProbability.lean) | Declarations: `pushShift_upper_band_probability_ge`, `selfDual_probability_le_shifted_upper_band` |
| [`Push/RawRightDirectIdentification`](Push/RawRightDirectIdentification.lean) | Declarations: `squareDualReflection_reached_iff`, `squareDualReflection_closedReveal_map`, `intervalArmRawRightReveal_eq_direct` |
| [`Push/RayIndexBelowBounds`](Push/RayIndexBelowBounds.lean) | Declarations: `rayStep_eq_height_difference_of_below_left`, `rayIndex_telescope_of_below_left_bound`, `rayStep_zero_of_below_right`, `rayIndex_zero_of_below_right_bound` |
| [`Push/RayIndexCutGradient`](Push/RayIndexCutGradient.lean) | Declarations: `rayIndex_horizontal_jump_ne_zero`, `rayRowMarker`, `rayIndex_vertical_jump_corrected_ne_zero`, `rayIndex_vertical_jump_ne_zero` |
| [`Push/RectangleBandEmbedding`](Push/RectangleBandEmbedding.lean) | Declarations: `rectangleBandEmbedding`, `rectangleBandEmbedding_map_le` |
| [`Push/RectangleBandEventBridge`](Push/RectangleBandEventBridge.lean) | Declarations: `rectangleHorizontalCrossingEvent_eq_arcs`, `rectangleBandConnectionEvent_eq_inner`, `rectangleBand_crossing_probability` |
| [`Push/RectangleBandSideErasure`](Push/RectangleBandSideErasure.lean) | Declarations: `rectangleBandConnectionEvent`, `rectangleBandConnectionEvent_sdiff_threeSideBonds` |
| [`Push/RectangleBondPullback`](Push/RectangleBondPullback.lean) | Declarations: `rectangle_original_bond_pullback`, `rectangle_closed_dual_step_pullback` |
| [`Push/RectangleCarrierInclusion`](Push/RectangleCarrierInclusion.lean) | Declarations: `rectanglePrimalEdgeBond_embedded`, `rectangleDualVertexEmbedding`, `rectangleDualEndpoints_embedded` |
| [`Push/RectangleCutRestriction`](Push/RectangleCutRestriction.lean) | Declarations: `rectangle_labelCut_restriction`, `mem_auxiliaryRegionReveal_iff_endpoints`, `rectangle_regionReveal_restriction` |
| [`Push/RectangleFilledFrontier`](Push/RectangleFilledFrontier.lean) | Declarations: `rectangleBottomRegion`, `rectangleFilledTopFrontier`, `rectangleFilledTopFrontier_subset_original`, `rectangleFilledTopFrontier_subset_open_and_revealed`, … |
| [`Push/RectangleGeometry`](Push/RectangleGeometry.lean) | Declarations: `mem_topWiredRectangle_iff`, `topWiredRectangle_subset`, `topWiredHeightEmbedding`, `topWiredHeightEmbedding_neighbor_closed`, … |
| [`Push/RectangleGraphPreconnected`](Push/RectangleGraphPreconnected.lean) | Declarations: `rectangle_graph_preconnected` |
| [`Push/RectangleHeightCarrier`](Push/RectangleHeightCarrier.lean) | Declarations: `rectangle_height_subset`, `rectangle_dual_height_subset`, `rectangle_dual_height_bottom_port` |
| [`Push/RectangleLabelFrontier`](Push/RectangleLabelFrontier.lean) | Declarations: `auxiliaryClosedConfiguration_rectangle_eq`, `rectangle_dual_label_frontier_crosses` |
| [`Push/RectanglePathReplacement`](Push/RectanglePathReplacement.lean) | Declarations: `rectangle_crossing_of_cut_restoration` |
| [`Push/RectangleThreeSideBonds`](Push/RectangleThreeSideBonds.lean) | Declarations: `rectangleThreeSideBonds`, `mem_rectangleThreeSideBonds_pair`, `rectangleThreeSideBonds_band_internal` |
| [`Push/RectangleTopFrontier`](Push/RectangleTopFrontier.lean) | Declarations: `rectangleTopReveal`, `rectangleTopReached`, `rectangleTopFrontier`, `rectangleTopReached_top`, … |
| [`Push/ReflectedSourceBandArmEvent`](Push/ReflectedSourceBandArmEvent.lean) | Declarations: `reflectedSourceBand_right_arm_iff` |
| [`Push/ReflectedSourceBandEmbedding`](Push/ReflectedSourceBandEmbedding.lean) | Declarations: `reflectedSourceBandEmbedding`, `reflectedSourceBandEmbedding_map_le`, `reflectedSourceBandEmbedding_range_iff`, `reflectedSourceBandEmbedding_adj_iff` |
| [`Push/RemainingRestore`](Push/RemainingRestore.lean) | Declarations: `restoreRemainingConfiguration`, `restoreRemainingConfiguration_inter`, `active_restriction_restoreRemainingConfiguration` |
| [`Push/RestoredConditionalLaw`](Push/RestoredConditionalLaw.lean) | Declarations: `pmf_map_congr_on_support`, `remainingLaw_map_restore_eq_filter`, `edgeRestrictionLaw_map_restore_eq_filter` |
| [`Push/RevealWalkIncidence`](Push/RevealWalkIncidence.lean) | Declarations: `unrevealed_incidence_propagates_along_walk` |
| [`Push/RoundedSourceArmExceptionalScale`](Push/RoundedSourceArmExceptionalScale.lean) | Declarations: `rounded_source_translated_rectangles_fit_iff`, `rounded_source_both_rectangles_fit` |
| [`Push/RoundedSourceArmGeometry`](Push/RoundedSourceArmGeometry.lean) | Declarations: `rounded_source_translated_rectangles_fit` |
| [`Push/SameLabelClosedCut`](Push/SameLabelClosedCut.lean) | Declarations: `auxiliaryClosed_labelCut_adj_of_same_label`, `constantLabelRegionToClosedCut`, `constantLabelRegion_connected_in_closedCut` |
| [`Push/ShiftedStripGeometry`](Push/ShiftedStripGeometry.lean) | Declarations: `baseStripWindowEmbedding`, `baseStripWindowEmbedding_map_le`, `baseStripWindowEmbedding_neighbor_closed`, `baseStripWindowEmbedding_boundary_avoid`, … |
| [`Push/SideCollarBarrierSeedIndices`](Push/SideCollarBarrierSeedIndices.lean) | Declarations: `sideCollar_barrier_right_ports_index` |
| [`Push/SideCollarBarrierSupport`](Push/SideCollarBarrierSupport.lean) | Declarations: `sideCollar_barrier_original_vertex_mem_trace` |
| [`Push/SideCollarBarrierTrace`](Push/SideCollarBarrierTrace.lean) | Declarations: `collar_fixed_edge_of_pair`, `sideCollar_barrier_trace_open_of_open_source_trace` |
| [`Push/SideCollarConnection`](Push/SideCollarConnection.lean) | Declarations: `sideCollarColumnVertex`, `column_step`, `sideCollar_column_connects_top`, `sideCollar_left_vertex_connects_top`, … |
| [`Push/SideCollarEvents`](Push/SideCollarEvents.lean) | Declarations: `sideCollar_interval_bounds`, `sideCollar_interval_top_iff_source_left` |
| [`Push/SideCollarExtension`](Push/SideCollarExtension.lean) | Declarations: `sideCollarSize`, `sideCollarEmbedding`, `sideCollarEmbedding_map_le`, `sideCollarOpenEdges`, … |
| [`Push/SideCollarFirstHitFiber`](Push/SideCollarFirstHitFiber.lean) | Declarations: `sideCollarFirstHitSelector_path_openOnFiber` |
| [`Push/SideCollarFirstHitPath`](Push/SideCollarFirstHitPath.lean) | Declarations: `sideCollarFirstHitSelector_path_in_open_record` |
| [`Push/SideCollarFirstHitSelector`](Push/SideCollarFirstHitSelector.lean) | Declarations: `SideCollarFirstHitRecord`, `sideCollarFirstHitSelector`, `sideCollarFirstHitSelector_isSome_of_pathRecord`, `sideCollarFirstHitSelector_isSome_iff` |
| [`Push/SideCollarFrontier`](Push/SideCollarFrontier.lean) | Declarations: `sideCollarLeftArmFrontier`, `sideCollar_subconfiguration_recovered`, `sideCollarLeftArmFrontier_subset_open_record`, `sourceLeftArm_on_sideCollar_frontier` |
| [`Push/SideCollarOpenTipBarrier`](Push/SideCollarOpenTipBarrier.lean) | Declarations: `sideCollar_exists_open_tip_barrier` |
| [`Push/SideCollarPathOpenness`](Push/SideCollarPathOpenness.lean) | Declarations: `sideCollarArmPathSelector_path_in_sample_and_record` |
| [`Push/SideCollarPathSelector`](Push/SideCollarPathSelector.lean) | Declarations: `SideCollarArmPathRecord`, `sideCollarArmPathSelector`, `sideCollarArmPathSelector_isSome_iff`, `sideCollarArmPathSelector_spec` |
| [`Push/SideCollarRawDetermination`](Push/SideCollarRawDetermination.lean) | Declarations: `sideCollarRawLeftArmReveal`, `sideCollar_raw_auxiliary_agreement`, `sideCollarLeftArmReveal_eq_of_raw_agreement`, `sideCollarLeftArmFrontier_eq_of_raw_agreement`, … |
| [`Push/SideCollarRawQueryIndex`](Push/SideCollarRawQueryIndex.lean) | Declarations: `sideCollar_exists_barrier_with_raw_query_endpoint_index` |
| [`Push/SideCollarReveal`](Push/SideCollarReveal.lean) | Declarations: `sideCollarLeftArmReveal` |
| [`Push/SideCollarSeparation`](Push/SideCollarSeparation.lean) | Declarations: `sideCollar_fixed_incidence_is_left`, `sideCollar_neighbor_lifts_off_left`, `sideCollar_outside_connection_implies_left`, `sideCollar_top_not_source` |
| [`Push/SlitBandPocketActiveBound`](Push/SlitBandPocketActiveBound.lean) | Declarations: `slitBandPocketArcBonds`, `slit_band_pockets_active_wiredArc_lower_bound` |
| [`Push/SlitBandPocketCrossing`](Push/SlitBandPocketCrossing.lean) | Declarations: `slit_band_pockets_connection_restricts`, `slit_band_pockets_wiredArc_lower_bound` |
| [`Push/SlitBandPocketEmbeddedBound`](Push/SlitBandPocketEmbeddedBound.lean) | Declarations: `slit_band_pockets_embedded_active_lower_bound` |
| [`Push/SlitBandPocketLaw`](Push/SlitBandPocketLaw.lean) | Declarations: `slitBandPocketCarrier`, `slitBandPocket_free`, `slit_band_pockets_no_bridge`, `slitBandPocket_root`, … |
| [`Push/SlitBarrierRowIndex`](Push/SlitBarrierRowIndex.lean) | Declarations: `slitBarrier_row_index_eq_right_boundary_of_trace_gap`, `slitBarrier_bottom_right_index_eq_boundary`, `slitBarrier_right_of_trace_index_eq_boundary` |
| [`Push/SlitCrosscutPocketGeometry`](Push/SlitCrosscutPocketGeometry.lean) | Declarations: `slit_crosscuts_cross_seeded_exteriors`, `slit_crosscuts_pocket_attachments_in_same_cut` |
| [`Push/SlitCrosscutPocketLaw`](Push/SlitCrosscutPocketLaw.lean) | Declarations: `slitCrosscutPocketCarrier` |
| [`Push/SourceAlphaBarrierIndex`](Push/SourceAlphaBarrierIndex.lean) | Declarations: `sourceAlpha_cutReach_index_zero_of_slitBarrier` |
| [`Push/SourceBandArmEvent`](Push/SourceBandArmEvent.lean) | Declarations: `sourceBand_left_arm_iff` |
| [`Push/SourceBandEmbedding`](Push/SourceBandEmbedding.lean) | Declarations: `sourceBandEmbedding`, `sourceBandEmbedding_map_le`, `sourceBandEmbedding_range_iff`, `sourceBandEmbedding_adj_iff` |
| [`Push/SourceBandRawQuerySeparation`](Push/SourceBandRawQuerySeparation.lean) | Declarations: `sourceBand_raw_query_off_trace_not_alpha` |
| [`Push/SourceGeometryOfConfinedPath`](Push/SourceGeometryOfConfinedPath.lean) | Declarations: `ConfinedPrefixFirstContact`, `confinedPrefixFirstContact_sourcePaths` |
| [`Push/SourceGeometryOfDirectPath`](Push/SourceGeometryOfDirectPath.lean) | Declarations: `caseTwoDirectPrefixSourcePaths_of_open_first_contact` |
| [`Push/SourceIdentityRestriction`](Push/SourceIdentityRestriction.lean) | Declarations: `sourceIdentity_map_le`, `embeddedConfigurationRestriction_sourceIdentity` |
| [`Push/SourcePocketActiveBound`](Push/SourcePocketActiveBound.lean) | Declarations: `sourcePocketActiveGraph`, `source_pocketAugmented_separate_wired_paths_lower_bound` |
| [`Push/SourcePocketActiveCarrier`](Push/SourcePocketActiveCarrier.lean) | Declarations: `pocketAugmented_mem_iff_of_seeded`, `sourceRectangle_pocket_active_map_le` |
| [`Push/SourcePocketExteriorProjection`](Push/SourcePocketExteriorProjection.lean) | Declarations: `source_pocketAugmentedCutExterior_iff`, `pocketAugmentedSourceLeftExterior_iff`, `pocketAugmentedSourceRightExterior_iff` |
| [`Push/SourcePocketFrozenBound`](Push/SourcePocketFrozenBound.lean) | Declarations: `sourcePocketSupportPaths_recorded_boundary_order`, `sourcePocket_conditional_lower_of_frozenBoundaryDomination`, `sourcePocketRecordedConfiguration`, `sourcePocket_record_conditional_lower_bound` |
| [`Push/SourcePocketIdentityRootBound`](Push/SourcePocketIdentityRootBound.lean) | Declarations: `subgraphRemovedEdges_edgeRestriction_eq`, `sourcePocket_source_roots_lower_bound_of_recordLocality` |
| [`Push/SourcePocketObservedRoots`](Push/SourcePocketObservedRoots.lean) | Declarations: `sourcePocket_observed_roots_of_active_connection` |
| [`Push/SourcePocketRecordBound`](Push/SourcePocketRecordBound.lean) | Declarations: `sourcePocket_revealRecord_lower_bound_of_recordLocality` |
| [`Push/SourcePocketRootRecordBound`](Push/SourcePocketRootRecordBound.lean) | Declarations: `sourcePocket_original_roots_lower_bound_of_recordLocality` |
| [`Push/SourceRecordAverage`](Push/SourceRecordAverage.lean) | Declarations: `stopped_event_lower_of_bounds_on_event` |
| [`Push/SourceSideArm`](Push/SourceSideArm.lean) | Declarations: `sourceSquareSideArmEvent`, `sourceSquareSideArmEvent_isUpperSet`, `sourceCaseTwoFirstArm`, `sourceCaseTwoSecondArm` |
| [`Push/SourceSideArmRestriction`](Push/SourceSideArmRestriction.lean) | Declarations: `sourceSquareSideArmEvent_subset_side_union` |
| [`Push/SourceTopArm`](Push/SourceTopArm.lean) | Declarations: `sourceSquareTopArmEvent`, `sourceSquareTopArmEvent_isUpperSet`, `sourceSquareTopArmEvent_subset_intervalArmEvent` |
| [`Push/SquareArmReflection`](Push/SquareArmReflection.lean) | Declarations: `squareArmReflectionVertex`, `squareArmReflectionVertex_involutive`, `squareArmReflectionIso`, `intervalArmEvent_reflection_iff` |
| [`Push/SquareDualReflectionStates`](Push/SquareDualReflectionStates.lean) | Declarations: `squareDualReflection_closed_configuration`, `squareDualReflection_left_ports_map` |
| [`Push/SquareDualReflectionVertices`](Push/SquareDualReflectionVertices.lean) | Declarations: `squareDualReflectionVertex`, `squareDualReflectionVertex_involutive`, `squareReflectedBond`, `squareReflectedBond_pair`, … |
| [`Push/SquareRegionActiveLocality`](Push/SquareRegionActiveLocality.lean) | Declarations: `squareRegionReveal`, `mem_squareRegionReveal_iff_cellFaces` |
| [`Push/SquareRegionAllMixedLocality`](Push/SquareRegionAllMixedLocality.lean) | Declarations: `squareRegion_mixed_incidence_has_frontier_adj_all` |
| [`Push/SquareRegionBottomEntry`](Push/SquareRegionBottomEntry.lean) | Declarations: `squareRegionFaceLabel_bottom_before`, `squareRegionFaceLabel_bottom_after`, `squareRegionFaceLabel_bottom_entry` |
| [`Push/SquareRegionBottomIncidence`](Push/SquareRegionBottomIncidence.lean) | Declarations: `squareRegion_bottom_after_reveal_has_frontier_adj` |
| [`Push/SquareRegionCellBridge`](Push/SquareRegionCellBridge.lean) | Declarations: `squareRegionFaceLabel`, `squareRegionFrontier`, `squareRegionCells`, `mem_squareRegionCells`, … |
| [`Push/SquareRegionFrontierWitness`](Push/SquareRegionFrontierWitness.lean) | Declarations: `squareRegionFrontier_contains_interval_arm` |
| [`Push/SquareRegionHorizontalClosure`](Push/SquareRegionHorizontalClosure.lean) | Declarations: `squareRegionCell_neighbor_horizontal_bounds` |
| [`Push/SquareRegionLeafBoundary`](Push/SquareRegionLeafBoundary.lean) | Declarations: `squareRegion_frontier_leaf_mem_source_or_top` |
| [`Push/SquareRegionLeafEscape`](Push/SquareRegionLeafEscape.lean) | Declarations: `squareRegion_frontier_leaf_has_outside_cell_neighbor` |
| [`Push/SquareRegionLeftSideIncidence`](Push/SquareRegionLeftSideIncidence.lean) | Declarations: `squareRegion_left_side_vertex_incident_reveal` |
| [`Push/SquareRegionSideClosure`](Push/SquareRegionSideClosure.lean) | Declarations: `squareRegionCells_left_mem`, `squareRegionCells_right_not_mem` |
| [`Push/SquareRegionSourceClosure`](Push/SquareRegionSourceClosure.lean) | Declarations: `squareRegionCells_bottom_before_mem`, `squareRegionCells_bottom_after_not_mem`, `squareRegionCell_neighbor_mem_off_source_top` |
| [`Push/StrictFirstHitPrefixSelection`](Push/StrictFirstHitPrefixSelection.lean) | Declarations: `firstHitPrefixCodeSet`, `firstHitPrefixSelector`, `firstContact_prefix_is_fixed`, `firstHitPrefixSelector_isSome_iff`, … |
| [`Push/StripCaseOneArmPreparation`](Push/StripCaseOneArmPreparation.lean) | Declarations: `strip_top_arm_probability_le_interval_arm`, `strip_case_one_arm_bounds_of_top`, `selfDual_strip_case_one_arm_bounds_all_offsets_of_top`, `selfDual_strip_rounded_case_one_local_lower_all_offsets_of_top` |
| [`Push/StripCaseOneLimit`](Push/StripCaseOneLimit.lean) | Declarations: `stripCaseOneFirstArm`, `stripCaseOneSecondArm`, `strip_intervalArm_product_lower_bound`, `strip_intervalArm_case_one_lower_bound` |
| [`Push/StripCaseOneRounded`](Push/StripCaseOneRounded.lean) | Declarations: `strip_rounded_case_one_stripLocalLower` |
| [`Push/StripCaseTwoArmPreparation`](Push/StripCaseTwoArmPreparation.lean) | Declarations: `selfDual_strip_case_two_arm_bounds_of_left` |
| [`Push/StripCaseTwoFirstArmSymmetry`](Push/StripCaseTwoFirstArmSymmetry.lean) | Declarations: `strip_limit_case_two_first_confined_sides_eq`, `strip_limit_case_two_left_eq_first` |
| [`Push/StripCaseTwoLeftArmBound`](Push/StripCaseTwoLeftArmBound.lean) | Declarations: `strip_case_two_left_arm_ge_sixth` |
| [`Push/StripCaseTwoRoundedArmBound`](Push/StripCaseTwoRoundedArmBound.lean) | Declarations: `selfDual_strip_case_two_second_arm_ge_sixth_of_first` |
| [`Push/StripCaseTwoSideSymmetry`](Push/StripCaseTwoSideSymmetry.lean) | Declarations: `strip_limit_case_two_confined_sides_eq`, `strip_limit_case_two_source_sides_eq` |
| [`Push/StripCaseTwoUniformArmBounds`](Push/StripCaseTwoUniformArmBounds.lean) | Declarations: `selfDual_strip_case_two_arm_bounds_all_offsets_of_left`, `selfDual_strip_rounded_case_two_arm_bounds_all_offsets_of_left` |
| [`Push/StripCaseTwoWideArmTranslation`](Push/StripCaseTwoWideArmTranslation.lean) | Declarations: `strip_limit_case_two_first_eq_wide_second`, `strip_case_two_second_arm_ge_sixth_of_first` |
| [`Push/StripHorizontalReflection`](Push/StripHorizontalReflection.lean) | Declarations: `stripHorizontalReflectionIso`, `stripWindowHorizontalReflectionIso`, `stripHorizontalReflection`, `stripHorizontalReflection_continuous` |
| [`Push/StripMapSymmetry`](Push/StripMapSymmetry.lean) | Declarations: `strip_limit_map_translation`, `strip_limit_map_reflection` |
| [`Push/StripOpenEmbedding`](Push/StripOpenEmbedding.lean) | Declarations: `stripWindowPlaneConfiguration_on_edge`, `baseStripEmbedding`, `baseStripEmbedding_edge_state` |
| [`Push/StripRSWSymmetryBridge`](Push/StripRSWSymmetryBridge.lean) | Declarations: `stripHorizontalTranslationConfiguration_eq_pullback`, `stripHorizontalReflectionConfiguration_eq_pullback`, `strip_limit_map_RSW_translation`, `strip_limit_map_RSW_reflection` |
| [`Push/StripReflectionConfined`](Push/StripReflectionConfined.lean) | Declarations: `stripConfinedConnection_reflection`, `strip_limit_confined_reflection` |
| [`Push/StripReflectionFiniteLaw`](Push/StripReflectionFiniteLaw.lean) | Declarations: `stripWindow_reflection_boundary_partition`, `stripWindow_law_reflection_map` |
| [`Push/StripReflectionPaths`](Push/StripReflectionPaths.lean) | Declarations: `stripHorizontalReflection_edge_involutive`, `stripReflectionOpenIso` |
| [`Push/StripReflectionProbability`](Push/StripReflectionProbability.lean) | Declarations: `stripWindowEventProbability_reflection`, `strip_limit_clopen_reflection` |
| [`Push/StripReflectionWindowStates`](Push/StripReflectionWindowStates.lean) | Declarations: `stripWindow_extension_reflection` |
| [`Push/StripSideArmEvent`](Push/StripSideArmEvent.lean) | Declarations: `stripSourceSideArmEvent_eq_confined` |
| [`Push/StripSideArmRestriction`](Push/StripSideArmRestriction.lean) | Declarations: `strip_source_side_arm_le_sum`, `strip_source_case_two_wide_arm_one_side` |
| [`Push/StripSourceArmLimit`](Push/StripSourceArmLimit.lean) | Declarations: `stripCaseTwoFirstArm`, `stripCaseTwoSecondArm`, `stripSourceSquareEvent_window_probability_tendsto`, `eventually_stripWindow_contains_sourceSquare` |
| [`Push/StripSourceCaseSplit`](Push/StripSourceCaseSplit.lean) | Declarations: `strip_source_top_arm_eq_rectangleArm`, `strip_source_left_arm_eq_rectangleArm`, `selfDual_strip_physical_case_split_of_verticalLower`, `selfDual_strip_source_case_split_of_verticalLower` |
| [`Push/StripSourceCylinder`](Push/StripSourceCylinder.lean) | Declarations: `stripSourceSquareRestriction`, `stripSourceSquareEvent`, `mem_stripSourceSquareRestriction`, `stripSourceSquareEvent_isClopen` |
| [`Push/StripSourceTranslation`](Push/StripSourceTranslation.lean) | Declarations: `stripSourceSquareRestriction_translation`, `stripSourceSquareEvent_preimage_translation`, `stripSourceSquareRestriction_monotone`, `stripSourceSquareEvent_isUpperSet`, … |
| [`Push/StripSourceVertexRange`](Push/StripSourceVertexRange.lean) | Declarations: `mem_range_intervalArmStripGraphEmbedding_iff` |
| [`Push/StripSourceWindowStates`](Push/StripSourceWindowStates.lean) | Declarations: `stripSourceSquareRestriction_window_eq`, `stripSourceSquareEvent_window_probability_eq` |
| [`Push/StripTopArmEvent`](Push/StripTopArmEvent.lean) | Declarations: `stripSourceTopArmEvent_eq_confined` |
| [`Push/StripTopArmTranslation`](Push/StripTopArmTranslation.lean) | Declarations: `strip_limit_top_arm_eq_translated_second` |
| [`Push/StripTranslationConfined`](Push/StripTranslationConfined.lean) | Declarations: `stripConfinedConnection_translation`, `strip_limit_confined_translation` |
| [`Push/StripTranslationGeometry`](Push/StripTranslationGeometry.lean) | Declarations: `stripTranslationIso`, `stripTranslation`, `stripTranslation_continuous`, `stripTranslation_monotone`, … |
| [`Push/StripTranslationPaths`](Push/StripTranslationPaths.lean) | Declarations: `stripTranslationOpenIso` |
| [`Push/StripTranslationProbability`](Push/StripTranslationProbability.lean) | Declarations: `stripTranslation_neg_cancel`, `strip_limit_clopen_le_translation`, `strip_limit_clopen_translation` |
| [`Push/StripTranslationWindowComparison`](Push/StripTranslationWindowComparison.lean) | Declarations: `stripWindowEventProbability_le_translation` |
| [`Push/StripTranslationWindowStates`](Push/StripTranslationWindowStates.lean) | Declarations: `stripWindow_translation_restriction_le` |
| [`Push/StripWindowCaseOne`](Push/StripWindowCaseOne.lean) | Declarations: `stripWindow_intervalArm_connection_probability_ge_product` |
| [`Push/ThirdRounding`](Push/ThirdRounding.lean) | Declarations: `floor_height_add_third_mul_three`, `floor_four_thirds_mul_three`, `three_mul_div_three_bounds` |
| [`Push/TopCapPath`](Push/TopCapPath.lean) | Declarations: `exists_top_cap_path` |
| [`Push/TopCappedCycle`](Push/TopCappedCycle.lean) | Declarations: `path_start_not_mem_tail`, `exists_top_capped_cycle` |
| [`Push/TopFrontierDMP`](Push/TopFrontierDMP.lean) | Declarations: `rectangleTopFrontierReveal`, `rectangleTopFrontierReveal_stable` |
| [`Push/TopFrontierSelector`](Push/TopFrontierSelector.lean) | Declarations: `TopFrontierRecord`, `rectangleTopFrontierSelector`, `rectangleTopFrontierSelector_spec`, `rectangleTopFrontierSelector_oneSidedStable` |
| [`Push/TopWiredCanonicalRectangle`](Push/TopWiredCanonicalRectangle.lean) | Declarations: `topWiredRectangle_eq_canonical`, `topWiredRectangle_base_three_eq_canonical`, `topWired_canonical_right_coordinate` |
| [`Push/TwoArcAttachmentLabels`](Push/TwoArcAttachmentLabels.lean) | Declarations: `twoArcAttachmentLabel`, `twoArcAttachmentLabel_eq_iff`, `twoArcAttachmentQuotientEmbedding`, `twoArcAttachmentQuotientEmbedding_apply` |
| [`Push/TwoArmWindowLimit`](Push/TwoArmWindowLimit.lean) | Declarations: `strip_local_product_lower_of_window_arm_limits` |
| [`Push/TwoCutPocketCrossing`](Push/TwoCutPocketCrossing.lean) | Declarations: `walk_avoiding_cut_stays_in_exterior`, `simple_walk_with_unique_cut_start_stays_in_exterior`, `twoCutPockets_crossing_segment_map` |
| [`Push/TwoCutPocketGeometry`](Push/TwoCutPocketGeometry.lean) | Declarations: `outside_cut_exterior_along_deleted_walk`, `twoCutPockets_attachments_in_same_cut` |
| [`Push/TwoRevealActiveCarrier`](Push/TwoRevealActiveCarrier.lean) | Declarations: `revealIncidentVertices`, `twoRevealActiveLeftArc`, `twoRevealActiveRightArc`, `twoRevealActiveBoundary`, … |
| [`Push/TwoRevealCrossingRestriction`](Push/TwoRevealCrossingRestriction.lean) | Declarations: `twoReveal_connection_restricts_to_active_arcs`, `twoReveal_squareCrossingRestrictsToArcs` |
| [`Push/TwoRevealCrossingSegment`](Push/TwoRevealCrossingSegment.lean) | Declarations: `clipped_edge_not_revealed`, `twoReveal_crossing_remaining_segment` |
| [`Push/TwoRevealExteriorComparison`](Push/TwoRevealExteriorComparison.lean) | Declarations: `twoReveal_exterior_partitions_le_of_boundary_labels`, `twoReveal_active_exterior_partitions_le_of_boundary_labels` |
| [`Push/UnconditionalPush`](Push/UnconditionalPush.lean) | Declarations: `selfDual_push` |
| [`Push/UpperBandCarrier`](Push/UpperBandCarrier.lean) | Declarations: `rectangle_upper_band_subset`, `rectangle_dual_upper_band_subset`, `upper_band_crossed_bond_endpoints_mem` |
| [`Push/UpperBandCrossingLift`](Push/UpperBandCrossingLift.lean) | Declarations: `upper_band_crossing_implies_reference_crossing` |
| [`Push/UpperBandDualStep`](Push/UpperBandDualStep.lean) | Declarations: `upper_band_closed_dual_step_pullback` |
| [`Push/UpperBandDualWalk`](Push/UpperBandDualWalk.lean) | Declarations: `upper_band_closed_dual_walk_pullback` |
| [`Push/UpperBandProduct`](Push/UpperBandProduct.lean) | Declarations: `upper_band_crossing_reference_product` |
| [`Push/UpperBandRecordCrossing`](Push/UpperBandRecordCrossing.lean) | Declarations: `upper_band_restricted_top_frontier_crosses`, `upper_band_crossing_on_filled_record` |
| [`Push/UpperBandTopBarrier`](Push/UpperBandTopBarrier.lean) | Declarations: `rectangle_topReached_above_upper_band_bottom` |
| [`Push/UpwardEmbeddedEvent`](Push/UpwardEmbeddedEvent.lean) | Declarations: `upwardEmbeddedEvent`, `upwardEmbeddedEvent_isUpperSet`, `subset_preimage_upwardEmbeddedEvent`, `measure_le_preimage_upwardEmbeddedEvent` |
| [`Push/WalkIntervalExit`](Push/WalkIntervalExit.lean) | Declarations: `walk_exists_interval_exit` |
| [`Push/WalkPullback`](Push/WalkPullback.lean) | Declarations: `exists_walk_pullback_support` |
| [`Push/WalkSupportStepPullback`](Push/WalkSupportStepPullback.lean) | Declarations: `exists_walk_pullback_support_steps` |
| [`Push/WiredPocketBoundary`](Push/WiredPocketBoundary.lean) | Declarations: `pocketInclusion`, `wiredPocketRetraction`, `pocketInduced_map_le` |
| [`RSW/AdjacentAnnulusPolygons`](RSW/AdjacentAnnulusPolygons.lean) | Neighboring source annulus polygons share an actual lattice vertex |
| [`RSW/AdjacentSegmentCover`](RSW/AdjacentSegmentCover.lean) | Declarations: `nat_interval_covered_by_adjacent_segments`, `int_interval_covered_by_adjacent_segments` |
| [`RSW/Analytic`](RSW/Analytic.lean) | Numeric leaves for the P4 to P5 argument. Source: DCST (15 May 2015), proof of Proposition 3, TeX lines 1519–1527, and the assembly of P4 … |
| [`RSW/AnnulusArmBound`](RSW/AnnulusArmBound.lean) | Declarations: `annulusProbability_le_boxCard_mul_oneArm`, `annulusProbability_le_polynomial_mul_oneArm` |
| [`RSW/AnnulusChainLocal`](RSW/AnnulusChainLocal.lean) | The actual sampled local annulus events in the exact buffered domain. |
| [`RSW/AnnulusChainPaths`](RSW/AnnulusChainPaths.lean) | Actual confined paths along a chain of sampled annulus polygons |
| [`RSW/AnnulusChainScale`](RSW/AnnulusChainScale.lean) | Integer scales for P5b(R=8) to buffered P5. DCST TeX line 1021 uses nonintegral radii and centers. |
| [`RSW/AnnulusChainWindows`](RSW/AnnulusChainWindows.lean) | Integer translates of local annulus windows fit the exact frozen buffer. |
| [`RSW/AnnulusCircuit`](RSW/AnnulusCircuit.lean) | The source annulus circuit event, with genuine Jordan enclosure. DCST TeX lines 984–987. |
| [`RSW/AnnulusEmbedding`](RSW/AnnulusEmbedding.lean) | Annulus witnesses under position-preserving open graph embeddings |
| [`RSW/AnnulusLongConnection`](RSW/AnnulusLongConnection.lean) | Declarations: `annulusCircuitEvent_has_long_connection` |
| [`RSW/AnnulusPositivity`](RSW/AnnulusPositivity.lean) | Nondegeneracy of the genuine finite annulus event. The all-open witness is the literal boundary of the square of radius n+1. |
| [`RSW/AnnulusRecordedSupport`](RSW/AnnulusRecordedSupport.lean) | Declarations: `annulus_event_inter_recorded_outerBonds_iff`, `annulus_event_visible_in_recorded_outerBonds` |
| [`RSW/AnnulusRecursion`](RSW/AnnulusRecursion.lean) | Choosing the small scale and iterating the source annulus recurrence. DCST Proposition 3, TeX lines 1519–1528. |
| [`RSW/AnnulusScreenProduct`](RSW/AnnulusScreenProduct.lean) | The actual screened-annulus upper product in Lemma 4. This module defines the screened-annulus pair event of DCST eq.(16), for … |
| [`RSW/AnnulusSeedRecord`](RSW/AnnulusSeedRecord.lean) | A core-seed record determines the actual shielded annulus event |
| [`RSW/AnnulusShielding`](RSW/AnnulusShielding.lean) | Full-inner-box shielding supplies the actual annulus witness |
| [`RSW/AnnulusTranslation`](RSW/AnnulusTranslation.lean) | Genuine sampled annulus circuits translate with their open graphs |
| [`RSW/AnnulusTranslationLaw`](RSW/AnnulusTranslationLaw.lean) | Exact translated finite free annulus probabilities, every real q≥1 |
| [`RSW/ArmOpen`](RSW/ArmOpen.lean) | The infinite arm event is open. Every open connection has a finite open-edge witness. |
| [`RSW/ArmStrict`](RSW/ArmStrict.lean) | A strict finite-energy upper bound for the frozen free arm. Closing the finite star of the origin excludes every positive-radius arm. |
| [`RSW/BooleanCylinderDetermination`](RSW/BooleanCylinderDetermination.lean) | Declarations: `boolean_measure_eq_of_allOpen` |
| [`RSW/BottomCollarCoreMarginal`](RSW/BottomCollarCoreMarginal.lean) | Declarations: `bottomCollarCoreRestriction`, `bottomCollar_core_law_map` |
| [`RSW/BottomCollarDualBoundary`](RSW/BottomCollarDualBoundary.lean) | Declarations: `bottomCollar_dual_openRemoved_empty`, `bottomCollarInducedDualBoundary_partition`, `bottomCollar_dual_law_at_selfDual` |
| [`RSW/BottomCollarInducedDualLaw`](RSW/BottomCollarInducedDualLaw.lean) | Declarations: `bottomCollarInducedDualGraph`, `bottomCollarInducedDualEquiv`, `bottomCollarInducedDualBoundary`, `bottomCollar_induced_dual_law_at_selfDual` |
| [`RSW/BottomCollarInnerMarginal`](RSW/BottomCollarInnerMarginal.lean) | Declarations: `bottomCollar_inner_map_le`, `bottomCollar_inner_partition`, `bottomCollar_inner_law_map` |
| [`RSW/BottomCollarNativeWalkReplay`](RSW/BottomCollarNativeWalkReplay.lean) | Declarations: `bottomCollarDualClosedExtensionHom`, `bottomCollarDualClosedExtensionHom_support` |
| [`RSW/BottomCollarResidualIdentification`](RSW/BottomCollarResidualIdentification.lean) | Declarations: `bottomCollar_primal_embedding_eq`, `bottomCollar_removed_dual_eq`, `bottomCollar_residual_graph_eq_map_inner` |
| [`RSW/BottomCollarSourcePartition`](RSW/BottomCollarSourcePartition.lean) | Declarations: `bottomCollar_source_partition`, `bottomCollar_source_map_le` |
| [`RSW/BottomCollarSourceState`](RSW/BottomCollarSourceState.lean) | Declarations: `rectangleGraph_eq_FKC`, `bottomCollarSourceState`, `bottomCollarSourceState_partition` |
| [`RSW/BoundingSquare`](RSW/BoundingSquare.lean) | Bounding squares for finite clusters. The square is built from coordinate extrema of the entire finite cloud. |
| [`RSW/BoxCorridors`](RSW/BoxCorridors.lean) | Coordinate exchange supplies vertical versions of the common-box corridor bound, using exact finite-law symmetry rather than translations … |
| [`RSW/BoxRayIndex`](RSW/BoxRayIndex.lean) | Constancy of the dual ray index throughout a primal box |
| [`RSW/BufferedAnnulusGluing`](RSW/BufferedAnnulusGluing.lean) | The actual sampled annulus chain glues in the exact frozen buffer |
| [`RSW/BufferedPositivity`](RSW/BufferedPositivity.lean) | Genuine finite-scale positivity for the exact buffered P5 event. |
| [`RSW/ClosedBlockEnergy`](RSW/ClosedBlockEnergy.lean) | Declarations: `measure_closed_edge_inter_lower`, `measure_closed_block_inter_lower`, `measure_disjoint_closed_blocks_failure_le` |
| [`RSW/ClosedBlockFailure`](RSW/ClosedBlockFailure.lean) | Declarations: `firstClosedBlockScan_none_probability_le`, `firstClosedBlockScan_none_probability_le_constant_card` |
| [`RSW/ClosedExtension`](RSW/ClosedExtension.lean) | Actual connections under closed finite-domain extension. The free finite-domain configuration closes every unsampled edge. |
| [`RSW/ClosedExtensionEmbedding`](RSW/ClosedExtensionEmbedding.lean) | Declarations: `finiteSubgraphConfiguration_embedded_closed_eq` |
| [`RSW/ClusterLocalization`](RSW/ClusterLocalization.lean) | Free localization of a confined actual cluster. For an arbitrary finite graph and vertex region W, the free probability that x and y are … |
| [`RSW/ConfinedWitness`](RSW/ConfinedWitness.lean) | Free localization of events with cluster-confined witnesses. The witness is a genuine subconfiguration of the sampled open bonds. |
| [`RSW/CorridorAnnulus`](RSW/CorridorAnnulus.lean) | A power-112 annulus bound conditional only on circuit extraction. Every probabilistic and translated-domain step is proved. |
| [`RSW/CorridorScale`](RSW/CorridorScale.lean) | A bounded reflected chain at every intermediate scale. The source lists fifteen translates, some outside the ambient box. |
| [`RSW/EmbeddedComparison`](RSW/EmbeddedComparison.lean) | Declarations: `embedded_boundary_expectation_le`, `embeddedBoundary_event_indicator_nonneg`, `embeddedBoundary_event_indicator_mono`, `embedded_boundary_probability_le` |
| [`RSW/EmbeddedConfinedWalkLift`](RSW/EmbeddedConfinedWalkLift.lean) | Declarations: `walk_lift_of_support_in_embedding_range` |
| [`RSW/EmbeddedDecreasingLower`](RSW/EmbeddedDecreasingLower.lean) | Declarations: `embedded_decreasing_reference_lower_of_closedInterior` |
| [`RSW/EmbeddedFreeConnection`](RSW/EmbeddedFreeConnection.lean) | Declarations: `embedded_restriction_actualConnected_mono`, `fkLaw_measure_toReal_eq_expectation`, `embedded_free_connection_probability_le_allq` |
| [`RSW/EmbeddedPath`](RSW/EmbeddedPath.lean) | Embedded restriction preserves actual paths and their vertex constraints. The confined corridor events in the corrected Proposition-3 … |
| [`RSW/ErasureGraph`](RSW/ErasureGraph.lean) | Open graph and confined witnesses after induced edge erasure |
| [`RSW/ErasureRemainingCommute`](RSW/ErasureRemainingCommute.lean) | Declarations: `edgeRestrictionConfigurationEquiv_inducedErasure` |
| [`RSW/ExteriorCircuitFinite`](RSW/ExteriorCircuitFinite.lean) | Lemma 5: the finite free arm bound. DCST TeX lines 1488–1515. |
| [`RSW/ExteriorCircuitInfinite`](RSW/ExteriorCircuitInfinite.lean) | Lemma 5 in the infinite-volume free measure. The finite statement passes to every genuine free infinite-volume limit by Portmanteau on the … |
| [`RSW/FinalCompositions`](RSW/FinalCompositions.lean) | Declarations: `selfDual_stripRSW_final`, `lemma4_recurrence_final`, `p4toP5RemainingGeometryProvider_final` |
| [`RSW/FiniteBoundary`](RSW/FiniteBoundary.lean) | Finite mixed-boundary probabilities on the frozen Boolean carrier. General boundary partitions modify FK weights only. |
| [`RSW/FiniteClosedDualMonotone`](RSW/FiniteClosedDualMonotone.lean) | Declarations: `finite_closedDualGraph_antitone` |
| [`RSW/FiniteClosedDualRectangle`](RSW/FiniteClosedDualRectangle.lean) | Declarations: `finiteClosedDualHorizontalRectangle`, `finiteClosedDualHorizontalRectangle_isLowerSet` |
| [`RSW/FiniteClosedDualWalk`](RSW/FiniteClosedDualWalk.lean) | Actual finite closed-dual walks on the face-base lattice |
| [`RSW/FiniteClusterCover`](RSW/FiniteClusterCover.lean) | Deterministic cluster cover in Lemma 5. DCST, proof of Lemma 5 (the box of a maximal pair), TeX lines 1493–1508. |
| [`RSW/FiniteConditionedDuality`](RSW/FiniteConditionedDuality.lean) | Declarations: `pmf_filter_map_equiv` |
| [`RSW/FiniteDecreasingAssociation`](RSW/FiniteDecreasingAssociation.lean) | Declarations: `finite_decreasing_positive_association` |
| [`RSW/FiniteDualClosure`](RSW/FiniteDualClosure.lean) | Exact sampled closed-dual states under finite closed extension |
| [`RSW/FiniteDualRectangleEmpty`](RSW/FiniteDualRectangleEmpty.lean) | Declarations: `squareLattice_le_finite_closedDual_empty`, `empty_mem_finiteClosedDualHorizontalRectangle` |
| [`RSW/FiniteDualRectangleErasure`](RSW/FiniteDualRectangleErasure.lean) | Declarations: `finiteClosedDualHorizontalRectangle_erasure_iff` |
| [`RSW/FiniteDualRectangleLocality`](RSW/FiniteDualRectangleLocality.lean) | Declarations: `finiteClosedDualHorizontalRectangle_replay_of_closedBonds`, `finiteClosedDualHorizontalRectangle_iff_of_bondStates` |
| [`RSW/FiniteDualScreen`](RSW/FiniteDualScreen.lean) | Actual finite closed-dual circuit screens. A screen is a simple dual cycle, with every crossed sampled primal bond closed, whose ray index … |
| [`RSW/FiniteFkg`](RSW/FiniteFkg.lean) | Finite products of increasing events on the exact Boolean finite carrier. |
| [`RSW/FiniteIso`](RSW/FiniteIso.lean) | Free finite laws and actual Boolean paths under graph isomorphisms. |
| [`RSW/FiniteLocalization`](RSW/FiniteLocalization.lean) | Localization on the frozen Boolean carrier. The bounding square may extend beyond the ambient finite domain. |
| [`RSW/FiniteLower`](RSW/FiniteLower.lean) | Finite positive minima and all-scale closure for the exact buffered event. |
| [`RSW/FiniteOmegaComparison`](RSW/FiniteOmegaComparison.lean) | Declarations: `embedded_exterior_partition_le_iff_fullExterior`, `embedded_exterior_partition_le_of_separation` |
| [`RSW/FinitePath`](RSW/FinitePath.lean) | Actual paths confined to a prescribed finite region, without confining an entire cluster. |
| [`RSW/FinitePathChain`](RSW/FinitePathChain.lean) | Concatenation and clipping of finite confined paths, used by the corrected common-box reflected construction. |
| [`RSW/FinitePlaneComparison`](RSW/FinitePlaneComparison.lean) | Declarations: `finitePlaneBoolRestriction`, `finite_free_event_le_infinite` |
| [`RSW/FinitePlaneConnections`](RSW/FinitePlaneConnections.lean) | Declarations: `finitePlaneBoolRestriction_connection`, `plane_annulus_subset_oneArm_union` |
| [`RSW/FiniteRestriction`](RSW/FiniteRestriction.lean) | Literal original-edge restriction and free comparison for arbitrary actual Boolean events, including the local annulus events in the P5b … |
| [`RSW/FiniteSlitBandLocalization`](RSW/FiniteSlitBandLocalization.lean) | Declarations: `orderedBand_avoids_exterior`, `finiteSlit_orderedBand_in_box` |
| [`RSW/FiniteSlitHorizontal`](RSW/FiniteSlitHorizontal.lean) | Declarations: `finiteSlit_horizontal_walk` |
| [`RSW/FiniteSlitInterior`](RSW/FiniteSlitInterior.lean) | Declarations: `sourceSquareSlitEmbedding`, `sourceSquareSlitEmbedding_mem_beta_iff`, `sourceSquareSlitEmbedding_adj_of_avoid_ray` |
| [`RSW/FiniteUnionSeed`](RSW/FiniteUnionSeed.lean) | Declarations: `finite_union_seed_lower` |
| [`RSW/FourCorridorCentered`](RSW/FourCorridorCentered.lean) | Declarations: `open_rectangle_common_vertex`, `fourCorridor_annulusCircuitEvent_centered` |
| [`RSW/FourCorridorCircuit`](RSW/FourCorridorCircuit.lean) | Declarations: `open_rectangle_common_vertex`, `fourCorridor_annulusCircuitEvent` |
| [`RSW/FourStripRayIndex`](RSW/FourStripRayIndex.lean) | The signed ray index of four supported lattice walks |
| [`RSW/FourStripSimpleCycle`](RSW/FourStripSimpleCycle.lean) | Four supported actual walks yield an actual simple nonzero-index cycle |
| [`RSW/FreeArmTranslation`](RSW/FreeArmTranslation.lean) | Declarations: `oneArmBoundaryEvent_zero_eq`, `oneArmBoundaryEvent_real_translation_of_limit`, `free_oneArmBoundaryEvent_real_eq`, `connectionEvent_subset_oneArmBoundaryEvent` |
| [`RSW/FrozenAwayWiring`](RSW/FrozenAwayWiring.lean) | Declarations: `boundaryConditionToFKC`, `frozenAway_partition_eq_wired` |
| [`RSW/FrozenBoundarySupport`](RSW/FrozenBoundarySupport.lean) | Declarations: `frozenBoundaryWithSupport` |
| [`RSW/FrozenCircuitInteriorComparison`](RSW/FrozenCircuitInteriorComparison.lean) | Declarations: `frozen_reference_lower_of_wiredCircuitPartition` |
| [`RSW/FrozenCircuitWiring`](RSW/FrozenCircuitWiring.lean) | Declarations: `wiredCircuitPartition_le_frozen_of_recordedConnections`, `wiredCircuitPartition_le_frozen_of_recordedRootPaths` |
| [`RSW/FrozenDecreasingAssociation`](RSW/FrozenDecreasingAssociation.lean) | Declarations: `frozen_decreasing_positive_association` |
| [`RSW/FrozenEventRestore`](RSW/FrozenEventRestore.lean) | Declarations: `frozen_event_probability_eq_restored_remaining` |
| [`RSW/FrozenPartialEmbeddedLower`](RSW/FrozenPartialEmbeddedLower.lean) | Declarations: `frozen_partial_decreasing_reference_lower_of_closedInterior` |
| [`RSW/FrozenTwoReferenceProduct`](RSW/FrozenTwoReferenceProduct.lean) | Declarations: `frozen_two_reference_product_lower_of_closedInteriors` |
| [`RSW/InducedAnnulusLaw`](RSW/InducedAnnulusLaw.lean) | Literal local-carrier identification for the shielded annulus bound |
| [`RSW/InducedComparison`](RSW/InducedComparison.lean) | Increasing events under enlargement of an induced free region |
| [`RSW/InducedConfiguration`](RSW/InducedConfiguration.lean) | Actual edge extension from induced vertex regions. These maps retain the sampled original bonds and close every other bond. |
| [`RSW/InducedConfinedComparison`](RSW/InducedConfinedComparison.lean) | Confined witnesses in a free induced sample compare with their free window |
| [`RSW/InducedConfinedWitness`](RSW/InducedConfinedWitness.lean) | Transport cluster-confined witnesses through literal induced extensions |
| [`RSW/InnerBoxGeometry`](RSW/InnerBoxGeometry.lean) | Unit lattice edges outside a closed inner box stay outside it |
| [`RSW/LatticePathIntersection`](RSW/LatticePathIntersection.lean) | Interpolation and actual lattice-vertex intersections. The interpolation follows PD/Duality/LatticeWalkInterpolation.lean, using real … |
| [`RSW/Lemma4BandBondGeometry`](RSW/Lemma4BandBondGeometry.lean) | Declarations: `lemma4_upper_dualBond_endpoint_geometry`, `lemma4_lower_dualBond_endpoint_geometry`, `lemma4MiddleReveal_image_endpoint` |
| [`RSW/Lemma4BandFactorFrozen`](RSW/Lemma4BandFactorFrozen.lean) | Declarations: `selfDual_lemma4_band_factor_frozen_of_stripRSW` |
| [`RSW/Lemma4BandFactorOfStripRSW`](RSW/Lemma4BandFactorOfStripRSW.lean) | Declarations: `selfDual_lemma4_band_factor_of_stripRSW` |
| [`RSW/Lemma4BandProduct`](RSW/Lemma4BandProduct.lean) | Declarations: `lemma4SideReferenceProbability`, `lemma4SideReferenceProbability_nonneg`, `lemma4_band_reference_product_lower` |
| [`RSW/Lemma4BandRestoration`](RSW/Lemma4BandRestoration.lean) | Declarations: `finiteSubgraphConfiguration_union_bondState_of_not_mem_image`, `lemma4DualBandEvent_union_middle_iff` |
| [`RSW/Lemma4BandToSquareComposition`](RSW/Lemma4BandToSquareComposition.lean) | Declarations: `selfDual_lemma4_coefficient_of_stripRSW_and_bandToSquare`, `selfDual_lemma4_of_stripRSW_and_bandToSquare` |
| [`RSW/Lemma4CollarCoreBandProbability`](RSW/Lemma4CollarCoreBandProbability.lean) | Declarations: `lemma4_nativeBand_probability_ge_asymmetricRectangle` |
| [`RSW/Lemma4CollarCoreBandReplay`](RSW/Lemma4CollarCoreBandReplay.lean) | Declarations: `lemma4_coreBand_replays_native` |
| [`RSW/Lemma4CoreComparison`](RSW/Lemma4CoreComparison.lean) | Declarations: `lemma4_symmetric_reference_le_nativeDualBand` |
| [`RSW/Lemma4DualBands`](RSW/Lemma4DualBands.lean) | Declarations: `lemma4DualBandEvent`, `lemma4BandConstructionEvent`, `lemma4DualBandEvent_isLowerSet` |
| [`RSW/Lemma4FullSideProbability`](RSW/Lemma4FullSideProbability.lean) | Declarations: `lemma4SideFull_law_map_reference`, `lemma4SideReferenceProbability_eq_fullSide` |
| [`RSW/Lemma4MiddleBandDisjoint`](RSW/Lemma4MiddleBandDisjoint.lean) | Declarations: `lemma4MiddleReveal_excludes_upper_dualBond`, `lemma4MiddleReveal_excludes_lower_dualBond` |
| [`RSW/Lemma4MiddleBandProduct`](RSW/Lemma4MiddleBandProduct.lean) | Declarations: `lemma4_band_construction_lower_of_middleGeometry` |
| [`RSW/Lemma4MiddleReveal`](RSW/Lemma4MiddleReveal.lean) | Declarations: `lemma4MiddleVertices`, `lemma4MiddleReveal`, `lemma4MiddleReveal_endpoint`, `lemma4MiddleReveal_records_annulus_bonds`, … |
| [`RSW/Lemma4NativeDualBand`](RSW/Lemma4NativeDualBand.lean) | Declarations: `lemma4NativeDualBandEvent` |
| [`RSW/Lemma4NativeDualBandInclusion`](RSW/Lemma4NativeDualBandInclusion.lean) | Declarations: `lemma4_nativeDualBand_subset_sourceDualBand` |
| [`RSW/Lemma4NativeDualBandReplay`](RSW/Lemma4NativeDualBandReplay.lean) | Declarations: `lemma4_nativeDualBand_normalized_replay`, `lemma4_nativeDualBand_normalized_inverse_replay` |
| [`RSW/Lemma4NativeDualComparisonConditional`](RSW/Lemma4NativeDualComparisonConditional.lean) | Declarations: `lemma4_side_reference_ge_padded_push_of_nativeBandInclusion_and_coreComparison`, `selfDual_lemma4_band_factor_of_nativeBandInclusion_and_coreComparison_and_stripRSW` |
| [`RSW/Lemma4OuterCircuitRecords`](RSW/Lemma4OuterCircuitRecords.lean) | Declarations: `selfDual_lemma4_two_annuli_lower_of_circuitRecords` |
| [`RSW/Lemma4PaddedPushComparison`](RSW/Lemma4PaddedPushComparison.lean) | Declarations: `floor_real_nat_mul`, `lemma4_padded_room`, `lemma4_padded_push_le_symmetric_reference` |
| [`RSW/Lemma4RectangleSource`](RSW/Lemma4RectangleSource.lean) | Declarations: `lemma4AmbientRectangle_set_eq`, `lemma4AmbientRectangleIso`, `lemma4RectangleBandEvent` |
| [`RSW/Lemma4ScreenUpper`](RSW/Lemma4ScreenUpper.lean) | The actual Lemma-4 screened-pair upper bound at the source centers |
| [`RSW/Lemma4SideAffineGeometry`](RSW/Lemma4SideAffineGeometry.lean) | Declarations: `lemma4SideInversePrimal`, `lemma4SideInverseFace`, `lemma4SideInverseBond`, `lemma4SideInversePrimal_injective`, … |
| [`RSW/Lemma4SideAffineStates`](RSW/Lemma4SideAffineStates.lean) | Declarations: `lemma4SideInverse_sampledEdges`, `lemma4SideInverse_bondState` |
| [`RSW/Lemma4SideAffineWalk`](RSW/Lemma4SideAffineWalk.lean) | Declarations: `lemma4SideInverseClosedDualHom`, `lemma4SideInverseClosedDualHom_support`, `lemma4_normalizedBand_to_originalSide` |
| [`RSW/Lemma4SideBandErasure`](RSW/Lemma4SideBandErasure.lean) | Declarations: `lemma4DualBandEvent_side_erasure_iff` |
| [`RSW/Lemma4SideBandProduct`](RSW/Lemma4SideBandProduct.lean) | Declarations: `lemma4SideSign`, `lemma4SideSign_eq_one_or_neg_one`, `lemma4_band_construction_lower_of_sideEventIdentity` |
| [`RSW/Lemma4SideBaseDeletion`](RSW/Lemma4SideBaseDeletion.lean) | Declarations: `lemma4SideFullGraph`, `lemma4SideBaseReveal`, `lemma4SideBaseReveal_endpoints`, `lemma4SideBaseReveal_prewired` |
| [`RSW/Lemma4SideDualBandProbability`](RSW/Lemma4SideDualBandProbability.lean) | Declarations: `lemma4SideInducedDualBandEvent`, `lemma4SideReferenceProbability_eq_inducedDual` |
| [`RSW/Lemma4SideInducedDualLaw`](RSW/Lemma4SideInducedDualLaw.lean) | Declarations: `lemma4SideInducedDualEquiv`, `lemma4SideFull_law_map_inducedDual` |
| [`RSW/Lemma4SidePrewiredLaw`](RSW/Lemma4SidePrewiredLaw.lean) | Declarations: `lemma4SideDeletionIso`, `lemma4SideRemainingEquiv`, `lemma4SideReference_law_eq_fullSide_marginal` |
| [`RSW/Lemma4SideRectangleIso`](RSW/Lemma4SideRectangleIso.lean) | Declarations: `lemma4SideRectangleVertexEquiv`, `lemma4SideFullRectangleIso`, `lemma4SideFullRectangleIso_base` |
| [`RSW/Lemma4SideRectangleLaw`](RSW/Lemma4SideRectangleLaw.lean) | Declarations: `lemma4SideRectangle_boundary_partition`, `lemma4SideFull_law_map_rectangle` |
| [`RSW/Lemma4SideReferenceEvents`](RSW/Lemma4SideReferenceEvents.lean) | Declarations: `lemma4SideReferenceEvent`, `lemma4SideReferenceEvent_isLowerSet`, `lemma4SideReferenceEvent_restriction_iff` |
| [`RSW/Lemma4SideReferencePositive`](RSW/Lemma4SideReferencePositive.lean) | Declarations: `empty_mem_lemma4SideReferenceEvent`, `lemma4SideReferenceProbability_pos` |
| [`RSW/Lemma4SideReferencePushConditional`](RSW/Lemma4SideReferencePushConditional.lean) | Declarations: `selfDual_lemma4SideReference_lower_of_dualPushComparison_and_stripRSW` |
| [`RSW/Lemma4SideRemovalEvent`](RSW/Lemma4SideRemovalEvent.lean) | Declarations: `lemma4SideRemainingEquiv_extension`, `lemma4SideFull_band_restore_iff` |
| [`RSW/Lemma4SideResidual`](RSW/Lemma4SideResidual.lean) | Declarations: `lemma4SideVertices`, `lemma4SideResidualGraph`, `lemma4SideBase`, `lemma4SideResidual_closed`, … |
| [`RSW/Lemma4SideResidualDeletion`](RSW/Lemma4SideResidualDeletion.lean) | Declarations: `lemma4SideResidualGraph_eq_delete_base` |
| [`RSW/Lemma4SourceBandFromStrip`](RSW/Lemma4SourceBandFromStrip.lean) | Declarations: `selfDual_lemma4_source_band_lower_of_stripRSW` |
| [`RSW/Lemma4SourceEvents`](RSW/Lemma4SourceEvents.lean) | Declarations: `lemma4AmbientGraph`, `lemma4AnnulusPairEvent`, `lemma4OuterAnnulusEvent`, `lemma4AnnulusPairEvent_isUpperSet`, … |
| [`RSW/Lemma4StaticBandProduct`](RSW/Lemma4StaticBandProduct.lean) | Declarations: `lemma4_band_construction_lower_of_staticMiddleGeometry` |
| [`RSW/Lemma4SymmetricReferenceRectangle`](RSW/Lemma4SymmetricReferenceRectangle.lean) | Declarations: `floor_nat_product`, `lemma4_symmetric_reference_eq_canonical` |
| [`RSW/Lemma4UniformBandsConditional`](RSW/Lemma4UniformBandsConditional.lean) | Declarations: `selfDual_lemma4_band_factor_of_dualPushComparison_and_stripRSW` |
| [`RSW/Lemma4UpperConditional`](RSW/Lemma4UpperConditional.lean) | Lemma-4 upper product with the exact source centers and probability a_n². All probability steps are proved. |
| [`RSW/Lemma4WiredAnnuli`](RSW/Lemma4WiredAnnuli.lean) | Declarations: `source_inner_box_containment`, `source_reference_window`, `lemma4_wired_two_annuli_probability_pos`, `selfDual_lemma4_wired_two_annuli_lower` |
| [`RSW/LocalPrefixBandConsequences`](RSW/LocalPrefixBandConsequences.lean) | Declarations: `selfDual_lemma4_source_band_lower_of_localPrefixSelectors` |
| [`RSW/LocalizedPair`](RSW/LocalizedPair.lean) | The localized pair bound of Lemma 5. This is the free-boundary estimate underlying source eq. (17), proved by exterior-seed cluster … |
| [`RSW/MiddleReferenceProduct`](RSW/MiddleReferenceProduct.lean) | Declarations: `middle_visible_joint_lower_of_closedInteriors` |
| [`RSW/MultiSeedComplementLaw`](RSW/MultiSeedComplementLaw.lean) | Declarations: `law_filter_seedRecord_map_complement_allParameters` |
| [`RSW/NestedRegionEmbedding`](RSW/NestedRegionEmbedding.lean) | Literal embeddings for an intersection inside an induced region |
| [`RSW/OneArm`](RSW/OneArm.lean) | The exact frozen one-arm event and its logarithmic rate. The free-limit bridge specializes the frozen every-exhaustion predicate to boxes. |
| [`RSW/OpenCycleAnnulus`](RSW/OpenCycleAnnulus.lean) | Declarations: `annulusCircuitEvent_of_openCycle_rayIndex` |
| [`RSW/OpenFourWalkAnnulus`](RSW/OpenFourWalkAnnulus.lean) | Declarations: `annulusCircuitEvent_of_fourIntersectingOpenWalks` |
| [`RSW/OverlappingAnnulusScreens`](RSW/OverlappingAnnulusScreens.lean) | The screened-annulus product for overlapping source reference boxes |
| [`RSW/P4AssemblyConditional`](RSW/P4AssemblyConditional.lean) | P4 to P5 at the explicit self-dual value, with all links as hypotheses. The corrected decay upgrade of Proposition 4, the annulus … |
| [`RSW/P4GeometryConditional`](RSW/P4GeometryConditional.lean) | P4 to P5 after both probabilistic gluing chains are proved. The recurrence of Lemma 4, two deterministic geometry statements and the … |
| [`RSW/P5bConditional`](RSW/P5bConditional.lean) | P5b(R=8) to exact buffered P5, conditional only on circuit-chain gluing. Local free comparison, finite FKG, integer window containment … |
| [`RSW/PairReflection`](RSW/PairReflection.lean) | The actual reflected-pair step of Proposition 3. DCST TeX line 1533. |
| [`RSW/PairScaleInterpolation`](RSW/PairScaleInterpolation.lean) | Interpolating Proposition 3 between sevenfold scales. The exact reflected-FKG construction remains a separate geometric input: a fixed … |
| [`RSW/PairStrict`](RSW/PairStrict.lean) | Strict subunit square-pair probabilities from the actual all-closed state. |
| [`RSW/PathInterlacing`](RSW/PathInterlacing.lean) | Interlaced paths in the upper half-plane. Two paths with alternating endpoints on the boundary line intersect. |
| [`RSW/PolygonBoxBounds`](RSW/PolygonBoxBounds.lean) | Actual inner and outer coordinate bounds for polygon Jordan regions |
| [`RSW/PolygonHorizontalExtent`](RSW/PolygonHorizontalExtent.lean) | A genuine enclosing polygon reaches both sides of its marked center |
| [`RSW/PolygonIntersection`](RSW/PolygonIntersection.lean) | Intersection of overlapping, nonnested polygon interiors. The P5b annulus chain requires an actual common boundary vertex. |
| [`RSW/PolygonOuterBox`](RSW/PolygonOuterBox.lean) | The closed outer box contains the actual polygon-domain closure |
| [`RSW/PolygonPaths`](RSW/PolygonPaths.lean) | Sampled polygon paths retain their actual vertex confinement |
| [`RSW/PolygonRayAnyLength`](RSW/PolygonRayAnyLength.lean) | Declarations: `latticePolygon_mem_domain_of_nonzero_rayIndex` |
| [`RSW/PolygonRayCell`](RSW/PolygonRayCell.lean) | Declarations: `polygonRayLatticeHom`, `polygonRay_bond_mem_iff_cell_difference`, `polygonRay_exterior_cell_adjacent` |
| [`RSW/PolygonRayExterior`](RSW/PolygonRayExterior.lean) | Declarations: `polygonRay_exterior_cell_zero`, `polygonRay_cellCenter_mem_domain_of_ne_zero` |
| [`RSW/PolygonRayLocation`](RSW/PolygonRayLocation.lean) | Declarations: `latticeVertex_mem_closure_southwest_cell`, `latticePolygonOfCycle_mem_domain_of_rayIndex_ne_zero` |
| [`RSW/PolygonRayTransport`](RSW/PolygonRayTransport.lean) | Declarations: `polygonRay_ext`, `latticePolygon_mem_domain_of_rayIndex_ne_zero` |
| [`RSW/PolygonTranslation`](RSW/PolygonTranslation.lean) | Translation of the actual polygon and its bounded Jordan interior |
| [`RSW/PolygonVertexIntersection`](RSW/PolygonVertexIntersection.lean) | Intersecting unit lattice polygons have a shared original vertex |
| [`RSW/PrewiredSubgraphMarginal`](RSW/PrewiredSubgraphMarginal.lean) | Declarations: `law_map_subgraphRestriction_of_prewired` |
| [`RSW/Prop3Conditional`](RSW/Prop3Conditional.lean) | The corrected Proposition-3 consumer. The annulus recurrence (Lemma 4) and reflected-FKG circuit construction remain explicit interfaces … |
| [`RSW/Prop3Corridor`](RSW/Prop3Corridor.lean) | Conditional results after the corrected reflected chain is discharged. All reflected-chain probability, finite-domain comparison, integer … |
| [`RSW/Prop3Geometry`](RSW/Prop3Geometry.lean) | Declarations: `selfDual_dualityP_corrected_of_induction1` |
| [`RSW/PushConditional`](RSW/PushConditional.lean) | Exact top-and-sides-wired finite rectangles and the Lemma-3 induction. The finite law and crossing probability of Lemma 3 (top and sides … |
| [`RSW/RankedBandGeometry`](RSW/RankedBandGeometry.lean) | Declarations: `bandOuterBoundary`, `band_exterior_edge`, `band_outer_pullback`, `rankedBand_exterior_partition_le` |
| [`RSW/RayIndexBoxBounds`](RSW/RayIndexBoxBounds.lean) | Ray indices outside a translated support box |
| [`RSW/RectangleBandBooleanBridge`](RSW/RectangleBandBooleanBridge.lean) | Declarations: `rectangleBandConnectionEvent_eq_finiteBoolEvent` |
| [`RSW/RectangleClosedDualStates`](RSW/RectangleClosedDualStates.lean) | Declarations: `rectanglePrimalEdgeBond_closedExtension_iff`, `rectangleSubgraphSourceDualEdge_facePair`, `rectangleSubgraphDualClosedExtensionHom` |
| [`RSW/RectangleDualSidePorts`](RSW/RectangleDualSidePorts.lean) | Declarations: `rectangleDual_vertical_edge_horizontal_inside`, `rectangleDual_horizontal_clamp_edge` |
| [`RSW/RectangleOneColumnComparison`](RSW/RectangleOneColumnComparison.lean) | Declarations: `rectangle_one_column_crossing_comparison` |
| [`RSW/RectangleSubgraphDualEdges`](RSW/RectangleSubgraphDualEdges.lean) | Declarations: `rectangleSubgraph_sourceDual_not_removed`, `rectangleSubgraphSourceDualEdge`, `rectangleSubgraphDualSourceEdge`, `rectangleSubgraphSourceDualEdgeEquiv`, … |
| [`RSW/ReflectedBlock`](RSW/ReflectedBlock.lean) | The reflected pair bound for an actual translated confined block. |
| [`RSW/ReflectedChain`](RSW/ReflectedChain.lean) | Reflected chains in a common finite free law. The doubled-square blocks meet at exactly the same prescribed vertex. |
| [`RSW/RemainingDecreasingAssociation`](RSW/RemainingDecreasingAssociation.lean) | Declarations: `remaining_decreasing_positive_association` |
| [`RSW/ResidualLawTransfer`](RSW/ResidualLawTransfer.lean) | Exact residual-law identities transfer event lower bounds |
| [`RSW/RootedWitnessRecord`](RSW/RootedWitnessRecord.lean) | Seed-rooted confined witnesses are determined by the complete record |
| [`RSW/SampledAnnulus`](RSW/SampledAnnulus.lean) | Actual annulus polygons in the common sampled ambient graph |
| [`RSW/SeedAvoidingAnnulus`](RSW/SeedAvoidingAnnulus.lean) | A genuine annulus witness avoids clusters confined to its left |
| [`RSW/SeedAvoidingConditional`](RSW/SeedAvoidingConditional.lean) | Conditional localization of a seed-separated confined witness |
| [`RSW/SeedAvoidingWitness`](RSW/SeedAvoidingWitness.lean) | Confined witnesses outside every explored seed cluster |
| [`RSW/SeedComplementConnection`](RSW/SeedComplementConnection.lean) | Actual connections under the all-boundary-seed exploration. Connections between unexposed vertices remain actual connections in the induced … |
| [`RSW/SeedComplementFreeBoundary`](RSW/SeedComplementFreeBoundary.lean) | Freeness after exploring every cluster from the original boundary |
| [`RSW/SeedComplementFreeLaw`](RSW/SeedComplementFreeLaw.lean) | Exact free law on the unexplored complement of boundary-rooted clusters |
| [`RSW/SeedComplementGeometry`](RSW/SeedComplementGeometry.lean) | Cluster confinement and exterior-seed exploration. The localization step of Lemma 5 is graph-theoretic: an actual cluster contained in W … |
| [`RSW/SeedComplementLaw`](RSW/SeedComplementLaw.lean) | Cluster-complement conditioning for every real q ≥ 1. The exploration geometry is imported unchanged from FKC. |
| [`RSW/SeedSeparatedProduct`](RSW/SeedSeparatedProduct.lean) | Free upper product for seed-separated witnesses in overlapping windows |
| [`RSW/SelfDualSetup`](RSW/SelfDualSetup.lean) | The explicit self-dual parameter and its constructed strip law. All subsequent §3.3 parameter specializations use the formula … |
| [`RSW/SevenfoldDecay`](RSW/SevenfoldDecay.lean) | The exact geometric-scale exponent in Proposition 3. DCST eqs. |
| [`RSW/ShieldedAnnulus`](RSW/ShieldedAnnulus.lean) | Shielded annulus events for Lemma 4. The shielding condition concerns the whole ambient sampled cluster of every witness edge, not merely … |
| [`RSW/SlitContactOrder`](RSW/SlitContactOrder.lean) | Declarations: `walk_prefix_avoids_ray_of_rayApproach`, `sourceSquare_walk_in_finiteSlit_of_avoid_ray`, `sourceSquare_leftSlit_prefix_in_finiteSlit_of_rayApproach` |
| [`RSW/SlitCrosscutHit`](RSW/SlitCrosscutHit.lean) | Declarations: `disjoint_bottom_right_walk_hits_left_slit` |
| [`RSW/SlitPrefixRetention`](RSW/SlitPrefixRetention.lean) | Declarations: `sourceSquare_leftSlit_prefix_in_finiteSlit_of_disjoint_walks` |
| [`RSW/SlitRayApproach`](RSW/SlitRayApproach.lean) | Declarations: `first_markedRay_contact_approaches_left` |
| [`RSW/SlitRayIndex`](RSW/SlitRayIndex.lean) | Declarations: `exists_slit_tip_loop_with_ray_indices` |
| [`RSW/SlitRetainedExistence`](RSW/SlitRetainedExistence.lean) | Declarations: `sourceSquare_exists_retained_leftSlit_prefix_of_disjoint_walks` |
| [`RSW/SlitTipPositive`](RSW/SlitTipPositive.lean) | Declarations: `bottom_right_walk_meets_bottom_return`, `disjoint_bottom_right_walk_tip_pos` |
| [`RSW/SquareEnumeration`](RSW/SquareEnumeration.lean) | Explicit bounding-square indices for Lemma 5. There are two orientations: left-to-right and bottom-to-top. Each index records an anchor in … |
| [`RSW/SquarePair`](RSW/SquarePair.lean) | Actual finite arm events and the nonempty square-pair maximum. DCST Lemma 5, TeX lines 1489–1513. |
| [`RSW/SquarePairDecay`](RSW/SquarePairDecay.lean) | The weighted-tail step in Proposition 3. DCST TeX line 1536. |
| [`RSW/SquareSymmetry`](RSW/SquareSymmetry.lean) | Moving an indexed square pair to the standard square. Translation and coordinate exchange preserve actual edges and the free law. |
| [`RSW/StoppedCircuitInteriorComparison`](RSW/StoppedCircuitInteriorComparison.lean) | Declarations: `stopped_reference_lower_of_circuitRecords` |
| [`RSW/StoppedConnection`](RSW/StoppedConnection.lean) | Conditional connection estimates on actual stopping records. The full stopped FK law is imported from `Exploration.FiniteStoppingSetDMP`. |
| [`RSW/StoppedRectangleDualRead`](RSW/StoppedRectangleDualRead.lean) | Declarations: `rectangleRecordDualRead`, `rectangleRecordDualRead_mem` |
| [`RSW/StoppingAverage`](RSW/StoppingAverage.lean) | Averaging connection estimates over actual stopping records. Record indices are precisely the realized pairs of revealed sets and recorded … |
| [`RSW/StoppingJointAverage`](RSW/StoppingJointAverage.lean) | Declarations: `stopped_joint_event_lower_of_record_bounds` |
| [`RSW/StoppingJointUpper`](RSW/StoppingJointUpper.lean) | Joint upper bounds for events measurable in a complete stopping record |
| [`RSW/StoppingUpper`](RSW/StoppingUpper.lean) | Declarations: `stopped_event_upper_of_record_bounds` |
| [`RSW/StretchedRate`](RSW/StretchedRate.lean) | Removing a stretched-exponential prefactor. The corrected Proposition 3 needs a positive rate in the exponent at every positive index. |
| [`RSW/StripArmCaseSplit`](RSW/StripArmCaseSplit.lean) | Declarations: `strip_arm_case_split_of_reflectionInvariant` |
| [`RSW/StripAssociation`](RSW/StripAssociation.lean) | Clopen positive association of the constructed top-only strip law. Finite top-wired FK laws are positively associated. |
| [`RSW/StripAsymmetricBoundaryComparison`](RSW/StripAsymmetricBoundaryComparison.lean) | Declarations: `stripWindowAsymmetricEmbedding`, `stripWindowAsymmetric_map_le`, `center_nonBoundary_closed`, `center_nonBoundary_avoids_outer`, … |
| [`RSW/StripAsymmetricLimit`](RSW/StripAsymmetricLimit.lean) | Declarations: `stripWindowReadProbabilityMeasures_tendsto`, `stripAsymmetricCenteredProbabilityMeasures_tendsto`, `selfDual_stripAsymmetricCenteredProbabilityMeasures_tendsto` |
| [`RSW/StripAsymmetricReadMeasures`](RSW/StripAsymmetricReadMeasures.lean) | Declarations: `stripWindowOriginalRead`, `stripWindowReadProbabilityMeasure`, `stripAsymmetricCenteredRead`, `stripAsymmetricCenteredProbabilityMeasure`, … |
| [`RSW/StripBandArm`](RSW/StripBandArm.lean) | Declarations: `stripBandArm`, `stripRectangleArm`, `stripBandArm_eq_iUnion_rectangleArm`, `stripBandArm_measurableSet` |
| [`RSW/StripBoundaryCylinderError`](RSW/StripBoundaryCylinderError.lean) | Declarations: `strip_cylinder_boundary_le_topOnly_add_failure` |
| [`RSW/StripBoundaryCylinderLimit`](RSW/StripBoundaryCylinderLimit.lean) | Declarations: `strip_cylinder_topOnly_le_boundary`, `strip_cylinder_boundary_difference_tendsto_zero` |
| [`RSW/StripBoundaryPatternLimit`](RSW/StripBoundaryPatternLimit.lean) | Declarations: `stripRectanglePatternEvent`, `pattern_insert_closed`, `pattern_insert_closed_probability`, `strip_pattern_boundary_difference_tendsto_zero` |
| [`RSW/StripCanonicalBandSeed`](RSW/StripCanonicalBandSeed.lean) | Declarations: `selfDual_strip_canonical_band_seed_of_translationInvariant_and_verticalLower`, `selfDual_strip_source_case_split_of_stripSymmetries_and_verticalLower` |
| [`RSW/StripCentralDualEdgeLabel`](RSW/StripCentralDualEdgeLabel.lean) | Declarations: `rectangleDualEdgeEquiv_physical_pair`, `stripCentralRetainedDualEdge_physical_pair` |
| [`RSW/StripCentralPrunedEmbedding`](RSW/StripCentralPrunedEmbedding.lean) | Declarations: `stripCentralPrimalHostEmbedding`, `stripCentralPrimalHost_map_le_pruned`, `stripCentralRetainedDualEdge`, `stripCentralPrimalWindowEmbedding`, … |
| [`RSW/StripCentralPrunedRead`](RSW/StripCentralPrunedRead.lean) | Declarations: `stripCentralPrunedDualRead`, `stripCentralPrunedDualRead_source` |
| [`RSW/StripCentralPrunedReflection`](RSW/StripCentralPrunedReflection.lean) | Declarations: `stripCentralRetainedDualEdge_reflected`, `stripCentralPrunedDualRead_reflected` |
| [`RSW/StripCentralRead`](RSW/StripCentralRead.lean) | Declarations: `stripCentralRectangleEmbedding`, `stripCentralRectangle_map_le`, `stripCentralRectangleConfiguration`, `stripCentralDualConfiguration`, … |
| [`RSW/StripClosedCutFailure`](RSW/StripClosedCutFailure.lean) | Declarations: `strip_left_closed_cut_failure_le`, `strip_right_closed_cut_failure_le`, `strip_either_closed_cut_failure_le`, `strip_closed_cut_failure_tendsto_zero` |
| [`RSW/StripClosedCutRecordLaw`](RSW/StripClosedCutRecordLaw.lean) | Declarations: `stripClosedCutRecord_law_map_interval_topOnly` |
| [`RSW/StripCrossingPositive`](RSW/StripCrossingPositive.lean) | Strict positivity of actual finite strip rectangle crossings |
| [`RSW/StripCutCylinderComparison`](RSW/StripCutCylinderComparison.lean) | Declarations: `stripClosedCutRecord_cylinder_probability_le_topOnly` |
| [`RSW/StripEventLimit`](RSW/StripEventLimit.lean) | Transport of finite-window connection bounds to the genuine strip law. Events are evaluated on the literal closed extension of the sampled … |
| [`RSW/StripEventMonotone`](RSW/StripEventMonotone.lean) | Monotone finite-window event bounds and positivity in the strip. Increasing events evaluated on closed extensions grow with the window. |
| [`RSW/StripEvents`](RSW/StripEvents.lean) | Finite-support actual path events in the strip. The support consists of literal strip edges whose two endpoints are in a finite vertex set. |
| [`RSW/StripFiniteScaleUniform`](RSW/StripFiniteScaleUniform.lean) | Uniform positive strip crossing bounds on a finite set of scales |
| [`RSW/StripFiniteSupportPositive`](RSW/StripFiniteSupportPositive.lean) | Positive probability of nonempty increasing finite-support strip events |
| [`RSW/StripGluing`](RSW/StripGluing.lean) | Finite gluing probabilities for the actual strip law. These lemmas perform only finite FKG multiplication and event inclusion. |
| [`RSW/StripHorizontalReflection`](RSW/StripHorizontalReflection.lean) | Declarations: `stripHorizontalReflectionIso`, `stripHorizontalReflectionConfiguration`, `stripHorizontalReflectionConfiguration_edge`, `stripHorizontalReflection_edge_involutive`, … |
| [`RSW/StripHorizontalTranslation`](RSW/StripHorizontalTranslation.lean) | Declarations: `stripHorizontalTranslationIso`, `stripHorizontalTranslationConfiguration`, `stripHorizontalTranslationConfiguration_edge`, `stripHorizontalTranslation_edge_neg_cancel`, … |
| [`RSW/StripInterlacing`](RSW/StripInterlacing.lean) | Actual interlaced strip paths and unconditional deterministic gluing. Continuous interlacing and the unit-bond endpoint lemma discharge the … |
| [`RSW/StripIntervalFrozenLaw`](RSW/StripIntervalFrozenLaw.lean) | Declarations: `stripInterval_frozen_partition_eq_top`, `stripInterval_frozen_law_eq_top` |
| [`RSW/StripLateralIndependence`](RSW/StripLateralIndependence.lean) | Declarations: `stripWindowCylinderProbability_boundary_difference_tendsto_zero`, `isTopWiredStripLimit_iff_top` |
| [`RSW/StripLaw`](RSW/StripLaw.lean) | Existence of the increasing-width top-wired strip law on a common carrier. Finite configurations are literally extended by closed edges … |
| [`RSW/StripLimit`](RSW/StripLimit.lean) | The top-only strip law satisfies the actual strip cylinder-limit predicate. The whole-plane finite approximations are used only as a common … |
| [`RSW/StripMonotone`](RSW/StripMonotone.lean) | Increasing-width comparison for top-wired strip windows. The argument follows FKconvergence, an earlier formalization by the same author … |
| [`RSW/StripNormalizedPatternRead`](RSW/StripNormalizedPatternRead.lean) | Declarations: `stripNormalizedEmbedding`, `stripNormalizedEmbedding_window_edge`, `stripNormalizedEmbedding_open_iff` |
| [`RSW/StripPlanarGluing`](RSW/StripPlanarGluing.lean) | Deterministic source gluing from the interlaced-path interface. This module reduces the actual translated-event inclusion to the basic … |
| [`RSW/StripPrunedFiniteDuality`](RSW/StripPrunedFiniteDuality.lean) | Declarations: `subgraphRemovedEdges_edgeRestriction`, `stripRectangleTopRowState`, `stripRectangleWithoutTopGraph`, `pruned_map_id`, … |
| [`RSW/StripPrunedTopPorts`](RSW/StripPrunedTopPorts.lean) | Declarations: `stripPruned_removedDualEdges_eq`, `removed_pair_iff_top`, `stripPrunedDual_adj_iff_not_top` |
| [`RSW/StripRSWConditional`](RSW/StripRSWConditional.lean) | Translated bottom-arc connections for Lemma 2. The events below are exactly the translated bottom-arc connections of the source proof, and … |
| [`RSW/StripRSWFromThirteen`](RSW/StripRSWFromThirteen.lean) | Rounded local estimates above the source-rectangle containment cutoff |
| [`RSW/StripReflectedAsymmetricEmbedding`](RSW/StripReflectedAsymmetricEmbedding.lean) | Declarations: `stripReflectedAsymmetricEmbedding`, `stripReflectedAsymmetricEmbedding_not_top`, `stripReflectedAsymmetricEmbedding_range`, `stripReflectedAsymmetricEmbedding_adj_iff`, … |
| [`RSW/StripReflectedAsymmetricLaw`](RSW/StripReflectedAsymmetricLaw.lean) | Declarations: `stripAsymmetricTopSidesBoundary`, `stripReflectedAsymmetric_boundary_iff`, `stripReflectedAsymmetric_boundary_partition`, `stripAsymmetricPrunedDualRead`, … |
| [`RSW/StripReflectedCentralDualRead`](RSW/StripReflectedCentralDualRead.lean) | Declarations: `stripReflectedCentralDualEmbedding`, `stripReflectedCentralDual_map_le`, `stripReflectedCentralDualConfiguration`, `stripReflectedCentralDualOpenHom` |
| [`RSW/StripReflectedCentralLawConditional`](RSW/StripReflectedCentralLawConditional.lean) | Declarations: `stripReflectedCentralDualConfiguration_event_isClopen`, `stripCentralDualConfiguration_event_isClopen`, `selfDual_stripCentral_vertical_lower_of_reflectedDualLaw_and_crossingTransport` |
| [`RSW/StripReflectedFiniteRead`](RSW/StripReflectedFiniteRead.lean) | Declarations: `stripReflectedCentralWindowEmbedding`, `stripReflectedCentralWindow_map_le`, `stripReflectedCentralAsymmetricEmbedding`, `stripReflectedCentralAsymmetric_map_le`, … |
| [`RSW/StripReflectedMarginalFiniteRead`](RSW/StripReflectedMarginalFiniteRead.lean) | Declarations: `selfDual_finite_central_dual_probability_eq_of_finiteRead`, `selfDual_strip_reflected_marginal_of_finiteRead` |
| [`RSW/StripReflectedMarginalSeed`](RSW/StripReflectedMarginalSeed.lean) | Declarations: `selfDual_stripCentral_vertical_lower_of_reflectedMarginal` |
| [`RSW/StripReflectedPortTransport`](RSW/StripReflectedPortTransport.lean) | Declarations: `stripReflectedCentralClampedVertex`, `reachable_of_adj_eq_or_adj`, `stripReflectedCentralClampedVertex_adj_or_eq`, `strip_reflected_dual_port_crossing_subset_shifted`, … |
| [`RSW/StripReflectedWindowState`](RSW/StripReflectedWindowState.lean) | Declarations: `stripHorizontalReflectionConfiguration_apply`, `stripHorizontalReflectionConfiguration_monotone`, `stripWindow_reflected_restriction_le` |
| [`RSW/StripReflectedWindowTop`](RSW/StripReflectedWindowTop.lean) | Declarations: `stripWindow_reflection_containment`, `stripWindowReflectionEmbedding`, `stripWindowReflection_graph_le`, `stripWindow_reflected_top_pullback_partition` |
| [`RSW/StripReflectionArm`](RSW/StripReflectionArm.lean) | Declarations: `stripRectangleArm_reflected_mem`, `stripRectangleArm_left_reflection_iff` |
| [`RSW/StripReflectionDomination`](RSW/StripReflectionDomination.lean) | Declarations: `stripWindowEventProbability_reflection_le`, `strip_limit_clopen_reflection_domination` |
| [`RSW/StripReflectionInvariant`](RSW/StripReflectionInvariant.lean) | Declarations: `strip_limit_clopen_reflection_eq`, `strip_limit_horizontalReflection_invariant`, `selfDualStripMeasure_horizontalReflection_invariant` |
| [`RSW/StripRoundedBandSeed`](RSW/StripRoundedBandSeed.lean) | Declarations: `selfDual_strip_vertical_has_rounded_band_seed` |
| [`RSW/StripRoundedGluing`](RSW/StripRoundedGluing.lean) | Translated strip gluing without the divisible-scale restriction |
| [`RSW/StripShiftedVerticalClip`](RSW/StripShiftedVerticalClip.lean) | Declarations: `stripConfined_vertical_subset_of_intervals`, `strip_shifted_vertical_subset_central` |
| [`RSW/StripSourceCylinderNormalization`](RSW/StripSourceCylinderNormalization.lean) | Declarations: `stripNormalizedOpenPattern`, `stripNormalizedClosedPattern`, `stripNormalizedPattern_exists_support`, `stripWindowCylinder_normalized_pattern_iff`, … |
| [`RSW/StripSymmetricSeeds`](RSW/StripSymmetricSeeds.lean) | Declarations: `selfDual_strip_source_case_split_of_verticalLower` |
| [`RSW/StripThreeSideExit`](RSW/StripThreeSideExit.lean) | Declarations: `stripBandArm_subset_three_rectangleArms` |
| [`RSW/StripTopRowEdgeRead`](RSW/StripTopRowEdgeRead.lean) | Declarations: `mem_stripRectangleTopRowState_iff`, `rectangleDual_top_port_crosses_top_row`, `rectangleDual_top_row_crosses_top_port` |
| [`RSW/StripTopRowWiring`](RSW/StripTopRowWiring.lean) | Declarations: `stripTopRowState`, `topVertex`, `topVertex_connected_zero`, `stripTopRowState_connects_top`, … |
| [`RSW/StripTranslatedWindowState`](RSW/StripTranslatedWindowState.lean) | Declarations: `stripHorizontalTranslationConfiguration_apply`, `stripHorizontalTranslationConfiguration_monotone`, `stripWindow_translated_restriction_le` |
| [`RSW/StripTranslatedWindowTop`](RSW/StripTranslatedWindowTop.lean) | Declarations: `stripWindow_translation_containment`, `stripWindow_translated_top_pullback_partition`, `stripWindow_translated_probability_le` |
| [`RSW/StripTranslationArm`](RSW/StripTranslationArm.lean) | Declarations: `stripBandArm_translated_mem`, `stripBandArm_translation_iff`, `stripBandArm_real_translation_of_translationInvariant` |
| [`RSW/StripTranslationDomination`](RSW/StripTranslationDomination.lean) | Declarations: `stripWindowEventProbability_translation_le`, `strip_limit_clopen_translation_domination` |
| [`RSW/StripTranslationInvariant`](RSW/StripTranslationInvariant.lean) | Declarations: `strip_limit_clopen_translation_eq`, `strip_limit_horizontalTranslation_invariant`, `selfDualStripMeasure_horizontalTranslation_invariant` |
| [`RSW/StripVerticalSeed`](RSW/StripVerticalSeed.lean) | Declarations: `stripVerticalCrossing`, `stripVerticalCrossing_subset_segment_bandArms`, `strip_vertical_crossing_has_band_seed` |
| [`RSW/StripWeakCylinderCriterion`](RSW/StripWeakCylinderCriterion.lean) | Declarations: `stripCoordinateAllOpen`, `stripNormalizedClosedExtension`, `stripNormalizedPlaneRestriction`, `stripNormalizedClosedExtension_apply`, … |
| [`RSW/StripWindow`](RSW/StripWindow.lean) | Top-wired strip windows and their genuine cylinder-limit predicate. The strip in Lemma 2 is ℤ × [-n,3n]. |
| [`RSW/StripWindowCutNormalization`](RSW/StripWindowCutNormalization.lean) | Declarations: `stripWindowCutIso` |
| [`RSW/StripWindowEdgeRead`](RSW/StripWindowEdgeRead.lean) | Declarations: `stripWindowPlaneConfiguration_edge`, `stripWindowOriginalRead_edge` |
| [`RSW/StripWindowPatternComparison`](RSW/StripWindowPatternComparison.lean) | Declarations: `stripWindowCutBoundary_supported`, `stripWindowCutBoundary_dominates_top`, `stripWindowCutBoundary_top_partition`, `stripWindow_normalized_pattern_probability`, … |
| [`RSW/StripWindowRectangleIso`](RSW/StripWindowRectangleIso.lean) | Declarations: `stripWindowRectangleIso`, `stripWindowRectangleIso_topRow_frozen_partition` |
| [`RSW/ThreeSideWalkExit`](RSW/ThreeSideWalkExit.lean) | Declarations: `walk_reach_three_sides` |
| [`RSW/TiltedFiniteEdgeStrict`](RSW/TiltedFiniteEdgeStrict.lean) | Declarations: `strictRemovedBoolEquiv`, `strictEdgeStateEquiv`, `strictEdgeStateEquiv_false`, `strictEdgeStateEquiv_true` |
| [`RSW/TiltedReducedActiveGeometry`](RSW/TiltedReducedActiveGeometry.lean) | Declarations: `tiltedReducedFiniteSourceBond_retained`, `tiltedReducedFiniteDualEdge_endpoints_mem`, `tiltedReducedFiniteDualEdge_surjective` |
| [`RSW/TiltedReducedActiveLaw`](RSW/TiltedReducedActiveLaw.lean) | Declarations: `tiltedReducedFiniteDualBoundary` |
| [`RSW/TiltedReducedBackground`](RSW/TiltedReducedBackground.lean) | Declarations: `tiltedReducedUpperBond`, `tiltedReducedUpperBond_crossed_complement`, `tiltedStripReducedCarrier_zero_isEmpty`, `selfDual_tiltedStrip_reflected_marginal_zero_height` |
| [`RSW/TiltedReducedCoreClosure`](RSW/TiltedReducedCoreClosure.lean) | Declarations: `reduced_dual_vertex_adj`, `tiltedReducedCoreDual_closedInterior` |
| [`RSW/TiltedReducedCoreEmbedding`](RSW/TiltedReducedCoreEmbedding.lean) | Declarations: `tiltedReducedCoreDualEmbedding`, `tiltedReducedCoreDualEmbedding_replay`, `tiltedReducedCoreDualEmbedding_interior` |
| [`RSW/TiltedReducedCoreGraph`](RSW/TiltedReducedCoreGraph.lean) | Declarations: `tiltedReducedCoreCrossedEdge`, `tiltedReducedCoreCrossedEdge_pair`, `tiltedReducedCoreCrossedEdge_sourceBond`, `tiltedReducedCoreDual_map_le` |
| [`RSW/TiltedReducedCoreRead`](RSW/TiltedReducedCoreRead.lean) | Declarations: `tiltedReducedCoreDualEdge_eq_embedding`, `tiltedReducedCoreRead_dual_source`, `tiltedReducedAllOpen`, `selfDual_tiltedReducedCore_allOpen_sandwich` |
| [`RSW/TiltedReducedFiniteDuality`](RSW/TiltedReducedFiniteDuality.lean) | Declarations: `tiltedReducedFiniteDualEquiv`, `tiltedWindowReducedDualConfiguration`, `tiltedWindowReducedDualConfiguration_law`, `selfDual_tiltedWindowReducedDualConfiguration_law` |
| [`RSW/TiltedReducedFiniteReads`](RSW/TiltedReducedFiniteReads.lean) | Declarations: `tiltedReducedFiniteDualEdge`, `tiltedReducedFiniteEdgeEquiv`, `tiltedReducedFiniteSourceBond`, `tiltedReducedFiniteSourceBond_pair`, … |
| [`RSW/TiltedReducedFiniteSandwich`](RSW/TiltedReducedFiniteSandwich.lean) | Declarations: `tiltedReducedFiniteDual_probability_sandwich` |
| [`RSW/TiltedReducedHost`](RSW/TiltedReducedHost.lean) | Declarations: `tiltedReducedHost`, `tiltedReducedHostEmbedding`, `tiltedReducedHost_map_le`, `tiltedReducedHost_cap_upper`, … |
| [`RSW/TiltedReducedLowerCorridor`](RSW/TiltedReducedLowerCorridor.lean) | Declarations: `host_dual_pair`, `tiltedReducedLowerCorridor_step`, `tiltedReducedLowerCorridor_reachable_bottom`, `tiltedReducedCore_top_partition_le` |
| [`RSW/TiltedReducedLowerEdges`](RSW/TiltedReducedLowerEdges.lean) | Declarations: `tiltedReducedHost_below_edge`, `tiltedReducedHost_below_dual_open`, `tiltedReducedCore_top_below` |
| [`RSW/TiltedReducedMarginal`](RSW/TiltedReducedMarginal.lean) | Declarations: `selfDual_tiltedStrip_reduced_allOpen_eq`, `selfDual_tiltedStrip_reflected_marginal` |
| [`RSW/TiltedReducedUpperPartition`](RSW/TiltedReducedUpperPartition.lean) | Declarations: `crossed_endpoint_source_box`, `host_bond_pair`, `retained_host_edge_sampled`, `tiltedReducedForcedDual_avoids_core`, … |
| [`RSW/TiltedReducedWindowRead`](RSW/TiltedReducedWindowRead.lean) | Declarations: `tiltedReducedWindowRead`, `tiltedReducedWindowRead_edge`, `tiltedReducedWindowRead_restriction`, `tiltedReducedWindowRead_monotone`, … |
| [`RSW/TiltedStripDualTransport`](RSW/TiltedStripDualTransport.lean) | Declarations: `tiltedStripCrossedBond` |
| [`RSW/TiltedStripFiniteReadEdges`](RSW/TiltedStripFiniteReadEdges.lean) | Declarations: `tiltedStripWindowOriginalRead_edge` |
| [`RSW/TiltedStripMarginalFiniteWindow`](RSW/TiltedStripMarginalFiniteWindow.lean) | Declarations: `tiltedStripWindowOriginalRead`, `tiltedStripFiniteCentralDualRead`, `tiltedStripFiniteReflectedCentralDualRead` |
| [`RSW/TiltedStripReducedCarrier`](RSW/TiltedStripReducedCarrier.lean) | Declarations: `tiltedStripReducedCarrier`, `tiltedStripReducedCrossedBond`, `tiltedStripReducedCrossedBond_involutive`, `tiltedStripReducedCarrier_iff`, … |
| [`RSW/TiltedStripReducedDualCoordinates`](RSW/TiltedStripReducedDualCoordinates.lean) | Declarations: `tiltedStripReducedDualVertex`, `tiltedStripReducedDualBond`, `tiltedStripReducedDualBond_pair`, `tiltedStripReducedDualBond_dualBondOfPrimal`, … |
| [`RSW/TiltedStripReducedLimit`](RSW/TiltedStripReducedLimit.lean) | Declarations: `selfDual_tiltedStrip_clopen_tendsto` |
| [`RSW/TiltedStripReducedReads`](RSW/TiltedStripReducedReads.lean) | Declarations: `tiltedStripReducedRestriction`, `tiltedStripReducedDualTransport`, `tiltedStripReducedRestriction_continuous`, `tiltedStripReducedDualTransport_continuous` |
| [`RSW/TiltedStripTopEdgeIndependence`](RSW/TiltedStripTopEdgeIndependence.lean) | Declarations: `tiltedWindowTopTopEdges`, `tiltedWindowTopTopEdges_related`, `tiltedWindowReducedGraph`, `tiltedWindowReducedGraph_law` |
| [`RSW/TiltedStripWindowReads`](RSW/TiltedStripWindowReads.lean) | Declarations: `tiltedStripCentralRetainedBond`, `tiltedStripCentralSourceEdge`, `tiltedStripCentralReflectedEdge`, `tiltedStripCentralWindowEdge`, … |
| [`RSW/TiltedUpperCorridor`](RSW/TiltedUpperCorridor.lean) | Declarations: `corridor_rectangle_reachable`, `tiltedUpperCorridorState`, `corridor_subrectangle_reachable`, `tiltedUpperCorridor_reachable_cap`, … |
| [`RSW/TranslatedAnnulus`](RSW/TranslatedAnnulus.lean) | Sampled annulus events in translated local windows. A local event reads literal ambient edge states on a translated copy of box(8m). |
| [`RSW/TranslatedAnnulusPositivity`](RSW/TranslatedAnnulusPositivity.lean) | Declarations: `all_true_mem_annulusCircuitEvent_translated`, `finite_annulus_pair_pos_of_reference_containment` |
| [`RSW/WalkChain`](RSW/WalkChain.lean) | Joining chains of actual paths while retaining the vertical constraint. Consecutive shared vertices suffice for a confined-band spanning … |
| [`RSW/WalkClipping`](RSW/WalkClipping.lean) | Clipping a nearest-neighbour walk to a coordinate interval. A chain of intersecting paths may leave the horizontal target rectangle. |
| [`RSW/WiredAnnulusLower`](RSW/WiredAnnulusLower.lean) | Declarations: `rectangle_in_centered_box`, `selfDual_finite_wired_annulus_lower_from_two` |
| [`RSW/WiredBoxSwap`](RSW/WiredBoxSwap.lean) | Declarations: `boxCoordinateSwap_frozen_wired_partition`, `finite_wired_box_probability_swap` |
| [`RSW/WiredCorridorLower`](RSW/WiredCorridorLower.lean) | Declarations: `rectangle_swap_contained_in_box`, `selfDual_finite_wired_corridor_lower` |
| [`RSW/WiredRectangleSample`](RSW/WiredRectangleSample.lean) | Declarations: `horizontalRectangle_wiredBox_mem_finite`, `wiredBox_horizontalRectangle_le_finite`, `selfDual_finite_wired_horizontal_lower` |
| [`StripDual/PrimalVertical`](StripDual/PrimalVertical.lean) | Declarations: `selfDual_strip_primal_vertical_lower_of_small_horizontal` |
| [`StripDual/ReflectedMarginal`](StripDual/ReflectedMarginal.lean) | Declarations: `selfDual_strip_reflected_marginal` |
| [`Touch/FiniteColumnSlopeReflection`](Touch/FiniteColumnSlopeReflection.lean) | Declarations: `tiltedHeight_columnSlopeReflection`, `tiltedTop_columnSlopeReflection`, `tiltedTop_columnSlopeReflection_iff` |
| [`Touch/FiniteHorizontalArcTransport`](Touch/FiniteHorizontalArcTransport.lean) | Declarations: `horizontalLeftPolygonVertex_rectBounds`, `horizontalLeftPolygonWindowVertex`, `horizontalLeftPolygonWindowVertex_val`, `horizontalLeftPolygonDirectGraphIso`, … |
| [`Touch/FiniteHorizontalDualCarrierEmbedding`](Touch/FiniteHorizontalDualCarrierEmbedding.lean) | Declarations: `horizontalLeftRectangleDualVertexToHost`, `horizontalLeftRectangleDualVertexToHost_val` |
| [`Touch/FiniteHorizontalFullRestriction`](Touch/FiniteHorizontalFullRestriction.lean) | Declarations: `horizontalLeftHalfVertexEmbedding` |
| [`Touch/FiniteHorizontalHalfGraph`](Touch/FiniteHorizontalHalfGraph.lean) | The level-zero split as a rectangle graph |
| [`Touch/FiniteRectangleEmbedding`](Touch/FiniteRectangleEmbedding.lean) | Declarations: `tiltedColumnRectangleVertexMap`, `tiltedColumnRectangleEmbedding`, `tiltedColumnGraph_map_le_boundingRectangle` |
| [`Touch/FiniteSplitDomains`](Touch/FiniteSplitDomains.lean) | Declarations: `TiltedColumnVertex`, `tiltedColumnLeftHalfDomain`, `tiltedColumnLeftHalfGraph`, `mem_tiltedColumnLeftHalfDomain` |
| [`Touch/FiniteStripPrimalEvents`](Touch/FiniteStripPrimalEvents.lean) | Declarations: `tiltedColumnBooleanReflectionIso`, `tiltedColumnBooleanReflectionIso_configuration` |
| [`Touch/FiniteStripSymmetry`](Touch/FiniteStripSymmetry.lean) | Finite column truncations for the tilted-strip half-height event. The finite carrier is the strip cut by `\|x\| ≤ L`; the enclosing frozen … |
| [`Touch/InfiniteColumnSlopeReflection`](Touch/InfiniteColumnSlopeReflection.lean) | Declarations: `tiltedStripSlopeReflectionIso`, `tiltedStripSlopeReflectionHomeomorph`, `tiltedStripSlopeReflectionHomeomorph_edge`, `tiltedOpenGraphSlopeReflectionIso`, … |
| [`Touch/InfiniteHalfHeightSlopeReflection`](Touch/InfiniteHalfHeightSlopeReflection.lean) | Declarations: `selfDualTiltedHalfHeight_real_reflection` |
| [`Touch/InfiniteSlopeReflectionLimit`](Touch/InfiniteSlopeReflectionLimit.lean) | Declarations: `tiltedWindowHorizontalReflectionIso`, `tiltedWindowTop_image_horizontalReflection`, `boundaryConditionIso_wired_image_horizontalReflection`, `tiltedWindowBoundary_iso_horizontalReflection`, … |
| [`Touch/InfiniteStripLemma6`](Touch/InfiniteStripLemma6.lean) | Declarations: `TiltedCentralWindowHalfHeightData`, `selfDual_tilted_touch_all_slopes_corrected_of_infiniteHalfHeight` |
| [`Touch/InfiniteStripSlopeReflectionLimit`](Touch/InfiniteStripSlopeReflectionLimit.lean) | Declarations: `reflectX_sym2_involutive`, `tiltedWindowEdge_reflect_ambient`, `tiltedWindowEdge_reflect_ambient_symm`, `tiltedStripEdge_reflect_ambient`, … |
| [`Touch/InfiniteTopEventCylinders`](Touch/InfiniteTopEventCylinders.lean) | Declarations: `walk_support_x_bound`, `tilted_edge_mem_windowCoordinates`, `walk_edge_open_transfers`, `strip_vertical_coordinate_bound`, … |
| [`Touch/ReducedCarrierLemma6`](Touch/ReducedCarrierLemma6.lean) | Declarations: `TiltedReducedCarrierConfiguration`, `tiltedReducedCarrierRead`, `TiltedReducedCarrierHalfHeightData` |
| [`Touch/ReducedMarginalComposition`](Touch/ReducedMarginalComposition.lean) | Declarations: `selfDual_tilted_touch_all_slopes_corrected_of_reducedMarginal` |
