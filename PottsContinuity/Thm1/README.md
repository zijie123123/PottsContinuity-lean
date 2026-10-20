# `PottsContinuity/Thm1/`

The Edwards-Sokal coupling in finite and infinite volume, Potts infinite-volume limits, the magnetisation identity and the transfer of critical points; Theorem 1 from Theorem 2.

52 modules, 9,059 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`ClusterColoring`](ClusterColoring.lean) | Finite colourings of connected components. This is the elementary finite counting layer for the ghost-vertex coupling. |
| [`CriticalPointTransfer`](CriticalPointTransfer.lean) | Declarations: `pottsRCProbability`, `isPottsCriticalPoint_log_sqrt_of_limit_magnetisation` |
| [`ESExpansion`](ESExpansion.lean) | Finite spin and bond expansion. Finite products express the Potts weight as a sum over auxiliary bond states. |
| [`FiniteConstraintCounts`](FiniteConstraintCounts.lean) | Declarations: `pottsES_card_functions_fixed_on_finset`, `pottsES_card_functions_pinned_and_fixed` |
| [`FiniteES`](FiniteES.lean) | The Edwards--Sokal graph keeps the outer endpoints of edges meeting `V` as distinct vertices and wires them in the boundary condition. |
| [`FiniteESBridge`](FiniteESBridge.lean) | Declarations: `pottsESOptionSpin`, `forall₂_mem_sym2_map`, `pottsESSpin_eq_optionSpin_forget`, `pottsESEdgeEquiv_agreement_iff`, … |
| [`FiniteESColoring`](FiniteESColoring.lean) | Declarations: `pottsESOriginVertex`, `pottsESSpin_originVertex`, `pottsESCompatible_iff_componentConst`, `pottsESCompatibleColoringEquiv`, … |
| [`FiniteESCylinder`](FiniteESCylinder.lean) | Declarations: `pottsESPatternColorings`, `pottsESConnectivityPatternFunctional`, `pottsES_cylinder_event_joint_law`, `pottsES_cylinder_event_connectivity_pattern` |
| [`FiniteESCylinderLimit`](FiniteESCylinderLimit.lean) | Declarations: `pottsESStatusVolume_monotone`, `pottsESStatus_subset_eventually`, `pottsES_pottsCylinder_probability_tendsto` |
| [`FiniteESMagnetisation`](FiniteESMagnetisation.lean) | Declarations: `pottsESOriginExteriorConnected`, `pottsESOriginExteriorConnectionProbability`, `pottsProb_zero_uniform`, `pottsES_finite_magnetisation_at_zero`, … |
| [`FiniteESMeasure`](FiniteESMeasure.lean) | Declarations: `pottsESCompatible_bool_iff`, `esGibbsWeight_eq_pottsWeight`, `esJointProbability_spin_marginal_potts`, `pottsESBoolCompatibleColoringEquiv`, … |
| [`FiniteESNonneg`](FiniteESNonneg.lean) | Declarations: `pottsESJointLawNonneg`, `pottsESJointLawNonneg_apply` |
| [`FiniteESPatternCount`](FiniteESPatternCount.lean) | Declarations: `pottsESGraphPatternColorings`, `pottsESGraphPatternColorings_card`, `pottsESInteriorVertex`, `pottsESObservedInteriorVertices`, … |
| [`FiniteESPatternQuotient`](FiniteESPatternQuotient.lean) | Declarations: `pottsESObservedComponentClasses`, `pottsES_existsUniqueObservedComponentColor`, `pottsESObservedComponentColor`, `pottsESObservedComponentColor_eq`, … |
| [`FiniteESPatternSignature`](FiniteESPatternSignature.lean) | Declarations: `pottsESPatternClassCompatible`, `pottsESObservedInteriorVertex_exists`, `pottsESPatternColorings_nonempty_imp_classCompatible`, `pottsESConnectivityPatternFunctional_eq_if_classCompatible`, … |
| [`FiniteESRootColoring`](FiniteESRootColoring.lean) | Declarations: `pottsESRootCompatibleColoringEquiv`, `pottsESRootCompatibleColorings_count_of_not_connected`, `pottsESRootCompatibleColorings_count_of_connected` |
| [`FiniteESSignatureAtomLimit`](FiniteESSignatureAtomLimit.lean) | Declarations: `pottsESStatusAtomExit_measurable`, `pottsESStatusAtomPair_measurable`, `pottsESStatusAtomEvent_measurable`, `pottsESFiniteStatusAtom_mass_eq_shell_probability`, … |
| [`FiniteESSignatureClasses`](FiniteESSignatureClasses.lean) | Declarations: `pottsESMarkedVertex`, `pottsESMarkedRelation`, `pottsESMarkedComponentClasses`, `pottsESMarkedQuotientEquivClasses`, … |
| [`FiniteESSignatureQuotient`](FiniteESSignatureQuotient.lean) | Declarations: `pottsESObservedSite`, `pottsESObservedPair`, `pottsESStatusSignature`, `pottsESStatusRawRelation`, … |
| [`FiniteESSignatureSums`](FiniteESSignatureSums.lean) | Declarations: `pottsES_sum_weighted_signature`, `pottsES_cylinder_event_status_sum` |
| [`FiniteESSpinMeasure`](FiniteESSpinMeasure.lean) | Declarations: `pottsESFiniteSpinDistribution`, `pottsESFiniteSpinDistribution_apply`, `pottsESFiniteSpinExtension_measurable`, `pottsESFiniteSpinProbabilityMeasure`, … |
| [`FiniteESStatusAtoms`](FiniteESStatusAtoms.lean) | Declarations: `pottsESStatusPositivePairs`, `pottsESStatusNegativePairs`, `pottsESStatusGhostPositive`, `pottsESStatusGhostNegative`, … |
| [`Parameters`](Parameters.lean) | Finite Edwards--Sokal parameter conversion for positive inverse temperature. |
| [`PottsInfiniteLimit`](PottsInfiniteLimit.lean) | Declarations: `exists_isPottsInfiniteVolumeLimit` |
| [`PottsInfiniteLimitPositive`](PottsInfiniteLimitPositive.lean) | Declarations: `pottsESSpinCylinder_isClopen`, `exists_isPottsInfiniteVolumeLimit_pos` |
| [`PottsInfiniteMagnetisation`](PottsInfiniteMagnetisation.lean) | Declarations: `allClosed_adj_false`, `reachable_allClosed_iff`, `allClosed_origin_notInfinite`, `pottsInfiniteLimit_magnetisation_identity`, … |
| [`ShellBondLimit`](ShellBondLimit.lean) | Declarations: `pottsESShellBondExtension`, `pottsESShellBondExtension_at`, `pottsESShellBondExtension_edge_open_iff`, `pottsESShellBondExtension_allOpen_iff`, … |
| [`ShellBoxComparison`](ShellBoxComparison.lean) | Declarations: `forgetESVertex`, `forgetESVertex_injective`, `pottsEdges_contains_adjacent_pair`, `pottsEdges_endpoints_adjacent`, … |
| [`ShellCylinderBridge`](ShellCylinderBridge.lean) | Declarations: `pottsESAllOpenCylinderEvent`, `pottsESAllOpenCylinderEvent_upper`, `pottsESBoxEmbeddedEdge_original`, `pottsESBoxEdge_shellWitness`, … |
| [`ShellCylinderLimit`](ShellCylinderLimit.lean) | Declarations: `pottsESSupport_mono`, `pottsESSupport_exhaustive`, `pottsES_wiredBoxReal_allOpen`, `pottsESWiredShell_allOpenProbability_tendsto` |
| [`ShellExitComparison`](ShellExitComparison.lean) | Declarations: `pottsESLatticeExitEvent_upper`, `pottsESLatticeExitProbability_le_wiredBox` |
| [`ShellExitDependence`](ShellExitDependence.lean) | Declarations: `pottsESOriginalEdgeEmbedding`, `pottsESLatticeEdgeSet`, `pottsESLatticeEdgeSet_mem_iff`, `pottsESOpenAdj_transfer`, … |
| [`ShellExitFiniteComparison`](ShellExitFiniteComparison.lean) | Declarations: `pottsESLatticeEdgeSet_subset_shellComparisonBox`, `pottsESOriginExteriorConnected_upper`, `pottsESShellRestriction_exit_iff`, `pottsESLatticeExitProbability_le_pottsESShell` |
| [`ShellExitInnerComparison`](ShellExitInnerComparison.lean) | Declarations: `pottsESShellBoxRestriction_exitEvent_iff`, `pottsESOriginExteriorConnectionProbability_le_wiredBoxExit` |
| [`ShellExitLimit`](ShellExitLimit.lean) | Declarations: `pottsESExit_nested_mono`, `pottsESExit_finset_eventually_contained`, `pottsESLatticeExitProbability_tendsto_infiniteAt` |
| [`ShellExitProbabilityLimit`](ShellExitProbabilityLimit.lean) | Declarations: `pottsESBoxEdges_mono`, `pottsESShellExitProbability_eq_finiteConnection`, `pottsESShellExitProbability_tendsto_infiniteAt` |
| [`ShellFullSignatures`](ShellFullSignatures.lean) | Declarations: `pottsESLatticeFullSignatureEvent`, `pottsESConnectionInfiniteFullSignatureEvent`, `pottsESLatticePairGhost_iInter_insert_union`, `pottsESConnectionPairGhost_iInter_insert_union`, … |
| [`ShellGhostConnectivity`](ShellGhostConnectivity.lean) | Declarations: `reachesWiredBoundary`, `boundaryReachRelation`, `componentSetoid_le_boundaryReachRelation`, `pottsESOriginExteriorConnected_iff_reachesBoundary`, … |
| [`ShellLocalComparison`](ShellLocalComparison.lean) | Declarations: `pottsESShellUpperCylinder_lower_bound` |
| [`ShellMagnetisationLimit`](ShellMagnetisationLimit.lean) | Declarations: `pottsESOriginPinnedProbability_tendsto` |
| [`ShellMixedConstraints`](ShellMixedConstraints.lean) | Declarations: `pottsESLatticeMixedConstraintEvent`, `pottsESConnectionInfiniteConstraintEvent`, `pottsESMixed_exit_iInter_eq`, `pottsESShellDecreasingCylinderProbability_tendsto`, … |
| [`ShellMixedPatterns`](ShellMixedPatterns.lean) | Declarations: `pottsESLatticeMixedPairPatternEvent`, `pottsESConnectionInfinitePairPatternEvent`, `pottsESLatticePairGhostPatternEvent`, `pottsESConnectionInfinitePairGhostPatternEvent`, … |
| [`ShellOuterCylinderBridge`](ShellOuterCylinderBridge.lean) | Declarations: `pottsESShellAdj_endpoints`, `pottsESShellEdge_map_forget`, `pottsESShellEmbeddedEdge_original`, `pottsESShellRestriction_cylinder_iff`, … |
| [`ShellPairConnectivity`](ShellPairConnectivity.lean) | Declarations: `pottsESReachesBoundary`, `pottsESBoundaryReachRelation`, `pottsESComponentSetoid_le_boundaryReachRelation`, `pottsESComponentRelation_iff_pathOrBoundary`, … |
| [`ShellPairEvent`](ShellPairEvent.lean) | Declarations: `pottsESLatticeExitEventFrom`, `pottsESLatticePairRelationEvent`, `pottsESOpenWalk_transfer`, `pottsESLatticeExitEventFrom_dependsOn`, … |
| [`ShellPairIntersections`](ShellPairIntersections.lean) | Declarations: `pottsESLatticePairIntersectionEvent`, `pottsESConnectionIntersectionEvent` |
| [`ShellPairPatterns`](ShellPairPatterns.lean) | Declarations: `pottsESLatticePairPatternEvent`, `pottsESConnectionPairPatternEvent` |
| [`ShellPathBridge`](ShellPathBridge.lean) | Declarations: `pottsESVertexCoordinate`, `pottsESLiftLatticeVertex`, `pottsESForgetVertex_injective`, `pottsESOpenAdj_from_latticeOpen`, … |
| [`Theorem1Conditional`](Theorem1Conditional.lean) | Declarations: `theorem_1_of_theorem2_of_limit_magnetisation` |
| [`Theorem1OfTheorem2`](Theorem1OfTheorem2.lean) | Theorem 1 from Theorem 2. The infinite-volume Potts measures exist for every `β ≥ 0`, and the corrected Edwards–Sokal identity `μ[σ₀ = i] = … |
| [`Uniqueness`](Uniqueness.lean) | Declarations: `pottsCylinder`, `pottsCylinder_measurable`, `pottsCylinder_isPiSystem`, `pottsCylinder_generate`, … |
| [`ZeroTemperature`](ZeroTemperature.lean) | Declarations: `eventually_subset_of_exhaustion`, `pottsEventProb_zero_cylinder`, `exists_isPottsInfiniteVolumeLimit_zero` |
