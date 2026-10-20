# `PottsContinuity/Thm4Side/`

Side factor of the screen estimate: conditioned laws and stochastic domination.

9 modules, 1,782 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`AuxiliaryArcPartition`](AuxiliaryArcPartition.lean) | Declarations: `SideHostVertex`, `SideHostGraph`, `slitSourceArcVertex`, `slitSourceArcVertex_mem_wiredArc`, … |
| [`AuxiliaryStatePartition`](AuxiliaryStatePartition.lean) | Declarations: `SideStateHostVertex`, `mapWalk_preimage`, `mapWalk_endpoint_mem_range`, `actualConnected_endpoint_mem_range`, … |
| [`DeterministicReveals`](DeterministicReveals.lean) | Declarations: `slitScreenRadius`, `int_abs_succ_bounds`, `int_abs_adj_bounds`, `slitScreenRadius_adj_step`, … |
| [`DualRectangleReveal`](DualRectangleReveal.lean) | Declarations: `slitRightDualRectangleRevealEdges`, `slitRightDualRectangleReveal`, `slitScreenEvent_rightDualRectangleReveal_invariant`, `slitLeftDualRectangleRevealEdges`, … |
| [`ResidualHalfEdges`](ResidualHalfEdges.lean) | Declarations: `slitResidual_edge_endpoints`, `slitResidual_adjacent_x_bounds`, `slitRightHalfReveal_complement_edge_iff` |
| [`RevealConditionedHost`](RevealConditionedHost.lean) | Declarations: `SideStateHostVertex'`, `SideStateHostGraph'`, `sideRevealResidualGraph`, `sideRevealActiveHostEmbedding`, … |
| [`ScreenSideSelection`](ScreenSideSelection.lean) | Declarations: `rightHalf_reveal_adj_of_radius_lt`, `leftHalf_reveal_adj_of_radius_lt`, `transfer_walk_of_fixed_reveal`, `slitScreenEvent_iff_of_agree_rightHalfReveal`, … |
| [`ScreenSideStochasticDomination`](ScreenSideStochasticDomination.lean) | Declarations: `SlitRotatedPushDomRecordInput` |
| [`SideExactLawSpecialization`](SideExactLawSpecialization.lean) | Declarations: `sideExactLawHostVertex`, `sideExactLawHostGraph`, `sideExactLawResidual`, `sideExactLawHostEmbedding`, … |
