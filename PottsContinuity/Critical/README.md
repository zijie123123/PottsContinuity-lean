# `PottsContinuity/Critical/`

Existence of the critical point: monotonicity in p, Peierls bounds, threshold construction.

9 modules, 1,841 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`DualCircuitCounting`](DualCircuitCounting.lean) | Declarations: `RCVolumeLimit`, `dualCodeCrossingEdgeList`, `dualCodeCrossingEdgeFinset`, `GoodDualWalkCode`, … |
| [`FiniteMonotonicity`](FiniteMonotonicity.lean) | Finite-volume monotonicity in the edge parameter. For fixed cluster weight and boundary partition, the finite FK law is stochastically … |
| [`InfiniteFKCylinder`](InfiniteFKCylinder.lean) | Declarations: `allClosed`, `allClosed_empty`, `allClosed_insert`, `allOpen_dependsOn_edge_compl`, … |
| [`InfinitePath`](InfinitePath.lean) | Declarations: `exists_path_of_infinite_component`, `infiniteAt_subset_openSimpleWalkEvent` |
| [`PathEventLimits`](PathEventLimits.lean) | Declarations: `walkCodeSupport`, `walk_edge_mem_walkCodeSupport`, `simpleOpenWalkCylinder`, `simpleOpenWalkCylinder_depends_on_walkCodeSupport`, … |
| [`PeierlsLow`](PeierlsLow.lean) | Declarations: `LatticeEdge`, `walkCodeEdgeList`, `walkCodeEdgeList_val`, `walkCodeEdgeList_length`, … |
| [`ThresholdConstruction`](ThresholdConstruction.lean) | Declarations: `wiredBoxCanonicalLimit`, `wiredBoxCanonicalLimit_tendsto`, `wiredBoxCanonicalLimit_PD`, `wiredBoxCanonicalLimit_frozen`, … |
| [`ThresholdMonotonicity`](ThresholdMonotonicity.lean) | Declarations: `IsIncreasingConfigurationEvent`, `wiredBoxConfiguration_mono`, `wiredBox_preimage_upper`, `wiredBoxProbabilityMeasure_apply_preimage`, … |
| [`WalkCounting`](WalkCounting.lean) | Declarations: `latticeStep`, `latticeDirection`, `latticeStep_adj`, `latticeStep_direction`, … |
