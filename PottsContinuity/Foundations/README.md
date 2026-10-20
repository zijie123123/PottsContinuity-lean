# `PottsContinuity/Foundations/`

Bridges between the definitions of `Frozen/` and the FK library of `PD/`; existence of limits along every exhaustion.

4 modules, 825 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`BoxBoundary`](BoxBoundary.lean) | Declarations: `mem_box_iff_interval`, `mem_box_iff_abs_le`, `adj_iff`, `abs_eq_natCast_iff`, … |
| [`Bridges`](Bridges.lean) | Declarations: `squareLattice_eq_PD`, `box_eq_PD`, `rcOpenGraph_eq_PD`, `rcInfiniteOpenGraph_eq_PD`, … |
| [`EveryExhaustion`](EveryExhaustion.lean) | Declarations: `eventually_edge_lift_exhaustion`, `endpoint_weight_eq_zero`, `rcProb_endpoint_own`, `endpoint_isRCInfiniteVolumeLimit_all_exhaustions`, … |
| [`HorizontalCrossingBridge`](HorizontalCrossingBridge.lean) | Declarations: `rectangleRestriction`, `openGraphAdj_restriction`, `horizontalCrossing_iff_PD_rectangleHorizontalCrossingEvent_of_restriction`, `pdRectangle_eq_frozenRectangle_of_corners`, … |
