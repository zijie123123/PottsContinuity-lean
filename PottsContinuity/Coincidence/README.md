# `PottsContinuity/Coincidence/`

Equality of free and wired measures for all but countably many p, via continuity of the pressure.

6 modules, 1,101 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`ActivityMarginals`](ActivityMarginals.lean) | Declarations: `activityParameters`, `freeActivityCanonicalLimit`, `freeActivityCanonicalLimit_tendsto`, `freeActivityCanonicalLimit_frozen`, … |
| [`Countability`](Countability.lean) | Declarations: `positiveQ`, `positiveQ_ge_one`, `closedProbability`, `probabilityToActivity`, … |
| [`Exports`](Exports.lean) | Declarations: `coincident_free_limit_unique_infinite_cluster` |
| [`FreeMonotonicity`](FreeMonotonicity.lean) | Declarations: `boxProbabilityMeasure_apply_preimage`, `freeBoxProbabilityMeasure_parameter_mono`, `freeBoxLimit_parameter_mono_of_clopen`, `simpleOpenWalkCylinder_antitone` |
| [`PressureContinuity`](PressureContinuity.lean) | Declarations: `PressureSquareLattice`, `horizontalUnitEdge`, `allOpen_singleton_eq_edgeOpen`, `edgeProbability_eq_of_map_preimage`, … |
| [`Set`](Set.lean) | Declarations: `freeWiredDisagreementSet`, `free_wired_limits_equal_of_not_mem` |
