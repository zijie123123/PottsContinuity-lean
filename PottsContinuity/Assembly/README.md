# `PottsContinuity/Assembly/`

Assembly of Theorem 3 from Lemma 6 and the implications between P1-P5.

6 modules, 714 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`AnnulusTransfer`](AnnulusTransfer.lean) | Assembly of the conditional annulus transfer. The finite two-block estimate is proved in `DualityExt.PositiveBoundaryMergePDTransfer`. |
| [`ExactRootRoutes`](ExactRootRoutes.lean) | Declarations: `hP4toP5_of_geometryProvider` |
| [`FourCorridorAssembly`](FourCorridorAssembly.lean) | Declarations: `P4toP5RemainingInputs`, `p4toP5RemainingGeometryProvider`, `p4toP5GeometryProvider_of_remainingInputs`, `hP4toP5_of_remainingGeometryProvider` |
| [`Links`](Links.lean) | Exact formulations of the five frozen Theorem 3 assertions. |
| [`NearFinal`](NearFinal.lean) | Declarations: `theorem_3_of_touch` |
| [`P5aEmbeddedInput`](P5aEmbeddedInput.lean) | Declarations: `P5AnnulusEmbeddedP5aFiniteInput` |
