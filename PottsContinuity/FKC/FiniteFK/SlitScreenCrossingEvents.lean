-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitScreenCrossingEvents.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitScreenMonotonicity
public import PottsContinuity.FKC.FiniteFK.SlitScreenActualClosedGraph
public import PottsContinuity.FKC.FiniteFK.SlitScreenLocalSupport

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- The right-screen bottom-to-top closed-dual crossing event on the actual
finite slit-box configuration space. The reachability semantics are inherited
unchanged from `slitScreenClosedDualReachabilityEvent`. -/
def slitScreenRightCrossingEvent (m : ℕ) :
    Set (Configuration (slitBoxGraph (16 * m))) :=
  slitScreenClosedDualReachabilityEvent (16 * m)
    (slitScreenRightFaceBases m)
    (slitScreenBottomTerminals m (slitScreenRightFaceBases m))
    (slitScreenTopTerminals m (slitScreenRightFaceBases m))

/-- The corresponding left-screen bottom-to-top closed-dual crossing event. -/
def slitScreenLeftCrossingEvent (m : ℕ) :
    Set (Configuration (slitBoxGraph (16 * m))) :=
  slitScreenClosedDualReachabilityEvent (16 * m)
    (slitScreenLeftFaceBases m)
    (slitScreenBottomTerminals m (slitScreenLeftFaceBases m))
    (slitScreenTopTerminals m (slitScreenLeftFaceBases m))

/-- The literal actual finite closed-edge crossing event for the right screen. -/
def slitScreenRightActualClosedDualCrossingEvent (m : ℕ) :
    Set (Configuration (slitBoxGraph (16 * m))) :=
  {A | ∃ x ∈ slitScreenBottomTerminals m (slitScreenRightFaceBases m),
    ∃ y ∈ slitScreenTopTerminals m (slitScreenRightFaceBases m),
      (slitScreenActualConfigurationClosedDualGraph m A
        (slitScreenRightFaceBases m)).Reachable x y}

/-- The literal actual finite closed-edge crossing event for the left screen. -/
def slitScreenLeftActualClosedDualCrossingEvent (m : ℕ) :
    Set (Configuration (slitBoxGraph (16 * m))) :=
  {A | ∃ x ∈ slitScreenBottomTerminals m (slitScreenLeftFaceBases m),
    ∃ y ∈ slitScreenTopTerminals m (slitScreenLeftFaceBases m),
      (slitScreenActualConfigurationClosedDualGraph m A
        (slitScreenLeftFaceBases m)).Reachable x y}

/-- For m≥1, the right event equals reachability in the literal finite graph
whose edges are the original slit edges closed by the configuration. -/
theorem slitScreenRightCrossingEvent_eq_actualClosedDual (m : ℕ) (hm : 1 ≤ m) :
    slitScreenRightCrossingEvent m =
      slitScreenRightActualClosedDualCrossingEvent m := by
  ext A
  change (∃ x ∈ slitScreenBottomTerminals m (slitScreenRightFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenRightFaceBases m),
        (slitScreenClosedDualInducedGraph
          (slitBoxConfigurationExtension (16 * m) A)
          (slitScreenRightFaceBases m)).Reachable x y) ↔
    (∃ x ∈ slitScreenBottomTerminals m (slitScreenRightFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenRightFaceBases m),
        (slitScreenActualConfigurationClosedDualGraph m A
          (slitScreenRightFaceBases m)).Reachable x y)
  exact slitScreenRightFiniteConfigurationCrossing_iff_slitRestricted m hm A

/-- The analogous exact event equality for the left screen. -/
theorem slitScreenLeftCrossingEvent_eq_actualClosedDual (m : ℕ) (hm : 1 ≤ m) :
    slitScreenLeftCrossingEvent m =
      slitScreenLeftActualClosedDualCrossingEvent m := by
  ext A
  change (∃ x ∈ slitScreenBottomTerminals m (slitScreenLeftFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenLeftFaceBases m),
        (slitScreenClosedDualInducedGraph
          (slitBoxConfigurationExtension (16 * m) A)
          (slitScreenLeftFaceBases m)).Reachable x y) ↔
    (∃ x ∈ slitScreenBottomTerminals m (slitScreenLeftFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenLeftFaceBases m),
        (slitScreenActualConfigurationClosedDualGraph m A
          (slitScreenLeftFaceBases m)).Reachable x y)
  exact slitScreenLeftFiniteConfigurationCrossing_iff_slitRestricted m hm A

/-- Agreement on the actual right-screen support makes membership in the
closed-dual right crossing event identical. -/
theorem slitScreenRightCrossingEvent_iff_of_agree_on_support
    (m : ℕ) (hm : 1 ≤ m) (A B : Configuration (slitBoxGraph (16 * m)))
    (hagree : ∀ e ∈ slitScreenActualClosedGraphSupport m
      (slitScreenRightFaceBases m), (e ∈ A ↔ e ∈ B)) :
    (A ∈ slitScreenRightCrossingEvent m ↔ B ∈ slitScreenRightCrossingEvent m) := by
  have hA : A ∈ slitScreenRightCrossingEvent m ↔
      A ∈ slitScreenRightActualClosedDualCrossingEvent m := by
    rw [slitScreenRightCrossingEvent_eq_actualClosedDual m hm]
  have hB : B ∈ slitScreenRightCrossingEvent m ↔
      B ∈ slitScreenRightActualClosedDualCrossingEvent m := by
    rw [slitScreenRightCrossingEvent_eq_actualClosedDual m hm]
  have hLocal : A ∈ slitScreenRightActualClosedDualCrossingEvent m ↔
      B ∈ slitScreenRightActualClosedDualCrossingEvent m := by
    change (∃ x ∈ slitScreenBottomTerminals m (slitScreenRightFaceBases m),
        ∃ y ∈ slitScreenTopTerminals m (slitScreenRightFaceBases m),
          (slitScreenActualConfigurationClosedDualGraph m A
            (slitScreenRightFaceBases m)).Reachable x y) ↔
      (∃ x ∈ slitScreenBottomTerminals m (slitScreenRightFaceBases m),
        ∃ y ∈ slitScreenTopTerminals m (slitScreenRightFaceBases m),
          (slitScreenActualConfigurationClosedDualGraph m B
            (slitScreenRightFaceBases m)).Reachable x y)
    exact slitScreenActualReachability_iff_of_agree_on_support
      (m := m) (F := slitScreenRightFaceBases m) (A := A) (B := B)
      (S := slitScreenBottomTerminals m (slitScreenRightFaceBases m))
      (T := slitScreenTopTerminals m (slitScreenRightFaceBases m)) hagree
  exact hA.trans (hLocal.trans hB.symm)

end PottsContinuity.FKC.FiniteFK
