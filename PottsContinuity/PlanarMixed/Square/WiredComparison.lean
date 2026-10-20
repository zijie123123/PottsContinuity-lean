module

public import PottsContinuity.PlanarMixed.Square.VerticalAlternative
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Actual wired-direction corner comparison

The corner restriction and graph comparison proof patterns are adapted from
FKconvergence/FiniteFK/RectangleDualCornerPrimalComparison.lean, changing BOTH
the actual event and its endpoint side equations from vertical to horizontal.
No boundary wiring is used as a substitute for sampled-path connectivity.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Every finite FK event transports under an actual graph isomorphism.
The event identity is an explicit structural premise of this generic helper. -/
theorem measure_event_configurationIso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (θ : Parameters) (e : G ≃g H)
    (ξ : BoundaryCondition V) (S : Set (Configuration G)) (T : Set (Configuration H))
    (hset : (configurationIso e) ⁻¹' T = S) :
    measure G θ ξ S = measure H θ (boundaryConditionIso e ξ) T := by
  have hm := congrArg PMF.toMeasure (law_configurationIso_map θ e ξ)
  rw [← PMF.toMeasure_map _ _ measurable_from_top] at hm
  change (law G θ ξ).toMeasure S = (law H θ (boundaryConditionIso e ξ)).toMeasure T
  rw [← hm, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top, hset]

/-- Horizontal actual crossing in the restricted corner graph. -/
def rectangleDualCornerHorizontalCrossingEvent (a : LatticeVertex) (w h : ℕ) :
    Set (Configuration (rectangleDualCornerCoreGraph a w h)) :=
  {C | ∃ u v : RectangleVertex a w h,
    u.val.1 = a.1 ∧ v.val.1 = a.1+(w:ℤ) ∧
      ActualConnected (rectangleDualCornerCoreGraph a w h) C u v}

theorem rectangleDualCornerHorizontalCrossingEvent_isUpperSet
    (a : LatticeVertex) (w h : ℕ) :
    IsUpperSet (rectangleDualCornerHorizontalCrossingEvent a w h) := by
  rintro C D hCD ⟨u, v, hu, hv, hc⟩
  exact ⟨u, v, hu, hv, actualConnected_mono hCD hc⟩

/-- The actual dual horizontal path survives the corner clamp. -/
theorem squareDualHorizontal_subset_cornerHorizontal (z : ℤ) (N : ℕ)
    (C : Configuration (rectangleDualGraph (z,z) N N))
    (hC : C ∈ squareDualHorizontalCrossingEvent z N) :
    rectangleDualCornerCoreConfigurationRestriction (z,z) N N C ∈
      rectangleDualCornerHorizontalCrossingEvent (z,z) N N := by
  rcases hC with ⟨u, v, hu, hv, hc⟩
  refine ⟨rectangleDualCornerClamp (z,z) N N u,
    rectangleDualCornerClamp (z,z) N N v, ?_, ?_,
    rectangleDualCornerClamp_actualConnected (z,z) N N C hc⟩
  · change max u.val.1 z = z
    rw [hu]
    exact max_eq_right (by omega)
  · change max v.val.1 z = z+(N:ℤ)
    rw [hv]
    exact max_eq_left (by omega)

/-- The actual joined-side dual horizontal event is bounded by the joined-side
corner horizontal event, with unchanged independent FK parameters. -/
theorem squareDualHorizontal_probability_le_cornerHorizontal
    (θ : Parameters) (z : ℤ) (N : ℕ) :
    (measure (rectangleDualGraph (z,z) N N) θ
      (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides (z,z) N N))
      (squareDualHorizontalCrossingEvent z N)).toReal ≤
    (measure (rectangleDualCornerCoreGraph (z,z) N N) θ
      (BoundaryCondition.wired (rectangleDualCornerSideColumns (z,z) N N))
      (rectangleDualCornerHorizontalCrossingEvent (z,z) N N)).toReal := by
  have hs : squareDualHorizontalCrossingEvent z N ⊆
      {C | rectangleDualCornerCoreConfigurationRestriction (z,z) N N C ∈
        rectangleDualCornerHorizontalCrossingEvent (z,z) N N} :=
    fun C hC => squareDualHorizontal_subset_cornerHorizontal z N C hC
  have hm := ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (μ := measure (rectangleDualGraph (z,z) N N) θ
      (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides (z,z) N N))) hs)
  exact hm.trans (rectangleDualCorner_marginal_bound (z,z) N N θ _
    (rectangleDualCornerHorizontalCrossingEvent_isUpperSet (z,z) N N))

theorem rectangleDualCornerHorizontalCrossing_restriction_subset
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hcross : subgraphConfigurationRestriction
      (rectangleDualCornerCoreGraph_le_rectangle a w h) A ∈
        rectangleDualCornerHorizontalCrossingEvent a w h) :
    A ∈ rectangleHorizontalCrossingEvent a w h := by
  rcases hcross with ⟨u, v, hu, hv, hconn⟩
  have hconnEmbed : ActualConnected (rectangleGraph a w h)
      (subgraphConfigurationEmbedding
        (rectangleDualCornerCoreGraph_le_rectangle a w h)
        (subgraphConfigurationRestriction
          (rectangleDualCornerCoreGraph_le_rectangle a w h) A)) u v := by
    change (openGraph (rectangleGraph a w h)
      (subgraphConfigurationEmbedding
        (rectangleDualCornerCoreGraph_le_rectangle a w h)
        (subgraphConfigurationRestriction
          (rectangleDualCornerCoreGraph_le_rectangle a w h) A))).Reachable u v
    rw [openGraph_subgraphConfigurationEmbedding]
    exact hconn
  have hEmbedSubset := subgraphConfigurationEmbedding_restriction_subset
    (rectangleDualCornerCoreGraph_le_rectangle a w h) A
  have hconnA := actualConnected_mono hEmbedSubset hconnEmbed
  exact ⟨u, v,
    Finset.mem_filter.mpr ⟨u.property, hu⟩,
    Finset.mem_filter.mpr ⟨v.property, hv⟩,
    hconnA⟩

/-- The actual corner-graph vertical crossing probability is bounded above by
the ordinary rectangle vertical crossing probability, with the same FK parameters
and boundary condition. -/
theorem rectangleDualCornerHorizontalCrossing_measure_toReal_le
    (a : LatticeVertex) (w h : ℕ) (q : Parameters)
    (ξ : BoundaryCondition (RectangleVertex a w h)) :
    (measure (rectangleDualCornerCoreGraph a w h) q ξ
      (rectangleDualCornerHorizontalCrossingEvent a w h)).toReal ≤
    (measure (rectangleGraph a w h) q ξ
      (rectangleHorizontalCrossingEvent a w h)).toReal := by
  have hcomp := subgraph_increasing_event_measure_toReal_le
    (rectangleDualCornerCoreGraph_le_rectangle a w h) q ξ
    (rectangleDualCornerHorizontalCrossingEvent a w h)
    (rectangleDualCornerHorizontalCrossingEvent_isUpperSet a w h)
  have hsubset : ∀ A : Configuration (rectangleGraph a w h),
      subgraphConfigurationRestriction
        (rectangleDualCornerCoreGraph_le_rectangle a w h) A ∈
          rectangleDualCornerHorizontalCrossingEvent a w h →
        A ∈ rectangleHorizontalCrossingEvent a w h := by
    intro A hA
    exact rectangleDualCornerHorizontalCrossing_restriction_subset a w h A hA
  have hmon :
      measure (rectangleGraph a w h) q ξ
        {A | subgraphConfigurationRestriction
          (rectangleDualCornerCoreGraph_le_rectangle a w h) A ∈
            rectangleDualCornerHorizontalCrossingEvent a w h} ≤
      measure (rectangleGraph a w h) q ξ
        (rectangleHorizontalCrossingEvent a w h) := by
    apply measure_mono
    exact hsubset
  have hmonReal := ENNReal.toReal_mono
    (measure_ne_top _ _) hmon
  exact hcomp.trans hmonReal

/-- Coordinate swap turns the joined left/right boundary into joined bottom/top. -/
theorem square_joinedSides_boundary_swap (z : ℤ) (N : ℕ) :
    boundaryConditionIso (squarePrimalGraphSwapIso z N)
      (BoundaryCondition.wired (rectangleDualCornerSideColumns (z,z) N N)) =
      BoundaryCondition.wired (rectangleDoubleCollarInnerBottom (z,z) N N ∪
        rectangleDoubleCollarInnerTop (z,z) N N) := by
  rw [boundaryConditionIso_wired_image]
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    change u.val.1 = z ∨ u.val.1 = z+(N:ℤ) at hu
    change (squarePrimalGraphSwapIso z N u).val.2 = z ∨
      (squarePrimalGraphSwapIso z N u).val.2 = z+(N:ℤ)
    exact hu
  · intro hv
    let e := squarePrimalGraphSwapIso z N
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    change (e.symm v).val.1 = z ∨ (e.symm v).val.1 = z+(N:ℤ)
    change v.val.2 = z ∨ v.val.2 = z+(N:ℤ) at hv
    exact hv

/-- Rotation of BOTH an actual horizontal event and its joined-side boundary. -/
theorem square_joinedHorizontal_eq_joinedVertical
    (θ : Parameters) (z : ℤ) (N : ℕ) :
    measure (rectangleGraph (z,z) N N) θ
      (BoundaryCondition.wired (rectangleDualCornerSideColumns (z,z) N N))
      (rectangleHorizontalCrossingEvent (z,z) N N) =
    measure (rectangleGraph (z,z) N N) θ
      (BoundaryCondition.wired (rectangleDoubleCollarInnerBottom (z,z) N N ∪
        rectangleDoubleCollarInnerTop (z,z) N N))
      (rectangleVerticalCrossingEvent (z,z) N N) := by
  have hset : (configurationIso (squarePrimalGraphSwapIso z N)) ⁻¹'
      rectangleVerticalCrossingEvent (z,z) N N = rectangleHorizontalCrossingEvent (z,z) N N := by
    ext C
    exact (rectangleHorizontalCrossingEvent_coordinateSwap_iff (z,z) N N C).symm
  rw [measure_event_configurationIso θ (squarePrimalGraphSwapIso z N) _ _ _ hset,
    square_joinedSides_boundary_swap]

/-- The actual dual wired-direction probability is at most q times the
primal separately wired-direction probability. This geometric comparison is
valid for ALL independent interior FK parameters, not just the self-dual point. -/
theorem squareDualHorizontal_probability_le_q_mul_separateVertical
    (θ : Parameters) (z : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    (measure (rectangleDualGraph (z,z) N N) θ
      (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides (z,z) N N))
      (squareDualHorizontalCrossingEvent z N)).toReal ≤
    θ.val * (measure (rectangleGraph (z,z) N N) θ
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom (z,z) N N)
        (rectangleDoubleCollarInnerTop (z,z) N N)
        (rectangleDoubleCollarInnerBottom_disjoint_top (z,z) N N hN))
      (rectangleVerticalCrossingEvent (z,z) N N)).toReal := by
  let u : RectangleVertex (z,z) N N := ⟨(z,z), by
    rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
  let v : RectangleVertex (z,z) N N := ⟨(z,z+(N:ℤ)), by
    rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
  have hu : u ∈ rectangleDoubleCollarInnerBottom (z,z) N N := rfl
  have hv : v ∈ rectangleDoubleCollarInnerTop (z,z) N N := rfl
  calc
    _ ≤ (measure (rectangleDualCornerCoreGraph (z,z) N N) θ
        (BoundaryCondition.wired (rectangleDualCornerSideColumns (z,z) N N))
        (rectangleDualCornerHorizontalCrossingEvent (z,z) N N)).toReal :=
      squareDualHorizontal_probability_le_cornerHorizontal θ z N
    _ ≤ (measure (rectangleGraph (z,z) N N) θ
        (BoundaryCondition.wired (rectangleDualCornerSideColumns (z,z) N N))
        (rectangleHorizontalCrossingEvent (z,z) N N)).toReal :=
      rectangleDualCornerHorizontalCrossing_measure_toReal_le (z,z) N N θ _
    _ = (measure (rectangleGraph (z,z) N N) θ
        (BoundaryCondition.wired (rectangleDoubleCollarInnerBottom (z,z) N N ∪
          rectangleDoubleCollarInnerTop (z,z) N N))
        (rectangleVerticalCrossingEvent (z,z) N N)).toReal :=
      congrArg ENNReal.toReal (square_joinedHorizontal_eq_joinedVertical θ z N)
    _ ≤ _ := measure_twoBlockBoundary_merge_le_mul θ _ _
      (rectangleDoubleCollarInnerBottom_disjoint_top (z,z) N N hN) hu hv _ _

end
end PottsContinuity.PlanarMixed.Square
