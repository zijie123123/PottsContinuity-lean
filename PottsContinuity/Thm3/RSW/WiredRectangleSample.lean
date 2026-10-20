module

public import PottsContinuity.Thm3.RSW.FinitePath
public import PottsContinuity.BD12.WiredBoxRadiusProbability
public import PottsContinuity.BD12.WeakRSWFiniteBox

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- A crossing in the wired whole-plane extension inside a contained rectangle
uses only original sampled box bonds and retains its entire confined path. -/
theorem horizontalRectangle_wiredBox_mem_finite (a : LatticeVertex) (w h N : ℕ)
    (hbox : PD.FK.latticeRectangle a w h ⊆ latticeBox (0,0) N)
    (A : Configuration (boxGraph (0,0) N))
    (hA : wiredBoxConfiguration (0,0) N A ∈ horizontalRectangle a w h) :
    horizontalCrossing (latticeBox (0,0) N) a.1 (a.1+w) a.2 (a.2+h)
      ((boolConfigurationEquiv _).symm A) := by
  let ω := wiredBoxConfiguration (0,0) N A
  have hrect := embeddedRestriction_domainGraph (PD.FK.latticeRectangle a w h) ω
  have hlarge : rcOpenGraph (latticeBox (0,0) N) ((boolConfigurationEquiv _).symm A) =
      (PD.rcInfiniteOpenGraph ω).induce (latticeBox (0,0) N : Set LatticeVertex) := by
    erw [rcOpenGraph_boolConfigurationEquiv_symm]
    exact (congrArg (openGraph (boxGraph (0,0) N))
      (embeddedRestriction_wiredBoxConfiguration (0,0) N A)).symm.trans
        (embeddedRestriction_domainGraph (latticeBox (0,0) N) ω)
  obtain ⟨u,v,hu,hv,⟨p⟩⟩ := hA
  let φ : openGraph (rectangleGraph a w h)
      (embeddedRestriction (rectangleGraph a w h)
        (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h)) ω) →g
      rcOpenGraph (latticeBox (0,0) N) ((boolConfigurationEquiv _).symm A) := {
    toFun := fun z => ⟨z.val,hbox z.property⟩
    map_rel' := by
      intro x y hxy
      rw [hlarge]
      have hh : ((PD.rcInfiniteOpenGraph ω).induce
          (PD.FK.latticeRectangle a w h : Set LatticeVertex)).Adj x y := by
        rw [← hrect]
        exact hxy
      exact hh }
  have hu' := (mem_latticeRectangle a u.val w h).mp u.property
  have hv' := (mem_latticeRectangle a v.val w h).mp v.property
  have hux := (Finset.mem_filter.mp hu).2
  have hvx := (Finset.mem_filter.mp hv).2
  refine ⟨φ u,φ v,p.map φ,?_,?_,?_⟩
  · change u.val ∈ ({a.1}:Set ℤ) ×ˢ Set.Icc a.2 (a.2+h)
    exact ⟨hux,hu'.2⟩
  · change v.val ∈ ({a.1+w}:Set ℤ) ×ˢ Set.Icc a.2 (a.2+h)
    exact ⟨hvx,hv'.2⟩
  · intro z hz
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
    obtain ⟨x,hx,rfl⟩ := hz
    exact (mem_latticeRectangle a x.val w h).mp x.property

/-- A contained rectangle crossing under the actual wired-box law is bounded
by the same original-bond crossing on the finite Boolean carrier. -/
theorem wiredBox_horizontalRectangle_le_finite (θ : Parameters)
    (a : LatticeVertex) (w h N : ℕ)
    (hbox : PD.FK.latticeRectangle a w h ⊆ latticeBox (0,0) N) :
    (wiredBoxProbabilityMeasure θ (0,0) N : Measure LatticeConfiguration).real
      (horizontalRectangle a w h) ≤
    finiteBoundaryEventProbability (latticeBox (0,0) N) θ
      (frozenBoundaryCondition (latticeBox (0,0) N) 1)
      (horizontalCrossing (latticeBox (0,0) N) a.1 (a.1+w) a.2 (a.2+h)) := by
  have hp : (wiredBoxProbabilityMeasure θ (0,0) N : Measure LatticeConfiguration).real
      (horizontalRectangle a w h) =
      (measure (boxGraph (0,0) N) θ (BoundaryCondition.wired (boxVertexBoundary (0,0) N))
        {A | wiredBoxConfiguration (0,0) N A ∈ horizontalRectangle a w h}).toReal := by
    change (((law (boxGraph (0,0) N) θ (BoundaryCondition.wired (boxVertexBoundary (0,0) N))).map
      (wiredBoxConfiguration (0,0) N)).toMeasure (horizontalRectangle a w h)).toReal = _
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top (horizontalRectangle_isCylinder a w h).measurableSet]
    rfl
  rw [hp]
  have hξ : frozenBoundaryCondition (latticeBox (0,0) N) 1 =
      BoundaryCondition.wired (boxVertexBoundary (0,0) N) := by
    simp only [frozenBoundaryCondition,show (1 : Fin 2) ≠ 0 by decide,ite_false]
    rfl
  unfold finiteBoundaryEventProbability
  rw [hξ]
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro A hA
  exact horizontalRectangle_wiredBox_mem_finite a w h N hbox A hA

/-- Theorem9 on every contained finite sampled rectangle, with frozen wired
boundary conditions and no event-transport or infinite-volume premise. -/
theorem selfDual_finite_wired_horizontal_lower (q : Set.Ici (1:ℝ))
    (α : ℝ) (hα : 1 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : LatticeVertex) (w h N : ℕ),
      0 < w → (w:ℝ) < α*h → PD.FK.latticeRectangle a w h ⊆ latticeBox (0,0) N →
      c ≤ finiteBoundaryEventProbability (latticeBox (0,0) N) (selfDualParameters q)
        (frozenBoundaryCondition (latticeBox (0,0) N) 1)
        (horizontalCrossing (latticeBox (0,0) N) a.1 (a.1+w) a.2 (a.2+h)) := by
  obtain ⟨c,hc,hbound⟩ := wired_finite_box_weakRSW_at_selfDual q α hα
  exact ⟨c,hc,fun a w h N hw hwh hbox =>
    (hbound a w h N hw hwh hbox).trans
      (wiredBox_horizontalRectangle_le_finite (selfDualParameters q) a w h N hbox)⟩

end
end PottsContinuity.RSW
