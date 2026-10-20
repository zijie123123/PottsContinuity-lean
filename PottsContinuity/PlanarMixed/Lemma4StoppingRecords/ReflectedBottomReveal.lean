module

public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.SourceCrossingFrontierRead
public import PottsContinuity.PlanarMixed.Square.RectangleVerticalReflection
public import PottsContinuity.Thm3.Push.IsoStoppingReveal

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK Exploration Push Square
noncomputable section
local instance routeSixBottomReadEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- Reflection preserves the exact horizontal event while exchanging the
upper and lower exterior exploration sides. -/
theorem horizontalCrossing_verticalReflection_iff
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h)) :
    configurationIso (rectangleGraphVerticalReflectionIso a w h) A ∈ rectangleHorizontalCrossingEvent a w h ↔
      A ∈ rectangleHorizontalCrossingEvent a w h := by
  let e := rectangleGraphVerticalReflectionIso a w h
  have hf : ∀ B : Configuration (rectangleGraph a w h),
      B ∈ rectangleHorizontalCrossingEvent a w h →
      configurationIso e B ∈ rectangleHorizontalCrossingEvent a w h := by
    intro B hB
    obtain ⟨u,v,hu,hv,hconn⟩ := hB
    refine ⟨e u,e v,?_,?_,(actualConnected_configurationIso e B u v).mpr hconn⟩
    · exact Finset.mem_filter.mpr ⟨(e u).property,(Finset.mem_filter.mp hu).2⟩
    · exact Finset.mem_filter.mpr ⟨(e v).property,(Finset.mem_filter.mp hv).2⟩
  constructor
  · rintro ⟨u,v,hu,hv,hconn⟩
    refine ⟨e.symm u,e.symm v,?_,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨(e.symm u).property,(Finset.mem_filter.mp hu).2⟩
    · exact Finset.mem_filter.mpr ⟨(e.symm v).property,(Finset.mem_filter.mp hv).2⟩
    · apply (actualConnected_configurationIso e A (e.symm u) (e.symm v)).mp
      simpa only [e.apply_symm_apply] using hconn
  · exact hf A

/-- The existing top-frontier exploration transported by the exact rectangle
reflection. This defines no new extremal selector. -/
abbrev rectangleBottomFrontierReveal (a : LatticeVertex) (w h : ℕ) :=
  isoStoppingReveal (rectangleGraphVerticalReflectionIso a w h)
    (Exploration.rectangleTopFrontierReveal a w h)

theorem rectangleBottomFrontierReveal_stable
    (a : LatticeVertex) (w h : ℕ)
    (A B : Configuration (rectangleGraph a w h))
    (hstates : B ∩ rectangleBottomFrontierReveal a w h A=A ∩ rectangleBottomFrontierReveal a w h A) :
    rectangleBottomFrontierReveal a w h B=rectangleBottomFrontierReveal a w h A :=
  isoStoppingReveal_stable _ _ (Exploration.rectangleTopFrontierReveal_stable a w h) A B hstates

theorem horizontalCrossing_readFrom_bottomFrontier
    (a : LatticeVertex) (w h : ℕ) :
    ReadFromReveal (rectangleBottomFrontierReveal a w h) (rectangleHorizontalCrossingEvent a w h) := by
  have hread := readFromReveal_isoStoppingReveal (rectangleGraphVerticalReflectionIso a w h)
    (Exploration.rectangleTopFrontierReveal a w h) (Exploration.rectangleTopFrontierReveal_stable a w h)
    (rectangleHorizontalCrossingEvent a w h) (horizontalCrossing_readFrom_topFrontier a w h)
  have heq : {A | (configurationIso (rectangleGraphVerticalReflectionIso a w h)).symm A ∈ rectangleHorizontalCrossingEvent a w h}=
      rectangleHorizontalCrossingEvent a w h := by
    ext A
    change ((configurationIso (rectangleGraphVerticalReflectionIso a w h)).symm A ∈ rectangleHorizontalCrossingEvent a w h) ↔ _
    have hh := horizontalCrossing_verticalReflection_iff a w h
      ((configurationIso (rectangleGraphVerticalReflectionIso a w h)).symm A)
    simpa only [Equiv.apply_symm_apply] using hh.symm
  rwa [heq] at hread

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
