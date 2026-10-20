module

public import PottsContinuity.Thm3.Push.CutPocketAugmentation

@[expose] public section

namespace PottsContinuity.Push
open PlanarMixed

/-- Avoiding the opposite seeded cut component places a vertex in the
pocket-augmented exterior. No planar assumption is needed for this direction. -/
theorem mem_pocketAugmented_of_not_opposite_reachable {V : Type*}
    (G : SimpleGraph V) (cut left right : Set V) (v : V)
    (hv : v ∉ cutReachRegion G cut left) :
    v ∈ pocketAugmentedCutExterior G cut left right := by
  classical
  by_cases hr : v ∈ closedCutExterior G cut right
  · exact Or.inl hr
  · right
    rintro (⟨u,hu,p,hp⟩ | hc)
    · rcases hu with hu | hu
      · exact hv ⟨u,hu,p,hp⟩
      · exact hr (Or.inl ⟨u,hu,p,hp⟩)
    · exact hr (Or.inr hc)

end PottsContinuity.Push
