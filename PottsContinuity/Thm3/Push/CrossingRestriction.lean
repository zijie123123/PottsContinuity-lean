module

public import PottsContinuity.Thm3.Push.RectangleGeometry
public import PottsContinuity.Foundations.HorizontalCrossingBridge

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.RCInfinite
noncomputable section

/-- Restriction reads the original sampled bond state, without changing any
boundary partition or adding virtual open edges. -/
theorem bool_embeddedRestriction_state {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (A : Configuration H) (e : G.edgeSet) :
    (boolConfigurationEquiv G).symm (embeddedConfigurationRestriction G H f hGH A) e =
      (boolConfigurationEquiv H).symm A (embeddedEdgeEmbedding G H f hGH e) := by
  classical
  change decide (e ∈ embeddedConfigurationRestriction G H f hGH A) =
    decide (embeddedEdgeEmbedding G H f hGH e ∈ A)
  simp only [mem_embeddedConfigurationRestriction]

/-- A crossing confined to a common rectangle is unchanged when the full
configuration is restricted to an intermediate induced domain. The same
actual sampled bonds and the same rectangle support are retained. -/
theorem horizontalCrossing_embeddedRestriction_iff
    (S T : Finset (ℤ × ℤ)) (hST : S ⊆ T)
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (hRS : PD.FK.latticeRectangle (a,c) (b-a).toNat (d-c).toNat ⊆ S)
    (A : Configuration (finiteLatticeGraph T)) :
    PottsContinuity.horizontalCrossing S a b c d
      ((boolConfigurationEquiv (finiteLatticeGraph S)).symm
        (embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T)
          (finiteLatticeVertexEmbedding hST) (finiteLatticeGraph_map_le hST) A)) ↔
    PottsContinuity.horizontalCrossing T a b c d
      ((boolConfigurationEquiv (finiteLatticeGraph T)).symm A) := by
  let hRT : PD.FK.latticeRectangle (a,c) (b-a).toNat (d-c).toNat ⊆ T :=
    fun _ hx => hST (hRS hx)
  let f := finiteLatticeVertexEmbedding hST
  let hGH := finiteLatticeGraph_map_le hST
  let ωS := (boolConfigurationEquiv (finiteLatticeGraph S)).symm
    (embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T) f hGH A)
  let ωT := (boolConfigurationEquiv (finiteLatticeGraph T)).symm A
  have hstate :
      Foundations.rectangleRestriction (a,c) (b-a).toNat (d-c).toNat S hRS ωS =
      Foundations.rectangleRestriction (a,c) (b-a).toNat (d-c).toNat T hRT ωT := by
    funext e
    let eS := (PottsContinuity.squareLattice.induceHomOfLE
      (show (PD.FK.latticeRectangle (a,c) (b-a).toNat (d-c).toNat : Set (ℤ × ℤ)) ⊆
        (S : Set (ℤ × ℤ)) from fun _ hx => hRS hx)).mapEdgeSet e
    let eT := (PottsContinuity.squareLattice.induceHomOfLE
      (show (PD.FK.latticeRectangle (a,c) (b-a).toNat (d-c).toNat : Set (ℤ × ℤ)) ⊆
        (T : Set (ℤ × ℤ)) from fun _ hx => hRT hx)).mapEdgeSet e
    change ωS eS = ωT eT
    dsimp only [ωS]
    erw [bool_embeddedRestriction_state]
    have heq : embeddedEdgeEmbedding (finiteLatticeGraph S) (finiteLatticeGraph T) f hGH eS = eT := by
      apply Subtype.ext
      erw [embeddedEdgeEmbedding_coe]
      change Sym2.map f (Sym2.map _ e.val) = Sym2.map _ e.val
      rw [Sym2.map_map]
      rfl
    exact congrArg ωT heq
  erw [Foundations.horizontalCrossing_iff_PD_rectangleHorizontalCrossingEvent_of_corners
    a b c d hab hcd S hRS,
    Foundations.horizontalCrossing_iff_PD_rectangleHorizontalCrossingEvent_of_corners
      a b c d hab hcd T hRT]
  rw [hstate]

end
end PottsContinuity.Push
