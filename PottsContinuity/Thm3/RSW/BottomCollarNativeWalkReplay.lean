module

public import PottsContinuity.Thm3.RSW.ClosedExtensionEmbedding
public import PottsContinuity.Thm3.RSW.RectangleClosedDualStates
public import PottsContinuity.Thm3.RSW.BottomCollarDualBoundary

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite DualityExt
noncomputable section

/-- Every native bottom-collar dual step replays on the original rectangle
closed extension with unchanged face coordinates. Deleted collar bonds are
not added as sampled steps. -/
def bottomCollarDualClosedExtensionHom (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    openGraph (bottomCollarInducedDualGraph a w h) (bottomCollarInducedDualEquiv a w h A) →g
      wholePlaneClosedDualGraph (finiteSubgraphConfiguration (PD.FK.latticeRectangle a w h) 0 A) := by
  let f : RectangleVertex a w h ↪ RectangleVertex (a.1,a.2-1) w (h+1) :=
    FKC.FiniteFK.rectangleArbitraryBottomCollarEmbedding a w h
  have hext := finiteSubgraphConfiguration_embedded_closed_eq
    (S := PD.FK.latticeRectangle a w h)
    (T := PD.FK.latticeRectangle (a.1,a.2-1) w (h+1))
    f (bottomCollar_source_map_le a w h) (fun _ => rfl) A
  let φ := rectangleSubgraphDualClosedExtensionHom (bottomCollar_source_map_le a w h)
    (isolatedExtensionConfigurationEquiv (rectangleGraph a w h) f A)
  refine ⟨Subtype.val,?_⟩
  intro u v huv
  have hp := φ.map_rel huv
  change (wholePlaneClosedDualGraph (finiteSubgraphConfiguration
    (PD.FK.latticeRectangle (a.1,a.2-1) w (h+1)) 0
    (embeddedConfigurationEmbedding (rectangleGraph a w h)
      (rectangleGraph (a.1,a.2-1) w (h+1)) f (bottomCollar_source_map_le a w h) A))).Adj
      u.val v.val at hp
  exact Eq.mp (congrArg (fun ω => (wholePlaneClosedDualGraph ω).Adj u.val v.val) hext) hp

/-- The replay retains the entire native sampled dual walk support. -/
theorem bottomCollarDualClosedExtensionHom_support (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {u v}
    (p : (openGraph (bottomCollarInducedDualGraph a w h)
      (bottomCollarInducedDualEquiv a w h A)).Walk u v) :
    (p.map (bottomCollarDualClosedExtensionHom a w h A)).support =
      p.support.map Subtype.val := by
  rw [SimpleGraph.Walk.support_map]
  rfl

end
end PottsContinuity.RSW
