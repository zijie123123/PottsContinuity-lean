module

public import PottsContinuity.Thm3.Prop4.RawConfinedReplayComparison
public import PottsContinuity.Thm3.Prop4.MarkedBoxRawSourceIdentity

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section

/-- Confined original-edge marked connection is preserved in both directions
by the coordinate-identical box/rectangle isomorphism. -/
theorem sourceBox_confined_event_iso (n : ℕ) (u v : (box n : Set LatticeVertex))
    (T : Set LatticeVertex) :
    {B : Configuration (finiteLatticeGraph (box n)) | configurationIso (boxTubeRectangleIso n) B ∈
      rectangleConfinedMarkedConnectionEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (boxTubeRectangleIso n u) (boxTubeRectangleIso n v) T} =
      {B | ∃ p : (openGraph (finiteLatticeGraph (box n)) B).Walk u v,
        ∀ z ∈ p.support, z.val ∈ T} := by
  let i : finiteLatticeGraph (box n) ≃g rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := boxTubeRectangleIso n
  ext B
  constructor
  · rintro ⟨p,hp⟩
    let j := (openGraphIso i B).symm
    let q := p.map j.toHom
    refine ⟨q,?_⟩
    intro z hz
    have he : q.support = p.support.map j.toHom := SimpleGraph.Walk.support_map j.toHom p
    have hz' := (congrArg (fun L => z ∈ L) he).mp hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz'
    exact hp x hx
  · rintro ⟨p,hp⟩
    let q := p.map (openGraphIso i B).toHom
    refine ⟨q,?_⟩
    intro z hz
    have he : q.support = p.support.map (openGraphIso i B).toHom := SimpleGraph.Walk.support_map (openGraphIso i B).toHom p
    have hz' := (congrArg (fun L => z ∈ L) he).mp hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz'
    exact hp x hx

end
end PottsContinuity.Thm3.Prop4
