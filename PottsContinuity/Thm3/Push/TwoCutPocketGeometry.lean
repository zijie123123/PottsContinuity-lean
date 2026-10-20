module

public import PottsContinuity.Thm3.Push.CutComponentPockets
public import PottsContinuity.Thm3.Push.ComponentPocketLaw

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarMixed
noncomputable section

private theorem outside_cut_exterior_along_deleted_walk {V : Type*}
    (G : SimpleGraph V) (A seeds S : Set V)
    (hA : A ⊆ S) {x y : {v : V // v ∉ S}}
    (p : (G.induce Sᶜ).Walk x y)
    (hx : x.val ∉ closedCutExterior G A seeds) :
    y.val ∉ closedCutExterior G A seeds := by
  induction p with
  | nil => exact hx
  | @cons x z y hxz p ih =>
    apply ih
    intro hz
    have hzA := cutComponent_attachment_mem_cut G A seeds hx hz hxz
    exact z.property (hA hzA)

/-- Each deleted component of the intersection of two closed cut exteriors
attaches along one of the two cuts. The cuts themselves are retained. -/
theorem twoCutPockets_attachments_in_same_cut {V : Type*}
    (G : SimpleGraph V) (A C seeds : Set V)
    (hAC : A ⊆ closedCutExterior G C seeds)
    (hCA : C ⊆ closedCutExterior G A seeds)
    (x y : {v : V // v ∉ closedCutExterior G A seeds ∩ closedCutExterior G C seeds})
    (hconn : (G.induce (closedCutExterior G A seeds ∩ closedCutExterior G C seeds)ᶜ).Reachable x y)
    (u v : {z : V // z ∈ closedCutExterior G A seeds ∩ closedCutExterior G C seeds})
    (hxu : G.Adj x.val u.val) (hyv : G.Adj y.val v.val) :
    (u.val ∈ A ∧ v.val ∈ A) ∨ (u.val ∈ C ∧ v.val ∈ C) := by
  classical
  let S := closedCutExterior G A seeds ∩ closedCutExterior G C seeds
  have hA : A ⊆ S := fun _ ha => ⟨Or.inr ha,hAC ha⟩
  have hC : C ⊆ S := fun _ hc => ⟨hCA hc,Or.inr hc⟩
  obtain ⟨p⟩ := hconn
  by_cases hxA : x.val ∈ closedCutExterior G A seeds
  · have hxC : x.val ∉ closedCutExterior G C seeds := fun hxC => x.property ⟨hxA,hxC⟩
    have hyC := outside_cut_exterior_along_deleted_walk G C seeds S hC p hxC
    exact Or.inr ⟨cutComponent_attachment_mem_cut G C seeds hxC u.property.2 hxu,
      cutComponent_attachment_mem_cut G C seeds hyC v.property.2 hyv⟩
  · have hyA := outside_cut_exterior_along_deleted_walk G A seeds S hA p hxA
    exact Or.inl ⟨cutComponent_attachment_mem_cut G A seeds hxA u.property.1 hxu,
      cutComponent_attachment_mem_cut G A seeds hyA v.property.1 hyv⟩

end
end PottsContinuity.Push
