module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.OpenColumnGeometry
public import PottsContinuity.Thm3.RSW.TiltedStripWindowReads
public import PottsContinuity.Thm3.Touch.InfiniteTopEventCylinders

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open Thm3.Prop4 PD.FK PD.FK.Medial
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The top-top edges, stated on unordered original strip edges. -/
def WiredTopEdge (N : ℕ) (t : ℝ) (e : (tiltedStripGraph N t).edgeSet) : Prop :=
  Sym2.lift ⟨fun u v : tiltedStripVertices N t =>
    tiltedTop N t u.val ∧ tiltedTop N t v.val,
    fun _ _ => propext and_comm⟩ e.val

/-- Extend the contracted carrier sample closed on the removed top-top bonds. -/
def topErasedConfiguration (N : ℕ) (t : ℝ) (ω : TiltedConfiguration N t) :
    TiltedConfiguration N t :=
  fun e => if WiredTopEdge N t e then false else ω e

/-- Every surviving open edge is an actual original open edge. -/
theorem topErasedOpenGraph_le (N : ℕ) (t : ℝ) (ω : TiltedConfiguration N t) :
    tiltedOpenGraph N t (topErasedConfiguration N t ω) ≤ tiltedOpenGraph N t ω := by
  intro u v h
  obtain ⟨ha,ho⟩ := (tiltedOpenGraph_adj_iff N t _ u v).mp h
  apply (tiltedOpenGraph_adj_iff N t _ u v).mpr
  refine ⟨ha,?_⟩
  dsimp only [topErasedConfiguration] at ho
  split_ifs at ho with ht
  exact ho

/-- Before a walk first reaches the wired class, no used edge joins two
vertices of that class. This applies to arbitrary real strip slopes. -/
theorem walk_reaches_top_after_top_erasure (N : ℕ) (t : ℝ)
    (ω : TiltedConfiguration N t) {u v : tiltedStripVertices N t}
    (p : (tiltedOpenGraph N t ω).Walk u v) (hv : tiltedTop N t v.val) :
    ∃ w : tiltedStripVertices N t, tiltedTop N t w.val ∧
      (tiltedOpenGraph N t (topErasedConfiguration N t ω)).Reachable u w := by
  induction p with
  | @nil a => exact ⟨a,hv,SimpleGraph.Reachable.refl a⟩
  | @cons a b c hab p ih =>
    by_cases ha : tiltedTop N t a.val
    · exact ⟨a,ha,SimpleGraph.Reachable.refl a⟩
    · obtain ⟨w,hw,hpath⟩ := ih hv
      obtain ⟨hedge,hopen⟩ := (tiltedOpenGraph_adj_iff N t ω a b).mp hab
      have hab' : (tiltedOpenGraph N t (topErasedConfiguration N t ω)).Adj a b := by
        apply (tiltedOpenGraph_adj_iff N t _ a b).mpr
        refine ⟨hedge,?_⟩
        simpa only [topErasedConfiguration,WiredTopEdge,Sym2.lift_mk,ha,
          false_and,ite_false] using hopen
      exact ⟨w,hw,hab'.reachable.trans hpath⟩

/-- Reaching the wired top is unchanged by deleting all top-top bonds. -/
theorem connectedToTop_topErased_iff (N : ℕ) (t : ℝ)
    (ω : TiltedConfiguration N t) (z : ℤ × ℤ) :
    tiltedConnectedToTop N t (topErasedConfiguration N t ω) z ↔
      tiltedConnectedToTop N t ω z := by
  constructor
  · rintro ⟨hz,v,hv,⟨p⟩⟩
    exact ⟨hz,v,hv,⟨p.mapLe (topErasedOpenGraph_le N t ω)⟩⟩
  · rintro ⟨hz,v,hv,⟨p⟩⟩
    obtain ⟨w,hw,hp⟩ := walk_reaches_top_after_top_erasure N t ω p hv
    exact ⟨hz,w,hw,hp⟩

/-- In fact the source's full lowest-height observable uses no top-top bond. -/
theorem lowestHeight_topErased_eq (N : ℕ) (hN : 1 ≤ N) (t : ℝ)
    (ω : TiltedConfiguration N t) (x : ℤ) :
    lowestTopConnectedHeight N hN t (topErasedConfiguration N t ω) x =
      lowestTopConnectedHeight N hN t ω x := by
  have hc : topConnectedColumn N t (topErasedConfiguration N t ω) x =
      topConnectedColumn N t ω x := by
    ext y
    rw [mem_topConnectedColumn,mem_topConnectedColumn,connectedToTop_topErased_iff]
  simp only [lowestTopConnectedHeight,lowestTopConnectedVertex,hc]

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
