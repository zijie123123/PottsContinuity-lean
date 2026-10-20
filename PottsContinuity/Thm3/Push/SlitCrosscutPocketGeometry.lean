module

public import PottsContinuity.Thm3.Push.TwoCutPocketGeometry
public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutBand
public import PottsContinuity.PlanarMixed.FiniteSlit.VerticalPaths

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- Both actual slit crosscuts lie in the seeded exterior of the other cut.
The left endpoint connects vertically to the bottom alpha arc; the right
endpoint is itself on beta. No pocket-separation premise is requested. -/
theorem slit_crosscuts_cross_seeded_exteriors
    {M : ℕ} {x y : ℤ} (D : CrosscutData M x y) (hM : 2 ≤ M) :
    {w | w ∈ D.first.support} ⊆
      closedCutExterior (graph M x y) {w | w ∈ D.second.support} (alpha M x ∪ beta M x y) ∧
    {w | w ∈ D.second.support} ⊆
      closedCutExterior (graph M x y) {w | w ∈ D.first.support} (alpha M x ∪ beta M x y) := by
  classical
  let l : Vertex M x := ⟨(x-1,0),
    (mem_rectangle_iff M x (by omega) _).mpr ⟨by omega,by omega,by omega,by omega⟩⟩
  obtain ⟨r,hr⟩ := vertical_walk M x y hM l D.firstEnd (by
    change x-1 = D.firstEnd.val.1
    exact D.first_end_column.symm)
  have hravoid : ∀ w ∈ r.support, w ∉ D.second.support := by
    intro w hw hwq
    have hh := (hr w hw).1
    have hq := (D.second_bounds w hwq).1
    change w.val.1 = x-1 at hh
    omega
  have hpavoid : ∀ w ∈ D.first.reverse.support, w ∉ D.second.support := by
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using D.disjoint
  constructor
  · intro w hw
    change w ∈ D.first.support at hw
    left
    have hwr : w ∈ D.first.reverse.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw
    refine ⟨l,Or.inl (Or.inl ⟨rfl,by dsimp [l]; omega⟩),
      r.append (D.first.reverse.takeUntil w hwr),?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact hravoid z hz
    · exact hpavoid z (D.first.reverse.support_takeUntil_subset_support hwr hz)
  · intro w hw
    change w ∈ D.second.support at hw
    left
    have hwr : w ∈ D.second.reverse.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw
    refine ⟨D.secondEnd,Or.inr (Or.inr (Or.inr ?_)),D.second.reverse.takeUntil w hwr,?_⟩
    · rw [D.second_end]
      exact ⟨rfl,le_rfl⟩
    · intro z hz hzp
      have hzq : z ∈ D.second.support := by
        simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using
          D.second.reverse.support_takeUntil_subset_support hwr hz
      exact D.disjoint z hzp hzq

/-- A deleted component for two actual slit crosscuts attaches to only one
of the two cuts, derived from their full geometric record. -/
theorem slit_crosscuts_pocket_attachments_in_same_cut
    {M : ℕ} {x y : ℤ} (D : CrosscutData M x y) (hM : 2 ≤ M) :
    let S := closedCutExterior (graph M x y) {w | w ∈ D.first.support} (alpha M x ∪ beta M x y) ∩
      closedCutExterior (graph M x y) {w | w ∈ D.second.support} (alpha M x ∪ beta M x y)
    ∀ (a b : {v : Vertex M x // v ∉ S}), ((graph M x y).induce Sᶜ).Reachable a b →
      ∀ u v : S, (graph M x y).Adj a.val u.val → (graph M x y).Adj b.val v.val →
        (u.val ∈ D.first.support ∧ v.val ∈ D.first.support) ∨
        (u.val ∈ D.second.support ∧ v.val ∈ D.second.support) := by
  dsimp only
  intro a b hab u v hau hbv
  have h := slit_crosscuts_cross_seeded_exteriors D hM
  exact twoCutPockets_attachments_in_same_cut (graph M x y)
    {w | w ∈ D.first.support} {w | w ∈ D.second.support} (alpha M x ∪ beta M x y)
    h.1 h.2 a b hab u v hau hbv

end
end PottsContinuity.Push
