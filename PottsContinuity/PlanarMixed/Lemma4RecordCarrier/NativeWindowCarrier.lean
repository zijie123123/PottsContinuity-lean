module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.SourceWindowBoundary
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.SourceNativeAttachment
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.IncidentVertexLaw
public import PottsContinuity.PlanarMixed.CanonicalCutCarrier

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK RSW Push
noncomputable section

/-- Literal strict-height source window, with both vertical side columns. -/
def lemma4NativeWindowVertices (n : ℕ) (j : Fin 3) :
    Set (box (56*n) : Set LatticeVertex) :=
  {u | (10*(j:ℤ)-13)*(n:ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (10*(j:ℤ)-7)*(n:ℤ) ∧
    -3*(n:ℤ) < u.val.2 ∧ u.val.2 < 3*(n:ℤ)}

/-- The actual unqueried window graph. The two boundary-column vertical edges
are omitted exactly as in the true-dual horizontal reference core. -/
def lemma4NativeWindowGraph (n : ℕ) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :
    SimpleGraph (box (56*n) : Set LatticeVertex) where
  Adj u v := (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A)).Adj u v ∧
    u ∈ lemma4NativeWindowVertices n j ∧ v ∈ lemma4NativeWindowVertices n j ∧
    ¬ (u.val.1=(10*(j:ℤ)-13)*(n:ℤ) ∧ v.val.1=(10*(j:ℤ)-13)*(n:ℤ)) ∧
    ¬ (u.val.1=(10*(j:ℤ)-7)*(n:ℤ) ∧ v.val.1=(10*(j:ℤ)-7)*(n:ℤ))
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm,h.2.2.1,h.2.1,fun hh => h.2.2.2.1 hh.symm,fun hh => h.2.2.2.2 hh.symm⟩⟩
  loopless := ⟨by intro u h; exact (edgeRestriction _ _).loopless.irrefl u h.1⟩

theorem lemma4NativeWindowGraph_le (n : ℕ) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :
    lemma4NativeWindowGraph n A j ≤ edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A) :=
  fun _ _ h => h.1

/-- Every incident native-window vertex lies in the exact strict-height window. -/
theorem lemma4_native_window_incident_vertex_coordinates
    (n : ℕ) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3)
    (u : incidentVertexSet (lemma4NativeWindowGraph n A j)) :
    u.val ∈ lemma4NativeWindowVertices n j := by
  obtain ⟨v,hv⟩ := u.property
  exact hv.2.1

/-- At every strict horizontal interior vertex the actual window retains the
ENTIRE native star. Vertical native exits are excluded by the actual queries. -/
theorem lemma4_native_window_contains_interior_star
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4BandConstructionEvent n) (j : Fin 3)
    (u v : (box (56*n) : Set LatticeVertex))
    (hu : u ∈ lemma4NativeWindowVertices n j)
    (hleft : u.val.1 ≠ (10*(j:ℤ)-13)*(n:ℤ))
    (hright : u.val.1 ≠ (10*(j:ℤ)-7)*(n:ℤ))
    (huv : (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A)).Adj u v) :
    (lemma4NativeWindowGraph n A j).Adj u v := by
  obtain ⟨hG,he⟩ := (edgeRestriction_adj_exists_not_mem _ _ u v).mp huv
  have hcoords := (PD.FK.squareLattice_adj_iff u.val v.val).mp hG
  change (10*(j:ℤ)-13)*(n:ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (10*(j:ℤ)-7)*(n:ℤ) ∧
    -3*(n:ℤ) < u.val.2 ∧ u.val.2 < 3*(n:ℤ) at hu
  have hglobal : -13*(n:ℤ) ≤ u.val.1 ∧ u.val.1 ≤ 13*(n:ℤ) := by
    change (10*(j:ℤ)-13)*(n:ℤ) ≤ u.val.1 ∧ _ at hu
    fin_cases j <;> dsimp at hu <;> omega
  have hheight := lemma4_unqueried_edge_preserves_window_height n hn A hA
    ⟨s(u,v),(lemma4AmbientGraph n).mem_edgeSet.mpr hG⟩ he u v rfl hglobal hu.2.2
  refine ⟨huv,hu,?_,fun hh => hleft hh.1,fun hh => hright hh.1⟩
  change (10*(j:ℤ)-13)*(n:ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (10*(j:ℤ)-7)*(n:ℤ) ∧ _
  exact ⟨by omega,by omega,hheight⟩

/-- An exterior native bond can attach to an active window vertex only on a
vertical side. This holds for every exterior state, before any FK comparison. -/
theorem lemma4_native_window_removed_edge_endpoint_on_side
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4BandConstructionEvent n) (j : Fin 3)
    (e : (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A)).edgeSet)
    (he : e.val ∉ (lemma4NativeWindowGraph n A j).edgeSet)
    (u : incidentVertexSet (lemma4NativeWindowGraph n A j)) (hu : u.val ∈ e.val) :
    u.val.val.1=(10*(j:ℤ)-13)*(n:ℤ) ∨ u.val.val.1=(10*(j:ℤ)-7)*(n:ℤ) := by
  by_contra hnot
  push Not at hnot
  obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective e.val
  have hp : e.val=s(x,y) := hxy.symm
  have hadj := e.property
  rw [hp] at hadj hu
  have hadj' := (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A)).mem_edgeSet.mp hadj
  have hregion := lemma4_native_window_incident_vertex_coordinates n A j u
  rcases Sym2.mem_iff'.mp hu with hux | huy
  · have hwindow := lemma4_native_window_contains_interior_star n hn A hA j u.val y hregion hnot.1 hnot.2 (hux ▸ hadj')
    apply he
    rw [hp,← hux]
    exact (lemma4NativeWindowGraph n A j).mem_edgeSet.mpr hwindow
  · have hwindow := lemma4_native_window_contains_interior_star n hn A hA j u.val x hregion hnot.1 hnot.2 (huy ▸ hadj'.symm)
    apply he
    rw [hp,← huy,Sym2.eq_swap]
    exact (lemma4NativeWindowGraph n A j).mem_edgeSet.mpr hwindow


/-- The actual recorded OPEN edges also attach to active window vertices only
on vertical sides. No extra condition on the frozen partition is assumed. -/
theorem lemma4_record_open_edge_at_active_window_vertex_on_side
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4BandConstructionEvent n) (j : Fin 3)
    (b : (lemma4AmbientGraph n).edgeSet) (hbA : b ∈ A)
    (hb : b ∈ lemma4JointSourceReveal n A)
    (u : incidentVertexSet (lemma4NativeWindowGraph n A j)) (hu : u.val ∈ b.val) :
    u.val.val.1=(10*(j:ℤ)-13)*(n:ℤ) ∨ u.val.val.1=(10*(j:ℤ)-7)*(n:ℤ) := by
  by_contra hnot
  push Not at hnot
  obtain ⟨v,hv⟩ := u.property
  obtain ⟨hG,hd⟩ := (edgeRestriction_adj_exists_not_mem _ _ u.val v).mp hv.1
  have hregion := lemma4_native_window_incident_vertex_coordinates n A j u
  change (10*(j:ℤ)-13)*(n:ℤ) ≤ u.val.val.1 ∧
    u.val.val.1 ≤ (10*(j:ℤ)-7)*(n:ℤ) ∧ _ at hregion
  have hx : (10*(j:ℤ)-13)*(n:ℤ) < u.val.val.1 ∧
      u.val.val.1 < (10*(j:ℤ)-7)*(n:ℤ) := by omega
  exact lemma4_joint_query_no_open_native_window_attachment n hn A hA j
    ⟨s(u.val,v),(lemma4AmbientGraph n).mem_edgeSet.mpr hG⟩ hd u.val
    (Sym2.mem_mk_left _ _) hx hregion.2.2 b hbA hb hu

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
