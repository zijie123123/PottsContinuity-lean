module

public import PottsContinuity.PlanarMixed.FiniteSlit.ExteriorTopPaths

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section

/-- Every left exterior vertex reaches the original top-left corner while
remaining in that exact projection fibre. -/
theorem left_exterior_to_top (M : ℕ) (x y : ℤ) (w h : ℕ) (hM : 2 ≤ M) (hh : h < M)
    (u : Vertex M x) (hu : exteriorProjection M x w h u = Sum.inr false) :
    ∃ p : (graph M x y).Walk u (leftTop M x (by omega)),
      ∀ z ∈ p.support, exteriorProjection M x w h z = Sum.inr false := by
  have huc := (exteriorProjection_eq_left_iff M x w h u).mp hu
  obtain ⟨p,hp⟩ := outside_walk_to_top M x y w h hM hh u (leftTop M x (by omega))
    rfl huc.1 (Or.inl ⟨huc.2,by change x-(M:ℤ) < x; omega⟩)
  refine ⟨p,?_⟩
  intro z hz
  have hh := hp z hz
  apply (exteriorProjection_eq_left_iff M x w h z).mpr
  refine ⟨hh.1,?_⟩
  rcases hh.2 with hl | hr
  · exact hl.2
  · omega

/-- The right exterior reaches the original top-right corner in its own fibre. -/
theorem right_exterior_to_top (M : ℕ) (x y : ℤ) (w h : ℕ) (hM : 2 ≤ M) (hh : h < M)
    (u : Vertex M x) (hu : exteriorProjection M x w h u = Sum.inr true) :
    ∃ p : (graph M x y).Walk u (rightTop M x (by omega)),
      ∀ z ∈ p.support, exteriorProjection M x w h z = Sum.inr true := by
  have huc := (exteriorProjection_eq_right_iff M x w h u).mp hu
  obtain ⟨p,hp⟩ := outside_walk_to_top M x y w h hM hh u (rightTop M x (by omega))
    rfl huc.1 (Or.inr ⟨huc.2,by change x ≤ x+(M:ℤ)-1; omega⟩)
  refine ⟨p,?_⟩
  intro z hz
  have hh := hp z hz
  apply (exteriorProjection_eq_right_iff M x w h z).mpr
  refine ⟨hh.1,?_⟩
  rcases hh.2 with hl | hr
  · omega
  · exact hr.2

/-- Every projection fibre is connected by actual retained reference walks.
This discharges the connected-fibre premise of the general collapse theorem. -/
theorem exteriorProjection_connected_fibres (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hh : h < M) :
    ∀ u v : Vertex M x, exteriorProjection M x w h u = exteriorProjection M x w h v →
      ∃ p : (graph M x y).Walk u v,
        ∀ z ∈ p.support, exteriorProjection M x w h z = exteriorProjection M x w h u := by
  intro u v huv
  cases hπu : exteriorProjection M x w h u with
  | inl a =>
    have hπv := huv.symm.trans hπu
    have hu := (exteriorProjection_eq_inl_iff M x w h u a).mp hπu
    have hv := (exteriorProjection_eq_inl_iff M x w h v a).mp hπv
    have he : u = v := Subtype.ext (hu.trans hv.symm)
    subst v
    refine ⟨.nil,?_⟩
    intro z hz
    have hz' : z = u := by simpa using hz
    subst z
    exact hπu
  | inr b =>
    cases b with
    | false =>
      obtain ⟨P,hP⟩ := left_exterior_to_top M x y w h hM hh u hπu
      obtain ⟨Q,hQ⟩ := left_exterior_to_top M x y w h hM hh v (huv.symm.trans hπu)
      refine ⟨P.append Q.reverse,?_⟩
      intro z hz
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact hP z hz
      · rw [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hz
        exact hQ z hz
    | true =>
      obtain ⟨P,hP⟩ := right_exterior_to_top M x y w h hM hh u hπu
      obtain ⟨Q,hQ⟩ := right_exterior_to_top M x y w h hM hh v (huv.symm.trans hπu)
      refine ⟨P.append Q.reverse,?_⟩
      intro z hz
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact hP z hz
      · rw [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hz
        exact hQ z hz

end
end PottsContinuity.PlanarMixed.FiniteSlit
