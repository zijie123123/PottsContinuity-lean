module

public import PottsContinuity.PlanarTopology.KSTRectangleWitness
public import PottsContinuity.BD12.RectangleOpenGraphs
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Pulling an open walk back from an isomorphically transported configuration
uses exactly the original open bonds. -/
theorem kstPathOpen_map_iso_inverse (e : PD.squareLattice ≃g PD.squareLattice)
    (ω : LatticeConfiguration) {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hp : kstPathOpen (latticeConfigurationIsoHomeomorph e ω) p) :
    kstPathOpen ω (p.map e.symm.toHom) := by
  intro f hf
  rw [SimpleGraph.Walk.edges_map] at hf
  obtain ⟨g,hg,hgf⟩ := List.mem_map.mp hf
  let g' : PD.squareLattice.edgeSet := ⟨g,p.edges_subset_edgeSet hg⟩
  have hf' : f = e.symm.mapEdgeSet g' := Subtype.ext hgf.symm
  have hh := hp g' hg
  rw [latticeConfigurationIsoHomeomorph_apply] at hh
  rwa [hf']

/-- A confined original open walk realizes actual connectivity in the sampled
finite rectangle restriction. This does not wire or identify boundary vertices. -/
theorem rectangle_connected_of_kst_open_walk (a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hp : kstPathOpen ω p)
    (hbox : ∀ z ∈ p.support, z ∈ latticeRectangle a w h) :
    ActualConnected (rectangleGraph a w h)
      (embeddedRestriction _ (frozenEdgeEmbedding (latticeRectangle a w h)) ω)
      ⟨u,hbox u p.start_mem_support⟩ ⟨v,hbox v p.end_mem_support⟩ := by
  induction p with
  | @nil u => exact .rfl
  | @cons u v z hadj p ih =>
    have htail : kstPathOpen ω p := by
      intro e he
      exact hp e (List.mem_cons.mpr (Or.inr he))
    have hbox' : ∀ x ∈ p.support, x ∈ latticeRectangle a w h :=
      fun x hx => hbox x (List.mem_cons.mpr (Or.inr hx))
    have hnext := ih htail hbox'
    have hstep : (openGraph (rectangleGraph a w h)
        (embeddedRestriction _ (frozenEdgeEmbedding (latticeRectangle a w h)) ω)).Adj
        ⟨u,hbox u (by simp)⟩ ⟨v,hbox' v p.start_mem_support⟩ := by
      apply (embeddedRestriction_openGraph_adj (rectangleGraph a w h)
        (frozenEdgeEmbedding (latticeRectangle a w h)) ω _ _).mpr
      let e : (rectangleGraph a w h).edgeSet :=
        ⟨s(⟨u,hbox u (by simp)⟩,⟨v,hbox' v p.start_mem_support⟩),hadj⟩
      refine ⟨e,rfl,?_⟩
      exact hp (frozenEdgeEmbedding (latticeRectangle a w h) e) (by
        change s(u,v) ∈ (p.cons hadj).edges
        simp)
    exact hstep.reachable.trans hnext

/-- The original open walk formulation implies the literal rectangle event. -/
theorem horizontalRectangle_of_kst_open_walk (a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hp : kstPathOpen ω p) (hu : u.1 = a.1) (hv : v.1 = a.1+(w : ℤ))
    (hbox : kstPathIn p a.1 (a.1+(w : ℤ)) a.2 (a.2+(h : ℤ))) :
    ω ∈ horizontalRectangle a w h := by
  have hmem : ∀ z ∈ p.support, z ∈ latticeRectangle a w h := by
    intro z hz
    have hh := hbox z hz
    exact (mem_latticeRectangle a z w h).mpr ⟨⟨hh.1,hh.2.1⟩,hh.2.2⟩
  refine ⟨⟨u,hmem u p.start_mem_support⟩,⟨v,hmem v p.end_mem_support⟩,
    Finset.mem_filter.mpr ⟨hmem u p.start_mem_support,hu⟩,
    Finset.mem_filter.mpr ⟨hmem v p.end_mem_support,hv⟩,?_⟩
  exact rectangle_connected_of_kst_open_walk a w h ω p hp hmem

end
end PottsContinuity.PlanarTopology
