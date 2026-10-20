module

public import PottsContinuity.PlanarTopology.SubpathExtraction
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- The path-graph isomorphism uses the actual chronological vertex number. -/
theorem path_trace_iso_vertex {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (i : Fin (p.length+1)) :
    (hp.pathGraphIsoToSubgraph i).val = p.getVert i.val := by
  change p.support[i.val]'_ = p.getVert i.val
  exact p.support_getElem_eq_getVert _

/-- Chronological ranks along every trace edge differ by exactly one unit. -/
theorem path_trace_rank_step {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (x y : p.toSubgraph.verts) (hxy : p.toSubgraph.coe.Adj x y) :
    |((hp.pathGraphIsoToSubgraph.symm x).val : ℤ)-
      ((hp.pathGraphIsoToSubgraph.symm y).val : ℤ)| ≤ 1 := by
  have h := hp.pathGraphIsoToSubgraph.symm.toHom.map_adj hxy
  change (SimpleGraph.pathGraph (p.length+1)).Adj
    (hp.pathGraphIsoToSubgraph.symm x) (hp.pathGraphIsoToSubgraph.symm y) at h
  rw [SimpleGraph.pathGraph_adj] at h
  rw [abs_le]
  rcases h with h | h <;> constructor <;> omega

/-- A path's trace ranks start at zero and end at its literal length. -/
theorem path_trace_rank_endpoints {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    (hp.pathGraphIsoToSubgraph.symm ⟨a,p.start_mem_verts_toSubgraph⟩).val = 0 ∧
      (hp.pathGraphIsoToSubgraph.symm ⟨b,p.end_mem_verts_toSubgraph⟩).val = p.length := by
  let e := hp.pathGraphIsoToSubgraph
  have hstart : e ⟨0,by omega⟩ = ⟨a,p.start_mem_verts_toSubgraph⟩ := by
    apply Subtype.ext
    rw [path_trace_iso_vertex]
    exact p.getVert_zero
  have hend : e ⟨p.length,by omega⟩ = ⟨b,p.end_mem_verts_toSubgraph⟩ := by
    apply Subtype.ext
    rw [path_trace_iso_vertex]
    exact p.getVert_length
  constructor
  · rw [← hstart,e.symm_apply_apply]
  · rw [← hend,e.symm_apply_apply]

/-- Contiguous subwalks map across graph homomorphisms even when the
source and target vertex TYPES differ. -/
theorem isSubwalk_map_hom {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}
    {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (h : p.IsSubwalk q) (f : G →g K) : (p.map f).IsSubwalk (q.map f) := by
  obtain ⟨r,s,he⟩ := h
  refine ⟨r.map f,s.map f,?_⟩
  rw [he,SimpleGraph.Walk.map_append,SimpleGraph.Walk.map_append]

set_option backward.isDefEq.respectTransparency false in
/-- A walk in a simple path's edge trace forces the actual chronological
segment between its endpoints to stay wherever that walk stays. Ordered form. -/
theorem path_subpath_of_trace_walk_of_rank_le {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (x y : p.toSubgraph.verts) (q : p.toSubgraph.coe.Walk x y)
    (H : Set V) (hq : ∀ z ∈ q.support, z.val ∈ H)
    (hxy : (hp.pathGraphIsoToSubgraph.symm x).val ≤
      (hp.pathGraphIsoToSubgraph.symm y).val) :
    ∃ r : G.Walk x.val y.val, r.IsSubwalk p ∧ r.IsPath ∧
      ∀ z ∈ r.support, z ∈ H := by
  let e := hp.pathGraphIsoToSubgraph
  let f : p.toSubgraph.verts → ℤ := fun z => (e.symm z).val
  have hstep : ∀ u v, p.toSubgraph.coe.Adj u v → |f u-f v| ≤ 1 :=
    path_trace_rank_step p hp
  have hfinj : Function.Injective f := by
    intro u v h
    apply e.symm.injective
    apply Fin.ext
    change ((e.symm u).val : ℤ) = ((e.symm v).val : ℤ) at h
    exact_mod_cast h
  have hs : f ⟨a,p.start_mem_verts_toSubgraph⟩ = 0 := by
    change ((hp.pathGraphIsoToSubgraph.symm ⟨a,p.start_mem_verts_toSubgraph⟩).val : ℤ) = 0
    rw [(path_trace_rank_endpoints p hp).1]
    rfl
  have ht : f ⟨b,p.end_mem_verts_toSubgraph⟩ = (p.length : ℤ) := by
    change ((hp.pathGraphIsoToSubgraph.symm ⟨b,p.end_mem_verts_toSubgraph⟩).val : ℤ) = _
    rw [(path_trace_rank_endpoints p hp).2]
  have hfx : 0 ≤ f x := Int.natCast_nonneg _
  have hfy : f y ≤ (p.length : ℤ) := by
    change ((e.symm y).val : ℤ) ≤ (p.length : ℤ)
    exact_mod_cast (Nat.le_of_lt_succ (e.symm y).isLt)
  have hxyZ : f x ≤ f y := by
    change ((e.symm x).val : ℤ) ≤ ((e.symm y).val : ℤ)
    exact_mod_cast hxy
  have hpp : p.mapToSubgraph.IsPath := by
    apply SimpleGraph.Walk.IsPath.of_map (f := p.toSubgraph.hom)
    simpa only [p.map_mapToSubgraph_hom] using hp
  obtain ⟨u,v,r,hr,hrp,hu,hv,hrslab⟩ := path_subpath_between_levels f hstep
    p.mapToSubgraph hpp hxyZ (by rw [hs]; exact hfx) (by rw [ht]; exact hfy)
  have hux : u = x := hfinj hu
  have hvy : v = y := hfinj hv
  subst u
  subst v
  have hrH : ∀ z ∈ r.support, z.val ∈ H := by
    intro z hz
    have hzb := hrslab z hz
    obtain ⟨z',q0,q1,hz',hqq,_⟩ := walk_prefix_at_level f hstep q (f z) hzb.1 hzb.2
    have hzq : z' ∈ q.support :=
      (SimpleGraph.Walk.isSubwalk_of_append_left hqq).support_subset q0.end_mem_support
    have heq : z' = z := hfinj hz'
    exact heq ▸ hq z' hzq
  have hsub : (r.map p.toSubgraph.hom).IsSubwalk p := by
    simpa only [p.map_mapToSubgraph_hom] using isSubwalk_map_hom hr p.toSubgraph.hom
  refine ⟨r.map p.toSubgraph.hom,hsub,SimpleGraph.Walk.isPath_of_isSubwalk hsub hp,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  exact hrH w hw

/-- Chronology recovery from a restricted edge trace: connectivity through a
set H produces a CONTIGUOUS subpath of the given simple path, in one of its
two orientations. No rerouting or replacement by an unrelated simple path. -/
theorem path_subpath_of_trace_walk {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (x y : p.toSubgraph.verts) (q : p.toSubgraph.coe.Walk x y)
    (H : Set V) (hq : ∀ z ∈ q.support, z.val ∈ H) :
    ∃ r : G.Walk x.val y.val, (r.IsSubwalk p ∨ r.reverse.IsSubwalk p) ∧ r.IsPath ∧
      ∀ z ∈ r.support, z ∈ H := by
  by_cases hxy : (hp.pathGraphIsoToSubgraph.symm x).val ≤
      (hp.pathGraphIsoToSubgraph.symm y).val
  · obtain ⟨r,hr,hrp,hrH⟩ := path_subpath_of_trace_walk_of_rank_le p hp x y q H hq hxy
    exact ⟨r,Or.inl hr,hrp,hrH⟩
  · have hyx : (hp.pathGraphIsoToSubgraph.symm y).val ≤
        (hp.pathGraphIsoToSubgraph.symm x).val := by omega
    have hqr : ∀ z ∈ q.reverse.support, z.val ∈ H := by
      intro z hz
      exact hq z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz)
    obtain ⟨r,hr,hrp,hrH⟩ := path_subpath_of_trace_walk_of_rank_le p hp y x q.reverse H hqr hyx
    refine ⟨r.reverse,Or.inr (by simpa only [SimpleGraph.Walk.reverse_reverse] using hr),
      hrp.reverse,?_⟩
    intro z hz
    exact hrH z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz)

set_option backward.isDefEq.respectTransparency false in
/-- Lift an actual walk whose every edge belongs to a given trace into that
trace's vertex subtype. Both endpoint memberships are explicit, also for nil walks. -/
theorem exists_trace_walk_of_edges_subset {V : Type*} {G : SimpleGraph V}
    {a b x y : V} (p : G.Walk a b) (q : G.Walk x y)
    (hx : x ∈ p.toSubgraph.verts) (hy : y ∈ p.toSubgraph.verts)
    (he : q.edges ⊆ p.edges) :
    ∃ r : p.toSubgraph.coe.Walk ⟨x,hx⟩ ⟨y,hy⟩, r.map p.toSubgraph.hom = q := by
  revert hx hy he
  induction q with
  | nil =>
    intro hx hy he
    exact ⟨.nil,rfl⟩
  | @cons x z y h q ih =>
    intro hx hy he
    have ht : p.toSubgraph.Adj x z :=
      SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr (he (by simp))
    have hz : z ∈ p.toSubgraph.verts := ht.snd_mem
    have hrest : q.edges ⊆ p.edges := by
      intro edge hedge
      apply he
      simp only [SimpleGraph.Walk.edges_cons,List.mem_cons]
      exact Or.inr hedge
    obtain ⟨r,hr⟩ := ih hz hy hrest
    have htcoe : p.toSubgraph.coe.Adj ⟨x,hx⟩ ⟨z,hz⟩ := ht
    refine ⟨r.cons htcoe,?_⟩
    simp only [SimpleGraph.Walk.map_cons,hr]

set_option backward.isDefEq.respectTransparency false in
/-- Connectivity using only the given simple path's edges yields a genuine
contiguous subpath with the same endpoints and the same confinement set. -/
theorem path_subpath_of_edges_subset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b x y : V} (p : G.Walk a b) (hp : p.IsPath) (q : G.Walk x y)
    (hx : x ∈ p.support) (hy : y ∈ p.support) (he : q.edges ⊆ p.edges)
    (H : Set V) (hq : ∀ z ∈ q.support, z ∈ H) :
    ∃ r : G.Walk x y, (r.IsSubwalk p ∨ r.reverse.IsSubwalk p) ∧ r.IsPath ∧
      ∀ z ∈ r.support, z ∈ H := by
  let x' : p.toSubgraph.verts := ⟨x,p.mem_verts_toSubgraph.mpr hx⟩
  let y' : p.toSubgraph.verts := ⟨y,p.mem_verts_toSubgraph.mpr hy⟩
  obtain ⟨q',hqq⟩ := exists_trace_walk_of_edges_subset p q x'.property y'.property he
  apply path_subpath_of_trace_walk p hp x' y' q' H
  intro z hz
  apply hq
  rw [← hqq,SimpleGraph.Walk.support_map]
  exact List.mem_map.mpr ⟨z,hz,rfl⟩

end PottsContinuity.PlanarTopology
