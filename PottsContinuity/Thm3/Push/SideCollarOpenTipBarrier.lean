module

public import PottsContinuity.Thm3.Push.SideCollarBarrierTrace
public import PottsContinuity.Thm3.Push.EmbeddedOpenGraph
public import PottsContinuity.PlanarMixed.FiniteSlit.RightBarrierLoop
public import PottsContinuity.PlanarTopology.RectangleCurveExclusion

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.Duality PlanarMixed.FiniteSlit PlanarTopology
noncomputable section

/-- Every actual open source tip supplies a closed barrier with its literal
translated trace. All barrier bonds in the sampled auxiliary square are
proved open, and the reference alpha/beta indices are computed. -/
theorem sideCollar_exists_open_tip_barrier
    (w h : ℕ) (A : Configuration (rectangleGraph (0,0) w h))
    {a v : RectangleVertex (0,0) w h}
    (q : (openGraph (rectangleGraph (0,0) w h) A).Walk a v)
    (ha : a.val.2 = 0) (hax : 0 < a.val.1) (hv : v.val.1 = 0) (hy : 0 < v.val.2) :
    ∃ Q : squareLattice.Walk (a.val.1+2,0) (2,v.val.2),
      Q.support = q.support.map (fun t => (t.val.1+2,t.val.2)) ∧
      Q.edges = q.edges.map (Sym2.map (fun t => (t.val.1+2,t.val.2))) ∧
      ∃ p : squareLattice.Walk (a.val.1+2,0) (a.val.1+2,0),
        (∀ e ∈ p.edges, e ∈ slitBarrierEdges (sideCollarSize w h+2) 2 v.val.2 (a.val.1+2) Q) ∧
        (∀ t : Vertex (sideCollarSize w h+2) 2,
          t ∈ alpha (sideCollarSize w h+2) 2 → rayIndex t.val p = 0) ∧
        (∀ t : Vertex (sideCollarSize w h+2) 2,
          t ∈ beta (sideCollarSize w h+2) 2 v.val.2 → t.val ∉ Q.support → rayIndex t.val p = -1) ∧
        (∀ t : ℤ, t < a.val.1+2 → rayIndex (t,0) p = 0) ∧
        (∀ f : (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)).edgeSet,
          (rectanglePrimalEdgeBond (0,0) (sideCollarSize w h) (sideCollarSize w h) f).toSym2 ∈ p.edges →
          f ∈ sideCollarExtension w h A) := by
  classical
  let N := sideCollarSize w h
  let B := sideCollarExtension w h A
  let f := sideCollarEmbedding w h
  have hind : ∀ u t : RectangleVertex (0,0) w h,
      (rectangleGraph (0,0) N N).Adj (f u) (f t) ↔ (rectangleGraph (0,0) w h).Adj u t := by
    intro u t
    change |(u.val.1+2)-(t.val.1+2)|+|u.val.2-t.val.2|=1 ↔
      |u.val.1-t.val.1|+|u.val.2-t.val.2|=1
    simp only [add_sub_add_right_eq_sub]
  let j := embeddedRestrictionOpenEmbedding (rectangleGraph (0,0) w h) (rectangleGraph (0,0) N N)
    f (sideCollarEmbedding_map_le w h) hind B
  have hres : embeddedConfigurationRestriction (rectangleGraph (0,0) w h) (rectangleGraph (0,0) N N)
      f (sideCollarEmbedding_map_le w h) B = A := sideCollarExtension_restriction w h A
  let J : openGraph (rectangleGraph (0,0) w h) A →g openGraph (rectangleGraph (0,0) N N) B :=
    { toFun := f
      map_rel' := by
        intro u t hut
        apply j.map_rel_iff'.mpr
        rw [hres]
        exact hut }
  let qB := q.map J
  have hstart : (J a).val = (a.val.1+2,0) := by
    change (a.val.1+2,a.val.2) = (a.val.1+2,0)
    exact Prod.ext rfl ha
  have hend : (J v).val = (2,v.val.2) := by
    change (v.val.1+2,v.val.2) = (2,v.val.2)
    exact Prod.ext (by omega) rfl
  let Q := (qB.map (rectangleOpenGraphToSquare (0,0) N N B)).copy hstart hend
  have hs : Q.support = q.support.map (fun t => (t.val.1+2,t.val.2)) := by
    calc
      Q.support = (qB.map (rectangleOpenGraphToSquare (0,0) N N B)).support :=
        SimpleGraph.Walk.support_copy _ hstart hend
      _ = q.support.map (fun t => (t.val.1+2,t.val.2)) := by
        rw [SimpleGraph.Walk.support_map]
        change (q.map J).support.map _ = _
        rw [SimpleGraph.Walk.support_map,List.map_map]
        rfl
  have he : Q.edges = q.edges.map (Sym2.map (fun t => (t.val.1+2,t.val.2))) := by
    calc
      Q.edges = (qB.map (rectangleOpenGraphToSquare (0,0) N N B)).edges :=
        SimpleGraph.Walk.edges_copy _ hstart hend
      _ = q.edges.map (Sym2.map (fun t => (t.val.1+2,t.val.2))) := by
        rw [SimpleGraph.Walk.edges_map]
        change (q.map J).edges.map _ = _
        rw [SimpleGraph.Walk.edges_map,List.map_map]
        congr 1
        funext e
        exact Sym2.map_map e
  have hQ : ∀ t ∈ Q.support,
      (2:ℤ) ≤ t.1 ∧ t.1 < 2+((N+2:ℕ):ℤ)-1 ∧ 0 ≤ t.2 ∧ t.2 < ((N+2:ℕ):ℤ) := by
    intro t ht
    rw [hs] at ht
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
    have hu := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
    dsimp only [Prod.fst,Prod.snd,zero_add] at hu
    dsimp [N,sideCollarSize]
    omega
  obtain ⟨p,hp,hα,hβ,hbottom⟩ := exists_right_slit_barrier (N+2) 2 v.val.2 (a.val.1+2)
    (by omega) hy (by omega) Q hQ
  refine ⟨Q,hs,he,p,hp,hα,hβ,hbottom,?_⟩
  have hyh := ((PD.FK.mem_latticeRectangle _ _ _ _).mp v.property).2
  apply sideCollar_barrier_trace_open_of_open_source_trace w h A (N+2) (by omega)
    (a.val.1+2) v.val.2 hy.le (by simpa only [Prod.snd,zero_add] using hyh.2) Q p _ hp
  intro g hg
  apply rectangle_open_walk_trace_subset (0,0) N N B qB
  apply (mem_rectangleTraceConfiguration (0,0) N N _ g).mpr
  change (rectanglePrimalEdgeBond (0,0) N N g).toSym2 ∈ Q.edges at hg
  have hm : Sym2.map (fun t : RectangleVertex (0,0) N N => t.val) g.val ∈ Q.edges :=
    (rectanglePrimalEdgeBond_toSym2_public (0,0) N N g) ▸ hg
  exact (SimpleGraph.Walk.edges_copy _ hstart hend) ▸ hm

end
end PottsContinuity.Push
