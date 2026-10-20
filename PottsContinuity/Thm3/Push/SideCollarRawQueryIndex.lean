module

public import PottsContinuity.Thm3.Push.SideCollarOpenTipBarrier
public import PottsContinuity.Thm3.Push.SideCollarBarrierSeedIndices
public import PottsContinuity.Thm3.Push.SideCollarBarrierSupport
public import PottsContinuity.Thm3.Push.OffTraceFaceIndex
public import PottsContinuity.Thm3.Push.ClosedDualTraceIndex
public import PottsContinuity.Thm3.Push.RawRightDirectIdentification
public import PottsContinuity.Thm3.Push.SideCollarRawDetermination

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.Duality PlanarMixed.FiniteSlit
noncomputable section

/-- One actual tip barrier assigns index minus one to EVERY off-tip endpoint
of EVERY original raw query. The common barrier and its arc index values are
retained; no endpoint separation or selector-locality premise is assumed. -/
theorem sideCollar_exists_barrier_with_raw_query_endpoint_index
    (w h : ℕ) (A : Configuration (rectangleGraph (0,0) w h)) (r : ℤ)
    {a v : RectangleVertex (0,0) w h}
    (q : (openGraph (rectangleGraph (0,0) w h) A).Walk a v)
    (ha : a.val.2 = 0) (hax : 0 < a.val.1) (har : a.val.1 ≤ r)
    (hv : v.val.1 = 0) (hy : 0 < v.val.2) :
    ∃ Q : squareLattice.Walk (a.val.1+2,0) (2,v.val.2),
      Q.support = q.support.map (fun t => (t.val.1+2,t.val.2)) ∧
      ∃ p : squareLattice.Walk (a.val.1+2,0) (a.val.1+2,0),
        (∀ e ∈ p.edges, e ∈ slitBarrierEdges (sideCollarSize w h+2) 2 v.val.2 (a.val.1+2) Q) ∧
        (∀ t : Vertex (sideCollarSize w h+2) 2,
          t ∈ alpha (sideCollarSize w h+2) 2 → rayIndex t.val p = 0) ∧
        (∀ t : Vertex (sideCollarSize w h+2) 2,
          t ∈ beta (sideCollarSize w h+2) 2 v.val.2 → t.val ∉ Q.support → rayIndex t.val p = -1) ∧
        (∀ e ∈ sideCollarRawLeftArmReveal w h r A, ∀ u ∈ e.val,
          u ∉ q.support → rayIndex (sideCollarEmbedding w h u).val p = -1) := by
  classical
  obtain ⟨Q,hQs,hQe,p,hallowed,hα,hβ,hbottom,hopen⟩ :=
    sideCollar_exists_open_tip_barrier w h A q ha hax hv hy
  let N := sideCollarSize w h
  let B := sideCollarExtension w h A
  have hQbounds : ∀ z ∈ Q.support, z.1 ≤ (w:ℤ)+2 ∧ 0 ≤ z.2 := by
    intro z hz
    rw [hQs] at hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    have hu := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
    dsimp only [zero_add] at hu
    exact ⟨by omega,hu.2.1⟩
  have hseed : ∀ t ∈ intervalArmRightDualPorts N (r+2), rayIndex (faceIndexMark t.val) p = -1 := by
    intro t ht
    exact sideCollar_barrier_right_ports_index w h (a.val.1+2) (r+2) v.val.2
      (by omega) (by omega) Q hQbounds p hallowed hβ t ht
  refine ⟨Q,hQs,p,hallowed,hα,hβ,?_⟩
  intro e he u hu hucut
  let E := embeddedEdgeEmbedding (rectangleGraph (0,0) w h) (rectangleGraph (0,0) N N)
    (sideCollarEmbedding w h) (sideCollarEmbedding_map_le w h)
  have heaux : E e ∈ intervalArmRawRightReveal N (r+2) B :=
    (mem_embeddedConfigurationRestriction _ _ _ _ _ e).mp he
  rw [intervalArmRawRightReveal_eq_direct] at heaux
  obtain ⟨f,hf,hidx⟩ := rectangle_raw_query_has_seed_index_of_open_trace (0,0) N N B
    (intervalArmRightDualPorts N (r+2)) p hopen (-1) hseed (E e) heaux
  let d := rectanglePrimalDualEdgeEquiv (0,0) N N (E e)
  let b := rectanglePrimalEdgeBond (0,0) N N (E e)
  have hface : f.val = b.faceBase false ∨ f.val = b.faceBase true := by
    change f ∈ s(rectangleDualEdgeSource (0,0) N N d,rectangleDualEdgeTarget (0,0) N N d) at hf
    rcases Sym2.mem_iff'.mp hf with hf | hf
    · exact Or.inl ((congrArg Subtype.val hf).trans (rectangleDualEdgeSource_faceBase (0,0) N N d))
    · exact Or.inr ((congrArg Subtype.val hf).trans (rectangleDualEdgeTarget_faceBase (0,0) N N d))
  have huE : sideCollarEmbedding w h u ∈ (E e).val := by
    change sideCollarEmbedding w h u ∈ Sym2.map (sideCollarEmbedding w h) e.val
    exact Sym2.mem_map.mpr ⟨u,hu,rfl⟩
  have hpoint : (sideCollarEmbedding w h u).val ∈ b.toSym2 := by
    have hm : (sideCollarEmbedding w h u).val ∈
        Sym2.map (fun t : RectangleVertex (0,0) N N => t.val) (E e).val :=
      Sym2.mem_map.mpr ⟨sideCollarEmbedding w h u,huE,rfl⟩
    exact (rectanglePrimalEdgeBond_toSym2_public (0,0) N N (E e)).symm ▸ hm
  have hincident : b.source = (sideCollarEmbedding w h u).val ∨ b.target = (sideCollarEmbedding w h u).val := by
    exact (Sym2.mem_iff'.mp hpoint).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
  have hoff : (sideCollarEmbedding w h u).val ∉ p.support := by
    intro hup
    have ht := sideCollar_barrier_original_vertex_mem_trace w h (N+2) (by omega)
      (a.val.1+2) v.val.2 Q p hallowed u hup
    rw [hQs] at ht
    obtain ⟨t,ht,heq⟩ := List.mem_map.mp ht
    have htu : sideCollarEmbedding w h t = sideCollarEmbedding w h u := Subtype.ext heq
    exact hucut ((sideCollarEmbedding w h).injective htu ▸ ht)
  have hlocal := rayIndex_incident_face_eq_of_off_support p (sideCollarEmbedding w h u).val hoff b hincident f.val hface
  exact hlocal.symm.trans hidx

end
end PottsContinuity.Push
