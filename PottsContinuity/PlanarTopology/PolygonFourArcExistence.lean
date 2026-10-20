module

public import PottsContinuity.PlanarTopology.DobrushinExteriorExtraction

@[expose] public section

namespace PottsContinuity.PlanarTopology
open FKC FKC.Medial FKC.FiniteFK

/-- Literal boundary vertices at a specified set of cyclic indices. -/
def polygonBoundaryVertices {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (I : Set (ZMod (m+3))) :
    Set (DomainVertex δ (P.domain δ)) :=
  {v | ∃ i ∈ I, P.boundaryVertex δ i = v}

/-- Actual exterior dual cells adjacent to the specified original boundary
edges. Their face bases, not auxiliary exterior caps, are the dual targets. -/
def polygonExteriorFaces {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (I : Set (ZMod (m+3))) : Set FKC.LatticeVertex :=
  {z | ∃ i ∈ I, z = (P.boundaryBond i).faceBase (P.boundaryOutsideSide δ i)}

/-- Every exterior retained occurrence has its actual surviving boundary label. -/
theorem retainedPort_exterior_label {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (a : ZMod (m+3)) (k : ℕ)
    (p : P.RetainedPort δ a k)
    (hp : ¬(openLatticeCell δ p.val.toLatticePort.faceBase ⊆ P.domain δ)) :
    ∃ r : ZMod (m+3) × Bool, p.val = P.boundaryCapPort δ r ∧
      ¬FKC.LatticePolygon.WiredArcIndex a k r.1 ∧
      domainPortPrimalVertex p.val =
        P.boundaryVertex δ (FKC.LatticePolygon.boundaryCapVertexIndex r) := by
  obtain ⟨r,hr⟩ := (P.domainPort_not_inside_iff_mem_boundaryCap δ p.val).mp hp
  refine ⟨r,hr.symm,?_,?_⟩
  · have h := p.property.resolve_left hp
    rw [← hr,P.boundaryCapPort_removed_iff] at h
    exact h
  · apply Subtype.ext
    rw [domainPortPrimalVertex_val,← hr,P.boundaryCapPort_primalVertex]
    rfl

/-- The endpoint index of a cyclic edge is its start or its cyclic successor. -/
theorem boundaryCapVertexIndex_val_cases {m : ℕ} (r : ZMod (m+3) × Bool) :
    (FKC.LatticePolygon.boundaryCapVertexIndex r).val = r.1.val ∨
    (FKC.LatticePolygon.boundaryCapVertexIndex r).val = r.1.val+1 ∨
    ((FKC.LatticePolygon.boundaryCapVertexIndex r).val = 0 ∧ r.1.val+1 = m+3) := by
  have : NeZero (m+3) := ⟨by omega⟩
  have : Fact (1 < m+3) := ⟨by omega⟩
  rcases r with ⟨i,b⟩
  cases b
  · exact Or.inl rfl
  · change (i+1).val = i.val ∨ (i+1).val = i.val+1 ∨
      ((i+1).val = 0 ∧ i.val+1 = m+3)
    rw [ZMod.val_add,ZMod.val_one]
    have hi := ZMod.val_lt i
    by_cases h : i.val+1 < m+3
    · exact Or.inr (Or.inl (Nat.mod_eq_of_lt h))
    · have he : i.val+1 = m+3 := by omega
      exact Or.inr (Or.inr ⟨by rw [he,Nat.mod_self],he⟩)

/-- A surviving edge of an initial arc has an index at least its length. -/
theorem surviving_initial_arc_index {m : ℕ} {k : ℕ} (i : ZMod (m+3))
    (h : ¬FKC.LatticePolygon.WiredArcIndex 0 k i) : k ≤ i.val := by
  by_contra hn
  apply h
  refine ⟨i.val,by omega,?_⟩
  simp

/-- Outside the initial wired arc, an exterior occurrence that avoids a
second closed boundary interval belongs to one of the two intervening arcs. -/
theorem exterior_initial_arc_classification {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (k l r : ℕ) (hk : 1 ≤ k) (hkl : k < l)
    (_hlr : l ≤ r) (_hr : r < m+3) (p : P.RetainedPort δ 0 k)
    (hp : ¬(openLatticeCell δ p.val.toLatticePort.faceBase ⊆ P.domain δ))
    (havoid : domainPortPrimalVertex p.val ∉
      polygonBoundaryVertices P δ {j | l ≤ j.val ∧ j.val ≤ r}) :
    domainPortPrimalVertex p.val ∈
        polygonBoundaryVertices P δ {j | j.val = 0 ∨ r < j.val} ∨
      domainPortPrimalVertex p.val ∈
        polygonBoundaryVertices P δ {j | k ≤ j.val ∧ j.val < l} := by
  obtain ⟨b,_,hb,hv⟩ := retainedPort_exterior_label P δ 0 k p hp
  let j := FKC.LatticePolygon.boundaryCapVertexIndex b
  have hnot : ¬(l ≤ j.val ∧ j.val ≤ r) := by
    intro h
    exact havoid ⟨j,h,hv.symm⟩
  have hi := surviving_initial_arc_index b.1 hb
  have hj := boundaryCapVertexIndex_val_cases b
  by_cases hL : j.val = 0 ∨ r < j.val
  · exact Or.inl ⟨j,hL,hv.symm⟩
  · right
    refine ⟨j,?_,hv.symm⟩
    change k ≤ j.val ∧ j.val < l
    dsimp only [j] at *
    rcases hj with hj | hj | ⟨hj,_⟩ <;> omega

/-- Exterior ports at the final complementary vertex arc have face bases
adjacent to final complementary BOUNDARY EDGES. -/
theorem exterior_final_arc_face {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (k r : ℕ) (hk : 1 ≤ k) (hr : r < m+3)
    (p : P.RetainedPort δ 0 k)
    (hp : ¬(openLatticeCell δ p.val.toLatticePort.faceBase ⊆ P.domain δ))
    (hv : domainPortPrimalVertex p.val ∈
      polygonBoundaryVertices P δ {j | j.val = 0 ∨ r < j.val}) :
    p.val.toLatticePort.faceBase ∈ polygonExteriorFaces P δ {i | r ≤ i.val} := by
  obtain ⟨b,hb,hmask,hvertex⟩ := retainedPort_exterior_label P δ 0 k p hp
  obtain ⟨j,hj,hjv⟩ := hv
  change j.val = 0 ∨ r < j.val at hj
  have he : j = FKC.LatticePolygon.boundaryCapVertexIndex b :=
    P.boundaryVertex_injective δ (hjv.trans hvertex)
  rw [he] at hj
  have hi := surviving_initial_arc_index b.1 hmask
  have hcases := boundaryCapVertexIndex_val_cases b
  have hiB : r ≤ b.1.val := by
    rcases hcases with h | h | ⟨h,htop⟩ <;> omega
  refine ⟨b.1,hiB,?_⟩
  rw [hb]
  rfl

/-- Exterior ports at the first complementary vertex arc have face bases
adjacent to first complementary boundary edges. -/
theorem exterior_middle_arc_face {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (k l : ℕ) (hk : 1 ≤ k)
    (p : P.RetainedPort δ 0 k)
    (hp : ¬(openLatticeCell δ p.val.toLatticePort.faceBase ⊆ P.domain δ))
    (hv : domainPortPrimalVertex p.val ∈
      polygonBoundaryVertices P δ {j | k ≤ j.val ∧ j.val < l}) :
    p.val.toLatticePort.faceBase ∈
      polygonExteriorFaces P δ {i | k ≤ i.val ∧ i.val < l} := by
  obtain ⟨b,hb,hmask,hvertex⟩ := retainedPort_exterior_label P δ 0 k p hp
  obtain ⟨j,hj,hjv⟩ := hv
  change k ≤ j.val ∧ j.val < l at hj
  have he : j = FKC.LatticePolygon.boundaryCapVertexIndex b :=
    P.boundaryVertex_injective δ (hjv.trans hvertex)
  rw [he] at hj
  have hi := surviving_initial_arc_index b.1 hmask
  have hcases := boundaryCapVertexIndex_val_cases b
  have hiB : k ≤ b.1.val ∧ b.1.val < l := by
    rcases hcases with h | h | ⟨h,_⟩ <;> omega
  refine ⟨b.1,hiB,?_⟩
  rw [hb]
  rfl

/-- Four cyclic boundary arcs of a simple unit-edge lattice polygon:
if the initial closed vertex arc does not connect to a disjoint closed vertex
arc, the exterior dual cells of the two intervening EDGE arcs are connected
by actual closed original-domain dual bonds. No probabilistic premise occurs.
This is the existence implication, not an assertion of mutual exclusion. -/
theorem polygon_four_arc_dual_exists_of_no_primal {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (k l r : ℕ) (hk : 1 ≤ k) (hkl : k < l)
    (hlr : l ≤ r) (hr : r < m+3)
    (C : Configuration (domainLatticeGraph δ (P.domain δ)))
    (hno : ¬∃ u ∈ P.forwardArcVertices δ 0 k,
      ∃ v ∈ polygonBoundaryVertices P δ {j | l ≤ j.val ∧ j.val ≤ r},
        ActualConnected _ C u v) :
    ∃ x ∈ polygonExteriorFaces P δ {i | r ≤ i.val},
      ∃ y ∈ polygonExteriorFaces P δ {i | k ≤ i.val ∧ i.val < l},
        (domainClosedDualGraph C).Reachable x y := by
  have hk2 : k ≤ m+2 := by omega
  have hkn : k < m+3 := by omega
  obtain ⟨w,_,_⟩ := P.dobrushinPortGraph_existsUnique_isPath δ 0 hk hk2 C
  have havoid : ∀ z ∈ w.support, domainPortPrimalVertex z.1.val ∉
      polygonBoundaryVertices P δ {j | l ≤ j.val ∧ j.val ≤ r} := by
    intro z hz hc
    obtain ⟨u,hu,huz⟩ := dobrushin_walk_original_seed_connection P δ 0 hk hk2 C w z hz
    exact hno ⟨u,hu,domainPortPrimalVertex z.1.val,hc,huz⟩
  have hs : domainPortPrimalVertex (P.wiredStartPort δ 0 hk2).val ∈
      polygonBoundaryVertices P δ {j | j.val = 0 ∨ r < j.val} := by
    refine ⟨0,Or.inl (by simp),?_⟩
    apply Subtype.ext
    simp only [P.boundaryVertex_val,domainPortPrimalVertex_val,P.wiredStartPort_primalVertex]
  have ht : domainPortPrimalVertex (P.wiredFinishPort δ 0 hk2).val ∈
      polygonBoundaryVertices P δ {j | k ≤ j.val ∧ j.val < l} := by
    refine ⟨(k : ZMod (m+3)),?_,?_⟩
    · change k ≤ (k : ZMod (m+3)).val ∧ (k : ZMod (m+3)).val < l
      rw [ZMod.val_natCast_of_lt hkn]
      exact ⟨le_rfl,hkl⟩
    · apply Subtype.ext
      simp only [P.boundaryVertex_val,domainPortPrimalVertex_val,
        P.wiredFinishPort_primalVertex,zero_add]
  have hsout : ¬(openLatticeCell δ
      (P.wiredStartPort δ 0 hk2).val.toLatticePort.faceBase ⊆ P.domain δ) := by
    apply (P.domainPort_not_inside_iff_mem_boundaryCap δ _).mpr
    exact ⟨(FKC.LatticePolygon.capStartTerminal (0 : ZMod (m+3)) hk2).val,rfl⟩
  have htout : ¬(openLatticeCell δ
      (P.wiredFinishPort δ 0 hk2).val.toLatticePort.faceBase ⊆ P.domain δ) := by
    apply (P.domainPort_not_inside_iff_mem_boundaryCap δ _).mpr
    exact ⟨(FKC.LatticePolygon.capFinishTerminal (0 : ZMod (m+3)) hk2).val,rfl⟩
  obtain ⟨x,_,y,_,hxout,hyout,hxL,hyR,hxy⟩ :=
    dobrushin_exterior_dual_connection_of_classification P δ 0 k C
      (polygonBoundaryVertices P δ {j | j.val = 0 ∨ r < j.val})
      (polygonBoundaryVertices P δ {j | k ≤ j.val ∧ j.val < l})
      w hs ht hsout htout (fun z hz hzout =>
        exterior_initial_arc_classification P δ k l r hk hkl hlr hr z.1 hzout (havoid z hz))
  exact ⟨x.1.val.toLatticePort.faceBase,exterior_final_arc_face P δ k r hk hr x.1 hxout hxL,
    y.1.val.toLatticePort.faceBase,exterior_middle_arc_face P δ k l hk y.1 hyout hyR,hxy⟩

end PottsContinuity.PlanarTopology
