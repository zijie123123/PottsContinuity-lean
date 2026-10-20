module

public import PottsContinuity.DualityExt.PositiveDualOpenAdjState
public import PottsContinuity.DualityExt.PositiveP5aAnnulusActualDualJordan
public import PottsContinuity.DualityExt.PositiveP5aPolygonPDWalk
public import PottsContinuity.DualityExt.PositivePolygonCycleEdgeIndex
public import PottsContinuity.DualityExt.PositiveAnnulusPrimalDMP

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.Duality

noncomputable section

private theorem p5aAnnulusWalk_edge_mem_step
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ x y : V, G.Adj x y ∧ e = s(x, y) := by
  induction p with
  | nil => simp at he
  | @cons u v w hadj p ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · exact ⟨u, v, hadj, he⟩
      · obtain ⟨x, y, hxy, heq⟩ := ih he
        exact ⟨x, y, hxy, heq⟩

private theorem p5aAnnulusMappedWalk_edge_mem_step
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) {u v : V} (p : G.Walk u v)
    {x y : W} (he : s(x, y) ∈ (p.map f).edges) :
    ∃ x' y' : V, G.Adj x' y' ∧ s(x', y') ∈ p.edges ∧
      (f x' = x ∧ f y' = y ∨ f x' = y ∧ f y' = x) := by
  rw [SimpleGraph.Walk.edges_map] at he
  rcases List.mem_map.mp he with ⟨e, he, hemap⟩
  obtain ⟨x', y', hadj, heq⟩ := p5aAnnulusWalk_edge_mem_step p he
  rw [heq] at he
  have hpair : s(f x', f y') = s(x, y) := by
    simpa [heq] using hemap
  rcases Sym2.eq_iff.mp hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨x', y', hadj, he, Or.inl ⟨h₁, h₂⟩⟩
  · exact ⟨x', y', hadj, he, Or.inr ⟨h₁, h₂⟩⟩

def annulusPrimalOpenGraphToSquare
    (N : ℕ) (C : Configuration (annulusSourceGraph N)) :
    openGraph (annulusSourceGraph N) C →g squareLattice where
  toFun x := x.1
  map_rel' := by
    intro x y hxy
    have hsource := openGraph_le (annulusSourceGraph N) C hxy
    change squareLattice.Adj x.1 y.1 at hsource
    exact hsource

private theorem annulusPrimalOuterBoundaryClass_mem_outerBoundary
    (N : ℕ) (hN : 2 ≤ N)
    {x : {v : PD.FK.LatticeVertex // v ∈ annulusVertexSet N}}
    (hx : x ∈ annulusPrimalOuterBoundaryClass N (by omega)) :
    x.1 ∈ annulusOuterBoundary (2 * N) := by
  change annulusSourceEmbedding N x ∈ annulusHostPrimalOuterClass N at hx
  simp only [annulusHostPrimalOuterClass, Set.mem_ofPred_eq] at hx
  change x.1 ∈ PottsContinuity.PD.vertexBoundary
    (PottsContinuity.PD.FK.latticeRectangle
      (annulusHostAnchor N) (4 * N) (4 * N)) at hx
  rw [PottsContinuity.PD.vertexBoundary] at hx
  rcases hx with ⟨hxRect, z, hxz, hzout⟩
  rw [PottsContinuity.PD.FK.mem_latticeRectangle] at hxRect hzout
  have hbox : x.1 ∈ latticeBox (0, 0) (2 * N) := by
    rw [mem_latticeBox]
    simp only [annulusHostAnchor] at hxRect
    constructor <;> constructor <;> omega
  have hcoord : x.1.1 = (2 * N : ℕ) ∨ x.1.1 = -(2 * N : ℤ) ∨
      x.1.2 = (2 * N : ℕ) ∨ x.1.2 = -(2 * N : ℤ) := by
    by_contra hnot
    have hinside : -(2 * N : ℤ) < x.1.1 ∧ x.1.1 < (2 * N : ℤ) ∧
        -(2 * N : ℤ) < x.1.2 ∧ x.1.2 < (2 * N : ℤ) := by
      simp only [annulusHostAnchor] at hxRect
      omega
    have hout : z.1 < -(2 * N : ℤ) ∨ (2 * N : ℤ) < z.1 ∨
        z.2 < -(2 * N : ℤ) ∨ (2 * N : ℤ) < z.2 := by
      simp only [annulusHostAnchor] at hzout
      by_contra h
      push Not at h
      apply hzout
      constructor
      · constructor <;> omega
      · constructor <;> omega
    have hadj : |x.1.1 - z.1| + |x.1.2 - z.2| = 1 := by
      change |x.1.1 - z.1| + |x.1.2 - z.2| = 1 at hxz
      exact hxz
    have hdx₁ : |x.1.1 - z.1| ≤ 1 := by
      have hn := abs_nonneg (x.1.2 - z.2)
      omega
    have hdx₂ : |x.1.2 - z.2| ≤ 1 := by
      have hn := abs_nonneg (x.1.1 - z.1)
      omega
    have hdx₁' := abs_le.mp hdx₁
    have hdx₂' := abs_le.mp hdx₂
    rcases hout with hxlo | hxhi | hylo | hyhi
    · omega
    · omega
    · omega
    · omega
  rw [annulusOuterBoundary, Finset.mem_filter]
  exact ⟨hbox, hcoord⟩

/-- A P5a annular dual Jordan witness excludes an actual open primal path
between the two separately wired annulus classes. -/
theorem p5aAnnulusSourceActualDualJordan_no_openCrossing
    (N : ℕ) (hN : 2 ≤ N)
    (C : Configuration (annulusSourceGraph N))
    (u v : {x : PD.FK.LatticeVertex // x ∈ annulusVertexSet N})
    (hu : u.1 ∈ latticeBox (0, 0) N)
    (hv : v.1 ∈ annulusOuterBoundary (2 * N))
    (q : (openGraph (annulusSourceGraph N) C).Walk u v)
    (hA : rectangleSubgraphDualConfigurationEquiv
        (annulusSourceGraph_map_le_host N)
        (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
          (annulusSourceEmbedding N) C) ∈
      p5aAnnulusSourceActualDualJordanEvent N hN) :
    False := by
  rcases hA with ⟨m, P, horigin, hshell, hopen⟩
  have hvertices (i : ZMod (m + 3)) :
      P.vertex i ∈
        PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1) := by
    rcases hopen i with ⟨hi, _, _⟩
    exact hi
  have hface (i : ZMod (m + 3)) : P.vertex i ∈ dualFaceBox (2 * N) :=
    (Finset.mem_sdiff.mp (hshell i)).1
  have hfaceAvoid (i : ZMod (m + 3)) : P.vertex i ∉ dualFaceBox N :=
    (Finset.mem_sdiff.mp (hshell i)).2
  have hinnerDomain := p5a_polygon_domain_contains_vertexBox
    P N hN hvertices horigin u.1 hu
  have hinner : rayIndex u.1 (p5aPolygonCyclePD P) ≠ 0 :=
    p5aPolygon_rayIndex_ne_zero_of_mem_domain P u.1 hinnerDomain
  have hnotDomain := polygon_domain_avoids_outerBoundary_of_faceBox
    P N hface v.1 hv
  have houter : rayIndex v.1 (p5aPolygonCyclePD P) = 0 :=
    p5aPolygonPDWalk_outerBoundary_rayIndex_zero hN P hvertices v.1 hv hnotDomain
  let G := annulusSourceGraph N
  let f := annulusSourceEmbedding N
  let hG := annulusSourceGraph_map_le_host N
  let k := annulusPrimalOpenGraphToSquare N C
  let q' := q.map k
  have havoid : ∀ e ∈ q'.edges, ∀ b : LatticeBond, b.toSym2 = e →
      (dualBondOfPrimal b).toSym2 ∉ (p5aPolygonCyclePD P).edges := by
    intro e he b hb hcycle
    obtain ⟨x, y, hxy, hEq⟩ := p5aAnnulusWalk_edge_mem_step q' he
    have he' : s(x, y) ∈ q'.edges := by simpa [hEq] using he
    obtain ⟨x', y', hxy', hsegment, horient⟩ :=
      p5aAnnulusMappedWalk_edge_mem_step k q he'
    have hsourceOpen : s(x', y') ∈ openEdges G C :=
      (openGraph_adj G C x' y').mp hxy'
    change ∃ g : G.edgeSet, g ∈ C ∧ g.val = s(x', y') at hsourceOpen
    rcases hsourceOpen with ⟨g, hg, hgv⟩
    have hsourcePair :
        Sym2.map (fun z : {x : LatticeVertex // x ∈ annulusVertexSet N} => z.1)
          g.val = s(x'.1, y'.1) := by
      rw [hgv]
      rfl
    let hostEdge : rectanglePrimalEdgeCarrier (annulusHostAnchor N)
        (4 * N) (4 * N) := subgraphEdgeEmbedding hG
      (isolatedExtensionEdgeEquiv G f g)
    let hostBond := rectanglePrimalEdgeBond (annulusHostAnchor N) (4 * N) (4 * N)
      hostEdge
    have hhostPair : hostBond.toSym2 = s(x, y) := by
      change (rectanglePrimalEdgeBond (annulusHostAnchor N) (4 * N) (4 * N)
        hostEdge).toSym2 = s(x, y)
      rw [rectanglePrimalEdgeBond_toSym2_public]
      have hedgeVal : hostEdge.val = Sym2.map f g.val := by
        simp [hostEdge, subgraphEdgeEmbedding_coe, isolatedExtensionEdgeEquiv_coe]
      rw [hedgeVal]
      simp only [Sym2.map_map]
      change Sym2.map
        (fun z : {x : PD.FK.LatticeVertex // x ∈ annulusVertexSet N} => z.1)
        g.val = s(x, y)
      rw [hsourcePair]
      rcases horient with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · change x'.1 = x at h₁
        change y'.1 = y at h₂
        rw [h₁, h₂]
      · change x'.1 = y at h₁
        change y'.1 = x at h₂
        rw [h₁, h₂]
        exact Sym2.eq_swap
    have hbeq : hostBond = b :=
      LatticeBond.toSym2_injective (hhostPair.trans (hb.trans hEq).symm)
    let d := dualBondOfPrimal b
    have hcycle' : s(d.source, d.target) ∈ (p5aPolygonCyclePD P).edges := by
      simpa [d, LatticeBond.toSym2] using hcycle
    obtain ⟨i, hindex⟩ := p5aPolygonCyclePD_edge_index P hcycle'
    have hdualIndex : d.toSym2 = s(P.vertex i, P.vertex (i + 1)) := by
      simpa only [LatticeBond.toSym2] using hindex
    rcases hopen i with ⟨hi, hj, hdualOpen⟩
    let ui := p5aAnnulusSourceFaceBaseEmbeddingActual N hN ⟨P.vertex i, hi⟩
    let vi := p5aAnnulusSourceFaceBaseEmbeddingActual N hN ⟨P.vertex (i + 1), hj⟩
    have hui : ui.1 = P.vertex i := rfl
    have hvi : vi.1 = P.vertex (i + 1) := rfl
    have hfacePair : Sym2.map (fun z : RectangleDualVertex
        (annulusHostAnchor N) (4 * N) (4 * N) => z.1) (s(ui, vi)) =
        s(P.vertex i, P.vertex (i + 1)) := by
      change s(ui.1, vi.1) = s(P.vertex i, P.vertex (i + 1))
      rw [hui, hvi]
    have hcross : Sym2.map (fun z : RectangleDualVertex
        (annulusHostAnchor N) (4 * N) (4 * N) => z.1) (s(ui, vi)) =
        (dualBondOfPrimal (rectanglePrimalEdgeBond (annulusHostAnchor N)
          (4 * N) (4 * N) hostEdge)).toSym2 := by
      calc
        _ = s(P.vertex i, P.vertex (i + 1)) := hfacePair
        _ = d.toSym2 := hdualIndex.symm
        _ = (dualBondOfPrimal hostBond).toSym2 := by
          rw [hbeq]
    exact embeddedRectangleDualOpenAdj_crossedSourceClosed f hG C g ui vi
      hcross hdualOpen hg
  exact no_primalWalk_of_distinct_rayIndex_and_crossedEdges_avoided
    (p5aPolygonCyclePD P) q' hinner houter havoid

/-- The same event separates the two wired classes in the FK component
relation, which also allows connections that use the boundary identifications. -/
theorem p5aAnnulusSourceActualDualJordan_twoBlockDisconnected
    (N : ℕ) (hN : 2 ≤ N)
    (C : Configuration (annulusSourceGraph N))
    (u v : {x : PD.FK.LatticeVertex // x ∈ annulusVertexSet N})
    (hu : u ∈ annulusPrimalInnerBoundaryClass N (by omega))
    (hv : v ∈ annulusPrimalOuterBoundaryClass N (by omega))
    (hA : rectangleSubgraphDualConfigurationEquiv
        (annulusSourceGraph_map_le_host N)
        (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
          (annulusSourceEmbedding N) C) ∈
      p5aAnnulusSourceActualDualJordanEvent N hN) :
    C ∈ positiveBoundaryDisconnectedEvent
      (positiveTwoBlockBoundary
        (annulusPrimalInnerBoundaryClass N (by omega))
        (annulusPrimalOuterBoundaryClass N (by omega))
        (annulusPrimalInnerOuter_disjoint N (by omega))) u v := by
  let G := annulusSourceGraph N
  let I := annulusPrimalInnerBoundaryClass N (by omega)
  let O := annulusPrimalOuterBoundaryClass N (by omega)
  let ξ := positiveTwoBlockBoundary I O (annulusPrimalInnerOuter_disjoint N (by omega))
  have hno : ∀ x ∈ I, ∀ y ∈ O,
      ¬ (openGraph G C).Reachable x y := by
    intro x hx y hy hxy
    obtain ⟨q⟩ := (actualConnected_iff_walk G C x y).mp hxy
    have hxHost : annulusSourceEmbedding N x ∈ annulusHostPrimalInnerClass N := hx
    change x.1 ∈ latticeBox (0, 0) (N - 1) ∨
      ∃ z, z ∈ latticeBox (0, 0) (N - 1) ∧ squareLattice.Adj z x.1 at hxHost
    have hxBox : x.1 ∈ latticeBox (0, 0) N := by
      rcases hxHost with hsmall | ⟨z, hz, hadj⟩
      · exact latticeBox_mono (0, 0) (by omega) hsmall
      · have hadj' := (squareLattice_adj_iff z x.1).mp hadj
        rw [mem_latticeBox] at hz ⊢
        rcases hadj' with ⟨h | h, hzY⟩ | ⟨hzX, h | h⟩ <;>
          rcases hz with ⟨⟨hz₁, hz₂⟩, ⟨hw₁, hw₂⟩⟩ <;>
          constructor <;> constructor <;> omega
    exact p5aAnnulusSourceActualDualJordan_no_openCrossing
      N hN C x y hxBox
      (annulusPrimalOuterBoundaryClass_mem_outerBoundary N hN hy) q hA
  let S : Setoid {x : PD.FK.LatticeVertex // x ∈ annulusVertexSet N} := {
    r := fun x y =>
      (openGraph G C).Reachable x y ∨
        (∃ a, a ∈ I ∧ ∃ b, b ∈ I ∧
          (openGraph G C).Reachable x a ∧ (openGraph G C).Reachable y b) ∨
        (∃ a, a ∈ O ∧ ∃ b, b ∈ O ∧
          (openGraph G C).Reachable x a ∧ (openGraph G C).Reachable y b)
    iseqv := by
      refine ⟨?_, ?_, ?_⟩
      · intro x
        exact Or.inl (SimpleGraph.Reachable.refl x)
      · intro x y hxy
        rcases hxy with hxy | hxy | hxy
        · exact Or.inl hxy.symm
        · rcases hxy with ⟨a, ha, b, hb, hxa, hyb⟩
          exact Or.inr (Or.inl ⟨b, hb, a, ha, hyb, hxa⟩)
        · rcases hxy with ⟨a, ha, b, hb, hxa, hyb⟩
          exact Or.inr (Or.inr ⟨b, hb, a, ha, hyb, hxa⟩)
      · intro x y z hxy hyz
        rcases hxy with hxy | hxy | hxy
        · rcases hyz with hyz | hyz | hyz
          · exact Or.inl (hxy.trans hyz)
          · rcases hyz with ⟨a, ha, b, hb, hya, hzb⟩
            exact Or.inr (Or.inl ⟨a, ha, b, hb, hxy.trans hya, hzb⟩)
          · rcases hyz with ⟨a, ha, b, hb, hya, hzb⟩
            exact Or.inr (Or.inr ⟨a, ha, b, hb, hxy.trans hya, hzb⟩)
        · rcases hxy with ⟨a, ha, b, hb, hxa, hyb⟩
          rcases hyz with hyz | hyz | hyz
          · exact Or.inr (Or.inl ⟨a, ha, b, hb, hxa, hyz.symm.trans hyb⟩)
          · rcases hyz with ⟨c, hc, d, hd, hyc, hzd⟩
            exact Or.inr (Or.inl ⟨a, ha, d, hd, hxa, hzd⟩)
          · rcases hyz with ⟨c, hc, d, hd, hyc, hzd⟩
            exact False.elim (hno b hb c hc (hyb.symm.trans hyc))
        · rcases hxy with ⟨a, ha, b, hb, hxa, hyb⟩
          rcases hyz with hyz | hyz | hyz
          · exact Or.inr (Or.inr ⟨a, ha, b, hb, hxa, hyz.symm.trans hyb⟩)
          · rcases hyz with ⟨c, hc, d, hd, hyc, hzd⟩
            exact False.elim (hno c hc b hb (hyc.symm.trans hyb))
          · rcases hyz with ⟨c, hc, d, hd, hyc, hzd⟩
            exact Or.inr (Or.inr ⟨a, ha, d, hd, hxa, hzd⟩) }
  have hboundary : ξ.partition ≤ S := by
    change (BoundaryCondition.wired I).partition ⊔
        (BoundaryCondition.wired O).partition ≤ S
    apply sup_le
    · intro x y hxy
      rcases (BoundaryCondition.wired_rel I x y).mp hxy with heq | hI
      · subst y
        exact Or.inl (SimpleGraph.Reachable.refl x)
      · exact Or.inr (Or.inl ⟨x, hI.1, y, hI.2,
          SimpleGraph.Reachable.refl x, SimpleGraph.Reachable.refl y⟩)
    · intro x y hxy
      rcases (BoundaryCondition.wired_rel O x y).mp hxy with heq | hO
      · subst y
        exact Or.inl (SimpleGraph.Reachable.refl x)
      · exact Or.inr (Or.inr ⟨x, hO.1, y, hO.2,
          SimpleGraph.Reachable.refl x, SimpleGraph.Reachable.refl y⟩)
  have hcomp : componentSetoid G ξ C ≤ S :=
    componentSetoid_le G ξ C S (by
      intro x y hxy
      exact Or.inl hxy) hboundary
  change ¬ (componentSetoid G ξ C).r u v
  intro huv
  have hrel : S.r u v := hcomp huv
  rcases hrel with hreach | hI | hO
  · exact hno u hu v (by
      exact hv) hreach
  · rcases hI with ⟨a, ha, b, hb, hua, hvb⟩
    exact hno b hb v hv (hvb.symm)
  · rcases hO with ⟨a, ha, b, hb, hua, hvb⟩
    exact hno u hu a ha hua

end

end PottsContinuity.DualityExt
