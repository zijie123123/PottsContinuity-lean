module

public import PottsContinuity.Thm4Records.SideCutSource
public import PottsContinuity.PlanarTopology.RectangleSampledClosedDual
public import PottsContinuity.PD.Duality.RectangleCrossingExclusion
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW
noncomputable section

/-- The source side rectangle retains exactly the original source labels. -/
theorem sideRectangleSource_graph_le (m : ℕ) (hm : 1 ≤ m) (right : Bool) :
    (rectangleGraph (sideRectangleBase m right) (4*m) (32*m)).map
      (sideRectangleSourceEmbedding m right) ≤ FKC.FiniteFK.slitBoxGraph (16*m) := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact (sideRectangleSource_adj m hm right x y hxy).1

def sideRectangleConfiguration (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    Configuration (rectangleGraph (sideRectangleBase m right) (4*m) (32*m)) :=
  embeddedConfigurationRestriction _ _ (sideRectangleSourceEmbedding m right)
    (sideRectangleSource_graph_le m hm right) X

/-- A source vertex in the censored window belongs to the literal rectangle. -/
def sideRectangleVertexOfSource (m : ℕ) (right : Bool)
    (u : FKC.FiniteFK.SlitBoxVertex (16*m)) (hu : u ∈ sideWindow m right) :
    SideRectangleVertex m right := by
  refine ⟨u.val,?_⟩
  have hy := (FKC.mem_latticeRectangle _ _ _ _).mp u.property
  rw [PD.FK.mem_latticeRectangle]
  cases right <;> dsimp [sideWindow,sideRectangleBase] at hu ⊢ <;>
    constructor <;> constructor <;> omega

@[simp] theorem sideRectangleSourceVertex_vertexOfSource (m : ℕ) (right : Bool)
    (u : FKC.FiniteFK.SlitBoxVertex (16*m)) (hu : u ∈ sideWindow m right) :
    sideRectangleSourceVertex m right (sideRectangleVertexOfSource m right u hu)=u :=
  Subtype.ext rfl

def sideRectangleDefaultVertex (m : ℕ) (right : Bool) : SideRectangleVertex m right := by
  refine ⟨sideRectangleBase m right,?_⟩
  rw [PD.FK.mem_latticeRectangle]
  constructor <;> constructor <;> omega

/-- Outside the censored window the source graph is isolated; those vertices
may therefore be mapped to an arbitrary fixed rectangle vertex. -/
def sourceToSideRectangle (m : ℕ) (right : Bool)
    (u : FKC.FiniteFK.SlitBoxVertex (16*m)) : SideRectangleVertex m right := by
  classical
  exact if hu : u ∈ sideWindow m right then sideRectangleVertexOfSource m right u hu
    else sideRectangleDefaultVertex m right

@[simp] theorem sourceToSideRectangle_of_mem (m : ℕ) (right : Bool)
    (u : FKC.FiniteFK.SlitBoxVertex (16*m)) (hu : u ∈ sideWindow m right) :
    sourceToSideRectangle m right u=sideRectangleVertexOfSource m right u hu := by
  simp [sourceToSideRectangle,hu]

/-- Every actual open censored step reads the same original rectangle bond. -/
def sideCensoredOpenToRectangle (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    openGraph (sideCensoredGraph m right)
      (Thm3.Prop4.censoredConfiguration (sideCensoredGraph_le m right) X) →g
    openGraph (rectangleGraph (sideRectangleBase m right) (4*m) (32*m))
      (sideRectangleConfiguration m hm right X) where
  toFun := sourceToSideRectangle m right
  map_rel' := by
    intro u v huv
    have hH := openGraph_le _ _ huv
    obtain ⟨e,he,heq⟩ := (openGraph_adj _ _ _ _).mp huv
    have heX := (Thm3.Prop4.mem_censoredConfiguration _ X e).mp he
    rw [sourceToSideRectangle_of_mem m right u hH.2.1,
      sourceToSideRectangle_of_mem m right v hH.2.2]
    have hrect : (rectangleGraph (sideRectangleBase m right) (4*m) (32*m)).Adj
        (sideRectangleVertexOfSource m right u hH.2.1)
        (sideRectangleVertexOfSource m right v hH.2.2) := by
      apply (PD.FK.rectangleGraph_adj_iff _ _ _ _ _).mpr
      apply (PD.FK.squareLattice_adj_iff _ _).mpr
      exact (FKC.squareLattice_adj_iff _ _).mp
        ((FKC.FiniteFK.slitBoxGraph_adj_iff _ _ _).mp hH.1).1
    let d : (rectangleGraph (sideRectangleBase m right) (4*m) (32*m)).edgeSet :=
      ⟨s(sideRectangleVertexOfSource m right u hH.2.1,
        sideRectangleVertexOfSource m right v hH.2.2),
        (rectangleGraph (sideRectangleBase m right) (4*m) (32*m)).mem_edgeSet.mpr hrect⟩
    apply (openGraph_adj _ _ _ _).mpr
    refine ⟨d,?_,rfl⟩
    apply (mem_embeddedConfigurationRestriction _ _ _ _ X d).mpr
    have hemb : embeddedEdgeEmbedding _ _ (sideRectangleSourceEmbedding m right)
        (sideRectangleSource_graph_le m hm right) d =
        Thm3.Prop4.censoredEdgeInclusion (sideCensoredGraph_le m right) e := by
      apply Subtype.ext
      change Sym2.map (sideRectangleSourceEmbedding m right) d.val = e.val
      rw [heq]
      change s(sideRectangleSourceVertex m right (sideRectangleVertexOfSource m right u hH.2.1),
        sideRectangleSourceVertex m right (sideRectangleVertexOfSource m right v hH.2.2))=s(u,v)
      rw [sideRectangleSourceVertex_vertexOfSource,sideRectangleSourceVertex_vertexOfSource]
    rw [hemb]
    exact heX

/-- A censored primal side connection gives the actual horizontal crossing
of the original rectangle read from the source configuration. -/
theorem sidePrimalConnection_implies_rectangle_horizontal
    (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hX : X ∈ sidePrimalConnectionEvent m right) :
    sideRectangleConfiguration m hm right X ∈
      rectangleHorizontalCrossingEvent (sideRectangleBase m right) (4*m) (32*m) := by
  obtain ⟨v,hv,s,hs,hsv⟩ := hX
  have hsw : s ∈ sideWindow m right := by
    cases right <;> dsimp [sideOuterSeeds,sideWindow] at hs ⊢ <;> constructor <;> omega
  have hvw : v ∈ sideWindow m right := sideOuterCluster_subset_sideWindow m right X ⟨s,hs,hsv⟩
  have hconn := hsv.map (sideCensoredOpenToRectangle m hm right X)
  change ActualConnected _ (sideRectangleConfiguration m hm right X)
    (sourceToSideRectangle m right s) (sourceToSideRectangle m right v) at hconn
  rw [sourceToSideRectangle_of_mem m right s hsw,
    sourceToSideRectangle_of_mem m right v hvw] at hconn
  cases right
  · refine ⟨sideRectangleVertexOfSource m false s hsw,
      sideRectangleVertexOfSource m false v hvw,?_,?_,hconn⟩
    · refine Finset.mem_filter.mpr ⟨(sideRectangleVertexOfSource m false s hsw).property,?_⟩
      change s.val.1=(sideRectangleBase m false).1
      exact hs
    · refine Finset.mem_filter.mpr ⟨(sideRectangleVertexOfSource m false v hvw).property,?_⟩
      change v.val.1=(sideRectangleBase m false).1+((4*m:ℕ):ℤ)
      dsimp [sideInnerVertices,sideRectangleBase] at hv ⊢
      omega
  · refine ⟨sideRectangleVertexOfSource m true v hvw,
      sideRectangleVertexOfSource m true s hsw,?_,?_,hconn.symm⟩
    · refine Finset.mem_filter.mpr ⟨(sideRectangleVertexOfSource m true v hvw).property,?_⟩
      change v.val.1=(sideRectangleBase m true).1
      exact hv
    · refine Finset.mem_filter.mpr ⟨(sideRectangleVertexOfSource m true s hsw).property,?_⟩
      change s.val.1=(sideRectangleBase m true).1+((4*m:ℕ):ℤ)
      dsimp [sideOuterSeeds,sideRectangleBase] at hs ⊢
      omega


private theorem sourceBond_endpoint_heights (m : ℕ)
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (b : FKC.Medial.LatticeBond)
    (hp : b.toSym2=Sym2.map Subtype.val e.val) :
    (-(16*(m:ℤ)) ≤ b.source.2 ∧ b.source.2 ≤ 16*(m:ℤ)) ∧
      (-(16*(m:ℤ)) ≤ b.target.2 ∧ b.target.2 ≤ 16*(m:ℤ)) := by
  have hb (z : ℤ × ℤ) (hz : z ∈ b.toSym2) :
      -(16*(m:ℤ)) ≤ z.2 ∧ z.2 ≤ 16*(m:ℤ) := by
    rw [hp] at hz
    obtain ⟨u,_,hu⟩ := Sym2.mem_map.mp hz
    have hc := (FKC.mem_latticeRectangle _ _ _ _).mp u.property
    rw [← hu]
    exact ⟨hc.2.1,by omega⟩
  exact ⟨hb _ (Sym2.mem_mk_left _ _),hb _ (Sym2.mem_mk_right _ _)⟩

private theorem crossedSideBond_endpoints_mem (m : ℕ) (right : Bool)
    (d : FKC.Medial.LatticeBond)
    (hd : d.source ∈ sideFaceBases m right ∧ d.target ∈ sideFaceBases m right)
    (hy : (-(16*(m:ℤ)) ≤ (FKC.Medial.primalBondOfDual d).source.2 ∧
      (FKC.Medial.primalBondOfDual d).source.2 ≤ 16*(m:ℤ)) ∧
      (-(16*(m:ℤ)) ≤ (FKC.Medial.primalBondOfDual d).target.2 ∧
      (FKC.Medial.primalBondOfDual d).target.2 ≤ 16*(m:ℤ))) :
    (FKC.Medial.primalBondOfDual d).source ∈ PD.FK.latticeRectangle
        (sideRectangleBase m right) (4*m) (32*m) ∧
    (FKC.Medial.primalBondOfDual d).target ∈ PD.FK.latticeRectangle
        (sideRectangleBase m right) (4*m) (32*m) := by
  rcases d with ⟨⟨x,y⟩,a⟩
  cases right <;> cases a <;>
    simp only [sideFaceBases,Bool.false_eq_true,ite_false,ite_true,
      FKC.FiniteFK.slitScreenRightFaceBases,FKC.FiniteFK.slitScreenLeftFaceBases,
      Finset.mem_product,Finset.mem_Icc,FKC.Medial.LatticeBond.source,
      FKC.Medial.LatticeBond.target] at hd <;>
    simp only [PD.FK.mem_latticeRectangle] <;>
    dsimp [sideRectangleBase,FKC.Medial.primalBondOfDual,
      FKC.Medial.LatticeBond.source,FKC.Medial.LatticeBond.target] at hy ⊢ <;>
    constructor <;> (try constructor) <;> (try constructor) <;> omega

/-- An actual source dual step inside a side window is an original sampled
closed-dual rectangle step with the same geometric face labels. -/
theorem sideActualClosed_to_rectangleSampled_adj
    (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (u v : ℤ × ℤ)
    (huv : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m X
      (sideFaceBases m right)).Adj u v) :
    (PlanarTopology.rectangleSampledClosedDualGraph (sideRectangleBase m right) (4*m) (32*m)
      (sideRectangleConfiguration m hm right X)).Adj u v := by
  obtain ⟨d,e,hcross,he,hdir,huF,hvF⟩ := huv
  have hd : d.source ∈ sideFaceBases m right ∧ d.target ∈ sideFaceBases m right := by
    rcases hdir with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨huF,hvF⟩
    · exact ⟨hvF,huF⟩
  let bF := FKC.Medial.primalBondOfDual d
  let b := latticeBondEquiv bF
  have hp := congrArg Subtype.val hcross
  change bF.toSym2=Sym2.map Subtype.val e.val at hp
  have hmemF := crossedSideBond_endpoints_mem m right d hd
    (sourceBond_endpoint_heights m e bF hp)
  have hmem : b.source ∈ PD.FK.latticeRectangle (sideRectangleBase m right) (4*m) (32*m) ∧
      b.target ∈ PD.FK.latticeRectangle (sideRectangleBase m right) (4*m) (32*m) := by
    simpa only [b,latticeBondEquiv_source,latticeBondEquiv_target] using hmemF
  let bR : RectanglePrimalBond (sideRectangleBase m right) (4*m) (32*m) := ⟨b,hmem⟩
  have hclosed : rectanglePrimalBondToEdge _ _ _ bR ∉ sideRectangleConfiguration m hm right X := by
    intro h
    have hmapped := (mem_embeddedConfigurationRestriction _ _ _ _ X _).mp h
    have hsame : embeddedEdgeEmbedding _ _ (sideRectangleSourceEmbedding m right)
        (sideRectangleSource_graph_le m hm right) (rectanglePrimalBondToEdge _ _ _ bR)=e := by
      apply Subtype.ext
      apply Sym2.map.injective Subtype.val_injective
      change s(b.source,b.target)=Sym2.map Subtype.val e.val
      rw [← hp]
      change s((latticeBondEquiv bF).source,(latticeBondEquiv bF).target)=bF.toSym2
      rw [latticeBondEquiv_source,latticeBondEquiv_target]
      rfl
    exact he (hsame ▸ hmapped)
  have hsample := PlanarTopology.rectangleSampledClosedDualGraph_adj_of_closed_bond
    (sideRectangleBase m right) (4*m) (32*m) (sideRectangleConfiguration m hm right X) bR hclosed
  have hd' : PD.FK.Medial.dualBondOfPrimal b=latticeBondEquiv d := by
    rw [← latticeBondEquiv_dualBondOfPrimal]
    simp only [bF,FKC.Medial.dualBondOfPrimal_primalBondOfDual]
  rw [hd'] at hsample
  simp only [latticeBondEquiv_source,latticeBondEquiv_target] at hsample
  rcases hdir with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hsample
  · exact hsample.symm

def sideActualClosedToRectangleSampled (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m X (sideFaceBases m right) →g
    PlanarTopology.rectangleSampledClosedDualGraph (sideRectangleBase m right) (4*m) (32*m)
      (sideRectangleConfiguration m hm right X) where
  toFun := id
  map_rel' := by
    intro u v huv
    exact sideActualClosed_to_rectangleSampled_adj m hm right X u v huv

private theorem sideFace_mem_dualExpanded (m : ℕ) (right : Bool)
    (u : ℤ × ℤ) (hu : u ∈ sideFaceBases m right) :
    u ∈ rectangleDualExpanded (sideRectangleBase m right) (4*m) (32*m) := by
  rw [rectangleDualExpanded,PD.FK.mem_latticeRectangle]
  cases right <;>
    simp only [sideFaceBases,Bool.false_eq_true,ite_false,ite_true,
      FKC.FiniteFK.slitScreenRightFaceBases,FKC.FiniteFK.slitScreenLeftFaceBases,
      Finset.mem_product,Finset.mem_Icc] at hu <;>
    dsimp [sideRectangleBase] <;> constructor <;> constructor <;> omega

/-- A genuine source dual screen excludes the censored primal side connection. -/
theorem sideCrossing_implies_no_primal_connection
    (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hX : X ∈ (if right then FKC.FiniteFK.slitScreenRightCrossingEvent m
      else FKC.FiniteFK.slitScreenLeftCrossingEvent m)) :
    X ∉ sidePrimalConnectionEvent m right := by
  intro hp
  have hsource : ∃ b ∈ FKC.FiniteFK.slitScreenBottomTerminals m (sideFaceBases m right),
      ∃ t ∈ FKC.FiniteFK.slitScreenTopTerminals m (sideFaceBases m right),
      (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m X (sideFaceBases m right)).Reachable b t := by
    cases right
    · rw [ite_eq_right Bool.false_ne_true,FKC.FiniteFK.slitScreenLeftCrossingEvent_eq_actualClosedDual m hm] at hX
      exact hX
    · rw [ite_eq_left rfl,FKC.FiniteFK.slitScreenRightCrossingEvent_eq_actualClosedDual m hm] at hX
      exact hX
  obtain ⟨b,hb,t,ht,hbt⟩ := hsource
  have hbF : b ∈ sideFaceBases m right := hb.1
  have htF : t ∈ sideFaceBases m right := ht.1
  have hbmem := sideFace_mem_dualExpanded m right b hbF
  have htmem := sideFace_mem_dualExpanded m right t htF
  obtain ⟨p⟩ := hbt.map (sideActualClosedToRectangleSampled m hm right X)
  have hfinite := PlanarTopology.rectangleSampledClosedDualGraph_walk_finite
    (sideRectangleBase m right) (4*m) (32*m) (sideRectangleConfiguration m hm right X) p hbmem htmem
  apply rectanglePrimalDualCrossings_exclusive (sideRectangleBase m right) (4*m) (32*m)
    (sideRectangleConfiguration m hm right X)
    (sidePrimalConnection_implies_rectangle_horizontal m hm right X hp)
  refine ⟨⟨b,hbmem⟩,⟨t,htmem⟩,?_,?_,hfinite⟩
  · change b.2=(sideRectangleBase m right).2-1
    exact hb.2
  · change t.2=(sideRectangleBase m right).2+((32*m:ℕ):ℤ)
    have h := ht.2
    dsimp [sideRectangleBase] at h ⊢
    omega

/-- Exact screen/primal alternative on the original finite slit sample. -/
theorem sidePrimalDualAlternative (m : ℕ) (hm : 1 ≤ m) (right : Bool) :
    SidePrimalDualAlternative m right := by
  intro X
  exact ⟨sideCrossing_implies_no_primal_connection m hm right X,
    sideCrossing_of_no_primal_connection m hm right X⟩

end
end PottsContinuity.Thm4Records
