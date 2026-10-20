module

public import PottsContinuity.Thm4Records.SideNativeAttachment
public import PottsContinuity.PD.Duality.RectangleDualCrossing

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW
noncomputable section

/-- The original primal rectangle whose outer cluster selects each screen. -/
def sideRectangleBase (m : ℕ) (right : Bool) : ℤ × ℤ :=
  (if right then (m:ℤ) else -(5*(m:ℤ)),-(16*(m:ℤ)))

abbrev SideRectangleVertex (m : ℕ) (right : Bool) :=
  RectangleVertex (sideRectangleBase m right) (4*m) (32*m)

/-- The side rectangle is read on the actual source vertex labels. -/
def sideRectangleSourceVertex (m : ℕ) (right : Bool)
    (v : SideRectangleVertex m right) : FKC.FiniteFK.SlitBoxVertex (16*m) := by
  refine ⟨v.val,?_⟩
  have hv := (PD.FK.mem_latticeRectangle _ _ _ _).mp v.property
  rw [FKC.mem_latticeRectangle]
  cases right <;> dsimp [sideRectangleBase] at hv ⊢ <;>
    constructor <;> constructor <;> omega

def sideRectangleSourceEmbedding (m : ℕ) (right : Bool) :
    SideRectangleVertex m right ↪ FKC.FiniteFK.SlitBoxVertex (16*m) where
  toFun := sideRectangleSourceVertex m right
  inj' := by
    intro u v h
    exact Subtype.ext (Subtype.mk.inj h)

theorem sideRectangleSourceVertex_mem_sideWindow (m : ℕ) (right : Bool)
    (v : SideRectangleVertex m right) :
    sideRectangleSourceVertex m right v ∈ sideWindow m right := by
  have hv := (PD.FK.mem_latticeRectangle _ _ _ _).mp v.property
  cases right <;> dsimp [sideRectangleBase,sideWindow,sideRectangleSourceVertex] at hv ⊢ <;>
    constructor <;> omega

/-- Every original side-rectangle adjacency is retained by the slit source. -/
theorem sideRectangleSource_adj (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (u v : SideRectangleVertex m right)
    (huv : (rectangleGraph (sideRectangleBase m right) (4*m) (32*m)).Adj u v) :
    (sideCensoredGraph m right).Adj (sideRectangleSourceVertex m right u)
      (sideRectangleSourceVertex m right v) := by
  have hu := sideRectangleSourceVertex_mem_sideWindow m right u
  have hv := sideRectangleSourceVertex_mem_sideWindow m right v
  refine ⟨?_,hu,hv⟩
  apply (FKC.FiniteFK.slitBoxGraph_adj_iff _ _ _).mpr
  constructor
  · apply (FKC.squareLattice_adj_iff _ _).mpr
    exact (PD.FK.squareLattice_adj_iff _ _).mp
      ((PD.FK.rectangleGraph_adj_iff _ _ _ _ _).mp huv)
  · intro h
    have hx := h.1.1
    cases right <;> dsimp [sideWindow] at hu <;>
      change u.val.1=0 at hx <;> change _ at hu <;> omega

/-- Cluster membership is constant across every sampled open side bond. -/
theorem sideRectangle_cluster_iff_of_open_adj
    (m : ℕ) (_hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (u v : SideRectangleVertex m right)
    (huv : (openGraph (FKC.FiniteFK.slitBoxGraph (16*m)) X).Adj
      (sideRectangleSourceVertex m right u) (sideRectangleSourceVertex m right v)) :
    (sideRectangleSourceVertex m right u ∈ Thm3.Prop4.censoredSeedCluster
      (sideCensoredGraph_le m right) (sideOuterSeeds m right) X ↔
     sideRectangleSourceVertex m right v ∈ Thm3.Prop4.censoredSeedCluster
      (sideCensoredGraph_le m right) (sideOuterSeeds m right) X) := by
  have hsource := openGraph_le _ _ huv
  have hH : (sideCensoredGraph m right).Adj (sideRectangleSourceVertex m right u)
      (sideRectangleSourceVertex m right v) :=
    ⟨hsource,sideRectangleSourceVertex_mem_sideWindow m right u,
      sideRectangleSourceVertex_mem_sideWindow m right v⟩
  have hopen : (openGraph (sideCensoredGraph m right)
      (Thm3.Prop4.censoredConfiguration (sideCensoredGraph_le m right) X)).Adj
      (sideRectangleSourceVertex m right u) (sideRectangleSourceVertex m right v) := by
    obtain ⟨e,he,heq⟩ := (openGraph_adj _ _ _ _).mp huv
    let eH : (sideCensoredGraph m right).edgeSet :=
      ⟨e.val,by rw [heq]; exact (sideCensoredGraph m right).mem_edgeSet.mpr hH⟩
    apply (openGraph_adj _ _ _ _).mpr
    refine ⟨eH,?_,heq⟩
    exact (Thm3.Prop4.mem_censoredConfiguration _ X eH).mpr he
  exact ⟨fun h => censoredSeedCluster_closed_under_open_adj _ _ X h hopen,
    fun h => censoredSeedCluster_closed_under_open_adj _ _ X h hopen.symm⟩

/-- Orient the outer-cluster cut so that its left side has label true. -/
def sideRectangleCutLabel (m : ℕ) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (v : SideRectangleVertex m right) : Bool := by
  classical
  exact if right then !decide (sideRectangleSourceVertex m right v ∈
    Thm3.Prop4.censoredSeedCluster (sideCensoredGraph_le m right) (sideOuterSeeds m right) X)
  else decide (sideRectangleSourceVertex m right v ∈
    Thm3.Prop4.censoredSeedCluster (sideCensoredGraph_le m right) (sideOuterSeeds m right) X)

/-- The oriented labels agree on every actual open side bond. -/
theorem sideRectangleCutLabel_eq_of_open_adj
    (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (u v : SideRectangleVertex m right)
    (huv : (openGraph (FKC.FiniteFK.slitBoxGraph (16*m)) X).Adj
      (sideRectangleSourceVertex m right u) (sideRectangleSourceVertex m right v)) :
    sideRectangleCutLabel m right X u = sideRectangleCutLabel m right X v := by
  have h := sideRectangle_cluster_iff_of_open_adj m hm right X u v huv
  cases right <;> simp [sideRectangleCutLabel,h]

/-- Every disagreeing cut bond is queried and genuinely closed in the original
source configuration. This statement retains every component of the cut. -/
theorem sideRectangleCut_bond_queried_closed
    (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (b : PD.FK.Medial.LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle (sideRectangleBase m right) (4*m) (32*m))
    (ht : b.target ∈ PD.FK.latticeRectangle (sideRectangleBase m right) (4*m) (32*m))
    (hdiff : sideRectangleCutLabel m right X ⟨b.source,hs⟩ !=
      sideRectangleCutLabel m right X ⟨b.target,ht⟩) :
    ∃ e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet,
      e.val = s(sideRectangleSourceVertex m right ⟨b.source,hs⟩,
        sideRectangleSourceVertex m right ⟨b.target,ht⟩) ∧
      e ∈ sideOuterClusterReveal m right X ∧ e ∉ X := by
  classical
  let u : SideRectangleVertex m right := ⟨b.source,hs⟩
  let v : SideRectangleVertex m right := ⟨b.target,ht⟩
  have hadj : (rectangleGraph (sideRectangleBase m right) (4*m) (32*m)).Adj u v :=
    (PD.FK.rectangleGraph_adj_iff _ _ _ _ _).mpr b.adjacent
  have hsrc := (sideRectangleSource_adj m hm right u v hadj).1
  let e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet :=
    ⟨s(sideRectangleSourceVertex m right u,sideRectangleSourceVertex m right v),
      (FKC.FiniteFK.slitBoxGraph (16*m)).mem_edgeSet.mpr hsrc⟩
  refine ⟨e,rfl,?_,?_⟩
  · have hreached : (sideRectangleSourceVertex m right u ∈ Thm3.Prop4.censoredSeedCluster
        (sideCensoredGraph_le m right) (sideOuterSeeds m right) X) ∨
        (sideRectangleSourceVertex m right v ∈ Thm3.Prop4.censoredSeedCluster
          (sideCensoredGraph_le m right) (sideOuterSeeds m right) X) := by
      by_cases hu : sideRectangleSourceVertex m right u ∈ Thm3.Prop4.censoredSeedCluster
          (sideCensoredGraph_le m right) (sideOuterSeeds m right) X
      · exact Or.inl hu
      by_cases hv : sideRectangleSourceVertex m right v ∈ Thm3.Prop4.censoredSeedCluster
          (sideCensoredGraph_le m right) (sideOuterSeeds m right) X
      · exact Or.inr hv
      change sideRectangleCutLabel m right X u != sideRectangleCutLabel m right X v at hdiff
      cases right <;> simp [sideRectangleCutLabel,hu,hv] at hdiff
    apply (Thm3.Prop4.mem_censoredSeedReveal _ _ X e).mpr
    rcases hreached with hu | hv
    · exact ⟨_,Sym2.mem_mk_left _ _,hu⟩
    · exact ⟨_,Sym2.mem_mk_right _ _,hv⟩
  · intro he
    have hopen : (openGraph (FKC.FiniteFK.slitBoxGraph (16*m)) X).Adj
        (sideRectangleSourceVertex m right u) (sideRectangleSourceVertex m right v) :=
      (openGraph_adj _ _ _ _).mpr ⟨e,he,rfl⟩
    have h := sideRectangleCutLabel_eq_of_open_adj m hm right X u v hopen
    change sideRectangleCutLabel m right X u != sideRectangleCutLabel m right X v at hdiff
    simp [h] at hdiff

/-- Failure to reach the inner side supplies the two constant boundary labels
required by the existing rectangle cut-duality theorem. -/
theorem sideRectangleCutLabel_boundary_of_no_primal_connection
    (m : ℕ) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hno : X ∉ sidePrimalConnectionEvent m right) :
    (∀ v : SideRectangleVertex m right, v.val.1=(sideRectangleBase m right).1 →
      sideRectangleCutLabel m right X v=true) ∧
    (∀ v : SideRectangleVertex m right,
      v.val.1=(sideRectangleBase m right).1+((4*m:ℕ):ℤ) →
      sideRectangleCutLabel m right X v=false) := by
  classical
  have hseed (v : SideRectangleVertex m right)
      (h : v.val.1 = if right then 5*(m:ℤ) else -(5*(m:ℤ))) :
      sideRectangleSourceVertex m right v ∈ Thm3.Prop4.censoredSeedCluster
        (sideCensoredGraph_le m right) (sideOuterSeeds m right) X :=
    ⟨sideRectangleSourceVertex m right v,h,SimpleGraph.Reachable.refl _⟩
  have hinner (v : SideRectangleVertex m right)
      (h : v.val.1 = if right then (m:ℤ) else -(m:ℤ)) :
      sideRectangleSourceVertex m right v ∉ Thm3.Prop4.censoredSeedCluster
        (sideCensoredGraph_le m right) (sideOuterSeeds m right) X := by
    intro hv
    exact hno ⟨sideRectangleSourceVertex m right v,h,hv⟩
  cases right
  · constructor
    · intro v hv
      have hc := hseed v hv
      simp [sideRectangleCutLabel,hc]
    · intro v hv
      have hi : v.val.1 = -(m:ℤ) := by
        dsimp [sideRectangleBase] at hv
        omega
      have hc := hinner v hi
      simp [sideRectangleCutLabel,hc]
  · constructor
    · intro v hv
      have hc := hinner v hv
      simp [sideRectangleCutLabel,hc]
    · intro v hv
      have hi : v.val.1 = 5*(m:ℤ) := by
        dsimp [sideRectangleBase] at hv
        omega
      have hc := hseed v hi
      simp [sideRectangleCutLabel,hc]

/-- A full cut-dual bottom/top crossing exists, before any cropping in R*. -/
theorem sideRectangleCutDual_crossing_of_no_primal_connection
    (m : ℕ) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hno : X ∉ sidePrimalConnectionEvent m right) :
    ∃ b ∈ rectangleDualBottomPorts (sideRectangleBase m right) (4*m) (32*m),
      ∃ t ∈ rectangleDualTopPorts (sideRectangleBase m right) (4*m) (32*m),
        (rectangleLabelCutDualGraph (sideRectangleBase m right) (4*m) (32*m)
          (sideRectangleCutLabel m right X)).Reachable b t :=
  rectangleLabelCutDual_bottom_top_reachable _ _ _ _
    (sideRectangleCutLabel_boundary_of_no_primal_connection m right X hno).1
    (sideRectangleCutLabel_boundary_of_no_primal_connection m right X hno).2

end
end PottsContinuity.Thm4Records
