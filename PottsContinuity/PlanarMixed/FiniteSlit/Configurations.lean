module

public import PottsContinuity.PlanarMixed.FiniteSlit.ActiveCarrier

/-! Canonical finite complementary configurations on the actual active
reflected graph. The inverse crossing bond is explicit, with no path or law choice. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial BD12
noncomputable section
local instance finiteSlitConfigurationsEdgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
local instance finiteSlitConfigurationsEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Literal inclusion of the balanced finite vertex carrier in the lattice. -/
def vertexEmbedding (M : ℕ) (x : ℤ) : Vertex M x ↪ LatticeVertex :=
  ⟨Subtype.val,Subtype.val_injective⟩

theorem graph_map_le_lattice (M : ℕ) (x y : ℤ) :
    (graph M x y).map (vertexEmbedding M x) ≤ PD.FK.squareLattice := by
  intro u v h
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
  exact hab.1

def edgeEmbedding (M : ℕ) (x y : ℤ) : (graph M x y).edgeSet ↪ PD.FK.squareLattice.edgeSet :=
  embeddedEdgeEmbedding _ _ (vertexEmbedding M x) (graph_map_le_lattice M x y)

theorem dualGraph_map_le_lattice (M : ℕ) (x y : ℤ) :
    (dualGraph M x y).map (vertexEmbedding M x) ≤ PD.FK.squareLattice := by
  intro u v h
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
  exact (dualGraph_le_graph M x y hab).1

def dualEdgeEmbedding (M : ℕ) (x y : ℤ) :
    (dualGraph M x y).edgeSet ↪ PD.FK.squareLattice.edgeSet :=
  embeddedEdgeEmbedding _ _ (vertexEmbedding M x) (dualGraph_map_le_lattice M x y)

/-- The normalized source crossing bond of any actual finite dual edge. -/
def dualPreimageBond (M : ℕ) (x y : ℤ) (e : (dualGraph M x y).edgeSet) : LatticeBond :=
  slitReflectedBondInv x (wholePlaneBondEdgeEquiv.symm (dualEdgeEmbedding M x y e))

/-- Every inverse crossing bond is sampled and active in the specified source. -/
theorem dualPreimageBond_active (M : ℕ) (x y : ℤ) (e : (dualGraph M x y).edgeSet) :
    ActiveBond M x y (dualPreimageBond M x y e) := by
  obtain ⟨⟨u,v⟩,heq⟩ := Sym2.mk_surjective e.val
  have hadj : (dualGraph M x y).Adj u v := by
    apply (dualGraph M x y).mem_edgeSet.mp
    exact Eq.mp (congrArg (fun z : Sym2 (Vertex M x) => z ∈ (dualGraph M x y).edgeSet)
      heq.symm) e.property
  obtain ⟨⟨b,hb,hpair⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hadj
  have hglobal : dualEdgeEmbedding M x y e = latticeBondEdge (slitReflectedBond x b) := by
    apply Subtype.ext
    change Sym2.map Subtype.val e.val = (slitReflectedBond x b).toSym2
    rw [← heq]
    exact hpair.symm
  have hinv : dualPreimageBond M x y e = b := by
    unfold dualPreimageBond
    have hi : wholePlaneBondEdgeEquiv.symm (latticeBondEdge (slitReflectedBond x b)) =
        slitReflectedBond x b := wholePlaneBondEdgeEquiv.symm_apply_apply _
    rw [hglobal,hi,slitReflectedBondInv_apply]
  exact hinv.symm ▸ hb

/-- The inverse bond gives an actual source edge by its explicit endpoints. -/
def sourcePreimageEdge (M : ℕ) (x y : ℤ) (e : (dualGraph M x y).edgeSet) :
    (graph M x y).edgeSet := by
  let b := dualPreimageBond M x y e
  have hb := dualPreimageBond_active M x y e
  let u : Vertex M x := ⟨b.source,hb.1⟩
  let v : Vertex M x := ⟨b.target,hb.2.1⟩
  have hadj : (graph M x y).Adj u v := by
    apply (graph_adj_iff_retained M x y u v).mpr
    exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨b,hb.2.2.1,rfl⟩,b.adjacent.ne⟩
  exact ⟨s(u,v),(graph M x y).mem_edgeSet.mpr hadj⟩

theorem sourcePreimageEdge_embedding (M : ℕ) (x y : ℤ) (e : (dualGraph M x y).edgeSet) :
    edgeEmbedding M x y (sourcePreimageEdge M x y e) = latticeBondEdge (dualPreimageBond M x y e) :=
  Subtype.ext rfl

/-- Complement the actual source state at the unique inverse crossing edge. -/
def dualConfiguration (M : ℕ) (x y : ℤ) (C : Configuration (graph M x y)) :
    Configuration (dualGraph M x y) := by
  classical
  exact Finset.univ.filter (fun e => sourcePreimageEdge M x y e ∉ C)

/-- Exact complementary state on every actual finite target edge. -/
theorem mem_dualConfiguration (M : ℕ) (x y : ℤ) (C : Configuration (graph M x y))
    (e : (dualGraph M x y).edgeSet) :
    e ∈ dualConfiguration M x y C ↔ sourcePreimageEdge M x y e ∉ C := by
  classical
  simp [dualConfiguration]

end
end PottsContinuity.PlanarMixed.FiniteSlit
