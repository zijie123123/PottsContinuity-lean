module

public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.ComplementaryStoppingRead
public import PottsContinuity.Thm3.RSW.RectangleClosedDualStates
public import PottsContinuity.PD.Duality.RectangleFlowDimension

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite RSW
noncomputable section

/-- The unique actually sampled original primal edge for a physical bond,
if present. No exterior bond is silently sampled. -/
def originalEdgeOfBond (V : Finset LatticeVertex) (b : LatticeBond) :
    Option (PD.FK.squareLattice.induce (V : Set LatticeVertex)).edgeSet := by
  classical
  exact if h : ∃ e, frozenEdgeEmbedding V e=latticeBondEdge b then some (Classical.choose h) else none

theorem originalEdgeOfBond_eq_some_iff (V : Finset LatticeVertex) (b : LatticeBond)
    (e : (PD.FK.squareLattice.induce (V : Set LatticeVertex)).edgeSet) :
    originalEdgeOfBond V b=some e ↔ frozenEdgeEmbedding V e=latticeBondEdge b := by
  classical
  unfold originalEdgeOfBond
  split_ifs with h
  · have hc := Classical.choose_spec h
    constructor
    · intro he
      exact Option.some.inj he ▸ hc
    · intro he
      have heq : Classical.choose h=e := (frozenEdgeEmbedding V).injective (hc.trans he.symm)
      exact congrArg some heq
  · simp only [false_iff]
    exact fun he => h ⟨e,he⟩

/-- The source variable read by a geometrically specified dual rectangle edge. -/
def rectangleDualOriginalEdge (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleGraph a w h).edgeSet) :=
  originalEdgeOfBond V (primalBondOfDual (rectanglePrimalEdgeBond a w h e))

def originalClosedDualRectangleRead (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex))) :=
  complementaryEdgeRead (PD.FK.squareLattice.induce (V : Set LatticeVertex))
    (rectangleGraph a w h) (rectangleDualOriginalEdge V a w h) A

/-- Every dual read keeps the exact complementary original state, including
unsampled deterministic exterior bonds. -/
theorem originalClosedDualRectangleRead_edge_iff
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex)))
    (e : (rectangleGraph a w h).edgeSet) :
    e ∈ originalClosedDualRectangleRead V a w h A ↔
      latticeConfigurationBondState (finiteSubgraphConfiguration V 0 A)
        (primalBondOfDual (rectanglePrimalEdgeBond a w h e))=false := by
  classical
  rw [originalClosedDualRectangleRead,mem_complementaryEdgeRead]
  change (∀ f, originalEdgeOfBond V _=some f → f ∉ A) ↔ decide (_ ∈ A.map (frozenEdgeEmbedding V))=false
  rw [decide_eq_false_iff_not]
  constructor
  · intro hall hm
    obtain ⟨f,hf,heq⟩ := Finset.mem_map.mp hm
    exact hall f ((originalEdgeOfBond_eq_some_iff V _ f).mpr heq) hf
  · intro hn f hf hfA
    exact hn (Finset.mem_map.mpr ⟨f,hfA,(originalEdgeOfBond_eq_some_iff V _ f).mp hf⟩)

theorem originalClosedDualRectangleRead_edgeSet_iff
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex)))
    (e : (rectangleGraph a w h).edgeSet) :
    e ∈ originalClosedDualRectangleRead V a w h A ↔
      Sym2.map Subtype.val e.val ∈
        (wholePlaneClosedDualGraph (finiteSubgraphConfiguration V 0 A)).edgeSet := by
  rw [originalClosedDualRectangleRead_edge_iff]
  have hpair := rectanglePrimalEdgeBond_toSym2_public a w h e
  change (rectanglePrimalEdgeBond a w h e).toSym2=Sym2.map Subtype.val e.val at hpair
  rw [← hpair]
  change _ ↔ (wholePlaneClosedDualGraph _).Adj
    (rectanglePrimalEdgeBond a w h e).source (rectanglePrimalEdgeBond a w h e).target
  constructor
  · intro he
    exact (wholePlaneClosedDualGraph_adj_iff_dualBond _ _ _).mpr
      ⟨rectanglePrimalEdgeBond a w h e,he,Or.inl ⟨rfl,rfl⟩⟩
  · exact closedDual_bond_state _ _

theorem originalClosedDualRectangleRead_openGraph_adj_iff
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex)))
    (u v : RectangleVertex a w h) :
    (openGraph (rectangleGraph a w h) (originalClosedDualRectangleRead V a w h A)).Adj u v ↔
      (rectangleGraph a w h).Adj u v ∧
        (wholePlaneClosedDualGraph (finiteSubgraphConfiguration V 0 A)).Adj u.val v.val := by
  constructor
  · intro hadj
    obtain ⟨e,he,heq⟩ := (openGraph_adj _ _ u v).mp hadj
    refine ⟨openGraph_le _ _ hadj,?_⟩
    have h := (originalClosedDualRectangleRead_edgeSet_iff V a w h A e).mp he
    rw [heq] at h
    exact (wholePlaneClosedDualGraph _).mem_edgeSet.mp h
  · rintro ⟨hadj,hclosed⟩
    let e : (rectangleGraph a w h).edgeSet := ⟨s(u,v),(rectangleGraph a w h).mem_edgeSet.mpr hadj⟩
    apply (openGraph_adj _ _ u v).mpr
    exact ⟨e,(originalClosedDualRectangleRead_edgeSet_iff V a w h A e).mpr hclosed,rfl⟩

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
