module

public import PottsContinuity.PlanarMixed.StripRSWSelectors.PaddedCompletion
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK Push BD12 Exploration PlanarTopology
noncomputable section

/-- Every actual confined open step remains open in the padded completion. -/
def prefixPaddingOpenHom (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    openGraph (caseTwoConfinedPrefixGraph n s hfit b) (caseTwoConfinedPrefixConfiguration n s hfit b C) →g
      openGraph (prefixAuxGraph n) (prefixAuxCompletion n s hfit b C) where
  toFun := prefixPaddingEmbedding n
  map_rel' := by
    intro u v huv
    obtain ⟨e,he,heq⟩ := (openGraph_adj _ _ u v).mp huv
    let f := embeddedEdgeEmbedding _ _ (prefixPaddingEmbedding n) (confinedPrefix_padding_map_le n s hfit b) e
    apply (openGraph_adj _ _ _ _).mpr
    refine ⟨f,Finset.mem_union_left _ ?_,?_⟩
    · rw [embeddedConfigurationEmbedding_eq_map]
      exact Finset.mem_map.mpr ⟨e,he,rfl⟩
    · change Sym2.map (prefixPaddingEmbedding n) e.val = _
      rw [heq]
      rfl

/-- The fixed upward ray connects any of its vertices to the padded top. -/
theorem prefixAuxRay_connected_top (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (u : PrefixAuxVertex n) (hu : u ∈ prefixAuxRay n s b) :
    ∃ v : PrefixAuxVertex n, v.val.2=((2*n+1:ℕ):ℤ) ∧
      ActualConnected (prefixAuxGraph n) (prefixAuxCompletion n s hfit b C) u v := by
  classical
  have hub := (mem_latticeRectangle _ _ _ _).mp u.property
  dsimp at hub
  let S : Set LatticeVertex := {z | z ∈ PD.FK.latticeRectangle (0,0) (2*n+1) (2*n+1) ∧
    z.1=u.val.1 ∧ u.val.2 ≤ z.2}
  obtain ⟨p,hp⟩ := vertical_walk_between u.val.1 u.val.2 ((2*n+1:ℕ):ℤ)
  have hs : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    have hh := hp z hz
    refine ⟨?_,hh.1,by omega⟩
    rw [PD.FK.mem_latticeRectangle]
    dsimp
    constructor <;> constructor <;> omega
  let φ : (squareLattice.induce S) →g openGraph (prefixAuxGraph n) (prefixAuxCompletion n s hfit b C) := {
    toFun := fun z => ⟨z.val,z.property.1⟩
    map_rel' := by
      intro a d had
      have hg : (prefixAuxGraph n).Adj ⟨a.val,a.property.1⟩ ⟨d.val,d.property.1⟩ := had
      apply (openGraph_adj _ _ _ _).mpr
      refine ⟨⟨_,hg⟩,Finset.mem_union_right _ ?_,rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro z hz
      rcases Sym2.mem_iff'.mp hz with rfl | rfl
      · exact ⟨a.property.2.1.trans hu.1,hu.2.trans a.property.2.2⟩
      · exact ⟨d.property.2.1.trans hu.1,hu.2.trans d.property.2.2⟩ }
  let q := (p.induce S hs).map φ
  refine ⟨φ ⟨_,hs _ p.end_mem_support⟩,rfl,?_⟩
  exact (q.copy (show φ ⟨_,hs _ p.start_mem_support⟩=u from rfl) rfl).reachable

/-- Every physical confined connection extends to an auxiliary vertical arm. -/
theorem prefixAuxCompletion_arm_of_confined_connection (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (hC : caseTwoConfinedPrefixConfiguration n s hfit b C ∈
      arcsConnectionEvent (caseTwoConfinedPrefixGraph n s hfit b)
        (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
        {z | z.val.1=4*(s:ℤ)-1 ∧ b.2.val.2≤z.val.2}) :
    prefixAuxCompletion n s hfit b C ∈ intervalArmEvent (2*n+1) (4*(s:ℤ)) (5*(s:ℤ)) := by
  obtain ⟨a,ha,t,ht,p⟩ := hC
  obtain ⟨v,hv,htv⟩ := prefixAuxRay_connected_top n s hfit b C (prefixPaddingEmbedding n t) ht
  refine ⟨prefixPaddingEmbedding n a,ha,v,hv,?_⟩
  exact (p.map (prefixPaddingOpenHom n s hfit b C)).trans htv

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
