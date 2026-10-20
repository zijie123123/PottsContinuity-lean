module

public import PottsContinuity.Thm3.Push.SourceBandRawQuerySeparation
public import PottsContinuity.Thm3.Push.AugmentedOppositeReach
public import PottsContinuity.Thm3.Push.PocketAugmentedSourceReveal
public import PottsContinuity.Thm3.Push.CaseTwoTipRawLocality
public import PottsContinuity.Thm3.Push.CaseTwoTraceCrop
public import PottsContinuity.Thm3.Push.SideCollarFirstHitPath

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- Every actual raw-tip query endpoint off the selected trace is excluded
from the opposite source alpha component, at positive recorded tip height.
No geometric separation or precursor-locality interface is assumed. -/
theorem caseTwoTip_raw_query_off_trace_not_alpha_of_pos_height
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (tip : SideCollarFirstHitRecord (5*s) (2*n))
    (v : RectangleVertex (0,0) (2*n) (2*n))
    (htip : caseTwoTipFirstHitSelector n s hfit C = some tip)
    (hlast : (caseTwoTipOriginalTrace n s hfit tip).getLast? = some v)
    (hy : 0 < v.val.2)
    (e : (rectangleGraph (0,0) (2*n) (2*n)).edgeSet)
    (he : e ∈ caseTwoTipRawReveal n s hfit C)
    (z : RectangleVertex (0,0) (2*n) (2*n)) (hz : z ∈ e.val)
    (hoff : z ∉ sourceCoordinateTrace (2*n) (2*n)
      (Subtype.val '' {t | t ∈ caseTwoTipOriginalTrace n s hfit tip})) :
    Sum.inl z ∉ cutReachRegion (sourceExteriorGraph (2*n) (2*n) (4*(s:ℤ)) v.val.2)
      (Sum.inl '' sourceCoordinateTrace (2*n) (2*n)
        (Subtype.val '' {t | t ∈ caseTwoTipOriginalTrace n s hfit tip}))
      (sourceAlpha (2*n) (2*n) (4*(s:ℤ))) := by
  classical
  let f := sourceBandEmbedding (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl
  let hmap := sourceBandEmbedding_map_le (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl
  let A := embeddedConfigurationRestriction _ _ f hmap C
  have hsel : sideCollarFirstHitSelector (5*s) (2*n) ((2*s:ℕ):ℤ) ((3*s:ℕ):ℤ) A = some tip := htip
  obtain ⟨a,ha,hal,har,b,hb,q,hq,hfirst⟩ :=
    sideCollarFirstHitSelector_path_in_open_record (5*s) (2*n) ((2*s:ℕ):ℤ) ((3*s:ℕ):ℤ) A tip hsel
  let Q := q.val.mapLe (openGraph_mono Finset.inter_subset_left)
  have hQs : Q.support = tip.2 := (SimpleGraph.Walk.support_mapLe_eq_support _ _).trans hq
  have htrace : caseTwoTipOriginalTrace n s hfit tip = Q.support.map f := by
    rw [hQs]
    rfl
  have hend : Q.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast Q.support_ne_nil,SimpleGraph.Walk.getLast_support]
  have hlastMap : (Q.support.map f).getLast? = some (f b) := by
    rw [List.getLast?_map,hend]
    rfl
  have hbeq : f b = v := Option.some.inj (hlastMap.symm.trans ((congrArg List.getLast? htrace).symm.trans hlast))
  have hheight : b.val.2 = v.val.2 := congrArg (fun t => t.val.2) hbeq
  have hcut0 : sourceCoordinateTrace (2*n) (2*n)
      (Subtype.val '' {t | t ∈ caseTwoTipOriginalTrace n s hfit tip}) =
      {t | t ∈ caseTwoTipOriginalTrace n s hfit tip} := by
    ext t
    constructor
    · rintro ⟨u,hu,heq⟩
      exact Subtype.ext heq ▸ hu
    · exact fun ht => ⟨t,ht,rfl⟩
  have hcut : sourceCoordinateTrace (2*n) (2*n)
      (Subtype.val '' {t | t ∈ caseTwoTipOriginalTrace n s hfit tip}) = f '' {t | t ∈ Q.support} := by
    rw [hcut0,htrace]
    ext t
    exact List.mem_map
  change e ∈ embeddedConfigurationEmbedding _ _ f hmap
    (sideCollarRawLeftArmReveal (5*s) (2*n) ((3*s:ℕ):ℤ) A) at he
  rw [embeddedConfigurationEmbedding_eq_map] at he
  obtain ⟨g,hg,hge⟩ := Finset.mem_map.mp he
  subst e
  change z ∈ Sym2.map f g.val at hz
  obtain ⟨u,hu,huz⟩ := Sym2.mem_map.mp hz
  subst z
  have huoff : u ∉ Q.support := by
    intro hut
    apply hoff
    rw [hcut]
    exact ⟨u,hut,rfl⟩
  have hn := sourceBand_raw_query_off_trace_not_alpha (2*n) (4*s) (5*s)
    (by omega) (by omega) A ((3*s:ℕ):ℤ) Q ha (by omega) har hb
    (by omega) g hg u hu huoff
  rw [← hcut] at hn
  simpa only [Nat.cast_mul,Nat.cast_ofNat,hheight] using hn

end
end PottsContinuity.Push
