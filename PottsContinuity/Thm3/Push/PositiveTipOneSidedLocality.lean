module

public import PottsContinuity.Thm3.Push.CaseTwoTipRawSeparation

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance positiveTipOneSidedEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- The tip queries use only the right augmented exterior and slit bonds. -/
theorem caseTwoTipRawReveal_subset_right_augmented_of_pos_height
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (tip : SideCollarFirstHitRecord (5*s) (2*n))
    (v : RectangleVertex (0,0) (2*n) (2*n))
    (htip : caseTwoTipFirstHitSelector n s hfit C = some tip)
    (hlast : (caseTwoTipOriginalTrace n s hfit tip).getLast? = some v)
    (hy : 0 < v.val.2) :
    caseTwoTipRawReveal n s hfit C ⊆
      rectangleSlitBonds (2*n) (2*n) (4*(s:ℤ)) v.val.2 ∪
      internalBonds (rectangleGraph (0,0) (2*n) (2*n))
        (pocketAugmentedSourceRightExterior (2*n) (2*n) (4*(s:ℤ)) v.val.2
          (sourceCoordinateTrace (2*n) (2*n)
            (Subtype.val '' {z | z ∈ caseTwoTipOriginalTrace n s hfit tip}))) := by
  classical
  intro e he
  by_cases hslit : e ∈ rectangleSlitBonds (2*n) (2*n) (4*(s:ℤ)) v.val.2
  · exact Finset.mem_union.mpr (Or.inl hslit)
  apply Finset.mem_union.mpr
  right
  simp only [internalBonds,Finset.mem_filter,Finset.mem_univ,true_and]
  intro z hz
  apply mem_pocketAugmented_of_not_opposite_reachable
  by_cases hcut : z ∈ sourceCoordinateTrace (2*n) (2*n)
      (Subtype.val '' {t | t ∈ caseTwoTipOriginalTrace n s hfit tip})
  · rintro ⟨u,hu,p,havoid⟩
    exact havoid (Sum.inl z) p.end_mem_support ⟨z,hcut,rfl⟩
  · exact caseTwoTip_raw_query_off_trace_not_alpha_of_pos_height
      n s hs hfit C tip v htip hlast hy e he z hz hcut

/-- A positive tip is stable on its own right exterior, independently of
any precursor record. -/
theorem caseTwoTipFirstHitSelector_stable_on_right_augmented_of_pos_height
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C D : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (tip : SideCollarFirstHitRecord (5*s) (2*n))
    (v : RectangleVertex (0,0) (2*n) (2*n))
    (htip : caseTwoTipFirstHitSelector n s hfit C = some tip)
    (hlast : (caseTwoTipOriginalTrace n s hfit tip).getLast? = some v)
    (hy : 0 < v.val.2)
    (hstates : D ∩ (rectangleSlitBonds (2*n) (2*n) (4*(s:ℤ)) v.val.2 ∪
      internalBonds (rectangleGraph (0,0) (2*n) (2*n))
        (pocketAugmentedSourceRightExterior (2*n) (2*n) (4*(s:ℤ)) v.val.2
          (sourceCoordinateTrace (2*n) (2*n)
            (Subtype.val '' {z | z ∈ caseTwoTipOriginalTrace n s hfit tip})))) =
      C ∩ (rectangleSlitBonds (2*n) (2*n) (4*(s:ℤ)) v.val.2 ∪
      internalBonds (rectangleGraph (0,0) (2*n) (2*n))
        (pocketAugmentedSourceRightExterior (2*n) (2*n) (4*(s:ℤ)) v.val.2
          (sourceCoordinateTrace (2*n) (2*n)
            (Subtype.val '' {z | z ∈ caseTwoTipOriginalTrace n s hfit tip}))))) :
    caseTwoTipFirstHitSelector n s hfit D = some tip := by
  have hsub := caseTwoTipRawReveal_subset_right_augmented_of_pos_height
    n s hs hfit C tip v htip hlast hy
  exact (caseTwoTipFirstHitSelector_eq_of_raw_reveal_subset n s hfit C D _ hsub
    (by simpa only [Finset.ext_iff,Finset.mem_inter] using hstates)).trans htip

end
end PottsContinuity.Push
