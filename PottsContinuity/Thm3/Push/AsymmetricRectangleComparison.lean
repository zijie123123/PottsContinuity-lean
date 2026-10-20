module

public import PottsContinuity.Thm3.Push.EnclosingComparison

@[expose] public section

namespace PottsContinuity.Push
open RSW PD.FK PD.RCInfinite MeasureTheory
noncomputable section

private theorem asymmetric_neighbor_closed
    (l r L R H : ℤ) (hST : PottsContinuity.latticeRectangle l r 0 H ⊆
      PottsContinuity.latticeRectangle L R 0 H) :
    ∀ x : (PottsContinuity.latticeRectangle l r 0 H : Set LatticeVertex),
      x ∉ ({v | v.val.1=l ∨ v.val.1=r ∨ v.val.2=H} : Set _) →
      ∀ y : (PottsContinuity.latticeRectangle L R 0 H : Set LatticeVertex),
      (finiteLatticeGraph _).Adj (finiteLatticeVertexEmbedding hST x) y →
      ∃ z, finiteLatticeVertexEmbedding hST z = y ∧ (finiteLatticeGraph _).Adj x z := by
  let S := PottsContinuity.latticeRectangle l r 0 H
  let T := PottsContinuity.latticeRectangle L R 0 H
  intro x hx y hxy
  have hm := x.property
  have hy := y.property
  change x.val ∈ S at hm
  change y.val ∈ T at hy
  simp only [S,T,PottsContinuity.latticeRectangle,
    Finset.mem_product,Finset.mem_Icc] at hm hy
  change ¬(x.val.1=l ∨ x.val.1=r ∨ x.val.2=H) at hx
  have hd : |x.val.1-y.val.1|+|x.val.2-y.val.2|=1 := hxy
  have hym : y.val ∈ S := by
    simp only [S,PottsContinuity.latticeRectangle,
      Finset.mem_product,Finset.mem_Icc]
    simp only [abs_eq_max_neg] at hd
    omega
  exact ⟨⟨y.val,hym⟩,rfl,hxy⟩

private theorem asymmetric_boundary_avoid
    (l r L R H : ℤ) (hL : L ≤ l) (hR : r ≤ R)
    (hST : PottsContinuity.latticeRectangle l r 0 H ⊆
      PottsContinuity.latticeRectangle L R 0 H) :
    ∀ x : (PottsContinuity.latticeRectangle l r 0 H : Set LatticeVertex),
      x ∉ ({v | v.val.1=l ∨ v.val.1=r ∨ v.val.2=H} : Set _) →
      finiteLatticeVertexEmbedding hST x ∉
        ({v | v.val.1=L ∨ v.val.1=R ∨ v.val.2=H} : Set _) := by
  let S := PottsContinuity.latticeRectangle l r 0 H
  intro x hx
  have hm := x.property
  change x.val ∈ S at hm
  simp only [S,PottsContinuity.latticeRectangle,
    Finset.mem_product,Finset.mem_Icc] at hm
  change ¬(x.val.1=l ∨ x.val.1=r ∨ x.val.2=H) at hx
  change ¬(x.val.1=L ∨ x.val.1=R ∨ x.val.2=H)
  omega

/-- Clipping an enclosing three-side-wired rectangle to an asymmetric
horizontal interval increases its actual band-crossing probability. -/
theorem asymmetric_rectangle_enclosing_comparison (θ : Parameters)
    (l r L R H : ℤ) (b : ℕ) (hL : L ≤ l) (hlr : l ≤ r) (hR : r ≤ R)
    (hb : (b:ℤ) ≤ H) :
    finiteBoundaryEventProbability (PottsContinuity.latticeRectangle L R 0 H) θ
      (BoundaryCondition.wired {v | v.val.1 = L ∨ v.val.1 = R ∨ v.val.2 = H})
      (horizontalCrossing (PottsContinuity.latticeRectangle L R 0 H) L R 0 b) ≤
    finiteBoundaryEventProbability (PottsContinuity.latticeRectangle l r 0 H) θ
      (BoundaryCondition.wired {v | v.val.1 = l ∨ v.val.1 = r ∨ v.val.2 = H})
      (horizontalCrossing (PottsContinuity.latticeRectangle l r 0 H) l r 0 b) := by
  let S := PottsContinuity.latticeRectangle l r 0 H
  let T := PottsContinuity.latticeRectangle L R 0 H
  have hST : S ⊆ T := by
    intro z hz
    simp only [S,T,PottsContinuity.latticeRectangle,
      Finset.mem_product,Finset.mem_Icc] at hz ⊢
    omega
  let ξ : BoundaryCondition (T : Set LatticeVertex) :=
    BoundaryCondition.wired {v | v.val.1 = L ∨ v.val.1 = R ∨ v.val.2 = H}
  let B : Set (S : Set LatticeVertex) := {v | v.val.1 = l ∨ v.val.1 = r ∨ v.val.2 = H}
  let E := finiteBoolEvent S (horizontalCrossing S l r 0 b)
  have hclosed := asymmetric_neighbor_closed l r L R H hST
  have havoid := asymmetric_boundary_avoid l r L R H hL hR hST
  have hcompare := embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    (finiteLatticeVertexEmbedding hST) (finiteLatticeGraph_map_le hST) θ ξ B
    hclosed havoid E (finiteBoolEvent_isUpperSet S _ (horizontalCrossing_isUpperSet S _ _ _ _))
  have hRS : PD.FK.latticeRectangle (l,0) (r-l).toNat b ⊆ S := by
    intro z hz
    rw [PD.FK.mem_latticeRectangle] at hz
    have hw : ((r-l).toNat:ℤ) = r-l := Int.toNat_of_nonneg (sub_nonneg.mpr hlr)
    simp only [S,PottsContinuity.latticeRectangle,
      Finset.mem_product,Finset.mem_Icc]
    omega
  change (PD.FK.measure (finiteLatticeGraph T) θ ξ
    (finiteBoolEvent T (horizontalCrossing T L R 0 b))).toReal ≤
    (PD.FK.measure (finiteLatticeGraph S) θ (BoundaryCondition.wired B) E).toReal
  refine le_trans ?_ hcompare
  apply measureReal_mono (μ := PD.FK.measure (finiteLatticeGraph T) θ ξ)
    (h₂ := measure_ne_top _ _)
  intro A hA
  apply (horizontalCrossing_embeddedRestriction_iff S T hST l r 0 (b:ℤ) hlr
    (by omega) (by simpa only [sub_zero, Int.toNat_natCast] using hRS) A).mpr
  exact horizontalCrossing_clip T ((boolConfigurationEquiv (finiteLatticeGraph T)).symm A)
    _ _ _ _ _ _ _ _ hL hlr hR le_rfl le_rfl hA

end
end PottsContinuity.Push
