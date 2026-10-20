module

public import PottsContinuity.Thm3.RSW.RectangleBandBooleanBridge
public import PottsContinuity.Thm3.Push.EnclosingComparison

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.RCInfinite MeasureTheory
noncomputable section

/-- Shrinking only the rightmost column increases the bottom-band crossing
probability under the literal three-side-wired laws. -/
theorem rectangle_one_column_crossing_comparison (θ : Parameters)
    (a : LatticeVertex) (w h b : ℕ) (hbh : b ≤ h) :
    finiteBoundaryEventProbability (PD.FK.latticeRectangle a (w+1) h) θ
      (BoundaryCondition.wired {v | v.val.1=a.1 ∨ v.val.1=a.1+((w+1:ℕ):ℤ) ∨
        v.val.2=a.2+(h:ℤ)})
      (horizontalCrossing (PD.FK.latticeRectangle a (w+1) h)
        a.1 (a.1+((w+1:ℕ):ℤ)) a.2 (a.2+(b:ℤ))) ≤
    finiteBoundaryEventProbability (PD.FK.latticeRectangle a w h) θ
      (BoundaryCondition.wired {v | v.val.1=a.1 ∨ v.val.1=a.1+(w:ℤ) ∨
        v.val.2=a.2+(h:ℤ)})
      (horizontalCrossing (PD.FK.latticeRectangle a w h)
        a.1 (a.1+(w:ℤ)) a.2 (a.2+(b:ℤ))) := by
  let S := PD.FK.latticeRectangle a w h
  let T := PD.FK.latticeRectangle a (w+1) h
  have hST : S ⊆ T := by
    intro z hz
    rw [mem_latticeRectangle] at hz ⊢
    push_cast
    omega
  let f := finiteLatticeVertexEmbedding hST
  let G := finiteLatticeGraph S
  let H := finiteLatticeGraph T
  let B : Set (S : Set LatticeVertex) :=
    {v | v.val.1=a.1 ∨ v.val.1=a.1+(w:ℤ) ∨ v.val.2=a.2+(h:ℤ)}
  let ξ : BoundaryCondition (T : Set LatticeVertex) := BoundaryCondition.wired
    {v | v.val.1=a.1 ∨ v.val.1=a.1+((w+1:ℕ):ℤ) ∨ v.val.2=a.2+(h:ℤ)}
  let E := finiteBoolEvent S (horizontalCrossing S a.1 (a.1+(w:ℤ)) a.2 (a.2+(b:ℤ)))
  have hclosed : ∀ ⦃x : (S : Set LatticeVertex)⦄, x ∉ B →
      ∀ ⦃y : (T : Set LatticeVertex)⦄, H.Adj (f x) y →
      ∃ z : (S : Set LatticeVertex), f z = y ∧ G.Adj x z := by
    intro x hx y hxy
    have hxm := (mem_latticeRectangle a x.val w h).mp x.property
    have hym := (mem_latticeRectangle a y.val (w+1) h).mp y.property
    change ¬ (x.val.1=a.1 ∨ x.val.1=a.1+(w:ℤ) ∨ x.val.2=a.2+(h:ℤ)) at hx
    have hd : |x.val.1-y.val.1|+|x.val.2-y.val.2|=1 := hxy
    have hyS : y.val ∈ S := by
      rw [mem_latticeRectangle]
      simp only [abs_eq_max_neg] at hd
      omega
    exact ⟨⟨y.val,hyS⟩,rfl,hxy⟩
  have havoid : ∀ ⦃x : (S : Set LatticeVertex)⦄, x ∉ B → f x ∉ ξ.boundary := by
    intro x hx
    have hxm := (mem_latticeRectangle a x.val w h).mp x.property
    change ¬ (x.val.1=a.1 ∨ x.val.1=a.1+(w:ℤ) ∨ x.val.2=a.2+(h:ℤ)) at hx
    change ¬ (x.val.1=a.1 ∨ x.val.1=a.1+((w+1:ℕ):ℤ) ∨ x.val.2=a.2+(h:ℤ))
    push_cast
    omega
  have hcompare := embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    f (finiteLatticeGraph_map_le hST) θ ξ B hclosed havoid E
    (finiteBoolEvent_isUpperSet S _ (horizontalCrossing_isUpperSet S _ _ _ _))
  have hRS : PD.FK.latticeRectangle (a.1,a.2)
      (a.1+(w:ℤ)-a.1).toNat (a.2+(b:ℤ)-a.2).toNat ⊆ S := by
    simpa only [add_sub_cancel_left,Int.toNat_natCast,Prod.mk.eta] using
      Push.rectangle_height_subset a w b h hbh
  apply le_trans _ hcompare
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro A hA
  apply (Push.horizontalCrossing_embeddedRestriction_iff S T hST _ _ _ _
    (by omega) (by omega) hRS A).mpr
  exact Push.horizontalCrossing_clip T ((boolConfigurationEquiv H).symm A)
    _ _ _ _ _ _ _ _ le_rfl (by omega) (by push_cast; omega) le_rfl le_rfl hA

end
end PottsContinuity.RSW
