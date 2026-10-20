module

public import PottsContinuity.PlanarTopology.BalancedCellFiniteWitness

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

/-- A genuine infinite marked root and a boundary-reaching marked root join
inside the rectangle through a finite local-uniqueness witness. -/
theorem rectangleConnectionEvent_transfer_of_finiteLocalUniqueness
    (a : LatticeVertex) (w h : ℕ) (A C B : Set LatticeVertex) (S T : Finset LatticeVertex)
    (hA : A ⊆ (S : Set LatticeVertex)) (hC : C ⊆ (S : Set LatticeVertex))
    (hCR : C ⊆ (PD.FK.latticeRectangle a w h : Set LatticeVertex))
    (hTR : (T : Set LatticeVertex) ⊆ (PD.FK.latticeRectangle a w h : Set LatticeVertex))
    (hBT : ∀ z ∈ B, z ∉ T) (ω : LatticeConfiguration)
    (hω : ω ∈ finiteLocalUniquenessEvent S T)
    (hinfiniteRoot : ω ∈ infiniteHit C) (hc : ω ∈ rectangleConnectionEvent a w h A B) :
    ω ∈ rectangleConnectionEvent a w h C B := by
  obtain ⟨q,hq,hi⟩ := hinfiniteRoot
  obtain ⟨u,hu,v,hv,hconn⟩ := (rectangleConnectionEvent_iff _ _ _ _ _ _).mp hc
  let qR : RectangleVertex a w h := ⟨q,hCR hq⟩
  obtain ⟨t,ht,htT⟩ := hi.exists_notMem_finset T
  let f : (PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle a w h : Set LatticeVertex) →g
      PD.rcInfiniteOpenGraph ω := { toFun := Subtype.val, map_rel' := fun h => h }
  have hqu := finiteLocalUniquenessEvent_connects_in_domain S T _ hTR ω hω qR u
    (hC hq) (hA hu) ⟨t,htT,ht⟩ ⟨v.val,hBT v.val hv,hconn.map f⟩
  exact (rectangleConnectionEvent_iff _ _ _ _ _ _).mpr ⟨qR,hq,v,hv,hqu.trans hconn⟩

/-- Two actual marked connections in possibly different rectangles glue inside
one containing rectangle. The local connector uses global outside witnesses,
so neither original path is required to lie in the other's rectangle. -/
theorem rectangleConnectionEvent_glue_of_finiteLocalUniqueness
    (a a₁ a₂ : LatticeVertex) (w h w₁ h₁ w₂ h₂ : ℕ)
    (A B L U : Set LatticeVertex) (S T : Finset LatticeVertex)
    (hD₁ : (PD.FK.latticeRectangle a₁ w₁ h₁ : Set LatticeVertex) ⊆ PD.FK.latticeRectangle a w h)
    (hD₂ : (PD.FK.latticeRectangle a₂ w₂ h₂ : Set LatticeVertex) ⊆ PD.FK.latticeRectangle a w h)
    (hTD : (T : Set LatticeVertex) ⊆ PD.FK.latticeRectangle a w h)
    (hA : A ⊆ (S : Set LatticeVertex)) (hB : B ⊆ (S : Set LatticeVertex))
    (hLT : ∀ z ∈ L, z ∉ T) (hUT : ∀ z ∈ U, z ∉ T)
    (ω : LatticeConfiguration) (hω : ω ∈ finiteLocalUniquenessEvent S T)
    (hfirst : ω ∈ rectangleConnectionEvent a₁ w₁ h₁ A L)
    (hsecond : ω ∈ rectangleConnectionEvent a₂ w₂ h₂ B U) :
    ω ∈ rectangleConnectionEvent a w h L U := by
  obtain ⟨u,hu,l,hl,huL⟩ := (rectangleConnectionEvent_iff _ _ _ _ _ _).mp hfirst
  obtain ⟨v,hv,t,ht,hvU⟩ := (rectangleConnectionEvent_iff _ _ _ _ _ _).mp hsecond
  let f₁ : (PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle a₁ w₁ h₁ : Set LatticeVertex) →g
      (PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle a w h : Set LatticeVertex) :=
    { toFun := fun z => ⟨z.val,hD₁ z.property⟩, map_rel' := fun h => h }
  let f₂ : (PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle a₂ w₂ h₂ : Set LatticeVertex) →g
      (PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle a w h : Set LatticeVertex) :=
    { toFun := fun z => ⟨z.val,hD₂ z.property⟩, map_rel' := fun h => h }
  let g₁ : (PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle a₁ w₁ h₁ : Set LatticeVertex) →g
      PD.rcInfiniteOpenGraph ω := { toFun := Subtype.val, map_rel' := fun h => h }
  let g₂ : (PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle a₂ w₂ h₂ : Set LatticeVertex) →g
      PD.rcInfiniteOpenGraph ω := { toFun := Subtype.val, map_rel' := fun h => h }
  have huv := finiteLocalUniquenessEvent_connects_in_domain S T _ hTD ω hω (f₁ u) (f₂ v)
    (hA hu) (hB hv) ⟨l.val,hLT l.val hl,huL.map g₁⟩ ⟨t.val,hUT t.val ht,hvU.map g₂⟩
  exact (rectangleConnectionEvent_iff _ _ _ _ _ _).mpr
    ⟨f₁ l,hl,f₂ t,ht,((huL.symm.map f₁).trans huv).trans (hvU.map f₂)⟩

end
end PottsContinuity.PlanarTopology
