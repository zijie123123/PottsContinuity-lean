module

public import PottsContinuity.PlanarMixed.FiniteSlit.ExteriorFibres

/-! Intrinsic source geometry with two auxiliary exterior vertices. Only the
original rectangle bonds carry FK states; the auxiliary graph is deterministic. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section

/-- Exactly the original retained slit bonds on the source vertex carrier. -/
def sourceRetainedGraph (w h : ℕ) (x y : ℤ) : SimpleGraph (RectangleVertex (0,0) w h) :=
  (slitRetainedBondGraph x y).comap Subtype.val

/-- Source boundary vertices adjacent to the left exterior component. -/
def sourceLeftPortal (w h : ℕ) (x : ℤ) : Set (RectangleVertex (0,0) w h) :=
  {u | u.val.1 = 0 ∨ (u.val.2 = (h:ℤ) ∧ u.val.1 < x)}

/-- Source boundary vertices adjacent to the right exterior component. -/
def sourceRightPortal (w h : ℕ) (x : ℤ) : Set (RectangleVertex (0,0) w h) :=
  {u | u.val.1 = (w:ℤ) ∨ (u.val.2 = (h:ℤ) ∧ x ≤ u.val.1)}

/-- The exact source-only exterior graph: retain every original source
vertex, and attach the two separate exterior vertices to their boundary portals. -/
def sourceExteriorGraph (w h : ℕ) (x y : ℤ) : SimpleGraph (ExteriorVertex w h) where
  Adj a b := match a,b with
    | Sum.inl u,Sum.inl v => (sourceRetainedGraph w h x y).Adj u v
    | Sum.inl u,Sum.inr s => if s then u ∈ sourceRightPortal w h x else u ∈ sourceLeftPortal w h x
    | Sum.inr s,Sum.inl u => if s then u ∈ sourceRightPortal w h x else u ∈ sourceLeftPortal w h x
    | Sum.inr _,Sum.inr _ => False
  symm := by
    constructor
    intro a b hab
    cases a <;> cases b <;> dsimp at hab ⊢
    · exact hab.symm
    · exact hab
    · exact hab
  loopless := by
    constructor
    intro a ha
    cases a with
    | inl u => exact (sourceRetainedGraph w h x y).loopless.irrefl u ha
    | inr s => exact ha

/-- There is no added bond between the two exterior vertices. -/
theorem sourceExteriorGraph_no_exterior_edge (w h : ℕ) (x y : ℤ) (s t : Bool) :
    ¬ (sourceExteriorGraph w h x y).Adj (Sum.inr s) (Sum.inr t) := fun h => h

end
end PottsContinuity.PlanarMixed.FiniteSlit
