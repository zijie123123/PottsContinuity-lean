module

public import PottsContinuity.Thm3.Push.CutPocketAugmentation
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceExteriorReveals

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance augmentedSourceRevealEdgeEq (w h : ℕ) :
    DecidableEq (rectangleGraph (0,0) w h).edgeSet := Classical.decEq _

/-- The left source exterior with unseeded vertex-cut pockets added explicitly. -/
def pocketAugmentedSourceLeftExterior (w h : ℕ) (x y : ℤ)
    (cut : Set (RectangleVertex (0,0) w h)) : Set (RectangleVertex (0,0) w h) :=
  {v | Sum.inl v ∈ pocketAugmentedCutExterior (sourceExteriorGraph w h x y)
    (Sum.inl '' cut) (sourceBeta w h x y) (sourceAlpha w h x)}

/-- The right source exterior with its own unseeded cut pockets added. -/
def pocketAugmentedSourceRightExterior (w h : ℕ) (x y : ℤ)
    (cut : Set (RectangleVertex (0,0) w h)) : Set (RectangleVertex (0,0) w h) :=
  {v | Sum.inl v ∈ pocketAugmentedCutExterior (sourceExteriorGraph w h x y)
    (Sum.inl '' cut) (sourceAlpha w h x) (sourceBeta w h x y)}

/-- A distinct source bond reveal for investigating pocket-aware locality.
No stopping property or mixed-domain comparison is asserted by this definition. -/
def pocketAugmentedSourceReveal (w h : ℕ) (x y : ℤ) (first second : Set LatticeVertex) :
    Configuration (rectangleGraph (0,0) w h) :=
  rectangleSlitBonds w h x y ∪
    (internalBonds (rectangleGraph (0,0) w h)
      (pocketAugmentedSourceLeftExterior w h x y (sourceCoordinateTrace w h first)) ∪
     internalBonds (rectangleGraph (0,0) w h)
      (pocketAugmentedSourceRightExterior w h x y (sourceCoordinateTrace w h second)))

/-- Left augmentation preserves every original closed-exterior vertex. -/
theorem sourceLeftExterior_subset_pocketAugmented (w h : ℕ) (x y : ℤ)
    (cut : Set (RectangleVertex (0,0) w h)) :
    sourceLeftExterior w h x y cut ⊆ pocketAugmentedSourceLeftExterior w h x y cut :=
  fun _ hv => Or.inl hv

/-- Right augmentation preserves every original closed-exterior vertex. -/
theorem sourceRightExterior_subset_pocketAugmented (w h : ℕ) (x y : ℤ)
    (cut : Set (RectangleVertex (0,0) w h)) :
    sourceRightExterior w h x y cut ⊆ pocketAugmentedSourceRightExterior w h x y cut :=
  fun _ hv => Or.inl hv

private theorem internalBonds_subset_of_subset {V : Type*} [Finite V]
    (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T) :
    internalBonds G S ⊆ internalBonds G T := by
  classical
  intro e he
  simp only [internalBonds,Finset.mem_filter,Finset.mem_univ,true_and] at he ⊢
  exact fun v hv => hST (he v hv)

/-- The literal augmented bond record contains the whole original native
record, including every slit bond and both old one-sided exteriors. -/
theorem sourceExteriorReveal_subset_pocketAugmented (w h : ℕ) (x y : ℤ)
    (first second : Set LatticeVertex) :
    sourceExteriorReveal w h x y first second ⊆
      pocketAugmentedSourceReveal w h x y first second := by
  unfold sourceExteriorReveal pocketAugmentedSourceReveal
  apply Finset.union_subset_union Finset.Subset.rfl
  apply Finset.union_subset_union
  · exact internalBonds_subset_of_subset _ (sourceLeftExterior_subset_pocketAugmented w h x y _)
  · exact internalBonds_subset_of_subset _ (sourceRightExterior_subset_pocketAugmented w h x y _)

end
end PottsContinuity.Push
