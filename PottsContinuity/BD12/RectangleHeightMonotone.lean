module

public import PottsContinuity.BD12.RectangleOpenGraphs
public import PottsContinuity.BD12.WiredSquare

/-! Enlarging only the height preserves an actual horizontal crossing,
which gives the easy-direction rectangle bound from the wired square bound. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory
noncomputable section

/-- A crossing persists when the rectangle height increases. -/
theorem horizontalRectangle_mono_height (a : LatticeVertex) (w h H : ℕ) (hh : h ≤ H) :
    horizontalRectangle a w h ⊆ horizontalRectangle a w H := by
  intro ω hω
  obtain ⟨u,v,hu,hv,hconn⟩ := hω
  have hsub : PD.FK.latticeRectangle a w h ⊆ PD.FK.latticeRectangle a w H := by
    intro z hz
    rw [mem_latticeRectangle] at hz ⊢
    exact ⟨hz.1,hz.2.1,by omega⟩
  let f : RectangleVertex a w h → RectangleVertex a w H := fun z => ⟨z.val,hsub z.property⟩
  let G := openGraph (rectangleGraph a w h)
    (embeddedRestriction (rectangleGraph a w h) (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h)) ω)
  let K := openGraph (rectangleGraph a w H)
    (embeddedRestriction (rectangleGraph a w H) (frozenEdgeEmbedding (PD.FK.latticeRectangle a w H)) ω)
  have hg := embeddedRestriction_domainGraph (PD.FK.latticeRectangle a w h) ω
  have hk := embeddedRestriction_domainGraph (PD.FK.latticeRectangle a w H) ω
  let g : G →g K := {
    toFun := f
    map_rel' := by
      intro x y hxy
      have hxy' : ((PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle a w h : Set LatticeVertex)).Adj x y := by
        rw [← hg]
        exact hxy
      have hxyBig : ((PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle a w H : Set LatticeVertex)).Adj (f x) (f y) := hxy'
      exact Eq.mpr (congrArg (fun L : SimpleGraph (RectangleVertex a w H) => L.Adj (f x) (f y)) hk) hxyBig }
  refine ⟨f u,f v,Finset.mem_filter.mpr ⟨(f u).property,(Finset.mem_filter.mp hu).2⟩,
    Finset.mem_filter.mpr ⟨(f v).property,(Finset.mem_filter.mp hv).2⟩,?_⟩
  exact hconn.map g

/-- The wired easy-direction bound at the explicit self-dual point. -/
theorem wired_selfDual_easy_rectangle_ge_half (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ)
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : w-1 ≤ h) :
    (1/2 : ℝ) ≤ μ.real (horizontalRectangle a w h) := by
  let : IsProbabilityMeasure μ := hμ.1
  have hwidth : w-1+1 = w := by omega
  have hsq := wired_square_crossing_ge_half q μ hμ a (w-1)
  rw [hwidth] at hsq
  exact hsq.trans (measureReal_mono (horizontalRectangle_mono_height a w (w-1) h hh))

end
end PottsContinuity.BD12
