module

public import PottsContinuity.PlanarTopology.TransposeLaw
public import PottsContinuity.BD12.RectangleOpenGraphs
public import PottsContinuity.BD12.DualStripOpen
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

/-- Coordinate interchange preserves original open rectangle edges. -/
def rectangleOpenTransposeHom (c : LatticeVertex) (w h : ℕ) (ω : LatticeConfiguration) :
    (PD.rcInfiniteOpenGraph ω).induce (latticeRectangle c w h : Set LatticeVertex) →g
      (PD.rcInfiniteOpenGraph (latticeConfigurationIsoHomeomorph latticeTransposeIso ω)).induce
        (latticeRectangle c.swap h w : Set LatticeVertex) where
  toFun u := ⟨u.val.swap,by
    have hu := (mem_latticeRectangle c u.val w h).mp u.property
    exact (mem_latticeRectangle c.swap u.val.swap h w).mpr ⟨hu.2,hu.1⟩⟩
  map_rel' := by
    intro u v huv
    exact (rcOpenConfigurationIso latticeTransposeIso ω).map_rel_iff'.mpr huv

theorem verticalRectangle_transpose (c : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) (hω : ω ∈ verticalRectangle c w h) :
    latticeConfigurationIsoHomeomorph latticeTransposeIso ω ∈ horizontalRectangle c.swap h w := by
  classical
  obtain ⟨u,v,hu,hv,hconn⟩ := hω
  let f := rectangleOpenTransposeHom c w h ω
  have hg := embeddedRestriction_domainGraph (latticeRectangle c.swap h w)
    (latticeConfigurationIsoHomeomorph latticeTransposeIso ω)
  change openGraph (rectangleGraph c.swap h w)
    (embeddedRestriction _ (frozenEdgeEmbedding (latticeRectangle c.swap h w)) _) = _ at hg
  refine ⟨f u,f v,Finset.mem_filter.mpr ⟨(f u).property,hu⟩,
    Finset.mem_filter.mpr ⟨(f v).property,hv⟩,?_⟩
  change (openGraph _ _).Reachable _ _
  rw [hg]
  exact hconn.map f

theorem horizontalRectangle_transpose (c : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) (hω : ω ∈ horizontalRectangle c w h) :
    latticeConfigurationIsoHomeomorph latticeTransposeIso ω ∈ verticalRectangle c.swap h w := by
  classical
  obtain ⟨u,v,hu,hv,hconn⟩ := hω
  let f := rectangleOpenTransposeHom c w h ω
  have hg := embeddedRestriction_domainGraph (latticeRectangle c w h) ω
  change openGraph (rectangleGraph c w h)
    (embeddedRestriction _ (frozenEdgeEmbedding (latticeRectangle c w h)) ω) = _ at hg
  change (openGraph _ _).Reachable u v at hconn
  rw [hg] at hconn
  exact ⟨f u,f v,(Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hv).2,hconn.map f⟩

theorem horizontalRectangle_transpose_preimage (c : LatticeVertex) (w h : ℕ) :
    latticeConfigurationIsoHomeomorph latticeTransposeIso ⁻¹' horizontalRectangle c.swap h w =
      verticalRectangle c w h := by
  ext ω
  constructor
  · intro hh
    have ht := horizontalRectangle_transpose c.swap h w _ hh
    simpa only [transposeConfiguration_twice,Prod.swap_swap] using ht
  · exact verticalRectangle_transpose c w h ω

theorem verticalRectangle_transpose_preimage (c : LatticeVertex) (w h : ℕ) :
    latticeConfigurationIsoHomeomorph latticeTransposeIso ⁻¹' verticalRectangle c.swap h w =
      horizontalRectangle c w h := by
  ext ω
  constructor
  · intro hh
    have ht := verticalRectangle_transpose c.swap h w _ hh
    simpa only [transposeConfiguration_twice,Prod.swap_swap] using ht
  · exact horizontalRectangle_transpose c w h ω

theorem transposeLaw_horizontalRectangle (μ : Measure LatticeConfiguration) (c : LatticeVertex) (w h : ℕ) :
    μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso) (horizontalRectangle c.swap h w) =
      μ (verticalRectangle c w h) := by
  rw [Measure.map_apply (latticeConfigurationIsoHomeomorph_measurable _) (horizontalRectangle_isCylinder _ _ _).measurableSet,
    horizontalRectangle_transpose_preimage]

theorem transposeLaw_verticalRectangle (μ : Measure LatticeConfiguration) (c : LatticeVertex) (w h : ℕ) :
    μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso) (verticalRectangle c.swap h w) =
      μ (horizontalRectangle c w h) := by
  rw [Measure.map_apply (latticeConfigurationIsoHomeomorph_measurable _) (verticalRectangle_isCylinder _ _ _).measurableSet,
    verticalRectangle_transpose_preimage]

end
end PottsContinuity.PlanarTopology
