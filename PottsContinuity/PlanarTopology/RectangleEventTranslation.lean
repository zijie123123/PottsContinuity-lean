module

public import PottsContinuity.BD12.RectangleOpenGraphs
public import PottsContinuity.BD12.DualStripOpen
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

theorem latticeRectangle_mem_translate_iff (a c z : LatticeVertex) (w h : ℕ) :
    latticeTranslate a z ∈ latticeRectangle (latticeTranslate a c) w h ↔
      z ∈ latticeRectangle c w h := by
  simp only [mem_latticeRectangle,latticeTranslate]
  omega

/-- Translation preserves each original open edge in the actual induced rectangle. -/
def rectangleOpenTranslationHom (a c : LatticeVertex) (w h : ℕ) (ω : LatticeConfiguration) :
    (PD.rcInfiniteOpenGraph ω).induce (latticeRectangle c w h : Set LatticeVertex) →g
      (PD.rcInfiniteOpenGraph (edgeTranslate a ω)).induce
        (latticeRectangle (latticeTranslate a c) w h : Set LatticeVertex) where
  toFun u := ⟨latticeTranslate a u.val,(latticeRectangle_mem_translate_iff a c u.val w h).mpr u.property⟩
  map_rel' := by
    intro u v huv
    exact (openGraphTranslationIso a ω).map_rel_iff'.mpr huv

theorem verticalRectangle_translate (a c : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) (hω : ω ∈ verticalRectangle c w h) :
    edgeTranslate a ω ∈ verticalRectangle (latticeTranslate a c) w h := by
  obtain ⟨u,v,hu,hv,hconn⟩ := hω
  let f := rectangleOpenTranslationHom a c w h ω
  refine ⟨f u,f v,?_,?_,hconn.map f⟩
  · change u.val.2+a.2 = c.2+a.2
    rw [hu]
  · change v.val.2+a.2 = c.2+a.2+(h:ℤ)
    rw [hv]
    omega

theorem horizontalRectangle_translate (a c : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) (hω : ω ∈ horizontalRectangle c w h) :
    edgeTranslate a ω ∈ horizontalRectangle (latticeTranslate a c) w h := by
  classical
  obtain ⟨u,v,hu,hv,hconn⟩ := hω
  have hg := embeddedRestriction_domainGraph (latticeRectangle c w h) ω
  change openGraph (rectangleGraph c w h)
    (embeddedRestriction _ (frozenEdgeEmbedding (latticeRectangle c w h)) ω) = _ at hg
  change (openGraph _ _).Reachable u v at hconn
  rw [hg] at hconn
  let f := rectangleOpenTranslationHom a c w h ω
  have ht := embeddedRestriction_domainGraph (latticeRectangle (latticeTranslate a c) w h) (edgeTranslate a ω)
  change openGraph (rectangleGraph (latticeTranslate a c) w h)
    (embeddedRestriction _ (frozenEdgeEmbedding (latticeRectangle (latticeTranslate a c) w h)) (edgeTranslate a ω)) = _ at ht
  refine ⟨f u,f v,Finset.mem_filter.mpr ⟨(f u).property,?_⟩,
    Finset.mem_filter.mpr ⟨(f v).property,?_⟩,?_⟩
  · change u.val.1+a.1 = c.1+a.1
    rw [(Finset.mem_filter.mp hu).2]
  · change v.val.1+a.1 = c.1+a.1+(w:ℤ)
    rw [(Finset.mem_filter.mp hv).2]
    omega
  · change (openGraph _ _).Reachable _ _
    rw [ht]
    exact hconn.map f

theorem verticalRectangle_translate_preimage (a c : LatticeVertex) (w h : ℕ) :
    edgeTranslate a ⁻¹' verticalRectangle (latticeTranslate a c) w h = verticalRectangle c w h := by
  ext ω
  constructor
  · intro hh
    have ht := verticalRectangle_translate (-a) (latticeTranslate a c) w h (edgeTranslate a ω) hh
    simpa only [← edgeTranslate_add,neg_add_cancel,edgeTranslate_zero,latticeTranslate_neg_cancel] using ht
  · exact verticalRectangle_translate a c w h ω

theorem horizontalRectangle_translate_preimage (a c : LatticeVertex) (w h : ℕ) :
    edgeTranslate a ⁻¹' horizontalRectangle (latticeTranslate a c) w h = horizontalRectangle c w h := by
  ext ω
  constructor
  · intro hh
    have ht := horizontalRectangle_translate (-a) (latticeTranslate a c) w h (edgeTranslate a ω) hh
    simpa only [← edgeTranslate_add,neg_add_cancel,edgeTranslate_zero,latticeTranslate_neg_cancel] using ht
  · exact horizontalRectangle_translate a c w h ω

theorem measure_verticalRectangle_translate (μ : Measure LatticeConfiguration)
    (a c : LatticeVertex) (hμ : μ.map (edgeTranslate a) = μ) (w h : ℕ) :
    μ (verticalRectangle (latticeTranslate a c) w h) = μ (verticalRectangle c w h) := by
  rw [← hμ,Measure.map_apply (edgeTranslate_measurable _) (verticalRectangle_isCylinder _ _ _).measurableSet,
    verticalRectangle_translate_preimage,hμ]

theorem measure_horizontalRectangle_translate (μ : Measure LatticeConfiguration)
    (a c : LatticeVertex) (hμ : μ.map (edgeTranslate a) = μ) (w h : ℕ) :
    μ (horizontalRectangle (latticeTranslate a c) w h) = μ (horizontalRectangle c w h) := by
  rw [← hμ,Measure.map_apply (edgeTranslate_measurable _) (horizontalRectangle_isCylinder _ _ _).measurableSet,
    horizontalRectangle_translate_preimage,hμ]

end
end PottsContinuity.PlanarTopology
