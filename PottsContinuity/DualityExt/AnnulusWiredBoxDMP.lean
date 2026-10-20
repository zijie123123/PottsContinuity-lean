module

public import PottsContinuity.DualityExt.AnnulusBoundaryIdentification
public import PottsContinuity.DualityExt.AnnulusPlaneEventRestriction
public import PottsContinuity.PD.RCInfinite.FiniteEnergy
public import PottsContinuity.Infinite.InducedDMP
public import PottsContinuity.PD.RCInfinite.SpatialComparison

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.Infinite
open MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance annulusDmpConfigFintype (N : ℕ) : Fintype (Configuration (annulusSourceGraph N)) := Fintype.ofFinite _
local instance annulusDmpConfigDecidableEq (N : ℕ) : DecidableEq (Configuration (annulusSourceGraph N)) := Classical.decEq _

def annulusToBoxVertex (N M : ℕ) (hNM : 2 * N ≤ M) :
    {x : LatticeVertex // x ∈ annulusVertexSet N} ↪ BoxVertex (0, 0) M where
  toFun := fun x => ⟨x.val, latticeBox_mono (0, 0) hNM (Finset.mem_sdiff.mp x.2 |>.1)⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : BoxVertex (0, 0) M => z.val) h

theorem annulusSourceGraph_map_le_boxGraph (N M : ℕ) (hNM : 2 * N ≤ M) :
    (annulusSourceGraph N).map (annulusToBoxVertex N M hNM) ≤ boxGraph (0, 0) M := by
  intro x y hxy
  rcases (SimpleGraph.map_adj _ _ _ _).mp hxy with ⟨u, v, huv, rfl, rfl⟩
  exact (boxGraph_adj_iff (0, 0) M _ _).2 huv

theorem annulusSourcePlaneRestriction_eq_boxRestriction
    (N M : ℕ) (hNM : 2 * N ≤ M)
    (C : Configuration (boxGraph (0, 0) M)) :
    annulusSourcePlaneConfiguration N (boxExtension 1 (0, 0) M C) =
      embeddedConfigurationRestriction (annulusSourceGraph N) (boxGraph (0, 0) M)
        (annulusToBoxVertex N M hNM)
        (annulusSourceGraph_map_le_boxGraph N M hNM) C := by
  classical
  apply Finset.ext
  intro e
  simp only [annulusSourcePlaneConfiguration, Finset.mem_filter,
    Finset.mem_univ, true_and, mem_embeddedConfigurationRestriction]
  have hEdge :
      boxEdgeEmbedding (0, 0) M (embeddedEdgeEmbedding
        (annulusSourceGraph N) (boxGraph (0, 0) M)
        (annulusToBoxVertex N M hNM)
        (annulusSourceGraph_map_le_boxGraph N M hNM) e) =
      embeddedEdgeEmbedding (annulusSourceGraph N)
        PottsContinuity.PD.FK.squareLattice
        (annulusSourcePlaneEmbedding N) (annulusSourcePlaneGraph_map_le_square N) e := by
    apply Subtype.ext
    change Sym2.map (fun v : BoxVertex (0, 0) M => v.val)
        (Sym2.map (annulusToBoxVertex N M hNM) e.val) =
      Sym2.map (fun x : {x : LatticeVertex // x ∈ annulusVertexSet N} => x.val) e.val
    rw [Sym2.map_map]
    rfl
  rw [← hEdge, boxExtension_at]
  simp only [decide_eq_true_eq]

end
end PottsContinuity.DualityExt
