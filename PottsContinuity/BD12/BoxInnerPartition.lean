module

public import PottsContinuity.BD12.BoxRadiusData
public import PottsContinuity.BD12.EmbeddedOpenRestriction
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! Canonical inner/outer closed-box edge partition and literal restriction. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical

/-- The shared vertex inclusion for nested centred boxes. -/
def radiusBoxInclusion (c : LatticeVertex) (n N : ℕ) (h : n ≤ N) :
    (latticeBox c n : Set LatticeVertex) ↪ (latticeBox c N : Set LatticeVertex) :=
  finiteLatticeVertexEmbedding (latticeBox_mono c h)

theorem radiusBoxInclusion_map_le (c : LatticeVertex) (n N : ℕ) (h : n ≤ N) :
    (finiteLatticeGraph (latticeBox c n)).map (radiusBoxInclusion c n N h) ≤
      finiteLatticeGraph (latticeBox c N) := finiteLatticeGraph_map_le (latticeBox_mono c h)

/-- The exact complementary outer edge carrier. -/
abbrev radiusBoxExteriorEdges (c : LatticeVertex) (n N : ℕ) (h : n ≤ N) :=
  {a : (finiteLatticeGraph (latticeBox c N)).edgeSet // a ∉ Set.range
    (FKC.FiniteFK.embeddedEdgeEmbedding (finiteLatticeGraph (latticeBox c n))
      (finiteLatticeGraph (latticeBox c N)) (radiusBoxInclusion c n N h) (radiusBoxInclusion_map_le c n N h))}

def radiusBoxEdgePartition (c : LatticeVertex) (n N : ℕ) (h : n ≤ N) :
    (finiteLatticeGraph (latticeBox c n)).edgeSet ⊕ radiusBoxExteriorEdges c n N h ≃
      (finiteLatticeGraph (latticeBox c N)).edgeSet :=
  graphInnerEdgePartition _ _ (radiusBoxInclusion c n N h) (radiusBoxInclusion_map_le c n N h)

/-- This restriction reads inner edges and leaves their original outer law intact. -/
def radiusBoxConfigurationRestriction (c : LatticeVertex) (n N : ℕ) (h : n ≤ N)
    (A : Configuration (finiteLatticeGraph (latticeBox c N))) :
    Configuration (finiteLatticeGraph (latticeBox c n)) :=
  FKC.FiniteFK.embeddedConfigurationRestriction _ _ (radiusBoxInclusion c n N h)
    (radiusBoxInclusion_map_le c n N h) A

theorem radiusBoxEdgePartition_projection (c : LatticeVertex) (n N : ℕ) (h : n ≤ N)
    (A : Configuration (finiteLatticeGraph (latticeBox c N))) :
    finitePartitionProjection (radiusBoxEdgePartition c n N h) A =
      radiusBoxConfigurationRestriction c n N h A := graphInnerEdgePartition_projection _ _ _ _ A

end
end PottsContinuity.BD12
