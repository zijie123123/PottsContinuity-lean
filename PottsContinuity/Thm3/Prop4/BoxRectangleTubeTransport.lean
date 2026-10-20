module

public import PottsContinuity.PlanarTopology.BoxSampledDualScreen
public import PottsContinuity.Thm3.Prop4.TubeRevealedEdges

/-!
# Literal tube and cut transport to the sampled rectangle carrier

The vertex map is the coordinate identity. Original bonds, tube-confined
source connections and the exact cut cardinality are retained.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

local instance boxTubeTransportSourceEdgeDecidableEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set LatticeVertex)).edgeSet := Classical.decEq _
local instance boxTubeTransportTargetEdgeDecidableEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- The coordinate identity `PlanarTopology.boxRectangleGraphIso`, stated directly on the
frozen source box carrier. -/
def boxTubeRectangleIso (n : ℕ) :
    squareLattice.induce (box n : Set LatticeVertex) ≃g
      rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) :=
  PlanarTopology.boxRectangleGraphIso n

@[simp] theorem boxTubeRectangleIso_val (n : ℕ) (z : (box n : Set LatticeVertex)) :
    (boxTubeRectangleIso n z).val = z.val := rfl

/-- The rectangle transport retains the original unordered lattice bond. -/
theorem box_rectangle_edge_coordinates (n : ℕ)
    (e : (squareLattice.induce (box n : Set LatticeVertex)).edgeSet) :
    Sym2.map Subtype.val
      (configurationIsoEdgeEquiv (boxTubeRectangleIso n) e).val =
      Sym2.map Subtype.val e.val := by
  change Sym2.map Subtype.val (Sym2.map (boxTubeRectangleIso n) e.val) = _
  rw [Sym2.map_map]
  rfl

/-- Cut membership on the target carrier is exactly the literal original
lattice cut, rather than an enlarged face-box surrogate. -/
theorem box_rectangle_tube_cut_mem (n : ℕ) (r : ℝ) (u v : LatticeVertex) (k : ℤ)
    (e : (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet) :
    e ∈ configurationIso (boxTubeRectangleIso n) (radiusTubeCutEdges n r u v k) ↔
      Sym2.map Subtype.val e.val ∈ radiusTubeCut n r u v k := by
  classical
  change e ∈ (radiusTubeCutEdges n r u v k).map
    (configurationIsoEdgeEquiv (boxTubeRectangleIso n)).toEmbedding ↔ _
  rw [Finset.mem_map_equiv]
  change ((configurationIsoEdgeEquiv (boxTubeRectangleIso n)).symm e ∈
    radiusTubeCutEdges n r u v k) ↔ _
  simp only [radiusTubeCutEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  have hc := box_rectangle_edge_coordinates n
    ((configurationIsoEdgeEquiv (boxTubeRectangleIso n)).symm e)
  rw [Equiv.apply_symm_apply] at hc
  rw [hc]

/-- The mapped restricted source event is exactly the original tube-confined
connection, with no added paths along a wired boundary class. -/
theorem box_rectangle_tube_connection_iff_walk (n : ℕ) (r : ℝ) (u v : LatticeVertex)
    (A : Configuration (squareLattice.induce (box n : Set LatticeVertex)))
    (a b : (box n : Set LatticeVertex)) (ha : a.val ∈ radiusTube n r u v) :
    ActualConnected _
      (configurationIso (boxTubeRectangleIso n) A ∩
        configurationIso (boxTubeRectangleIso n) (radiusTubeRevealedEdges n r u v))
      (boxTubeRectangleIso n a) (boxTubeRectangleIso n b) ↔
      ∃ p : (openGraph _ A).Walk a b, ∀ z ∈ p.support, z.val ∈ radiusTube n r u v := by
  have hm : configurationIso (boxTubeRectangleIso n)
      (A ∩ radiusTubeRevealedEdges n r u v) =
      configurationIso (boxTubeRectangleIso n) A ∩
        configurationIso (boxTubeRectangleIso n) (radiusTubeRevealedEdges n r u v) :=
    Finset.map_inter A (radiusTubeRevealedEdges n r u v)
  rw [← hm,actualConnected_configurationIso]
  exact radiusTube_revealed_connection_iff_walk n r u v A a b ha

end
end PottsContinuity.Thm3.Prop4
