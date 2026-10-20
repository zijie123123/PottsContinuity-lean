module

public import PottsContinuity.PlanarMixed.CanonicalCutCarrier

/-! Canonical one-sided reveals depend only on their own cut and reference
side. Their union is the exact remaining-edge complement for ordered cuts.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK
noncomputable section
local instance cutExteriorEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The complete closed exterior accessible from the designated side,
including the cut itself. -/
def closedCutExterior {V : Type*} (G : SimpleGraph V) (cut side : Set V) : Set V :=
  cutReachRegion G cut side ∪ cut

section
variable {V : Type*} {G : SimpleGraph V} {L R A C : Set V}
variable (h : OrderedCutPair G L R A C)

/-- The left label class is exactly the closed left cut exterior. -/
theorem orderedCutRank_le_one_iff_exterior (v : V) :
    orderedCutRank G L R A C h v ≤ 1 ↔ v ∈ closedCutExterior G A L := by
  classical
  unfold orderedCutRank closedCutExterior
  split_ifs <;> simp_all

/-- The right label class is exactly the closed right cut exterior. -/
theorem orderedCutRank_three_le_iff_exterior (v : V) :
    3 ≤ orderedCutRank G L R A C h v ↔ v ∈ closedCutExterior G C R := by
  classical
  by_cases hvL : v ∈ cutReachRegion G A L
  · have hnC : v ∉ C := h.leftRegion_avoids_second hvL
    have hnR : v ∉ cutReachRegion G C R := fun hvR =>
      Set.disjoint_left.mp h.regions_disjoint hvL hvR
    simp [orderedCutRank, closedCutExterior, hvL, hnC, hnR]
  by_cases hvA : v ∈ A
  · have hnC : v ∉ C := fun hvC => Set.disjoint_left.mp h.disjoint hvA hvC
    have hnR : v ∉ cutReachRegion G C R := fun hvR => h.rightRegion_avoids_first hvR hvA
    simp [orderedCutRank, closedCutExterior, hvL, hvA, hnC, hnR]
  unfold orderedCutRank closedCutExterior
  simp only [ite_eq_right hvL, ite_eq_right hvA, Set.mem_union]
  split_ifs <;> simp_all

variable [Finite V]

end
end
end PottsContinuity.PlanarMixed
