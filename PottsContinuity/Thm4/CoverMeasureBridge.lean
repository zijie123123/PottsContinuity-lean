module

public import PottsContinuity.Thm4.BoundaryLowerFour
public import PottsContinuity.Thm4.FKCGraphBridge
public import PottsContinuity.Thm4.FKCProbabilityBridge
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBoundaryLowerBound

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK
noncomputable section

/-- Actual origin-to-vertex probability, defined on the whole retained carrier.
There is no zero extension to vertices outside this carrier. -/
def coverOriginConnectionProbability (n : ℕ) (q : Set.Ici (1 : ℝ))
    (v : ParafermionicAmbientVertex n) : ℝ :=
  (measure (ParafermionicAmbientGraph n) (selfDualParameters q)
    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
    {A | ActualConnected (ParafermionicAmbientGraph n) A
      (parafermionicCoverBoxOrigin n) v}).toReal

/-- The two definitions select exactly the same full exterior-neighbor boundary. -/
theorem coverExteriorBoundary_image (n : ℕ) :
    (coverExteriorBoundary n).image Subtype.val =
      PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteExteriorNeighborBoundary n := by
  classical
  ext v
  simp only [Finset.mem_image, coverExteriorBoundary, Finset.mem_filter,
    Finset.mem_univ, true_and,
    PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteExteriorNeighborBoundary]
  constructor
  · rintro ⟨u, ⟨w, hw, hout⟩, rfl⟩
    refine ⟨u.property, w, ?_, hout⟩
    rwa [fkc_coverGraph_eq] at hw
  · rintro ⟨hv, w, hw, hout⟩
    refine ⟨⟨v, hv⟩, ⟨w, ?_, hout⟩, rfl⟩
    rwa [fkc_coverGraph_eq]

/-- FKC's connection weight at a retained vertex is the actual PD probability. -/
theorem fkc_coverOriginConnectionWeight_eq (n : ℕ)
    (q : PottsContinuity.FKC.ClusterWeight) (v : ParafermionicAmbientVertex n) :
    PottsContinuity.FKC.FiniteFK.parafermionicCoverBoxOriginConnectionWeight n q v.val =
      coverOriginConnectionProbability n ⟨q, q.2.1⟩ v := by
  erw [PottsContinuity.FKC.FiniteFK.parafermionicCoverBoxOriginConnectionWeight_subtype]
  change (PottsContinuity.FKC.FiniteFK.measure
    (PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph n) q
    (PottsContinuity.FKC.FiniteFK.BoundaryCondition.free
      (∅ : Set (ParafermionicAmbientVertex n)))
    {A | PottsContinuity.FKC.FiniteFK.ActualConnected
      (PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph n) A
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverBoxOrigin n) v}).toReal = _
  rw [fkc_measure_eq, ← fkc_ambientGraph_eq n]
  rfl

theorem fkc_boundary_connection_sum_eq (n : ℕ)
    (q : PottsContinuity.FKC.ClusterWeight) :
    (∑ v ∈ PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteExteriorNeighborBoundary n,
      PottsContinuity.FKC.FiniteFK.parafermionicCoverBoxOriginConnectionWeight n q v) =
      ∑ v ∈ coverExteriorBoundary n, coverOriginConnectionProbability n ⟨q, q.2.1⟩ v := by
  classical
  rw [← coverExteriorBoundary_image n, Finset.sum_image
    (fun _ _ _ _ h => Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro v _
  exact fkc_coverOriginConnectionWeight_eq n q v

end
end PottsContinuity.Thm4
