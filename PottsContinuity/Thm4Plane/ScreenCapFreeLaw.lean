module

public import PottsContinuity.Thm4Plane.ScreenFreeComponent
public import PottsContinuity.PD.FK.EmbeddedMarginalLaw
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import PottsContinuity.Thm4.FKCProbabilityBridge
public import PottsContinuity.Infinite.Parameters
public import PottsContinuity.PD.Duality.FiniteDuality

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC.FiniteFK

noncomputable section

local instance screenCapFreeLawOuterEdgeFintype
    (m : ℕ) : Fintype (slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _
local instance screenCapFreeLawOuterEdgeDecidableEq
    (m : ℕ) : DecidableEq (slitBoxGraph (16 * m)).edgeSet := Classical.decEq _
local instance screenCapFreeLawMappedEdgeFintype
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V}
    {f : V ↪ W} : Fintype (G.map f).edgeSet := Fintype.ofFinite _
local instance screenCapFreeLawRemainingFintype
    (m : ℕ) (R : PottsContinuity.PD.FK.Configuration
      (slitBoxGraph (16 * m))) :
    Fintype (PottsContinuity.PD.FK.RemainingConfiguration
      (slitBoxGraph (16 * m)) R) := Fintype.ofFinite _
local instance screenCapFreeLawRemovedFintype
    (m : ℕ) (R : PottsContinuity.PD.FK.Configuration
      (slitBoxGraph (16 * m))) :
    Fintype (PottsContinuity.PD.FK.RemovedConfiguration
      (slitBoxGraph (16 * m)) R) := Fintype.ofFinite _

/-- The plane comparison's source parameter is the same PD record as the
explicit self-dual finite parameter. -/
theorem pdParameters_eq_criticalParameters_of_selfDualValue
    (q : Set.Ici (1 : ℝ)) (p : Set.Icc (0 : ℝ) 1)
    (hp : (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    PottsContinuity.Infinite.pdParameters p
      ⟨q, PottsContinuity.PD.FK.clusterWeight_pos
        (PottsContinuity.PD.FK.criticalParameters q)⟩
      hp0 hp1 q.property =
      PottsContinuity.PD.FK.criticalParameters q := by
  unfold PottsContinuity.Infinite.pdParameters
    PottsContinuity.PD.FK.criticalParameters
  apply congrArg (fun r : Set.Ioo (0 : ℝ) 1 =>
    ({ val := (q : ℝ), property := q.property, edgeProbability := r } :
      PottsContinuity.PD.FK.Parameters))
  apply Subtype.ext
  change (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ))
  exact hp

end
end PottsContinuity.Thm4Plane
