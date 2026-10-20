module

public import PottsContinuity.BD12.BoxInnerPartition
public import PottsContinuity.BD12.InducedOpenRestriction
public import PottsContinuity.BD12.WalkRadiusPrefix
public import PottsContinuity.BD12.RadiusOneArmComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! First-radius-hit equality on actual nested lattice boxes. A connection in
an arbitrary outer sampled configuration can be witnessed in the inner box. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical

/-- The literal outer one-arm event agrees with its inner-edge restriction,
for every outer configuration, including either radius-zero case. -/
theorem box_radius_shell_connection_iff_restriction
    (c : LatticeVertex) (n N : ℕ) (hnN : n ≤ N)
    (A : PD.FK.Configuration (finiteLatticeGraph (latticeBox c N))) :
    (∃ b : (latticeBox c N : Set LatticeVertex), boxGlobalRadius c N b = n ∧
      FKC.FiniteFK.ActualConnected (finiteLatticeGraph (latticeBox c N)) A (radiusBoxCenter c N) b) ↔
    (∃ b : (latticeBox c n : Set LatticeVertex), boxGlobalRadius c n b = n ∧
      FKC.FiniteFK.ActualConnected (finiteLatticeGraph (latticeBox c n))
        (radiusBoxConfigurationRestriction c n N hnN A) (radiusBoxCenter c n) b) := by
  let G := finiteLatticeGraph (latticeBox c n)
  let H := finiteLatticeGraph (latticeBox c N)
  let f := radiusBoxInclusion c n N hnN
  let hGH := radiusBoxInclusion_map_le c n N hnN
  constructor
  · rintro ⟨b, hb, hconn⟩
    obtain ⟨z, hz, hzconn⟩ := reachable_radius_inside_induced_ball (boxGlobalRadius c N)
      (fun h => boxGlobalRadius_step c N ((FKC.FiniteFK.openGraph_le H A) h)) hconn n
      (by simp only [boxGlobalRadius_center]; omega) hb.ge
    let hom : (FKC.FiniteFK.openGraph H A).induce {v | boxGlobalRadius c N v ≤ n} →g
        FKC.FiniteFK.openGraph G (radiusBoxConfigurationRestriction c n N hnN A) := {
      toFun := fun v => ⟨v.val.val, (latticeRadius_le_iff_mem_box c v.val.val n).mp v.property⟩
      map_rel' := by
        intro x y hxy
        have hinner : G.Adj
            ⟨x.val.val, (latticeRadius_le_iff_mem_box c x.val.val n).mp x.property⟩
            ⟨y.val.val, (latticeRadius_le_iff_mem_box c y.val.val n).mp y.property⟩ :=
          (FKC.FiniteFK.openGraph_le H A) hxy
        exact (embeddedOpenRestriction_adj G H f hGH A _ _ hinner).mpr hxy }
    exact ⟨hom z, hz, hzconn.map hom⟩
  · rintro ⟨b, hb, hconn⟩
    exact ⟨f b, hb, embeddedOpenRestriction_connected_map G H f hGH A hconn⟩

/-- Equality of the actual outer and restricted inner one-arm indicators. -/
theorem box_radiusOneArmIndicator_eq_restriction
    (c : LatticeVertex) (n N : ℕ) (hnN : n ≤ N)
    (A : PD.FK.Configuration (finiteLatticeGraph (latticeBox c N))) :
    radiusOneArmIndicator (finiteLatticeGraph (latticeBox c N)) (boxGlobalRadius c N)
        (radiusBoxCenter c N) n A =
      radiusOneArmIndicator (finiteLatticeGraph (latticeBox c n)) (boxGlobalRadius c n)
        (radiusBoxCenter c n) n (radiusBoxConfigurationRestriction c n N hnN A) := by
  have h := box_radius_shell_connection_iff_restriction c n N hnN A
  by_cases hO : ∃ b : (latticeBox c N : Set LatticeVertex), boxGlobalRadius c N b = n ∧
      FKC.FiniteFK.ActualConnected (finiteLatticeGraph (latticeBox c N)) A (radiusBoxCenter c N) b
  · simp only [radiusOneArmIndicator, finiteConnectionToSetIndicator,
      mem_finiteRadiusShell, ite_eq_left hO]
    exact (ite_eq_left (h.mp hO)).symm
  · simp only [radiusOneArmIndicator, finiteConnectionToSetIndicator,
      mem_finiteRadiusShell, ite_eq_right hO]
    exact (ite_eq_right (fun hi => hO (h.mpr hi))).symm

end
end PottsContinuity.BD12
