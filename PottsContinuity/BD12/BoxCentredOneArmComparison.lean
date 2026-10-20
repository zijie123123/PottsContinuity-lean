module

public import PottsContinuity.BD12.BoxRadiusRestriction
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! A restricted centred one-arm event uses genuine original outer edges.
Enlarging its path domain can only increase its indicator. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical

/-- The inner centred event is contained in the full outer centred event,
with the actual centre and radius unchanged. -/
theorem box_centred_one_arm_indicator_le_outer
    (c : LatticeVertex) (n N : ℕ) (hnN : n ≤ N)
    (u : (latticeBox c n : Set LatticeVertex)) (j : ℕ)
    (A : Configuration (finiteLatticeGraph (latticeBox c N))) :
    radiusOneArmIndicator (finiteLatticeGraph (latticeBox c n)) (boxCentredRadius c n u) u j
        (radiusBoxConfigurationRestriction c n N hnN A) ≤
      radiusOneArmIndicator (finiteLatticeGraph (latticeBox c N))
        (fun v => latticeRadius u.val v.val) (radiusBoxInclusion c n N hnN u) j A := by
  let G := finiteLatticeGraph (latticeBox c n)
  let H := finiteLatticeGraph (latticeBox c N)
  let f := radiusBoxInclusion c n N hnN
  let hGH := radiusBoxInclusion_map_le c n N hnN
  let C := radiusBoxConfigurationRestriction c n N hnN A
  change finiteConnectionToSetIndicator G u (finiteRadiusShell (boxCentredRadius c n u) j) C ≤
    finiteConnectionToSetIndicator H (f u)
      (finiteRadiusShell (fun v => latticeRadius u.val v.val) j) A
  by_cases hin : ∃ b, b ∈ finiteRadiusShell (boxCentredRadius c n u) j ∧ FKC.FiniteFK.ActualConnected G C u b
  · obtain ⟨b, hb, hconn⟩ := hin
    have hb' : boxCentredRadius c n u b = j := (mem_finiteRadiusShell _ _ _).mp hb
    have hout : ∃ b, b ∈ finiteRadiusShell (fun v : (latticeBox c N : Set LatticeVertex) =>
        latticeRadius u.val v.val) j ∧ FKC.FiniteFK.ActualConnected H A (f u) b :=
      ⟨f b, (mem_finiteRadiusShell _ _ _).mpr hb',
        embeddedOpenRestriction_connected_map G H f hGH A hconn⟩
    have hin' : ∃ b, b ∈ finiteRadiusShell (boxCentredRadius c n u) j ∧ FKC.FiniteFK.ActualConnected G C u b :=
      ⟨b, hb, hconn⟩
    simp only [finiteConnectionToSetIndicator, ite_eq_left hin', ite_eq_left hout, le_refl]
  · simp only [finiteConnectionToSetIndicator, ite_eq_right hin]
    exact (finiteConnectionToSetIndicator_mem_Icc H (f u)
      (finiteRadiusShell (fun v => latticeRadius u.val v.val) j) A).1

end
end PottsContinuity.BD12
