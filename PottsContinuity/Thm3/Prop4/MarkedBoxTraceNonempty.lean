module

public import PottsContinuity.Thm3.Prop4.MarkedFaceFrontierConnectivity
public import PottsContinuity.Thm3.Prop4.MarkedJointRawPaths

/-! # Genuine source connections give both existing concrete marked traces -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section

/-- The original lower box trace is nonempty on EVERY genuine source
connection, with its existing definition preserved exactly. -/
theorem markedLowerBoxTrace_nonempty_of_marked_connection
    (n : ℕ) (hn : 1 ≤ n) (u v : (box n : Set LatticeVertex))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (A : Configuration (finiteLatticeGraph (box n)))
    (hA : ActualConnected (finiteLatticeGraph (box n)) A u v) :
    (markedLowerBoxTrace n u v A).Nonempty := by
  classical
  apply Finset.map_nonempty.mpr
  apply (recordedConnectingFrontierTrace_nonempty_iff _ _ _ _ _ _ _ _).mpr
  have hconn := (actualConnected_configurationIso (boxTubeRectangleIso n) A u v).mpr hA
  have hright : (boxTubeRectangleIso n v).val.1 = -(n : ℤ)+(2*n : ℕ) := by
    rw [boxTubeRectangleIso_val,hv]
    push_cast
    omega
  exact markedLowerFrontier_connects_of_marked_connection (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    (by omega) (by omega) (boxTubeRectangleIso n u) (boxTubeRectangleIso n v)
    (by simpa only [boxTubeRectangleIso_val] using hu) hright
    (configurationIso (boxTubeRectangleIso n) A) hconn

/-- The original upper box trace is nonempty on every genuine source
connection, by the exact half-turn definition and the proved lower fit. -/
theorem markedUpperBoxTrace_nonempty_of_marked_connection
    (n : ℕ) (hn : 1 ≤ n) (u v : (box n : Set LatticeVertex))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (A : Configuration (finiteLatticeGraph (box n)))
    (hA : ActualConnected (finiteLatticeGraph (box n)) A u v) :
    (markedUpperBoxTrace n u v A).Nonempty := by
  classical
  apply Finset.map_nonempty.mpr
  apply markedLowerBoxTrace_nonempty_of_marked_connection n hn
    (boxHalfTurnIso n v) (boxHalfTurnIso n u)
  · change -v.val.1 = -(n : ℤ)
    omega
  · change -u.val.1 = (n : ℤ)
    omega
  · exact (actualConnected_configurationIso (boxHalfTurnIso n) A v u).mpr hA.symm

/-- Both WHOLE existing concrete marked traces are actual raw recorded
u-v walks on every genuine source connection. The old nonempty-trace
premises are discharged, without a completed record. -/
theorem markedJointBoxRawReveal_recorded_paths_of_marked_connection
    (n : ℕ) (hn : 1 ≤ n) (u v : (box n : Set LatticeVertex))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (A : Configuration (finiteLatticeGraph (box n)))
    (hA : ActualConnected (finiteLatticeGraph (box n)) A u v) :
    ∃ pU pL : (openGraph (finiteLatticeGraph (box n))
      (Exploration.revealRecordConfiguration (markedJointBoxRawReveal n u v) A).val).Walk u v,
      pU.support.toFinset = markedUpperBoxTrace n u v A ∧
        pL.support.toFinset = markedLowerBoxTrace n u v A :=
  markedJointBoxRawReveal_recorded_paths n u v A
    (markedLowerBoxTrace_nonempty_of_marked_connection n hn u v hu hv A hA)
    (markedUpperBoxTrace_nonempty_of_marked_connection n hn u v hu hv A hA)

end
end PottsContinuity.Thm3.Prop4
