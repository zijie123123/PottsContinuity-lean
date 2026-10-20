module

public import PottsContinuity.BD12.SeparatingSeedConnection
public import PottsContinuity.BD12.WalkRadiusLevel
public import PottsContinuity.BD12.DRTMeanOrder
public import Mathlib.Data.Nat.Dist

/-! Graph-metric comparison between a connection to a global shell and a
centred one-arm event. No planarity or stochastic domination is required. -/

@[expose] public section

namespace PottsContinuity.BD12
open FKC.FiniteFK
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance oneArmEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance oneArmEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Actual connection from o to the exact radius-n level of a supplied radius
function. For a centred lattice/graph radius this is its ordinary one-arm event. -/
abbrev radiusOneArmIndicator (r : V → ℕ) (o : V) (n : ℕ) :=
  finiteConnectionToSetIndicator G o (finiteRadiusShell r n)

/-- Larger radius levels imply smaller levels along the same actual open walk. -/
theorem radiusOneArmIndicator_antitone (r : V → ℕ) (o : V) (ho : r o = 0)
    (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1) (A : Configuration G) :
    Antitone (fun n => radiusOneArmIndicator G r o n A) := by
  intro m n hmn
  by_cases hn : ∃ b, b ∈ finiteRadiusShell r n ∧ ActualConnected G A o b
  · obtain ⟨b, hb, ⟨p⟩⟩ := hn
    have hrb : r b = n := (mem_finiteRadiusShell r n b).mp hb
    obtain ⟨z, hzp, hrz⟩ := walk_visits_radius_level r
      (fun h => hstep ((openGraph_le G A) h)) p m (by omega) (by omega)
    have hm : ∃ b, b ∈ finiteRadiusShell r m ∧ ActualConnected G A o b :=
      ⟨z, (mem_finiteRadiusShell r m z).mpr hrz, (p.takeUntil z hzp).reachable⟩
    have hn' : ∃ b, b ∈ finiteRadiusShell r n ∧ ActualConnected G A o b := ⟨b, hb, ⟨p⟩⟩
    simp only [radiusOneArmIndicator, finiteConnectionToSetIndicator, ite_eq_left hn', ite_eq_left hm, le_refl]
  · simp only [radiusOneArmIndicator, finiteConnectionToSetIndicator, ite_eq_right hn]
    exact (finiteConnectionToSetIndicator_mem_Icc G o (finiteRadiusShell r m) A).1

/-- The shell endpoint has centred radius at least the difference of its global
radius from the origin's. The actual open path then hits that centred level. -/
theorem seedShell_indicator_le_radiusOneArm (r d : V → ℕ) (u : V) (k : ℕ)
    (hdu : d u = 0) (hstep : ∀ {x y}, G.Adj x y → d y ≤ d x + 1)
    (hdom : ∀ v, Nat.dist (r v) (r u) ≤ d v) (A : Configuration G) :
    (if actualMultiClusterConnected G (finiteRadiusShell r k) A u then (1 : ℝ) else 0) ≤
      radiusOneArmIndicator G d u (Nat.dist k (r u)) A := by
  by_cases hs : actualMultiClusterConnected G (finiteRadiusShell r k) A u
  · obtain ⟨s, hsS, hsu⟩ := hs
    have hrs : r s = k := (mem_finiteRadiusShell r k s).mp hsS
    obtain ⟨p⟩ := hsu.symm
    obtain ⟨z, hzp, hdz⟩ := walk_visits_radius_level d
      (fun h => hstep ((openGraph_le G A) h)) p (Nat.dist k (r u)) (by omega) (by simpa only [hrs] using hdom s)
    have hevent : ∃ b, b ∈ finiteRadiusShell d (Nat.dist k (r u)) ∧ ActualConnected G A u b :=
      ⟨z, (mem_finiteRadiusShell d _ z).mpr hdz, (p.takeUntil z hzp).reachable⟩
    have hs' : actualMultiClusterConnected G (finiteRadiusShell r k) A u := ⟨s, hsS, hsu⟩
    simp only [ite_eq_left hs', radiusOneArmIndicator, finiteConnectionToSetIndicator, ite_eq_left hevent, le_refl]
  · simp only [ite_eq_right hs]
    exact (finiteConnectionToSetIndicator_mem_Icc G u (finiteRadiusShell d _) A).1

/-- Actual FK one-arm probabilities decrease with the radius. -/
theorem drt_radius_one_arm_antitone (q : Set.Ioi (0 : ℝ)) (ξ : PD.FK.BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (r : V → ℕ) (o : V) (ho : r o = 0) (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1) :
    Antitone (fun n => drtMean G q ξ J β (radiusOneArmIndicator G r o n)) := by
  intro m n hmn
  exact drtMean_mono G q ξ J β _ _ (fun A => radiusOneArmIndicator_antitone G r o ho hstep A hmn)

end
end PottsContinuity.BD12
