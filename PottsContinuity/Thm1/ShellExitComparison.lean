module

public import PottsContinuity.Thm1.ShellExitDependence
public import PottsContinuity.Infinite.LocalComparisons
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

theorem pottsESLatticeExitEvent_upper (V : Finset (ℤ × ℤ)) :
    IsUpperSet (pottsESLatticeExitEvent V) := by
  intro ω η hωη hω
  change ∃ y, y ∉ V ∧ (PD.rcInfiniteOpenGraph ω).Reachable (0, 0) y at hω
  obtain ⟨y, hy, hreach⟩ := hω
  have hGraph : PD.rcInfiniteOpenGraph ω ≤ PD.rcInfiniteOpenGraph η := by
    intro x z hxz
    obtain ⟨hedge, hopen⟩ := (rcInfiniteOpenGraph_adj ω x z).mp hxz
    have hstate : η ⟨s(x, z), hedge⟩ = true := by
      exact (Bool.le_iff_imp.mp (hωη ⟨s(x, z), hedge⟩) hopen)
    exact (rcInfiniteOpenGraph_adj η x z).mpr ⟨hedge, hstate⟩
  exact ⟨y, hy, hreach.mono hGraph⟩

/-- The infinite wired probability of a finite-set exit event is bounded by
its wired finite-box probability once the finitely many relevant edges fit. -/
theorem pottsESLatticeExitProbability_le_wiredBox
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 μ)
    (V : Finset (ℤ × ℤ)) (h0 : (0, 0) ∈ V) (m : ℕ)
    (hF : (pottsESLatticeEdgeSet V :
        Set PottsContinuity.PD.FK.squareLattice.edgeSet) ⊆
      boxEdges (0, 0) m) :
    μ.real (pottsESLatticeExitEvent V) ≤
      (boxMeasure θ 1 (0, 0) m : Measure LatticeConfiguration).real
        (pottsESLatticeExitEvent V) := by
  exact PottsContinuity.Infinite.limit_le_wired_box_local θ μ hμ m
    (pottsESLatticeExitEvent_isCylinder V h0)
    (PottsContinuity.PD.RCInfinite.DependsOn.mono
      (pottsESLatticeExitEvent_dependsOn V h0) hF)
    (pottsESLatticeExitEvent_upper V)

end

end PottsContinuity.Thm1
