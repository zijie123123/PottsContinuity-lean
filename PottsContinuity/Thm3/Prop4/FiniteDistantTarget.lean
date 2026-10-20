module

public import PottsContinuity.Thm3.Prop4.FiniteArmComparison
public import PottsContinuity.Thm3.Prop4.SquareEscape
public import PottsContinuity.PD.Duality.Rectangle

/-!
# Finite target sets beyond the requested arm radius

A path to a distant target first hits the exact frozen box boundary.
No union over the possible target vertices is needed.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The complete finite target event is bounded by one infinite arm whenever
every embedded target has square displacement at least the requested radius. -/
theorem finite_free_distant_target_le_infinite_arm {V : Type*} [Finite V]
    (G : SimpleGraph V) (θ : Parameters)
    (f : V ↪ (ℤ × ℤ)) (hG : G.map f ≤ squareLattice) (u : V) (T : Set V) (r : ℕ)
    (hu : f u = (0,0))
    (hT : ∀ z ∈ T, (r : ℤ) ≤ max |(f z).1| |(f z).2|)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    (measure G θ (BoundaryCondition.free ∅) (targetConnectionEvent u T)).toReal ≤
      RSW.oneArmProbability μ r := by
  let : IsProbabilityMeasure μ := hμ.1
  have hθ : Infinite.pdParameters θ.toP θ.toQ (edgeParameter_pos θ)
      (edgeParameter_lt_one θ) θ.property = θ := by cases θ; rfl
  have hcmp := Infinite.finite_graph_free_le_infinite_local θ.toP θ.toQ
    (edgeParameter_pos θ) (edgeParameter_lt_one θ) θ.property G f hG
    (targetConnectionEvent u T) (targetConnectionEvent_upper u T) μ hμ
  rw [hθ] at hcmp
  apply hcmp.trans
  change μ.real (Infinite.latticeGraphEvent G f hG (targetConnectionEvent u T)) ≤
    μ.real (RSW.infiniteArmEvent r)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨z,hz,hconn⟩ := hω
  have hmap := SimpleGraph.Reachable.map (finiteRestrictionOpenHom G f hG ω) hconn
  change (PottsContinuity.rcInfiniteOpenGraph ω).Reachable (f u) (f z) at hmap
  rw [hu] at hmap
  obtain ⟨d,hd,hconn'⟩ := lattice_reachable_hits_square_boundary _
    (infiniteOpenGraph_le_squareLattice ω) (0,0) (f z) r (by
      simpa only [sub_zero] using hT z hz) hmap
  have hd0 : d+(0,0) = d := by ext <;> simp
  rw [hd0] at hconn'
  exact ⟨d,hd,hconn'⟩

/-- An entire vertical column at horizontal distance at least r gives one
infinite arm bound, even when targets lie above or below that box boundary. -/
theorem rectangle_free_column_target_le_infinite_arm (θ : Parameters)
    (a : LatticeVertex) (w h : ℕ) (u : RectangleVertex a w h) (k : ℤ) (r : ℕ)
    (hr : (r : ℤ) ≤ |k-u.val.1|)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    (measure (rectangleGraph a w h) θ (BoundaryCondition.free ∅)
      (targetConnectionEvent u {z | z.val.1 = k})).toReal ≤ RSW.oneArmProbability μ r := by
  let f : RectangleVertex a w h ↪ (ℤ × ℤ) :=
    ⟨fun z => z.val-u.val,fun _ _ hxy => Subtype.ext (sub_left_inj.mp hxy)⟩
  have hG : (rectangleGraph a w h).map f ≤ squareLattice := by
    intro x y hxy
    obtain ⟨z,t,hadj,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ x y).mp hxy
    change |z.val.1-t.val.1|+|z.val.2-t.val.2|=1 at hadj
    change |(z.val.1-u.val.1)-(t.val.1-u.val.1)|+
      |(z.val.2-u.val.2)-(t.val.2-u.val.2)|=1
    simpa only [sub_sub_sub_cancel_right] using hadj
  apply finite_free_distant_target_le_infinite_arm _ θ f hG u _ r (by
    change u.val-u.val = (0,0)
    exact sub_self u.val) _ μ hμ
  intro z hz
  change (r : ℤ) ≤ max |z.val.1-u.val.1| |z.val.2-u.val.2|
  change z.val.1 = k at hz
  rw [hz]
  exact hr.trans (le_max_left _ _)

end
end PottsContinuity.Thm3.Prop4
