module

public import PottsContinuity.PlanarTopology.HalfPlaneArchAvoidance
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.RCInfinite PD.Duality BD12
noncomputable section

/-- An actual boundary-attached complementary dual arch screens every primal
boundary root between its endpoint heights from infinity in the right half-plane.
Repeated vertices of the supplied arch are allowed. -/
theorem boundary_attached_dual_arch_finite_halfplane_cluster
    (ω : LatticeConfiguration) (l u y : ℤ) (hgap : l+1 < u)
    (q : PD.squareLattice.Walk (-1,l) (-1,u))
    (hq : kstPathOpen (wholePlaneDualConfigurationHomeomorph ω) q)
    (hgeom : ∀ z ∈ q.support, 0 ≤ z.1 ∨ z = (-1,l) ∨ z = (-1,u))
    (hly : l < y) (hyu : y ≤ u) :
    {z : {z : LatticeVertex // 0 ≤ z.1} |
      ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable
        ⟨(0,y),by norm_num⟩ z}.Finite := by
  obtain ⟨r,hr⟩ := vertical_walk_between (-1) u l
  let C := q.append r
  have hrcol : ∀ z ∈ r.support, z.1 = -1 := fun z hz => (hr z hz).1
  have hrzero : rayIndex (0,y) r = 0 :=
    rayIndex_zero_of_right (0,y) r (fun z hz => by have := hrcol z hz; dsimp; omega)
  have hidx : rayIndex (0,y) C ≠ 0 := by
    change rayIndex (0,y) (q.append r) ≠ 0
    rw [rayIndex_append,boundary_attached_arch_rayIndex l u y hgap q hgeom hly hyu,hrzero]
    norm_num
  have hf := finite_avoidance_component_of_rayIndex_ne_zero C (0,y) hidx
  have hpre : (Subtype.val ⁻¹' {w | (circuitAvoidanceGraph C).Reachable (0,y) w} :
      Set {z : LatticeVertex // 0 ≤ z.1}).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hf
  apply hpre.subset
  intro z hz
  let e : (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1} →g
      circuitAvoidanceGraph C :=
    { toFun := Subtype.val
      map_rel' := fun {v w} h => halfplane_open_edge_avoids_arch_closure ω q hq r hrcol
        v.property w.property h }
  exact hz.map e

/-- The unit boundary segment's two primal vertices are both screened by the
same sampled dual arch, with its genuine crossing end bonds retained. -/
theorem boundary_attached_dual_arch_screens_unit_segment
    (ω : LatticeConfiguration) (l u : ℤ) (hl : l ≤ -1) (hu : 1 ≤ u)
    (q : PD.squareLattice.Walk (-1,l) (-1,u))
    (hq : kstPathOpen (wholePlaneDualConfigurationHomeomorph ω) q)
    (hgeom : ∀ z ∈ q.support, 0 ≤ z.1 ∨ z = (-1,l) ∨ z = (-1,u)) :
    ∀ y : ℤ, (y = 0 ∨ y = 1) →
      {z : {z : LatticeVertex // 0 ≤ z.1} |
        ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable
          ⟨(0,y),by norm_num⟩ z}.Finite := by
  intro y hy
  exact boundary_attached_dual_arch_finite_halfplane_cluster ω l u y (by omega)
    q hq hgeom (by omega) (by omega)

end
end PottsContinuity.PlanarTopology
