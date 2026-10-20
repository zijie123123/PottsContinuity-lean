module

public import PottsContinuity.PlanarTopology.HalfPlaneArmLimit
public import PottsContinuity.BD12.RectangleOpenGraphs
public import PottsContinuity.BD12.DualStripOpen
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.RCInfinite BD12
noncomputable section

/-- All actual half-plane vertices in a finite rectangle based at the origin. -/
def halfPlaneRectangleSeeds (w h : ℕ) : Finset {z : LatticeVertex // 0 ≤ z.1} := by
  classical
  exact (latticeRectangle (0,0) w h).subtype (fun z => 0 ≤ z.1)

@[simp] theorem mem_halfPlaneRectangleSeeds (w h : ℕ) (u : {z : LatticeVertex // 0 ≤ z.1}) :
    u ∈ halfPlaneRectangleSeeds w h ↔ u.val ∈ latticeRectangle (0,0) w h := by
  classical
  simp [halfPlaneRectangleSeeds]

/-- Forgetting the finite rectangle preserves every original open edge in
the containing right half-plane. -/
def rectangleToHalfPlaneOpenHom (ω : LatticeConfiguration) (w h : ℕ) :
    (PD.rcInfiniteOpenGraph ω).induce (latticeRectangle (0,0) w h : Set LatticeVertex) →g
      (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1} where
  toFun u := ⟨u.val,by
    have hh := (mem_latticeRectangle (0,0) u.val w h).mp u.property
    simpa using hh.1.1⟩
  map_rel' := fun h => h

/-- A horizontal crossing of width n+1 leaves the radius-n box through an
actual half-plane connection from the fixed finite left side. -/
theorem horizontalRectangle_subset_halfPlaneArm (n K : ℕ) :
    horizontalRectangle (0,0) (n+1) K ⊆ sampledGraphArmEvent
      (fun ω => (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1})
      (halfPlaneRectangleSeeds 0 K) {v | v.val ∈ latticeBox (0,0) n} := by
  classical
  rintro ω ⟨u,v,hu,hv,hconn⟩
  have hux : u.val.1 = 0 := (Finset.mem_filter.mp hu).2
  have hvx : v.val.1 = (n+1 : ℕ) := by simpa using (Finset.mem_filter.mp hv).2
  have hboxu := (mem_latticeRectangle (0,0) u.val (n+1) K).mp u.property
  have hgu := embeddedRestriction_domainGraph (latticeRectangle (0,0) (n+1) K) ω
  change openGraph (rectangleGraph (0,0) (n+1) K)
    (embeddedRestriction _ (frozenEdgeEmbedding (latticeRectangle (0,0) (n+1) K)) ω) = _ at hgu
  change (openGraph _ _).Reachable u v at hconn
  rw [hgu] at hconn
  let f := rectangleToHalfPlaneOpenHom ω (n+1) K
  refine ⟨f u,?_,f v,?_,hconn.map f⟩
  · apply (mem_halfPlaneRectangleSeeds 0 K (f u)).mpr
    rw [mem_latticeRectangle]
    dsimp only [f,rectangleToHalfPlaneOpenHom]
    change (0 ≤ u.val.1 ∧ u.val.1 ≤ 0+(0:ℕ)) ∧ (0 ≤ u.val.2 ∧ u.val.2 ≤ 0+(K:ℤ))
    simp only [zero_add] at hboxu
    omega
  · intro hvbox
    change (f v).val ∈ latticeBox (0,0) n at hvbox
    dsimp only [f,rectangleToHalfPlaneOpenHom] at hvbox
    have hh := (mem_latticeBox (0,0) v.val n).mp hvbox
    simp only [zero_sub,zero_add] at hh
    omega

/-- A vertical crossing of height n+1 similarly leaves the radius-n box
from the fixed finite bottom side, retaining original bonds. -/
theorem verticalRectangle_subset_halfPlaneArm (n W : ℕ) :
    verticalRectangle (0,0) W (n+1) ⊆ sampledGraphArmEvent
      (fun ω => (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1})
      (halfPlaneRectangleSeeds W 0) {v | v.val ∈ latticeBox (0,0) n} := by
  classical
  rintro ω ⟨u,v,hu,hv,hconn⟩
  let f := rectangleToHalfPlaneOpenHom ω W (n+1)
  have hboxu := (mem_latticeRectangle (0,0) u.val W (n+1)).mp u.property
  refine ⟨f u,?_,f v,?_,hconn.map f⟩
  · apply (mem_halfPlaneRectangleSeeds W 0 (f u)).mpr
    rw [mem_latticeRectangle]
    dsimp only [f,rectangleToHalfPlaneOpenHom]
    change (0 ≤ u.val.1 ∧ u.val.1 ≤ 0+(W:ℤ)) ∧ (0 ≤ u.val.2 ∧ u.val.2 ≤ 0+(0:ℕ))
    simp only [zero_add] at hboxu hu
    omega
  · intro hvbox
    change (f v).val ∈ latticeBox (0,0) n at hvbox
    dsimp only [f,rectangleToHalfPlaneOpenHom] at hvbox
    have hh := (mem_latticeBox (0,0) v.val n).mp hvbox
    simp only [zero_sub,zero_add] at hh hv
    omega

end
end PottsContinuity.PlanarTopology
