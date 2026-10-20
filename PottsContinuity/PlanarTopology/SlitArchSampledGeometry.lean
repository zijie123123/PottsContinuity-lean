module

public import PottsContinuity.Thm4Plane.ScreenArchCrossedCut
public import PottsContinuity.PlanarTopology.BottomArchSeparation

@[expose] public section

namespace PottsContinuity.PlanarTopology
noncomputable section
open FKC FKC.FiniteFK FKC.Medial Thm4Plane

/-- Identity on vertex coordinates from the actual slit-screen dual graph to
the square graph used by the signed-index toolkit. -/
def slitScreenDualToIndexLattice (n : ℕ) (A : Configuration (slitBoxGraph n))
    (F : Finset LatticeVertex) :
    generalScreenActualClosedDualGraph n A F →g PD.squareLattice where
  toFun := id
  map_rel' := by
    rintro u v ⟨d,e,_,_,hdir,_,_⟩
    have hd : PD.squareLattice.Adj d.source d.target :=
      (PD.FK.squareLattice_adj_iff _ _).mpr
        ((FKC.squareLattice_adj_iff _ _).mp d.adjacent)
    rcases hdir with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hd
    · exact hd.symm

/-- The two graph presentations retain exactly the same dual edge labels. -/
theorem slitScreenDualToIndexLattice_walk_edges (n : ℕ)
    (A : Configuration (slitBoxGraph n)) (F : Finset LatticeVertex)
    {s t : LatticeVertex} (p : (generalScreenActualClosedDualGraph n A F).Walk s t) :
    (p.map (slitScreenDualToIndexLattice n A F)).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [SimpleGraph.Walk.map_cons,SimpleGraph.Walk.edges_cons,ih]; rfl

/-- Support is likewise unchanged by the coordinate identity. -/
theorem slitScreenDualToIndexLattice_walk_support (n : ℕ)
    (A : Configuration (slitBoxGraph n)) (F : Finset LatticeVertex)
    {s t : LatticeVertex} (p : (generalScreenActualClosedDualGraph n A F).Walk s t) :
    (p.map (slitScreenDualToIndexLattice n A F)).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [SimpleGraph.Walk.map_cons,SimpleGraph.Walk.support_cons,ih]; rfl

/-- The source carrier excludes the central-left column below the cap and
above the middle connector. -/
theorem slitScreen_arch_column_bounds (m : ℕ) (_hm : 1 ≤ m)
    (z : LatticeVertex) (hz : z ∈ generalScreenArchFaceBases (16*m))
    (hx : z.1 = -1) : -(16*(m : ℤ)) ≤ z.2 ∧ z.2 < 0 := by
  simp only [generalScreenArchFaceBases,Finset.mem_union] at hz
  rcases hz with (hl | hr) | hc
  · have := (generalScreenLeftFaceBases_mem_iff (16*m) z.1 z.2).mp hl
    push_cast at this
    omega
  · have := (generalScreenRightFaceBases_mem_iff (16*m) z.1 z.2).mp hr
    push_cast at this
    omega
  · have := (generalScreenMiddleFaceBases_mem_iff (16*m) z.1 z.2).mp hc
    push_cast at this
    omega

/-- Every vertex of an actual screen walk stays in its prescribed face
carrier when its initial vertex belongs to that carrier. -/
theorem slitScreen_actual_walk_support (n : ℕ) (A : Configuration (slitBoxGraph n))
    (F : Finset LatticeVertex) {s t : LatticeVertex}
    (p : (generalScreenActualClosedDualGraph n A F).Walk s t) (hs : s ∈ F) :
    ∀ z ∈ p.support, z ∈ F := by
  induction p with
  | nil => simpa using hs
  | @cons s r t hadj p ih =>
    obtain ⟨d,e,hcross,hclosed,hdir,hstart,hr⟩ := hadj
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hs
    · exact ih hr z hz

end
end PottsContinuity.PlanarTopology
