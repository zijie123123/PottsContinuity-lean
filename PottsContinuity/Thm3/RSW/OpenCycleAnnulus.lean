module

public import PottsContinuity.Thm3.RSW.PolygonRayLocation
public import PottsContinuity.Thm3.RSW.AnnulusCircuit
public import PottsContinuity.Thm3.Easy.P5FrameClosedWalk

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
noncomputable section

/-- A sampled open cycle in the annulus with nonzero index supplies the literal
source annulus event, including genuine bounded Jordan enclosure. -/
theorem annulusCircuitEvent_of_openCycle_rayIndex
    (V : Finset LatticeVertex)
    (ω : (PottsContinuity.squareLattice.induce (V : Set LatticeVertex)).edgeSet → Bool)
    (c : LatticeVertex) (n : ℕ) {z : (V : Set LatticeVertex)}
    (p : (rcOpenGraph V ω).Walk z z) (hp : p.IsCycle)
    (hindex : rayIndex c (p.map (Thm3.Easy.p5ClosedWalkToSquareLattice V ω)) ≠ 0)
    (hradial : ∀ v ∈ p.support,
      (n:ℤ) < max |v.val.1-c.1| |v.val.2-c.2| ∧
      max |v.val.1-c.1| |v.val.2-c.2| ≤ 2*(n:ℤ)) :
    ω ∈ annulusCircuitEvent V c n := by
  let φ := Thm3.Easy.p5ClosedWalkToSquareLattice V ω
  let q := p.map φ
  have hφ : Function.Injective φ := fun _ _ h => Subtype.ext h
  have hq : q.IsCycle := (p.isCycle_map_iff_of_injective hφ).mpr hp
  let r := q.map polygonRayLatticeHom
  have hr : r.IsCycle := (q.isCycle_map_iff_of_injective
    (show Function.Injective polygonRayLatticeHom from fun _ _ h => h)).mpr hq
  let P := FKC.latticePolygonOfCycle hr
  have hcurrent (i : ZMod (r.length-3+3)) : P.vertex i = (p.getVert i.val).val := by
    change (q.map polygonRayLatticeHom).getVert i.val = (p.getVert i.val).val
    rw [SimpleGraph.Walk.getVert_map]
    change (p.map φ).getVert i.val = (p.getVert i.val).val
    rw [SimpleGraph.Walk.getVert_map]
    rfl
  have hnext (i : ZMod (r.length-3+3)) :
      P.vertex (i+1) = (p.getVert (i.val+1)).val := by
    rw [FKC.latticePolygonOfCycle_vertex_succ hr]
    rw [SimpleGraph.Walk.getVert_map]
    change (p.map φ).getVert (i.val+1) = (p.getVert (i.val+1)).val
    rw [SimpleGraph.Walk.getVert_map]
    rfl
  have hoff : c ∉ q.support := by
    intro hc
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hc
    obtain ⟨v,hv,hvc⟩ := hc
    have h := (hradial v hv).1
    change v.val = c at hvc
    rw [hvc] at h
    simp only [sub_self,abs_zero,max_self] at h
    omega
  have hcenter := latticePolygonOfCycle_mem_domain_of_rayIndex_ne_zero q hq c hoff hindex
  refine ⟨r.length-3,P,hcenter,?_,?_⟩
  · intro i
    rw [hcurrent]
    exact hradial _ (p.getVert_mem_support i.val)
  · intro i
    have hi : i.val < p.length := by
      have hi := i.val_lt
      have hlen : r.length = p.length := by simp only [r,q,SimpleGraph.Walk.length_map]
      have h3 := hr.three_le_length
      omega
    have hV (j : ZMod (r.length-3+3)) : P.vertex j ∈ V := by
      rw [hcurrent]
      exact (p.getVert j.val).property
    refine ⟨hV i,hV (i+1),?_⟩
    have hu : (⟨P.vertex i,hV i⟩ : (V : Set LatticeVertex)) = p.getVert i.val :=
      Subtype.ext (hcurrent i)
    have hv : (⟨P.vertex (i+1),hV (i+1)⟩ : (V : Set LatticeVertex)) =
        p.getVert (i.val+1) := Subtype.ext (hnext i)
    rw [hu,hv]
    exact p.adj_getVert_succ hi

end
end PottsContinuity.RSW
