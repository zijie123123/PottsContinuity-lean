module

public import PottsContinuity.Thm3.OuterCircuit.SelectorIndex
public import PottsContinuity.Thm3.RSW.PolygonRayLocation

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.FKC
open PottsContinuity.DualityExt
open SimpleGraph

noncomputable section

/-- The radial shell required of a candidate outer circuit. -/
def outerCircuitShellVertex (n : ℕ) (x : PD.FK.LatticeVertex) : Prop :=
  (7*n : ℤ) < max |x.1| |x.2| ∧ max |x.1| |x.2| ≤ (14*n : ℤ)

def outerCircuitCandidateShape {n : ℕ} (i : OuterCircuitPolygonCode n) : Prop :=
  FKC.latticeEmbed ⟨1, zero_lt_one⟩ (0, 0) ∈
      (outerCircuitCodePolygon i).domain ⟨1, zero_lt_one⟩ ∧
    ∀ j : ZMod (i.1.val + 3),
      outerCircuitShellVertex n ((outerCircuitCodePolygon i).vertex j)

theorem outerCircuitCandidateShape_origin_rayIndex_ne_zero {n : ℕ}
    (i : OuterCircuitPolygonCode n)
    (hshape : outerCircuitCandidateShape i) :
    PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark (-1, -1))
      (sourcePolygonWalk (outerCircuitCodePolygon i)) ≠ 0 := by
  have hindex : PD.Duality.rayIndex (0, 0)
      (p5aPolygonCyclePD (outerCircuitCodePolygon i)) ≠ 0 :=
    p5aPolygon_origin_rayIndex_ne_zero (outerCircuitCodePolygon i) hshape.1
  change PD.Duality.rayIndex (0, 0)
    (sourcePolygonWalk (outerCircuitCodePolygon i)) ≠ 0
  rw [sourcePolygonWalk_eq_p5aPolygonCyclePD]
  exact hindex

theorem outerCircuitSourceEdge_endpoint_shell {n m : ℕ}
    (P : FKC.LatticePolygon m)
    (hrad : ∀ j : ZMod (m + 3), outerCircuitShellVertex n (P.vertex j))
    {u v : PD.FK.LatticeVertex}
    (he : s(u, v) ∈ (sourcePolygonWalk P).edges) :
    outerCircuitShellVertex n u ∧ outerCircuitShellVertex n v := by
  obtain ⟨j, hEq⟩ := sourcePolygonWalk_edge_index P he
  rw [Sym2.eq_iff] at hEq
  rcases hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hrad j, hrad (j + 1)⟩
  · exact ⟨hrad (j + 1), hrad j⟩

theorem outerCircuitSourceWalk_support_shell {n m : ℕ}
    (P : FKC.LatticePolygon m)
    (hrad : ∀ j : ZMod (m + 3), outerCircuitShellVertex n (P.vertex j))
    {x : PD.FK.LatticeVertex} (hx : x ∈ (sourcePolygonWalk P).support) :
    outerCircuitShellVertex n x := by
  have hnotnil : ¬ (sourcePolygonWalk P).Nil := by
    intro hnil
    have hlength := (sourcePolygonWalk_isCycle P).three_le_length
    have hzero := (Walk.length_eq_zero_iff).mpr hnil
    omega
  obtain ⟨e, he, hxe⟩ :=
    (Walk.mem_support_iff_exists_mem_edges_of_not_nil hnotnil).mp hx
  induction e using Sym2.inductionOn with
  | _ u v =>
    have hEndpoints := outerCircuitSourceEdge_endpoint_shell P hrad he
    have hmem : x = u ∨ x = v := by
      simpa using hxe
    rcases hmem with rfl | rfl
    · exact hEndpoints.1
    · exact hEndpoints.2

theorem outerCircuitEnvelopeWalk_vertex_shell {n m₁ m₂ : ℕ}
    (P : FKC.LatticePolygon m₁) (Q : FKC.LatticePolygon m₂)
    (hradP : ∀ j : ZMod (m₁ + 3), outerCircuitShellVertex n (P.vertex j))
    (hradQ : ∀ j : ZMod (m₂ + 3), outerCircuitShellVertex n (Q.vertex j))
    {z : PD.FK.LatticeVertex} (c : PD.FK.squareLattice.Walk z z)
    (hc : c.IsCycle)
    (hEdges : ∀ e ∈ c.edges,
      e ∈ (sourcePolygonWalk P).edges ∨ e ∈ (sourcePolygonWalk Q).edges)
    {x : PD.FK.LatticeVertex} (hx : x ∈ c.support) :
    outerCircuitShellVertex n x := by
  have hnotnil : ¬ c.Nil := by
    intro hnil
    have hlength := hc.three_le_length
    have hzero := (Walk.length_eq_zero_iff).mpr hnil
    omega
  obtain ⟨e, he, hxe⟩ :=
    (Walk.mem_support_iff_exists_mem_edges_of_not_nil hnotnil).mp hx
  rcases hEdges e he with hP | hQ
  · have hmem := (sourcePolygonWalk P).mem_support_of_mem_edges hP hxe
    exact outerCircuitSourceWalk_support_shell P hradP hmem
  · have hmem := (sourcePolygonWalk Q).mem_support_of_mem_edges hQ hxe
    exact outerCircuitSourceWalk_support_shell Q hradQ hmem

noncomputable def outerCircuitEnvelopePolygon {z : PD.FK.LatticeVertex}
    (c : PD.FK.squareLattice.Walk z z) (hc : c.IsCycle) :
    FKC.LatticePolygon ((c.map RSW.polygonRayLatticeHom).length - 3) := by
  let hp : (c.map RSW.polygonRayLatticeHom).IsCycle :=
    (c.isCycle_map_iff_of_injective
      (f := RSW.polygonRayLatticeHom) (by intro a b h; exact h)).mpr hc
  exact FKC.latticePolygonOfCycle hp

theorem outerCircuitEnvelopePolygon_vertex_shell {n m₁ m₂ : ℕ}
    (P : FKC.LatticePolygon m₁) (Q : FKC.LatticePolygon m₂)
    (hradP : ∀ j : ZMod (m₁ + 3), outerCircuitShellVertex n (P.vertex j))
    (hradQ : ∀ j : ZMod (m₂ + 3), outerCircuitShellVertex n (Q.vertex j))
    {z : PD.FK.LatticeVertex} (c : PD.FK.squareLattice.Walk z z)
    (hc : c.IsCycle)
    (hEdges : ∀ e ∈ c.edges,
      e ∈ (sourcePolygonWalk P).edges ∨ e ∈ (sourcePolygonWalk Q).edges)
    (j : ZMod ((c.map RSW.polygonRayLatticeHom).length - 3 + 3)) :
    outerCircuitShellVertex n ((outerCircuitEnvelopePolygon c hc).vertex j) := by
  let p := c.map RSW.polygonRayLatticeHom
  have hp : p.IsCycle :=
    (c.isCycle_map_iff_of_injective
      (f := RSW.polygonRayLatticeHom) (by intro a b h; exact h)).mpr hc
  change outerCircuitShellVertex n (p.getVert j.val)
  rw [Walk.getVert_map]
  exact outerCircuitEnvelopeWalk_vertex_shell P Q hradP hradQ c hc hEdges
    (c.getVert_mem_support j.val)

end
end PottsContinuity.OuterCircuit
