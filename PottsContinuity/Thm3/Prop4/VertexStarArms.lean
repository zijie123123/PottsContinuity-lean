module

public import PottsContinuity.Thm3.Prop4.TubeBoundaryArms
public import PottsContinuity.Thm3.Prop4.SplitRadius

/-!
# Primal arms surviving the split at a genuine path vertex

Closing all original edges incident to the selected vertex retains a prefix
from each endpoint to a neighbour of that vertex. The same modified
configuration carries both arms. This does not assert dual separation.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

noncomputable section

open PD.FK

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance starEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Exactly the original edges incident to the specified vertex. -/
def vertexStarEdges (z : V) : Finset G.edgeSet := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  exact Finset.univ.filter (fun e => z ∈ e.val)

/-- Star closing removes an edge exactly when that edge meets the selected vertex. -/
theorem mem_vertexStarEdges (z : V) (e : G.edgeSet) :
    e ∈ vertexStarEdges G z ↔ z ∈ e.val := by
  classical
  simp [vertexStarEdges]

/-- Stop immediately before the first visit to the selected vertex. -/
theorem connected_neighbour_after_star_closing (A : Configuration G) (z a : V)
    (haz : a ≠ z) (hconn : ActualConnected G A a z) :
    ∃ p : V, G.Adj z p ∧ ActualConnected G (A \ vertexStarEdges G z) a p := by
  classical
  obtain ⟨w⟩ := hconn
  induction w with
  | nil => exact (haz rfl).elim
  | @cons a c z hac w ih =>
    obtain ⟨e,he,heval⟩ := (openGraph_adj G A a c).mp hac
    have hG : G.Adj a c := G.mem_edgeSet.mp (by rw [← heval]; exact e.property)
    by_cases hcz : c = z
    · subst c
      exact ⟨a,hG.symm,SimpleGraph.Reachable.refl a⟩
    · obtain ⟨p,hp,hcp⟩ := ih hcz
      have henot : e ∉ vertexStarEdges G z := by
        rw [mem_vertexStarEdges,heval,Sym2.mem_iff]
        exact not_or.mpr ⟨Ne.symm haz,Ne.symm hcz⟩
      have hnew : (openGraph G (A \ vertexStarEdges G z)).Adj a c :=
        (openGraph_adj G _ a c).mpr ⟨e,Finset.mem_sdiff.mpr ⟨he,henot⟩,heval⟩
      exact ⟨p,hp,hnew.reachable.trans hcp⟩

/-- Both endpoint prefixes survive in the very same star-closed configuration. -/
theorem connected_two_neighbours_after_star_closing (A : Configuration G) (z a b : V)
    (haz : a ≠ z) (hbz : b ≠ z)
    (ha : ActualConnected G A a z) (hb : ActualConnected G A b z) :
    ∃ p q : V, G.Adj z p ∧ G.Adj z q ∧
      ActualConnected G (A \ vertexStarEdges G z) a p ∧
      ActualConnected G (A \ vertexStarEdges G z) b q := by
  obtain ⟨p,hp,hap⟩ := connected_neighbour_after_star_closing G A z a haz ha
  obtain ⟨q,hq,hbq⟩ := connected_neighbour_after_star_closing G A z b hbz hb
  exact ⟨p,q,hp,hq,hap,hbq⟩

/-- A lattice vertex star contains at most the four genuine incident edges. -/
theorem lattice_vertexStar_card_le_four (n : ℕ) (z : (box n : Set (ℤ × ℤ))) :
    (vertexStarEdges (squareLattice.induce (box n : Set (ℤ × ℤ))) z).card ≤ 4 := by
  classical
  let G := squareLattice.induce (box n : Set (ℤ × ℤ))
  let f : G.edgeSet → Sym2 (ℤ × ℤ) := Sym2.map Subtype.val ∘ Subtype.val
  have hinj : Function.Injective f := by
    intro e d h
    apply Subtype.ext
    exact Sym2.map.injective Subtype.val_injective h
  let S : Finset (Sym2 (ℤ × ℤ)) :=
    {s(z.val,(z.val.1+1,z.val.2)),s(z.val,(z.val.1-1,z.val.2)),
      s(z.val,(z.val.1,z.val.2+1)),s(z.val,(z.val.1,z.val.2-1))}
  have hsub : (vertexStarEdges G z).image f ⊆ S := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
    have hz := (mem_vertexStarEdges G z e).mp he
    let p := e.val.out.1
    let q := e.val.out.2
    have heq : e.val = s(p,q) := (Quot.out_eq _).symm
    have hG : G.Adj p q := G.mem_edgeSet.mp (heq ▸ e.property)
    rw [heq,Sym2.mem_iff] at hz
    have hcases {v : (box n : Set (ℤ × ℤ))} (hzv : G.Adj z v) :
        v.val = (z.val.1+1,z.val.2) ∨ v.val = (z.val.1-1,z.val.2) ∨
        v.val = (z.val.1,z.val.2+1) ∨ v.val = (z.val.1,z.val.2-1) := by
      change PD.FK.squareLattice.Adj z.val v.val at hzv
      rw [PD.FK.squareLattice_adj_iff] at hzv
      simp only [Prod.ext_iff]
      omega
    rcases hz with hzp | hzq
    · have hf : f e = s(z.val,q.val) := by
        change Sym2.map Subtype.val e.val = _
        rw [heq,Sym2.map_mk,← hzp]
      obtain h | h | h | h := hcases (by rw [hzp]; exact hG)
      all_goals
        rw [hf,h]
        simp only [S,Finset.mem_insert,Finset.mem_singleton]
        tauto
    · have hf : f e = s(z.val,p.val) := by
        change Sym2.map Subtype.val e.val = _
        rw [heq,Sym2.map_mk,← hzq]
        exact Sym2.eq_swap
      obtain h | h | h | h := hcases (by rw [hzq]; exact hG.symm)
      all_goals
        rw [hf,h]
        simp only [S,Finset.mem_insert,Finset.mem_singleton]
        tauto
  calc
    (vertexStarEdges G z).card = ((vertexStarEdges G z).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ S.card := Finset.card_le_card hsub
    _ ≤ 4 := by simp only [S]; exact Finset.card_le_four

end
end PottsContinuity.Thm3.Prop4
