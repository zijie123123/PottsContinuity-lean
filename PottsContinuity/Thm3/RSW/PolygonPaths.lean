module

public import PottsContinuity.Thm3.RSW.FinitePathChain
public import PottsContinuity.Thm3.RSW.AnnulusCircuit

/-! # Sampled polygon paths retain their actual vertex confinement -/

@[expose] public section

namespace PottsContinuity.RSW

/-- Following successive cyclic indices connects any two vertices, with no
chosen representative path or extra graph edges. -/
theorem cyclic_index_reachable {X : Type*} (H : SimpleGraph X) (m : ℕ)
    (u : ZMod (m+3) → X) (hcycle : ∀ i, H.Adj (u i) (u (i+1)))
    (i j : ZMod (m+3)) : H.Reachable (u i) (u j) := by
  let : NeZero (m+3) := ⟨by omega⟩
  have hnat : ∀ k : ℕ, H.Reachable (u i) (u (i+(k:ZMod (m+3)))) := by
    intro k
    induction k with
    | zero => simpa only [Nat.cast_zero,add_zero] using (SimpleGraph.Reachable.refl (u i))
    | succ k ih =>
      have hh := ih.trans (hcycle (i+(k:ZMod (m+3)))).reachable
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hh
  have heq : i+(((j-i).val:ℕ):ZMod (m+3)) = j := by
    rw [ZMod.natCast_zmod_val]
    ring
  simpa only [heq] using hnat (j-i).val

/-- Between any two vertices of a sampled open polygon there is an actual
open path confined to any prescribed finite set containing its vertices. -/
theorem open_polygon_finitePathEvent
    (V S : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    {m : ℕ} (P : FKC.LatticePolygon m)
    (hopen : ∀ i : ZMod (m+3), ∃ hi : P.vertex i ∈ V, ∃ hj : P.vertex (i+1) ∈ V,
      (rcOpenGraph V ω).Adj ⟨P.vertex i,hi⟩ ⟨P.vertex (i+1),hj⟩)
    (hS : ∀ i, P.vertex i ∈ S) (i j : ZMod (m+3)) :
    ω ∈ finitePathEvent V S (P.vertex i) (P.vertex j) := by
  have hmem : ∀ i, P.vertex i ∈ V := by
    intro i
    obtain ⟨hi,_,_⟩ := hopen i
    exact hi
  let B : Set (V : Set (ℤ × ℤ)) := {v | v.val ∈ S}
  let H := (rcOpenGraph V ω).induce B
  let u : ZMod (m+3) → B := fun i => ⟨⟨P.vertex i,hmem i⟩,hS i⟩
  have hcycle : ∀ i, H.Adj (u i) (u (i+1)) := by
    intro i
    obtain ⟨hi,hj,hadj⟩ := hopen i
    exact hadj
  obtain ⟨p⟩ := cyclic_index_reachable H m u hcycle i j
  let hom : H →g rcOpenGraph V ω := { toFun := Subtype.val, map_rel' := fun h => h }
  have hs : ∀ z ∈ (p.map hom).support, z.val ∈ S := by
    intro z hz
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
    obtain ⟨b,_,rfl⟩ := hz
    exact b.property
  exact ⟨hmem i,hmem j,p.map hom,hs⟩

end PottsContinuity.RSW
