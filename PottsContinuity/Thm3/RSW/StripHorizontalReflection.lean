module

public import PottsContinuity.Thm3.RSW.StripBandArm

@[expose] public section

namespace PottsContinuity.RSW
noncomputable section

/-- Integer horizontal reflection, preserving every vertex in the strip. -/
def stripHorizontalReflectionIso (n : ℕ) (c : ℤ) : stripGraph n ≃g stripGraph n where
  toEquiv := {
    toFun := fun z => ⟨(c-z.val.1,z.val.2),z.property⟩
    invFun := fun z => ⟨(c-z.val.1,z.val.2),z.property⟩
    left_inv := by intro z; apply Subtype.ext; apply Prod.ext <;> dsimp; omega
    right_inv := by intro z; apply Subtype.ext; apply Prod.ext <;> dsimp; omega }
  map_rel_iff' := by
    intro u v
    change |(c-u.val.1)-(c-v.val.1)|+|u.val.2-v.val.2|=1 ↔
      |u.val.1-v.val.1|+|u.val.2-v.val.2|=1
    rw [sub_sub_sub_cancel_left,abs_sub_comm v.val.1 u.val.1]

/-- Relabel the actual strip edge states by horizontal reflection. -/
def stripHorizontalReflectionConfiguration (n : ℕ) (c : ℤ) :
    StripConfiguration n ≃ₜ StripConfiguration n :=
  Homeomorph.piCongrLeft (Y := fun _ : (stripGraph n).edgeSet => Bool)
    (SimpleGraph.Iso.mapEdgeSet (stripHorizontalReflectionIso n c))

/-- Each reflected bond retains exactly its original sampled state. -/
theorem stripHorizontalReflectionConfiguration_edge (n : ℕ) (c : ℤ)
    (ω : StripConfiguration n) (e : (stripGraph n).edgeSet) :
    stripHorizontalReflectionConfiguration n c ω
      ((stripHorizontalReflectionIso n c).mapEdgeSet e) = ω e :=
  Homeomorph.piCongrLeft_apply_apply (Y := fun _ : (stripGraph n).edgeSet => Bool)
    (SimpleGraph.Iso.mapEdgeSet (stripHorizontalReflectionIso n c)) ω e

/-- Reflecting an actual bond twice gives the original bond. -/
theorem stripHorizontalReflection_edge_involutive (n : ℕ) (c : ℤ) :
    Function.Involutive (stripHorizontalReflectionIso n c).mapEdgeSet := by
  intro e
  apply Subtype.ext
  change Sym2.map (stripHorizontalReflectionIso n c)
    (Sym2.map (stripHorizontalReflectionIso n c) e.val) = e.val
  rw [Sym2.map_map]
  have hfun : (fun z : stripVertices n =>
      stripHorizontalReflectionIso n c (stripHorizontalReflectionIso n c z)) = id := by
    funext z
    apply Subtype.ext
    apply Prod.ext <;> dsimp [stripHorizontalReflectionIso]; omega
  change Sym2.map (fun z => stripHorizontalReflectionIso n c (stripHorizontalReflectionIso n c z)) e.val = e.val
  rw [hfun]
  exact congrFun Sym2.map_id e.val

/-- Horizontal state reflection is an involution on its whole carrier. -/
theorem stripHorizontalReflectionConfiguration_involutive (n : ℕ) (c : ℤ) :
    Function.Involutive (stripHorizontalReflectionConfiguration n c) := by
  intro ω
  funext e
  calc
    _ = stripHorizontalReflectionConfiguration n c
        (stripHorizontalReflectionConfiguration n c ω)
        ((stripHorizontalReflectionIso n c).mapEdgeSet
          ((stripHorizontalReflectionIso n c).mapEdgeSet e)) := by
      rw [stripHorizontalReflection_edge_involutive n c e]
    _ = stripHorizontalReflectionConfiguration n c ω
        ((stripHorizontalReflectionIso n c).mapEdgeSet e) :=
      stripHorizontalReflectionConfiguration_edge n c _ _
    _ = ω e := stripHorizontalReflectionConfiguration_edge n c ω e

/-- Reflection maps the actual original open walk into the reflected sample. -/
def stripHorizontalReflectionOpenHom (n : ℕ) (c : ℤ) (ω : StripConfiguration n) :
    stripOpenGraph n ω →g stripOpenGraph n (stripHorizontalReflectionConfiguration n c ω) where
  toFun := stripHorizontalReflectionIso n c
  map_rel' := by
    intro u v huv
    have hb := stripOpenGraph_le n ω huv
    have hs : (stripGraph n).Adj
        (stripHorizontalReflectionIso n c u) (stripHorizontalReflectionIso n c v) :=
      (stripHorizontalReflectionIso n c).map_rel_iff.mpr hb
    have ho := (SimpleGraph.fromEdgeSet_adj _).mp huv
    obtain ⟨hbase,hstate⟩ := ho.1
    have heq : (stripHorizontalReflectionIso n c).mapEdgeSet ⟨s(u,v),hbase⟩ =
        ⟨s(stripHorizontalReflectionIso n c u,stripHorizontalReflectionIso n c v),
          (stripGraph n).mem_edgeSet.mpr hs⟩ := by apply Subtype.ext; rfl
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨⟨(stripGraph n).mem_edgeSet.mpr hs,?_⟩,hs.ne⟩
    rw [← heq,stripHorizontalReflectionConfiguration_edge]
    exact hstate

end
end PottsContinuity.RSW
