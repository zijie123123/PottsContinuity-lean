module

public import PottsContinuity.Thm3.RSW.StripBandArm

@[expose] public section

namespace PottsContinuity.RSW
noncomputable section

/-- Integer horizontal translation, preserving every original strip vertex. -/
def stripHorizontalTranslationIso (n : ℕ) (c : ℤ) : stripGraph n ≃g stripGraph n where
  toEquiv := {
    toFun := fun z => ⟨(z.val.1+c,z.val.2),z.property⟩
    invFun := fun z => ⟨(z.val.1-c,z.val.2),z.property⟩
    left_inv := by intro z; apply Subtype.ext; apply Prod.ext <;> dsimp; omega
    right_inv := by intro z; apply Subtype.ext; apply Prod.ext <;> dsimp; omega }
  map_rel_iff' := by
    intro u v
    change |(u.val.1+c)-(v.val.1+c)|+|u.val.2-v.val.2|=1 ↔
      |u.val.1-v.val.1|+|u.val.2-v.val.2|=1
    rw [add_sub_add_right_eq_sub]

/-- Relabel the actual strip edge states by horizontal translation. -/
def stripHorizontalTranslationConfiguration (n : ℕ) (c : ℤ) :
    StripConfiguration n ≃ₜ StripConfiguration n :=
  Homeomorph.piCongrLeft (Y := fun _ : (stripGraph n).edgeSet => Bool)
    (SimpleGraph.Iso.mapEdgeSet (stripHorizontalTranslationIso n c))

/-- Each reflected bond retains exactly its original sampled state. -/
theorem stripHorizontalTranslationConfiguration_edge (n : ℕ) (c : ℤ)
    (ω : StripConfiguration n) (e : (stripGraph n).edgeSet) :
    stripHorizontalTranslationConfiguration n c ω
      ((stripHorizontalTranslationIso n c).mapEdgeSet e) = ω e :=
  Homeomorph.piCongrLeft_apply_apply (Y := fun _ : (stripGraph n).edgeSet => Bool)
    (SimpleGraph.Iso.mapEdgeSet (stripHorizontalTranslationIso n c)) ω e

/-- Opposite translations cancel on every original bond. -/
theorem stripHorizontalTranslation_edge_neg_cancel (n : ℕ) (c : ℤ)
    (e : (stripGraph n).edgeSet) :
    (stripHorizontalTranslationIso n (-c)).mapEdgeSet
      ((stripHorizontalTranslationIso n c).mapEdgeSet e) = e := by
  apply Subtype.ext
  change Sym2.map (stripHorizontalTranslationIso n (-c))
    (Sym2.map (stripHorizontalTranslationIso n c) e.val) = e.val
  rw [Sym2.map_map]
  have hfun : (fun z : stripVertices n =>
      stripHorizontalTranslationIso n (-c) (stripHorizontalTranslationIso n c z)) = id := by
    funext z
    apply Subtype.ext
    apply Prod.ext <;> dsimp [stripHorizontalTranslationIso]; omega
  change Sym2.map (fun z => stripHorizontalTranslationIso n (-c) (stripHorizontalTranslationIso n c z)) e.val = e.val
  rw [hfun]
  exact congrFun Sym2.map_id e.val

/-- Opposite translations cancel on the whole sampled state carrier. -/
theorem stripHorizontalTranslationConfiguration_neg_cancel (n : ℕ) (c : ℤ)
    (ω : StripConfiguration n) :
    stripHorizontalTranslationConfiguration n (-c)
      (stripHorizontalTranslationConfiguration n c ω) = ω := by
  funext e
  calc
    _ = stripHorizontalTranslationConfiguration n (-c)
        (stripHorizontalTranslationConfiguration n c ω)
        ((stripHorizontalTranslationIso n (-c)).mapEdgeSet
          ((stripHorizontalTranslationIso n c).mapEdgeSet e)) := by
      rw [stripHorizontalTranslation_edge_neg_cancel n c e]
    _ = stripHorizontalTranslationConfiguration n c ω
        ((stripHorizontalTranslationIso n c).mapEdgeSet e) :=
      stripHorizontalTranslationConfiguration_edge n (-c) _ _
    _ = ω e := stripHorizontalTranslationConfiguration_edge n c ω e

/-- Translation maps actual original open walks into the translated sample. -/
def stripHorizontalTranslationOpenHom (n : ℕ) (c : ℤ) (ω : StripConfiguration n) :
    stripOpenGraph n ω →g stripOpenGraph n (stripHorizontalTranslationConfiguration n c ω) where
  toFun := stripHorizontalTranslationIso n c
  map_rel' := by
    intro u v huv
    have hb := stripOpenGraph_le n ω huv
    have hs : (stripGraph n).Adj
        (stripHorizontalTranslationIso n c u) (stripHorizontalTranslationIso n c v) :=
      (stripHorizontalTranslationIso n c).map_rel_iff.mpr hb
    have ho := (SimpleGraph.fromEdgeSet_adj _).mp huv
    obtain ⟨hbase,hstate⟩ := ho.1
    have heq : (stripHorizontalTranslationIso n c).mapEdgeSet ⟨s(u,v),hbase⟩ =
        ⟨s(stripHorizontalTranslationIso n c u,stripHorizontalTranslationIso n c v),
          (stripGraph n).mem_edgeSet.mpr hs⟩ := by apply Subtype.ext; rfl
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨⟨(stripGraph n).mem_edgeSet.mpr hs,?_⟩,hs.ne⟩
    rw [← heq,stripHorizontalTranslationConfiguration_edge]
    exact hstate

end
end PottsContinuity.RSW
