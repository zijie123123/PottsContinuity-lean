module

public import PottsContinuity.PlanarTopology.AlphaTargetAlternative
public import PottsContinuity.PlanarTopology.KSTRectangleRealization
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- The actual whole-plane arm event is the literal central connection in its
finite rectangle restriction. This includes all original bonds and vertices. -/
theorem kstArm_iff_alpha_target_primal (k : ℕ) (ω : LatticeConfiguration) :
    ω ∈ kstArm (64*k) ↔ alphaTargetPrimalCrossing k
      (embeddedRestriction (rectangleGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))
        (frozenEdgeEmbedding (latticeRectangle (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))) ω) := by
  constructor
  · rintro ⟨u,v,p,_,hp,hu,hv,hux,hvx,hbox⟩
    have huX : |u.1| ≤ (k : ℤ) := by push_cast at hux; omega
    have hvX : |v.1| ≤ (k : ℤ) := by push_cast at hvx; omega
    have hmem : ∀ z ∈ p.support,
        z ∈ latticeRectangle (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k) := by
      intro z hz
      have hh := hbox z hz
      push_cast at hh
      have hx : |z.1| ≤ 65*(k : ℤ) := by omega
      have hxb := abs_le.mp hx
      have hyb := abs_le.mp hh.2
      apply (mem_latticeRectangle _ z _ _).mpr
      push_cast
      exact ⟨⟨hxb.1,by omega⟩,hyb.1,by omega⟩
    refine ⟨⟨u,hmem u p.start_mem_support⟩,?_,⟨v,hmem v p.end_mem_support⟩,?_,
      rectangle_connected_of_kst_open_walk _ _ _ ω p hp hmem⟩
    · exact ⟨by push_cast at hu; exact hu,(abs_le.mp huX).1,(abs_le.mp huX).2⟩
    · exact ⟨by push_cast at hv; exact hv,(abs_le.mp hvX).1,(abs_le.mp hvX).2⟩
  · rintro ⟨u,hu,v,hv,hconn⟩
    obtain ⟨r,hr⟩ := hconn.exists_isPath
    let p := r.map (rectangleOpenGraphToSquare _ _ _ _)
    refine ⟨u.val,v.val,p,hr.map Subtype.val_injective,
      kstPathOpen_of_rectangle_walk _ _ _ ω r,?_,?_,?_,?_,?_⟩
    · push_cast
      exact hu.1
    · push_cast
      exact hv.1
    · have hh := abs_le.mpr hu.2
      push_cast
      omega
    · have hh := abs_le.mpr hv.2
      push_cast
      omega
    · intro z hz
      obtain ⟨z',_,he⟩ := rectangleOpenWalk_mapped_support_preimage _ _ _ _ r hz
      have hh := (mem_latticeRectangle _ z'.val (130*k) (128*k)).mp z'.property
      rw [he] at hh
      simp only [Nat.cast_mul,Nat.cast_ofNat] at hh
      have hx : |z.1| ≤ 65*(k : ℤ) := abs_le.mpr ⟨hh.1.1,by omega⟩
      have hy : |z.2| ≤ 64*(k : ℤ) := abs_le.mpr ⟨hh.2.1,by omega⟩
      push_cast
      omega

end
end PottsContinuity.PlanarTopology
