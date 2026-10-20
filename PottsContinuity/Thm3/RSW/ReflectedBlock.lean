module

public import PottsContinuity.Thm3.RSW.FinitePath

/-! The reflected pair bound for an actual translated confined block. -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- The full doubled-width block, before clipping to a target corridor. -/
def reflectedBlock (m : ℕ) (a b : ℤ) : Finset (ℤ × ℤ) :=
  latticeRectangle (a-(m:ℤ)) (a+(m:ℤ)) b (b+(m:ℤ))

/-- Free-domain comparison transports the reflected pair estimate into a
translated block of the ambient sample, retaining its actual path support.
The translation acts on the local free graph, not on the ambient FK law. -/
theorem squarePair_sq_le_translated_block_path (θ : Parameters)
    (V : Finset (ℤ × ℤ)) (m : ℕ) (i j : Fin (m+1)) (a b : ℤ)
    (hblock : reflectedBlock m a b ⊆ V) :
    (squarePairProbability θ m i j)^2 ≤
      finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0)
        (fun ω => ω ∈ finitePathEvent V (reflectedBlock m a b)
          (a-(m:ℤ), b+(j.val:ℤ)) (a+(m:ℤ), b+(j.val:ℤ))) := by
  let R := latticeRectangle (-(m:ℤ)) m 0 m
  let G := squareLattice.induce (R:Set (ℤ × ℤ))
  have himage (v : (R:Set (ℤ × ℤ))) :
      (a+v.val.1,b+v.val.2) ∈ reflectedBlock m a b := by
    have hv := v.property
    simp only [R,reflectedBlock,latticeRectangle,Finset.mem_coe,
      Finset.mem_product,Finset.mem_Icc] at hv ⊢
    omega
  let f : (R:Set (ℤ × ℤ)) ↪ (V:Set (ℤ × ℤ)) :=
    ⟨fun v => ⟨(a+v.val.1,b+v.val.2), hblock (himage v)⟩, by
      intro u v h
      apply Subtype.ext
      have hv := congrArg (fun z : (V:Set (ℤ × ℤ)) => z.val) h
      change (a+u.val.1,b+u.val.2) = (a+v.val.1,b+v.val.2) at hv
      exact Prod.ext (add_left_cancel (congrArg Prod.fst hv))
        (add_left_cancel (congrArg Prod.snd hv))⟩
  have hmap : G.map f ≤ squareLattice.induce (V:Set (ℤ × ℤ)) := by
    intro x y hxy
    obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj f G x y).mp hxy
    change |(a+u.val.1)-(a+v.val.1)|+|(b+u.val.2)-(b+v.val.2)|=1
    have hx : (a+u.val.1)-(a+v.val.1) = u.val.1-v.val.1 := by ring
    have hy : (b+u.val.2)-(b+v.val.2) = u.val.2-v.val.2 := by ring
    rw [hx,hy]
    exact huv
  have hxR : (-(m:ℤ),(j.val:ℤ)) ∈ R := by
    simp only [R,latticeRectangle,Finset.mem_product,Finset.mem_Icc]; omega
  have hyR : ((m:ℤ),(j.val:ℤ)) ∈ R := by
    simp only [R,latticeRectangle,Finset.mem_product,Finset.mem_Icc]; omega
  have hsource := squarePair_probability_sq_le_reflected_connection θ m i j
  rw [finite_free_connection_probability_eq θ R _ _ hxR hyR] at hsource
  have htarget := embedded_free_connection_le_finitePathProbability G V
    (reflectedBlock m a b) θ f hmap himage ⟨_,hxR⟩ ⟨_,hyR⟩
  exact hsource.trans (by simpa [f,G,sub_eq_add_neg] using htarget)

end
end PottsContinuity.RSW
