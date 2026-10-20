module

public import PottsContinuity.Thm3.RSW.FiniteIso
public import PottsContinuity.Thm3.RSW.CorridorScale

/-! Coordinate exchange supplies vertical versions of the common-box corridor
bound, using exact finite-law symmetry rather than translations of that law. -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- The actual vertical crossing of a rectangle, with both endpoints and the
whole walk confined to that rectangle. -/
def finiteVerticalCrossing (V : Finset (ℤ × ℤ)) (a b c d : ℤ)
    (ω : (squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool) : Prop :=
  ∃ (x y : (V:Set (ℤ × ℤ))) (w : (rcOpenGraph V ω).Walk x y),
    x.val ∈ Set.Icc a b ×ˢ ({c}:Set ℤ) ∧
    y.val ∈ Set.Icc a b ×ˢ ({d}:Set ℤ) ∧
    ∀ v ∈ w.support, v.val ∈ Set.Icc a b ×ˢ Set.Icc c d

/-- Vertical crossings are increasing in actual open edges. -/
theorem finiteVerticalCrossing_isUpperSet (V : Finset (ℤ × ℤ)) (a b c d : ℤ) :
    IsUpperSet {ω | finiteVerticalCrossing V a b c d ω} := by
  rintro ω η h ⟨x,y,p,hx,hy,hp⟩
  refine ⟨x,y,p.mapLe (rcOpenGraph_mono V h),hx,hy,?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
  exact hp v hv

/-- The centered square is invariant under exchanging its two coordinates. -/
def boxCoordinateSwapIso (N : ℕ) :
    (squareLattice.induce (box N:Set (ℤ × ℤ))) ≃g
      squareLattice.induce (box N:Set (ℤ × ℤ)) where
  toEquiv :=
    { toFun := fun v => ⟨(v.val.2,v.val.1), by
        have hv := v.property
        simp only [box,Finset.mem_coe,Finset.mem_product] at hv ⊢
        exact ⟨hv.2,hv.1⟩⟩
      invFun := fun v => ⟨(v.val.2,v.val.1), by
        have hv := v.property
        simp only [box,Finset.mem_coe,Finset.mem_product] at hv ⊢
        exact ⟨hv.2,hv.1⟩⟩
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl }
  map_rel_iff' := by
    intro u v
    change |u.val.2-v.val.2|+|u.val.1-v.val.1|=1 ↔
      |u.val.1-v.val.1|+|u.val.2-v.val.2|=1
    rw [add_comm]

/-- Exchanging coordinates maps an actual horizontal walk to a vertical walk. -/
theorem horizontalCrossing_box_swap (N : ℕ) (a b c d : ℤ)
    (ω : (squareLattice.induce (box N:Set (ℤ × ℤ))).edgeSet → Bool)
    (hω : horizontalCrossing (box N) a b c d ω) :
    finiteVerticalCrossing (box N) c d a b
      (finiteBoolIso (box N) (box N) (boxCoordinateSwapIso N) ω) := by
  obtain ⟨x,y,p,hx,hy,hp⟩ := hω
  let hom := (finiteBoolOpenIso (box N) (box N) (boxCoordinateSwapIso N) ω).toHom
  have hs : ∀ v ∈ (p.map hom).support,
      v.val ∈ Set.Icc c d ×ˢ Set.Icc a b := by
    intro v hv
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hv
    obtain ⟨z,hz,rfl⟩ := hv
    change (z.val.2,z.val.1) ∈ Set.Icc c d ×ˢ Set.Icc a b
    exact ⟨(hp z hz).2,(hp z hz).1⟩
  refine ⟨hom x,hom y,p.map hom,?_,?_,hs⟩
  · change (x.val.2,x.val.1) ∈ Set.Icc c d ×ˢ ({a}:Set ℤ)
    exact ⟨hx.2,hx.1⟩
  · change (y.val.2,y.val.1) ∈ Set.Icc c d ×ˢ ({b}:Set ℤ)
    exact ⟨hy.2,hy.1⟩

/-- The same power-28 bound holds for any vertical corridor fitting in the
box, at every interior FK parameter and all real cluster weights ≥1. -/
theorem squarePair_pow_twentyEight_le_box_vertical_corridor (θ : Parameters)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m < n) (hnm : n ≤ 7*m)
    (i j : Fin (m+1)) (b : ℤ)
    (hb0 : -(8*(n:ℤ)) ≤ b) (hb1 : b+(m:ℤ) ≤ 8*(n:ℤ)) :
    (squarePairProbability θ m i j)^28 ≤
      finiteBoundaryEventProbability (box (8*n)) θ (frozenBoundaryCondition (box (8*n)) 0)
        (finiteVerticalCrossing (box (8*n)) b (b+(m:ℤ)) (-2*(n:ℤ)) (2*(n:ℤ))) := by
  have hhor := squarePair_pow_twentyEight_le_box_corridor θ n m hn hm hmn hnm i j b hb0 hb1
  have hiso := finite_free_probability_iso (box (8*n)) (box (8*n))
    (boxCoordinateSwapIso (8*n)) θ
    (finiteVerticalCrossing (box (8*n)) b (b+(m:ℤ)) (-2*(n:ℤ)) (2*(n:ℤ)))
  rw [hiso]
  exact hhor.trans (measureReal_mono (fun _ h => horizontalCrossing_box_swap _ _ _ _ _ _ h))

end
end PottsContinuity.RSW
