module

public import PottsContinuity.PlanarMixed.FiniteSlit.BarrierEdges

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.Duality PlanarMixed.FiniteSlit

/-- Literal horizontal translation on original integer lattice coordinates. -/
def horizontalBarrierTranslationHom (d : ℤ) : squareLattice →g squareLattice where
  toFun v := (v.1+d,v.2)
  map_rel' := by
    intro u v huv
    change |(u.1+d)-(v.1+d)|+|u.2-v.2|=1
    change |u.1-v.1|+|u.2-v.2|=1 at huv
    simpa only [add_sub_add_right_eq_sub] using huv

/-- Ray indices transport without an endpoint correction under horizontal
translation, for arbitrary walks and arbitrary marks. -/
theorem rayIndex_horizontalBarrierTranslation (d : ℤ) (v : LatticeVertex)
    {a b : LatticeVertex} (p : squareLattice.Walk a b) :
    rayIndex (v.1+d,v.2) (p.map (horizontalBarrierTranslationHom d)) = rayIndex v p := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
    change rayStep (v.1+d,v.2) (a.1+d,a.2) (b.1+d,b.2) +
      rayIndex (v.1+d,v.2) (p.map (horizontalBarrierTranslationHom d)) =
      rayStep v a b + rayIndex v p
    rw [ih]
    congr 1
    simp only [rayStep,add_le_add_iff_right]

/-- Every permitted slit-barrier edge keeps its exact role under literal
horizontal translation, including both attachments and every outside return. -/
theorem slitBarrierEdges_horizontalBarrierTranslation
    (M : ℕ) (x y b d : ℤ) {t : LatticeVertex}
    (q : squareLattice.Walk (b,0) t) (e : Sym2 LatticeVertex)
    (he : e ∈ slitBarrierEdges M x y b q) :
    Sym2.map (horizontalBarrierTranslationHom d) e ∈
      slitBarrierEdges M (x+d) y (b+d) (q.map (horizontalBarrierTranslationHom d)) := by
  rcases he with hq | hroot | ⟨htip,ht⟩ | ⟨u,v,huv,hout⟩
  · left
    have hm : Sym2.map (horizontalBarrierTranslationHom d) e ∈
        q.edges.map (Sym2.map (horizontalBarrierTranslationHom d)) := List.mem_map.mpr ⟨e,hq,rfl⟩
    exact (SimpleGraph.Walk.edges_map _ _).symm ▸ hm
  · right; left
    rw [hroot]
    rfl
  · right; right; left
    constructor
    · rw [htip]
      apply Sym2.eq_iff.mpr
      left
      constructor
      · apply Prod.ext
        · change x-1+d = x+d-1
          omega
        · rfl
      · rfl
    · have hm : (x+d,y) ∈ q.support.map (horizontalBarrierTranslationHom d) :=
        List.mem_map.mpr ⟨(x,y),ht,rfl⟩
      exact (SimpleGraph.Walk.support_map _ _).symm ▸ hm
  · right; right; right
    refine ⟨(u.1+d,u.2),(v.1+d,v.2),?_,?_⟩
    · rw [huv]
      rfl
    · rcases hout with hcol | hbottom | htop | hleft | hright
      · exact Or.inl ⟨by dsimp; omega,by dsimp; omega,hcol.2.2.1,hcol.2.2.2⟩
      · exact Or.inr (Or.inl hbottom)
      · exact Or.inr (Or.inr (Or.inl htop))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp; omega,by dsimp; omega⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by dsimp; omega,by dsimp; omega⟩)))

/-- A whole closed barrier is transported with every original allowed edge. -/
theorem slitBarrierWalk_horizontalBarrierTranslation
    (M : ℕ) (x y b d : ℤ) {t z : LatticeVertex}
    (q : squareLattice.Walk (b,0) t) (p : squareLattice.Walk z z)
    (hallowed : ∀ e ∈ p.edges, e ∈ slitBarrierEdges M x y b q) :
    ∀ e ∈ (p.map (horizontalBarrierTranslationHom d)).edges,
      e ∈ slitBarrierEdges M (x+d) y (b+d) (q.map (horizontalBarrierTranslationHom d)) := by
  intro e he
  rw [SimpleGraph.Walk.edges_map] at he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  exact slitBarrierEdges_horizontalBarrierTranslation M x y b d q f (hallowed f hf)


/-- The left wired arc and its zero index translate on the actual finite
reference carrier, preserving its full bottom, side and top portions. -/
theorem slitAlpha_index_horizontalBarrierTranslation
    (M : ℕ) (hM : 1 ≤ M) (x d : ℤ) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hα : ∀ u : Vertex M x, u ∈ alpha M x → rayIndex u.val p = 0) :
    ∀ v : Vertex M (x+d), v ∈ alpha M (x+d) →
      rayIndex v.val (p.map (horizontalBarrierTranslationHom d)) = 0 := by
  intro v hv
  have hvB := (mem_rectangle_iff M (x+d) hM v.val).mp v.property
  let u : Vertex M x := ⟨(v.val.1-d,v.val.2),(mem_rectangle_iff M x hM _).mpr
    ⟨by dsimp; omega,by dsimp; omega,hvB.2.2.1,hvB.2.2.2⟩⟩
  have hu : u ∈ alpha M x := by
    change ((v.val.2 = 0 ∧ v.val.1-d ≤ x) ∨ v.val.1-d = x-(M:ℤ) ∨
      (v.val.2=(M:ℤ) ∧ v.val.1-d ≤ x-1))
    change ((v.val.2 = 0 ∧ v.val.1 ≤ x+d) ∨ v.val.1 = x+d-(M:ℤ) ∨
      (v.val.2=(M:ℤ) ∧ v.val.1 ≤ x+d-1)) at hv
    omega
  have heq : (u.val.1+d,u.val.2) = v.val := by
    apply Prod.ext
    · change v.val.1-d+d=v.val.1
      omega
    · rfl
  have hi := rayIndex_horizontalBarrierTranslation d u.val p
  rw [heq,hα u hu] at hi
  exact hi

end PottsContinuity.Push
