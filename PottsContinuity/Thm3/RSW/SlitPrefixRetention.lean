module

public import PottsContinuity.Thm3.RSW.SlitRayApproach
public import PottsContinuity.Thm3.RSW.SlitContactOrder

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK BD12 PlanarMixed.FiniteSlit
noncomputable section

/-- The complete source-square prefix before its first left-slit contact
is retained, from actual disjoint source walks alone. No rayApproach input remains. -/
theorem sourceSquare_leftSlit_prefix_in_finiteSlit_of_disjoint_walks
    (n : ℕ) (x y B b : ℤ) (hx0 : 0 ≤ x) (hxn : x ≤ (2*n:ℕ))
    {u v : RectangleVertex (0,0) (2*n) (2*n)}
    (p : (rectangleGraph (0,0) (2*n) (2*n)).Walk u v)
    (hu : u.val.2 = 0) (hv : v.val.1 = B) (hxa : x ≤ u.val.1) (hab : u.val.1 < b)
    (q : squareLattice.Walk (b,0) (x,y))
    (hp : ∀ w ∈ p.support,
      0 ≤ w.val.1 ∧ w.val.1 ≤ B ∧ 0 ≤ w.val.2 ∧ w.val.2 ≤ (2*n:ℕ))
    (hq : ∀ w ∈ q.support,
      x ≤ w.1 ∧ w.1 ≤ B ∧ 0 ≤ w.2 ∧ w.2 ≤ (2*n:ℕ))
    (hdis : ∀ w ∈ p.support, w.val ∉ q.support)
    (k : ℕ) (hk : k ≤ p.length)
    (hfirst : ∀ j : ℕ, j < k → ¬ ((p.getVert j).val.1 = x-1 ∧ y ≤ (p.getVert j).val.2)) :
    ∃ r : (graph (2*n+2) x y).Walk
      (sourceSquareSlitEmbedding n x hx0 hxn u)
      (sourceSquareSlitEmbedding n x hx0 hxn (p.getVert k)),
      r.edges = (p.take k).edges.map (Sym2.map (sourceSquareSlitEmbedding n x hx0 hxn)) ∧
      ∀ w ∈ r.support, w ∉ beta (2*n+2) x y := by
  let φ : rectangleGraph (0,0) (2*n) (2*n) →g squareLattice := {
    toFun := Subtype.val
    map_rel' := fun h => h }
  have huEq : u.val = (u.val.1,0) := Prod.ext rfl hu
  have hvEq : v.val = (B,v.val.2) := Prod.ext hv rfl
  let P := (p.map φ).copy huEq hvEq
  have hget : ∀ j : ℕ, P.getVert j = (p.getVert j).val := by
    intro j
    simp only [P,SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_map]
    rfl
  have hlen : P.length = p.length := by
    simp only [P,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map]
  have hP : ∀ w ∈ P.support,
      0 ≤ w.1 ∧ w.1 ≤ B ∧ 0 ≤ w.2 ∧ w.2 ≤ ((2*n:ℕ):ℤ) := by
    intro w hw
    rw [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map] at hw
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
    exact hp z hz
  have hPd : ∀ w ∈ P.support, w ∉ q.support := by
    intro w hw
    rw [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map] at hw
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
    exact hdis z hz
  have hy : 0 < y := disjoint_bottom_right_walk_tip_pos u.val.1 b B v.val.2 x y
    hxa hab.le (hq _ q.start_mem_support).2.1 P q
    (fun w hw => (hP w hw).2.2.1)
    (fun w hw => ⟨(hq w hw).2.1,(hq w hw).2.2.1⟩) hPd
  apply sourceSquare_leftSlit_prefix_in_finiteSlit_of_rayApproach n x y hx0 hxn p
    (by intro h; have hh := h.2; rw [hu] at hh; omega) k hk hfirst
  intro m hmpos hmle hmhit hmfirst
  have hmhit' : (P.getVert m).1 = x ∧ y ≤ (P.getVert m).2 := by
    rw [hget m]
    exact hmhit
  have hmfirst' : ∀ j : ℕ, j < m → ¬ ((P.getVert j).1 = x ∧ y ≤ (P.getVert j).2) := by
    intro j hj
    rw [hget j]
    exact hmfirst j hj
  have h := first_markedRay_contact_approaches_left u.val.1 b B v.val.2 x y
    ((2*n:ℕ):ℤ) hab P q hP hq hPd m hmpos (le_of_le_of_eq hmle hlen.symm) hmhit' hmfirst'
  exact ⟨(congrArg Prod.fst (hget (m-1))).symm.trans h.1,
    (lt_of_lt_of_eq h.2.2 (congrArg Prod.snd (hget (m-1)))).le⟩

end
end PottsContinuity.RSW
