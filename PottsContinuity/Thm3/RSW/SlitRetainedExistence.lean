module

public import PottsContinuity.Thm3.RSW.SlitPrefixRetention

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK BD12 PlanarMixed.FiniteSlit
noncomputable section

/-- Actual disjoint source walks determine a first LEFT-slit prefix whose
entire original bond list is retained and whose endpoint is genuinely free. -/
theorem sourceSquare_exists_retained_leftSlit_prefix_of_disjoint_walks
    (n : ℕ) (x y B b : ℤ) (hx : 1 ≤ x) (hxn : x ≤ (2*n:ℕ))
    {u v : RectangleVertex (0,0) (2*n) (2*n)}
    (p : (rectangleGraph (0,0) (2*n) (2*n)).Walk u v)
    (hu : u.val.2 = 0) (hv : v.val.1 = B) (hxa : x ≤ u.val.1) (hab : u.val.1 < b)
    (q : squareLattice.Walk (b,0) (x,y))
    (hp : ∀ w ∈ p.support,
      0 ≤ w.val.1 ∧ w.val.1 ≤ B ∧ 0 ≤ w.val.2 ∧ w.val.2 ≤ (2*n:ℕ))
    (hq : ∀ w ∈ q.support,
      x ≤ w.1 ∧ w.1 ≤ B ∧ 0 ≤ w.2 ∧ w.2 ≤ (2*n:ℕ))
    (hdis : ∀ w ∈ p.support, w.val ∉ q.support) :
    ∃ k : ℕ, 0 < k ∧ k ≤ p.length ∧
      ((p.getVert k).val.1 = x-1 ∧ y ≤ (p.getVert k).val.2) ∧
      (∀ j : ℕ, j < k → ¬ ((p.getVert j).val.1 = x-1 ∧ y ≤ (p.getVert j).val.2)) ∧
      ∃ r : (graph (2*n+2) x y).Walk
        (sourceSquareSlitEmbedding n x (by omega) hxn u)
        (sourceSquareSlitEmbedding n x (by omega) hxn (p.getVert k)),
        r.edges = (p.take k).edges.map (Sym2.map (sourceSquareSlitEmbedding n x (by omega) hxn)) ∧
        (∀ w ∈ r.support, w ∉ beta (2*n+2) x y) ∧
        sourceSquareSlitEmbedding n x (by omega) hxn (p.getVert k) ∈ freeSlit (2*n+2) x y := by
  classical
  have hx0 : 0 ≤ x := by omega
  let φ : rectangleGraph (0,0) (2*n) (2*n) →g squareLattice := {
    toFun := Subtype.val
    map_rel' := fun h => h }
  have huEq : u.val = (u.val.1,0) := Prod.ext rfl hu
  have hvEq : v.val = (B,v.val.2) := Prod.ext hv rfl
  let P := (p.map φ).copy huEq hvEq
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
  obtain ⟨z,hzp,hzx,hzy⟩ := disjoint_bottom_right_walk_hits_left_slit u.val.1 b B v.val.2
    x y ((2*n:ℕ):ℤ) (hp _ p.start_mem_support).1 hab (hq _ q.start_mem_support).2.1
    hx hxa hy (hq _ q.end_mem_support).2.2.2 P q hP
    (fun w hw => ⟨by have := (hq w hw).1; omega,(hq w hw).2⟩) hPd
  have hsP : P.support = p.support.map Subtype.val := by
    simp only [P,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map]
    rfl
  have hzp' : z ∈ p.support.map Subtype.val :=
    (congrArg (fun l : List LatticeVertex => z ∈ l) hsP).mp hzp
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hzp'
  have hwl : w.val.1 = x-1 ∧ y ≤ w.val.2 := ⟨hzx,hzy⟩
  obtain ⟨j,hj,hjlen⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
  have hex : ∃ k : ℕ, k ≤ p.length ∧
      ((p.getVert k).val.1 = x-1 ∧ y ≤ (p.getVert k).val.2) := by
    refine ⟨j,hjlen,?_⟩
    rw [hj]
    exact hwl
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hfirst : ∀ j : ℕ, j < k →
      ¬ ((p.getVert j).val.1 = x-1 ∧ y ≤ (p.getVert j).val.2) := by
    intro j hj hL
    exact Nat.find_min hex hj ⟨hj.le.trans hk.1,hL⟩
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have he := hk.2.1
    change (p.getVert k).val.1 = x-1 at he
    rw [hk0,SimpleGraph.Walk.getVert_zero] at he
    omega
  obtain ⟨r,hredges,hravoid⟩ := sourceSquare_leftSlit_prefix_in_finiteSlit_of_disjoint_walks
    n x y B b hx0 hxn p hu hv hxa hab q hp hq hdis k hk.1 hfirst
  refine ⟨k,hkpos,hk.1,hk.2,hfirst,r,hredges,hravoid,?_⟩
  change (p.getVert k).val.1 = x-1 ∧ y ≤ (p.getVert k).val.2 ∧
    (p.getVert k).val.2 < ((2*n+2:ℕ):ℤ)
  exact ⟨hk.2.1,hk.2.2,by have := (hp _ (p.getVert_mem_support k)).2.2.2; omega⟩

end
end PottsContinuity.RSW
