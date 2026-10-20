module

public import PottsContinuity.Thm3.RSW.FiniteSlitHorizontal
public import PottsContinuity.Thm3.RSW.RankedBandGeometry
public import PottsContinuity.PlanarMixed.OrderedCutBands
public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutSeparation
public import PottsContinuity.PlanarMixed.FiniteSlit.ReferenceConsumers

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- A vertex in the closed ordered band belongs to neither accessible exterior. -/
theorem orderedBand_avoids_exterior {V : Type*} {G : SimpleGraph V}
    {L R A C : Set V} (h : OrderedCutPair G L R A C)
    (v : rankedBandVertices (orderedCutRank G L R A C h)) :
    v.val ∉ cutReachRegion G A L ∧ v.val ∉ cutReachRegion G C R := by
  classical
  have hv := v.property
  constructor
  · intro hvL
    simp only [rankedBandVertices, Set.mem_ofPred_eq, orderedCutRank, ite_eq_left hvL] at hv
    omega
  · intro hvR
    have hnL : v.val ∉ cutReachRegion G A L :=
      fun hvL => Set.disjoint_left.mp h.regions_disjoint hvL hvR
    have hnA := h.rightRegion_avoids_first hvR
    have hnC := cutReachRegion_avoids_cut hvR
    simp only [rankedBandVertices, Set.mem_ofPred_eq, orderedCutRank,
      ite_eq_right hnL, ite_eq_right hnA, ite_eq_right hnC, ite_eq_left hvR] at hv
    omega

/-- The entire closed slit band stays inside the box containing its physical
cuts. The artificial outer arcs and all vertices above the cuts are excluded. -/
theorem finiteSlit_orderedBand_in_box
    (M : ℕ) (x y B N : ℤ) (hM : 2 ≤ M) (hx : 1 ≤ x) (hxB : x ≤ B)
    (A C : Set (Vertex M x))
    (hcuts : OrderedCutPair (graph M x y) (alpha M x) (beta M x y) A C)
    (hA : ∀ w ∈ A, 0 ≤ w.val.1 ∧ w.val.1 ≤ B ∧ w.val.2 ≤ N)
    (hC : ∀ w ∈ C, 0 ≤ w.val.1 ∧ w.val.1 ≤ B ∧ w.val.2 ≤ N)
    (v : rankedBandVertices
      (orderedCutRank (graph M x y) (alpha M x) (beta M x y) A C hcuts)) :
    0 ≤ v.val.val.1 ∧ v.val.val.1 ≤ B ∧ 0 ≤ v.val.val.2 ∧ v.val.val.2 ≤ N := by
  classical
  let z := v.val
  have hz := (mem_rectangle_iff M x (by omega) z.val).mp z.property
  have havoid := orderedBand_avoids_exterior hcuts v
  have hleft : (z.val.1 < 0 ∨ N < z.val.2) → z.val.1 ≤ x-1 → False := by
    intro hout hside
    let l : Vertex M x := ⟨(x-(M:ℤ),z.val.2),
      (mem_rectangle_iff M x (by omega) _).mpr ⟨le_rfl,by omega,hz.2.2⟩⟩
    have hl : l ∈ alpha M x := Or.inr (Or.inl rfl)
    obtain ⟨p,hp⟩ := finiteSlit_horizontal_walk M x y (by omega) l z rfl
      (Or.inr (Or.inl (by change max (x-(M:ℤ)) z.val.1 ≤ x-1; omega)))
    apply havoid.1
    refine ⟨l,hl,p,?_⟩
    intro w hw hwA
    have hwcoord := hp w hw
    have hwbox := hA w hwA
    change min (x-(M:ℤ)) z.val.1 ≤ w.val.1 ∧
      w.val.1 ≤ max (x-(M:ℤ)) z.val.1 ∧ w.val.2 = z.val.2 at hwcoord
    rw [max_eq_right hz.1] at hwcoord
    rcases hout with hout | hout <;> omega
  have hright : (B < z.val.1 ∨ N < z.val.2) → x ≤ z.val.1 → False := by
    intro hout hside
    let r : Vertex M x := ⟨(x+(M:ℤ)-1,z.val.2),
      (mem_rectangle_iff M x (by omega) _).mpr ⟨by omega,le_rfl,hz.2.2⟩⟩
    have hr : r ∈ beta M x y := Or.inl rfl
    obtain ⟨p,hp⟩ := finiteSlit_horizontal_walk M x y (by omega) r z rfl
      (Or.inr (Or.inr (by change x ≤ min (x+(M:ℤ)-1) z.val.1; omega)))
    apply havoid.2
    refine ⟨r,hr,p,?_⟩
    intro w hw hwC
    have hwcoord := hp w hw
    have hwbox := hC w hwC
    change min (x+(M:ℤ)-1) z.val.1 ≤ w.val.1 ∧
      w.val.1 ≤ max (x+(M:ℤ)-1) z.val.1 ∧ w.val.2 = z.val.2 at hwcoord
    rw [min_eq_right hz.2.1] at hwcoord
    rcases hout with hout | hout <;> omega
  have h0 : 0 ≤ z.val.1 := by
    by_contra hn
    exact hleft (Or.inl (by omega)) (by omega)
  have hB : z.val.1 ≤ B := by
    by_contra hn
    exact hright (Or.inl (by omega)) (by omega)
  have hN : z.val.2 ≤ N := by
    by_contra hn
    by_cases hside : z.val.1 ≤ x-1
    · exact hleft (Or.inr (by omega)) hside
    · exact hright (Or.inr (by omega)) (by omega)
  exact ⟨h0,hB,hz.2.2.1,hN⟩

end
end PottsContinuity.RSW
