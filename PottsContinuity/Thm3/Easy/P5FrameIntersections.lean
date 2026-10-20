module

public import Mathlib
public import PottsContinuity.PlanarTopology.RectangleIntersection
public import PottsContinuity.Thm3.Easy.P5FourFrameConditional
public import PottsContinuity.Thm3.RSW.FinitePathChain

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity
open PottsContinuity.PD.FK

def p5OpenGraphToLattice (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    rcOpenGraph V ω →g squareLattice where
  toFun := fun z => z.1
  map_rel' := by
    intro z w hzw
    have h := PottsContinuity.RSW.rcOpenGraph_le_induced V ω hzw
    change squareLattice.Adj z.1 w.1 at h
    exact h

/-- The closed coordinate strip occupied by the frame crossing with index
`i`. This definition accounts for all four indices of `Fin 4`. -/
def p5FrameCrossingCorridor (n m : ℕ) (i : Fin 4) : Set (ℤ × ℤ) :=
  let r := 8 * (m : ℤ)
  match i.val with
  | 0 => {z | z.1 ∈ Set.Icc (-r) r ∧
      z.2 ∈ Set.Icc ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m)}
  | 1 => {z | z.1 ∈ Set.Icc (-r) r ∧
      z.2 ∈ Set.Icc (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m)}
  | 2 => {z | z.1 ∈ Set.Icc ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) ∧
      z.2 ∈ Set.Icc (-r) r}
  | _ => {z | z.1 ∈ Set.Icc (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) ∧
      z.2 ∈ Set.Icc (-r) r}

/-- A selected open walk witnessing one of the four P5 frame crossings. -/
structure P5FrameCrossingWalk (n m : ℕ)
    (ω : (squareLattice.induce
      (p5aAnnulusVertexSet n : Set (ℤ × ℤ))).edgeSet → Bool)
    (i : Fin 4) where
  start : (p5aAnnulusVertexSet n : Set (ℤ × ℤ))
  finish : (p5aAnnulusVertexSet n : Set (ℤ × ℤ))
  path : (rcOpenGraph (p5aAnnulusVertexSet n) ω).Walk start finish
  endpoints :
    match i.val with
    | 0 => start.1.1 = -(8 * (m : ℤ)) ∧ finish.1.1 = 8 * (m : ℤ)
    | 1 => start.1.1 = -(8 * (m : ℤ)) ∧ finish.1.1 = 8 * (m : ℤ)
    | 2 => start.1.2 = -(8 * (m : ℤ)) ∧ finish.1.2 = 8 * (m : ℤ)
    | _ => start.1.2 = -(8 * (m : ℤ)) ∧ finish.1.2 = 8 * (m : ℤ)
  inside : ∀ z ∈ path.support,
    z.1 ∈ p5FrameCrossingCorridor n m i

/-- Every P5 frame crossing has an actual witness record retaining its path
and its exact corridor. The proof eliminates the four frame cases directly. -/
theorem p5FrameCrossing_exists_walk
    (n m : ℕ) (i : Fin 4)
    (ω : (squareLattice.induce
      (p5aAnnulusVertexSet n : Set (ℤ × ℤ))).edgeSet → Bool)
    (h : p5FrameCrossing n m i ω) :
    Nonempty (P5FrameCrossingWalk n m ω i) := by
  fin_cases i
  · change horizontalCrossing (p5aAnnulusVertexSet n)
      (-(8 * (m : ℤ))) (8 * (m : ℤ))
      ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) ω at h
    rcases h with ⟨x, y, p, hx, hy, hpath⟩
    have hx' : x.1.1 = -(8 * (m : ℤ)) := by
      have hmem := (Set.mem_prod.mp hx).1
      simpa using hmem
    have hy' : y.1.1 = 8 * (m : ℤ) := by
      have hmem := (Set.mem_prod.mp hy).1
      simpa using hmem
    refine ⟨⟨x, y, p, ⟨hx', hy'⟩, ?_⟩⟩
    intro z hz
    rcases hpath z hz with ⟨⟨hxl, hyl⟩, ⟨hxh, hyh⟩⟩
    change z.1.1 ∈ Set.Icc (-(8 * (m : ℤ))) (8 * (m : ℤ)) ∧
      z.1.2 ∈ Set.Icc ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m)
    simp only [Set.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  · change horizontalCrossing (p5aAnnulusVertexSet n)
      (-(8 * (m : ℤ))) (8 * (m : ℤ))
      (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) ω at h
    rcases h with ⟨x, y, p, hx, hy, hpath⟩
    have hx' : x.1.1 = -(8 * (m : ℤ)) := by
      have hmem := (Set.mem_prod.mp hx).1
      simpa using hmem
    have hy' : y.1.1 = 8 * (m : ℤ) := by
      have hmem := (Set.mem_prod.mp hy).1
      simpa using hmem
    refine ⟨⟨x, y, p, ⟨hx', hy'⟩, ?_⟩⟩
    intro z hz
    rcases hpath z hz with ⟨⟨hxl, hyl⟩, ⟨hxh, hyh⟩⟩
    change z.1.1 ∈ Set.Icc (-(8 * (m : ℤ))) (8 * (m : ℤ)) ∧
      z.1.2 ∈ Set.Icc (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m)
    simp only [Set.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  · change p5VerticalCrossing (p5aAnnulusVertexSet n)
      (-(8 * (m : ℤ))) (8 * (m : ℤ))
      ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) ω at h
    rcases h with ⟨x, y, p, hx, hy, hxc, hyc, hpath⟩
    refine ⟨⟨x, y, p, ⟨hx, hy⟩, ?_⟩⟩
    intro z hz
    exact Set.mem_prod.mpr (hpath z hz)
  · change p5VerticalCrossing (p5aAnnulusVertexSet n)
      (-(8 * (m : ℤ))) (8 * (m : ℤ))
      (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) ω at h
    rcases h with ⟨x, y, p, hx, hy, hxc, hyc, hpath⟩
    refine ⟨⟨x, y, p, ⟨hx, hy⟩, ?_⟩⟩
    intro z hz
    exact Set.mem_prod.mpr (hpath z hz)

/-- The explicit-walk form of the rectangle intersection lemma. Unlike the
existential crossing wrapper below, this theorem preserves the supplied
walks, which lets four frame intersections be assembled coherently. -/
theorem horizontal_vertical_open_walks_meet
    (V : Finset (ℤ × ℤ)) (r a b c d : ℤ) (hab : a ≤ b)
    (hband : -(r) ≤ a ∧ b ≤ r ∧ -(r) ≤ c ∧ d ≤ r)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    {x y u v : (V : Set (ℤ × ℤ))}
    (p : (rcOpenGraph V ω).Walk x y)
    (q : (rcOpenGraph V ω).Walk u v)
    (hps : ∀ z ∈ p.support,
      z.1.1 ∈ Set.Icc (-r) r ∧ z.1.2 ∈ Set.Icc a b)
    (hqs : ∀ z ∈ q.support,
      z.1.1 ∈ Set.Icc c d ∧ z.1.2 ∈ Set.Icc (-r) r)
    (hx : x.1.1 = -r) (hy : y.1.1 = r)
    (hu : u.1.2 = -r) (hv : v.1.2 = r) :
    ∃ z : (V : Set (ℤ × ℤ)), z ∈ p.support ∧ z ∈ q.support := by
  let φ := p5OpenGraphToLattice V ω
  let p' := p.map φ
  let q' := q.map φ
  have hpbounds : ∀ z ∈ p'.support,
      -r ≤ z.1 ∧ z.1 ≤ r ∧ a ≤ z.2 ∧ z.2 ≤ b := by
    intro z hz
    change z ∈ (p.map φ).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hps w hw with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨h1, h2, h3, h4⟩
  have hqbound : ∀ z ∈ q'.support,
      c ≤ z.1 ∧ z.1 ≤ d ∧ -r ≤ z.2 ∧ z.2 ≤ r := by
    intro z hz
    change z ∈ (q.map φ).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hqs w hw with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨h1, h2, h3, h4⟩
  have hpx : (φ x).1 = -r := by
    change x.1.1 = -r
    exact hx
  have hpy : (φ y).1 = r := by
    change y.1.1 = r
    exact hy
  have hqu : (φ u).2 = -r := by
    change u.1.2 = -r
    exact hu
  have hqv : (φ v).2 = r := by
    change v.1.2 = r
    exact hv
  obtain ⟨z, hzp, hzq⟩ :=
    PottsContinuity.PlanarTopology.rectangle_walks_common_vertex
      p' q' (by omega) (by omega)
      (fun z hz => by
        obtain ⟨h1, h2, h3, h4⟩ := hpbounds z hz
        exact ⟨h1, h2, le_trans hband.1 h3, le_trans h4 hband.2.1⟩)
      (fun z hz => by
        obtain ⟨h1, h2, h3, h4⟩ := hqbound z hz
        exact ⟨le_trans hband.2.2.1 h1, le_trans h2 hband.2.2.2, h3, h4⟩)
      hpx hpy hqu hqv
  change z ∈ (p.map φ).support at hzp
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hzp
  change z ∈ (q.map φ).support at hzq
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
  rcases hzp with ⟨x', hx', rfl⟩
  rcases hzq with ⟨y', hy', heq⟩
  have hxy : y' = x' := by
    apply Subtype.ext
    change y'.1 = x'.1 at heq
    exact heq
  subst y'
  exact ⟨x', hx', hy'⟩

/-- The four adjacent corner intersections can be witnessed on one chosen
walk for each frame. Each of the four common vertices is therefore attached
to the same pair of side walks that reaches the other corner of that frame. -/
theorem p5_frame_crossings_coherent_adjacent_meet
    (n m : ℕ) (hnm : n + 2 ≤ 6 * m)
    (ω : (squareLattice.induce
      (p5aAnnulusVertexSet n : Set (ℤ × ℤ))).edgeSet → Bool)
    (hTop : p5FrameCrossing n m 0 ω)
    (hBottom : p5FrameCrossing n m 1 ω)
    (hRight : p5FrameCrossing n m 2 ω)
    (hLeft : p5FrameCrossing n m 3 ω) :
    ∃ (top : P5FrameCrossingWalk n m ω 0)
      (bottom : P5FrameCrossingWalk n m ω 1)
      (right : P5FrameCrossingWalk n m ω 2)
      (left : P5FrameCrossingWalk n m ω 3),
      ∃ (zTR zBR zBL zTL :
        (p5aAnnulusVertexSet n : Set (ℤ × ℤ))),
        zTR ∈ top.path.support ∧ zTR ∈ right.path.support ∧
        zBR ∈ bottom.path.support ∧ zBR ∈ right.path.support ∧
        zBL ∈ bottom.path.support ∧ zBL ∈ left.path.support ∧
        zTL ∈ top.path.support ∧ zTL ∈ left.path.support ∧
        zTR.1.1 ∈ Set.Icc ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) ∧
        zTR.1.2 ∈ Set.Icc ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) ∧
        zBR.1.1 ∈ Set.Icc ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) ∧
        zBR.1.2 ∈ Set.Icc (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) ∧
        zBL.1.1 ∈ Set.Icc (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) ∧
        zBL.1.2 ∈ Set.Icc (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) ∧
        zTL.1.1 ∈ Set.Icc (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) ∧
        zTL.1.2 ∈ Set.Icc ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) := by
  rcases p5FrameCrossing_exists_walk n m 0 ω hTop with ⟨top⟩
  rcases p5FrameCrossing_exists_walk n m 1 ω hBottom with ⟨bottom⟩
  rcases p5FrameCrossing_exists_walk n m 2 ω hRight with ⟨right⟩
  rcases p5FrameCrossing_exists_walk n m 3 ω hLeft with ⟨left⟩
  have hnmZ : (n : ℤ) + 2 ≤ 6 * (m : ℤ) := by exact_mod_cast hnm
  have hfit : (n : ℤ) + 2 + 2 * (m : ℤ) ≤ 8 * (m : ℤ) := by
    linarith
  have topBounds : ∀ z ∈ top.path.support,
      z.1.1 ∈ Set.Icc (-(8 * (m : ℤ))) (8 * (m : ℤ)) ∧
      z.1.2 ∈ Set.Icc ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) := by
    intro z hz
    simpa [p5FrameCrossingCorridor] using top.inside z hz
  have bottomBounds : ∀ z ∈ bottom.path.support,
      z.1.1 ∈ Set.Icc (-(8 * (m : ℤ))) (8 * (m : ℤ)) ∧
      z.1.2 ∈ Set.Icc (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) := by
    intro z hz
    simpa [p5FrameCrossingCorridor] using bottom.inside z hz
  have rightBounds : ∀ z ∈ right.path.support,
      z.1.1 ∈ Set.Icc ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) ∧
      z.1.2 ∈ Set.Icc (-(8 * (m : ℤ))) (8 * (m : ℤ)) := by
    intro z hz
    simpa [p5FrameCrossingCorridor] using right.inside z hz
  have leftBounds : ∀ z ∈ left.path.support,
      z.1.1 ∈ Set.Icc (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) ∧
      z.1.2 ∈ Set.Icc (-(8 * (m : ℤ))) (8 * (m : ℤ)) := by
    intro z hz
    simpa [p5FrameCrossingCorridor] using left.inside z hz
  have hTR := horizontal_vertical_open_walks_meet
    (p5aAnnulusVertexSet n) (8 * (m : ℤ))
    ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m)
    ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m)
    (by omega) (by refine ⟨by omega, by omega, by omega, by omega⟩)
    ω top.path right.path topBounds rightBounds
    top.endpoints.1 top.endpoints.2 right.endpoints.1 right.endpoints.2
  have hBR := horizontal_vertical_open_walks_meet
    (p5aAnnulusVertexSet n) (8 * (m : ℤ))
    (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m)
    ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m)
    (by omega) (by refine ⟨by omega, by omega, by omega, by omega⟩)
    ω bottom.path right.path bottomBounds rightBounds
    bottom.endpoints.1 bottom.endpoints.2 right.endpoints.1 right.endpoints.2
  have hBL := horizontal_vertical_open_walks_meet
    (p5aAnnulusVertexSet n) (8 * (m : ℤ))
    (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m)
    (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m)
    (by omega) (by refine ⟨by omega, by omega, by omega, by omega⟩)
    ω bottom.path left.path bottomBounds leftBounds
    bottom.endpoints.1 bottom.endpoints.2 left.endpoints.1 left.endpoints.2
  have hTL := horizontal_vertical_open_walks_meet
    (p5aAnnulusVertexSet n) (8 * (m : ℤ))
    ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m)
    (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m)
    (by omega) (by refine ⟨by omega, by omega, by omega, by omega⟩)
    ω top.path left.path topBounds leftBounds
    top.endpoints.1 top.endpoints.2 left.endpoints.1 left.endpoints.2
  rcases hTR with ⟨zTR, htopTR, hrightTR⟩
  rcases hBR with ⟨zBR, hbottomBR, hrightBR⟩
  rcases hBL with ⟨zBL, hbottomBL, hleftBL⟩
  rcases hTL with ⟨zTL, htopTL, hleftTL⟩
  have hTRx := (rightBounds zTR hrightTR).1
  have hTRy := (topBounds zTR htopTR).2
  have hBRx := (rightBounds zBR hrightBR).1
  have hBRy := (bottomBounds zBR hbottomBR).2
  have hBLx := (leftBounds zBL hleftBL).1
  have hBLy := (bottomBounds zBL hbottomBL).2
  have hTLx := (leftBounds zTL hleftTL).1
  have hTLy := (topBounds zTL htopTL).2
  exact ⟨top, bottom, right, left, zTR, zBR, zBL, zTL,
    htopTR, hrightTR, hbottomBR, hrightBR,
    hbottomBL, hleftBL, htopTL, hleftTL,
    hTRx, hTRy, hBRx, hBRy, hBLx, hBLy, hTLx, hTLy⟩

end PottsContinuity.Thm3.Easy
