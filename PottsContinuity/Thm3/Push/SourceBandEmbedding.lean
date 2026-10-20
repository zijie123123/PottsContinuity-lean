module

public import PottsContinuity.Thm3.Push.EmbeddedFirstHitSelector

@[expose] public section

namespace PottsContinuity.Push
open PD.FK

/-- Literal translated rectangle in the original source square. The size
premises guarantee containment; no out-of-band vertex is assigned a value. -/
def sourceBandEmbedding (N a w h : ℕ) (hw : a+w ≤ N) (hh : h ≤ N) :
    RectangleVertex (0,0) w h ↪ RectangleVertex (0,0) N N where
  toFun v := ⟨(v.val.1+(a:ℤ),v.val.2),by
    have hv := (mem_latticeRectangle (0,0) v.val w h).mp v.property
    rw [mem_latticeRectangle]
    dsimp at hv ⊢
    constructor <;> constructor <;> omega⟩
  inj' := by
    intro u v heq
    have hx := congrArg (fun z => z.val.1) heq
    have hy := congrArg (fun z => z.val.2) heq
    apply Subtype.ext
    apply Prod.ext
    · change u.val.1+(a:ℤ)=v.val.1+(a:ℤ) at hx
      omega
    · exact hy

/-- The translated source band retains every original nearest-neighbour bond. -/
theorem sourceBandEmbedding_map_le (N a w h : ℕ) (hw : a+w ≤ N) (hh : h ≤ N) :
    (rectangleGraph (0,0) w h).map (sourceBandEmbedding N a w h hw hh) ≤ rectangleGraph (0,0) N N := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro u v huv
  change |u.val.1+(a:ℤ)-(v.val.1+(a:ℤ))|+|u.val.2-v.val.2|=1
  change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 at huv
  simpa only [add_sub_add_right_eq_sub] using huv

/-- Exactly the original vertices in the stated band lie in its embedding. -/
theorem sourceBandEmbedding_range_iff (N a w h : ℕ) (hw : a+w ≤ N) (hh : h ≤ N)
    (v : RectangleVertex (0,0) N N) :
    v ∈ Set.range (sourceBandEmbedding N a w h hw hh) ↔
      (a:ℤ) ≤ v.val.1 ∧ v.val.1 ≤ a+w ∧ v.val.2 ≤ h := by
  constructor
  · rintro ⟨u,rfl⟩
    have hu := (mem_latticeRectangle (0,0) u.val w h).mp u.property
    change (a:ℤ) ≤ u.val.1+a ∧ u.val.1+a ≤ a+w ∧ u.val.2 ≤ h
    dsimp at hu
    omega
  · rintro ⟨hlo,hhi,hheight⟩
    have hv := (mem_latticeRectangle (0,0) v.val N N).mp v.property
    let u : RectangleVertex (0,0) w h := ⟨(v.val.1-a,v.val.2),by
      rw [mem_latticeRectangle]
      dsimp at hv ⊢
      constructor <;> constructor <;> omega⟩
    refine ⟨u,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change v.val.1-(a:ℤ)+a=v.val.1
      omega
    · rfl

/-- Band restriction is induced on its literal source vertices. -/
theorem sourceBandEmbedding_adj_iff (N a w h : ℕ) (hw : a+w ≤ N) (hh : h ≤ N)
    (u v : RectangleVertex (0,0) w h) :
    (rectangleGraph (0,0) N N).Adj (sourceBandEmbedding N a w h hw hh u)
      (sourceBandEmbedding N a w h hw hh v) ↔ (rectangleGraph (0,0) w h).Adj u v := by
  change |u.val.1+(a:ℤ)-(v.val.1+(a:ℤ))|+|u.val.2-v.val.2|=1 ↔
    |u.val.1-v.val.1|+|u.val.2-v.val.2|=1
  simp only [add_sub_add_right_eq_sub]

end PottsContinuity.Push
