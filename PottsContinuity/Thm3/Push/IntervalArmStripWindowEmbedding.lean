module

public import PottsContinuity.Thm3.Push.IntervalArmEmbeddedCaseOne
public import PottsContinuity.Thm3.RSW.StripFiniteScaleUniform
public import PottsContinuity.Thm3.RSW.StripEventLimit

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK

/-- Translate the entire source square into the actual infinite strip. -/
def intervalArmStripVertex (n : ℕ) (x : ℤ) (v : RectangleVertex (0,0) (2*n) (2*n)) :
    RSW.stripVertices n :=
  ⟨(x+v.val.1,v.val.2),by
    have hv := (PD.FK.mem_latticeRectangle (0,0) v.val (2*n) (2*n)).mp v.property
    change -(n : ℤ) ≤ v.val.2 ∧ v.val.2 ≤ 3*(n : ℤ)
    dsimp at hv
    omega⟩

/-- The translated square is a literal induced subgraph of the strip. -/
def intervalArmStripGraphEmbedding (n : ℕ) (x : ℤ) :
    rectangleGraph (0,0) (2*n) (2*n) ↪g RSW.stripGraph n where
  toFun := intervalArmStripVertex n x
  inj' := by
    intro u v huv
    have heq := congrArg Subtype.val huv
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    apply Subtype.ext
    apply Prod.ext
    · change x+u.val.1=x+v.val.1 at hx
      omega
    · exact hy
  map_rel_iff' := by
    intro u v
    change |(x+u.val.1)-(x+v.val.1)|+|u.val.2-v.val.2|=1 ↔
      |u.val.1-v.val.1|+|u.val.2-v.val.2|=1
    simp only [add_sub_add_left_eq_sub]

/-- Translate every original square vertex into a containing actual finite
strip window. The bounds guarantee membership on the whole source carrier. -/
def intervalArmStripWindowEmbedding (n m : ℕ) (x : ℤ)
    (hlo : -(m : ℤ) ≤ x) (hhi : x+2*(n : ℤ) ≤ (m : ℤ)) :
    RectangleVertex (0,0) (2*n) (2*n) ↪ (RSW.stripWindow n m : Set LatticeVertex) where
  toFun v := ⟨(x+v.val.1,v.val.2),by
    have hv := (PD.FK.mem_latticeRectangle (0,0) v.val (2*n) (2*n)).mp v.property
    change (x+v.val.1,v.val.2) ∈ RSW.stripWindow n m
    simp only [RSW.stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    constructor <;> constructor <;> dsimp at hv <;> omega⟩
  inj' := by
    intro u v huv
    have heq := congrArg Subtype.val huv
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    apply Subtype.ext
    apply Prod.ext
    · change x+u.val.1=x+v.val.1 at hx
      omega
    · exact hy

/-- The finite-window embedding preserves all original source bonds. -/
theorem intervalArmStripWindow_map_le (n m : ℕ) (x : ℤ)
    (hlo : -(m : ℤ) ≤ x) (hhi : x+2*(n : ℤ) ≤ (m : ℤ)) :
    (rectangleGraph (0,0) (2*n) (2*n)).map (intervalArmStripWindowEmbedding n m x hlo hhi) ≤
      PottsContinuity.squareLattice.induce (RSW.stripWindow n m : Set LatticeVertex) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro u v huv
  change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 at huv
  change |(x+u.val.1)-(x+v.val.1)|+|u.val.2-v.val.2|=1
  simpa only [add_sub_add_left_eq_sub] using huv

end PottsContinuity.Push
