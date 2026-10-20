module

public import PottsContinuity.Thm3.Push.SideCollarExtension
public import PottsContinuity.Thm3.Push.EmbeddedFrontierWiring
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- A vertex on the complete fixed auxiliary collar column. -/
def sideCollarColumnVertex (w h : ℕ) (j : Fin (sideCollarSize w h+1)) :
    RectangleVertex (0,0) (sideCollarSize w h) (sideCollarSize w h) :=
  ⟨(1,(j.val:ℤ)),by
    rw [mem_latticeRectangle]
    have hj := j.isLt
    dsimp [sideCollarSize] at hj ⊢
    constructor <;> constructor <;> omega⟩

private theorem column_step (w h : ℕ) (i j : Fin (sideCollarSize w h+1))
    (hij : j.val = i.val+1) :
    (openGraph (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h))
      (sideCollarOpenEdges w h)).Adj (sideCollarColumnVertex w h i) (sideCollarColumnVertex w h j) := by
  classical
  have hadj : (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)).Adj
      (sideCollarColumnVertex w h i) (sideCollarColumnVertex w h j) := by
    change |(1:ℤ)-1|+|(i.val:ℤ)-(j.val:ℤ)|=1
    have hdiff : (i.val:ℤ)-(j.val:ℤ) = -1 := by omega
    rw [hdiff]
    norm_num
  let e : (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)).edgeSet := ⟨s(sideCollarColumnVertex w h i,sideCollarColumnVertex w h j),
    (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)).mem_edgeSet.mpr hadj⟩
  have he : e ∈ sideCollarOpenEdges w h := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,⟨_,_,rfl,Or.inl rfl,rfl⟩⟩
  rw [openGraph_adj]
  exact ⟨e,he,rfl⟩

/-- Every collar-column vertex connects to the auxiliary top by actual fixed
open edges. There is no boundary identification in this connection. -/
theorem sideCollar_column_connects_top (w h : ℕ) (j : Fin (sideCollarSize w h+1)) :
    ActualConnected (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h))
      (sideCollarOpenEdges w h) (sideCollarColumnVertex w h j)
      (sideCollarColumnVertex w h (Fin.last (sideCollarSize w h))) := by
  have hzero : ∀ i : Fin (sideCollarSize w h+1), ActualConnected
      (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h))
      (sideCollarOpenEdges w h) (sideCollarColumnVertex w h 0) (sideCollarColumnVertex w h i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact ⟨.nil⟩
    | succ i ih => exact ih.trans (column_step w h _ _ rfl).reachable
  exact (hzero j).symm.trans (hzero (Fin.last _))

/-- Each original left-side vertex reaches the actual auxiliary top through
its fixed spoke and column, for every original sampled configuration. -/
theorem sideCollar_left_vertex_connects_top (w h : ℕ)
    (C : Configuration (rectangleGraph (0,0) w h))
    (u : RectangleVertex (0,0) w h) (hu : u.val.1 = 0) :
    ActualConnected (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h))
      (sideCollarExtension w h C) (sideCollarEmbedding w h u)
      (sideCollarColumnVertex w h (Fin.last (sideCollarSize w h))) := by
  classical
  have hbox := (mem_latticeRectangle (0,0) u.val w h).mp u.property
  have hy : (u.val.2.toNat:ℤ) = u.val.2 := Int.toNat_of_nonneg hbox.2.1
  let j : Fin (sideCollarSize w h+1) := ⟨u.val.2.toNat,by dsimp [sideCollarSize]; dsimp at hbox; omega⟩
  let z := sideCollarColumnVertex w h j
  have hz : z.val.2 = u.val.2 := hy
  have hadj : (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)).Adj z
      (sideCollarEmbedding w h u) := by
    change |(1:ℤ)-(u.val.1+2)|+|(j.val:ℤ)-u.val.2|=1
    rw [hu,hy]
    norm_num
  let e : (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)).edgeSet := ⟨s(z,sideCollarEmbedding w h u),(rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)).mem_edgeSet.mpr hadj⟩
  have he : e ∈ sideCollarOpenEdges w h := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,⟨z,sideCollarEmbedding w h u,rfl,Or.inr ?_,rfl⟩⟩
    exact ⟨by change u.val.1+2=2; omega,hz,by rw [hz]; exact hbox.2.1,
      by rw [hz]; simpa only [zero_add] using hbox.2.2⟩
  have hopen : (openGraph (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h))
      (sideCollarOpenEdges w h)).Adj z (sideCollarEmbedding w h u) := by
    rw [openGraph_adj]
    exact ⟨e,he,rfl⟩
  exact actualConnected_mono Finset.subset_union_right
    (hopen.reachable.symm.trans (sideCollar_column_connects_top w h j))

/-- Every actual source connection to its left side extends to an actual
auxiliary-top connection, while the original sampled bonds stay unchanged. -/
theorem sideCollar_source_left_connection_implies_top (w h : ℕ)
    (C : Configuration (rectangleGraph (0,0) w h)) (a : RectangleVertex (0,0) w h)
    (hleft : ∃ b : RectangleVertex (0,0) w h, b.val.1 = 0 ∧
      ActualConnected (rectangleGraph (0,0) w h) C a b) :
    ActualConnected (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h))
      (sideCollarExtension w h C) (sideCollarEmbedding w h a)
      (sideCollarColumnVertex w h (Fin.last (sideCollarSize w h))) := by
  obtain ⟨b,hb,hab⟩ := hleft
  exact (actualConnected_mono Finset.subset_union_left
    (actualConnected_embeddedConfiguration _ _ (sideCollarEmbedding w h)
      (sideCollarEmbedding_map_le w h) C hab)).trans (sideCollar_left_vertex_connects_top w h C b hb)

end
end PottsContinuity.Push
