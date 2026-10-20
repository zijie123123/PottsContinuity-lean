module

public import PottsContinuity.PlanarMixed.ActiveBandWindows
public import PottsContinuity.PlanarMixed.GlobalCrosscutSideLabels
public import PottsContinuity.PlanarMixed.SourceCrosscutShapes

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

/-- Literal reference window in the original full Lemma-4 dual square,
with a coordinate swap so the ENTIRE two recorded traces are vertical cuts. -/
def lemma4GlobalWindow (n : ℕ) (hn : 1 ≤ n) (j : Fin 3) :
    RectangleVertex (lemma4CrosscutSquareBase n j) (6*n-1) (6*n-1) ↪
      RectangleVertex (0,0) (112*n+1) (112*n+1) where
  toFun v := ⟨(v.val.2+56*(n:ℤ)+1,v.val.1+56*(n:ℤ)+1),by
    have hv := (mem_latticeRectangle (lemma4CrosscutSquareBase n j) v.val (6*n-1) (6*n-1)).mp v.property
    rw [mem_latticeRectangle]
    fin_cases j <;> norm_num [lemma4CrosscutSquareBase] at hv ⊢ <;> omega⟩
  inj' := by
    intro u v huv
    have h := congrArg Subtype.val huv
    apply Subtype.ext
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at hx hy ⊢ <;> omega

theorem lemma4GlobalWindow_map_le (n : ℕ) (hn : 1 ≤ n) (j : Fin 3) :
    (rectangleGraph (lemma4CrosscutSquareBase n j) (6*n-1) (6*n-1)).map
      (lemma4GlobalWindow n hn j) ≤ rectangleGraph (0,0) (112*n+1) (112*n+1) := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
  change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 at huv
  change |(u.val.2+56*(n:ℤ)+1)-(v.val.2+56*(n:ℤ)+1)|+
    |(u.val.1+56*(n:ℤ)+1)-(v.val.1+56*(n:ℤ)+1)|=1
  have hswap : |u.val.2-v.val.2|+|u.val.1-v.val.1|=1 := by omega
  simpa only [add_sub_add_right_eq_sub] using hswap

section Lemma4
variable (n : ℕ) (hn : 1 ≤ n) (j : Fin 3)
variable (D : SquareCrosscutData (112*n+1))
variable (hfirst : ∀ z ∈ D.first.support, 53*(n:ℤ)+1 ≤ z.val.1)
variable (hsecond : ∀ z ∈ D.second.support, z.val.1 ≤ 59*(n:ℤ))
local notation "g" => lemma4GlobalWindow n hn j
local notation "r" => D.rank ∘ g
local notation "G" => rectangleGraph (lemma4CrosscutSquareBase n j) (6*n-1) (6*n-1)

include hfirst in
/-- Actual lower reference side lies below the ENTIRE original lower trace. -/
theorem lemma4GlobalWindow_bottom_rank (v : RectangleVertex (lemma4CrosscutSquareBase n j) (6*n-1) (6*n-1))
    (hv : v ∈ Square.rectangleDoubleCollarInnerBottom (lemma4CrosscutSquareBase n j) (6*n-1) (6*n-1)) :
    r v ≤ 1 := by
  apply D.rank_le_one_of_x_le_first (53*(n:ℤ)+1) hfirst
  change v.val.2+56*(n:ℤ)+1 ≤ 53*(n:ℤ)+1
  change v.val.2 = -3*(n:ℤ) at hv
  omega

include hsecond in
/-- Actual upper reference side lies above the ENTIRE original upper trace. -/
theorem lemma4GlobalWindow_top_rank (v : RectangleVertex (lemma4CrosscutSquareBase n j) (6*n-1) (6*n-1))
    (hv : v ∈ Square.rectangleDoubleCollarInnerTop (lemma4CrosscutSquareBase n j) (6*n-1) (6*n-1)) :
    3 ≤ r v := by
  apply D.three_le_rank_of_second_x_le (59*(n:ℤ)) hsecond
  change 59*(n:ℤ) ≤ v.val.2+56*(n:ℤ)+1
  change v.val.2 = -3*(n:ℤ)+((6*n-1:ℕ):ℤ) at hv
  omega

include hfirst hsecond in
/-- G2 reference partition comparison with all original trace pieces retained. -/
theorem lemma4GlobalWindow_reference_partition_le
    (B : RemovedConfiguration G
      (subgraphRemovedEdges ((edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)).map
        (rankedBandEmbedding r)) G)) :
    (isolatedExtensionPullbackBoundary (rankedBandEmbedding r)
      (frozenBoundary (twoBlockBoundary
        (Square.rectangleDoubleCollarInnerBottom (lemma4CrosscutSquareBase n j) (6*n-1) (6*n-1))
        (Square.rectangleDoubleCollarInnerTop (lemma4CrosscutSquareBase n j) (6*n-1) (6*n-1))
        (Square.rectangleDoubleCollarInnerBottom_disjoint_top _ _ _ (by omega))) B.val)).partition ≤
      (rankedBandBoundary r).partition :=
  band_active_reference_partition_le G r
    (bandWindow_rank_edges _ _ g (lemma4GlobalWindow_map_le n hn j) D.rank
      (orderedCutRank_edges D.orderedCuts)) _ _ _
    (lemma4GlobalWindow_bottom_rank n hn j D hfirst)
    (lemma4GlobalWindow_top_rank n hn j D hsecond) B

include hfirst hsecond in
/-- G2 actual sampled clipping connects the FULL original traces in R*. -/
theorem lemma4GlobalWindow_reference_crossing_restricts
    (C : Configuration G)
    (hC : C ∈ arcsConnectionEvent G
      (Square.rectangleDoubleCollarInnerBottom (lemma4CrosscutSquareBase n j) (6*n-1) (6*n-1))
      (Square.rectangleDoubleCollarInnerTop (lemma4CrosscutSquareBase n j) (6*n-1) (6*n-1))) :
    embeddedConfigurationRestriction (edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)) G
      (rankedBandEmbedding r) (bandActive_map_le G r) C ∈
        arcsConnectionEvent _ {v | g v.val ∈ D.first.support} {v | g v.val ∈ D.second.support} := by
  have h := band_active_reference_crossing_restricts G r
    (bandWindow_rank_edges _ _ g (lemma4GlobalWindow_map_le n hn j) D.rank
      (orderedCutRank_edges D.orderedCuts)) _ _
    (lemma4GlobalWindow_bottom_rank n hn j D hfirst)
    (lemma4GlobalWindow_top_rank n hn j D hsecond) C hC
  simpa only [rankedBandFirstArc,rankedBandSecondArc,Function.comp_apply,
    D.rank_first_iff,D.rank_second_iff] using h

/-- Correct G2 active inclusion follows from the SAME global labels. -/
theorem lemma4GlobalWindow_active_map_le :
    (edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)).map
      (bandWindowEmbedding g D.rank) ≤
        edgeRestriction (rankedBandGraph (rectangleGraph (0,0) (112*n+1) (112*n+1)) D.rank)
          (bandArcBonds _ D.rank) :=
  bandWindow_active_map_le G _ g (lemma4GlobalWindow_map_le n hn j) D.rank
end Lemma4

/-- The actual general-C window in the original height-(32m+1) square carrier. -/
def generalCGlobalWindow (m : ℕ) (hm : 1 ≤ m) :
    RectangleVertex (-(5*(m:ℤ)),-(12*(m:ℤ))) (10*m-1) (10*m-1) ↪
      RectangleVertex (0,0) (32*m+1) (32*m+1) where
  toFun v := ⟨(v.val.1+5*(m:ℤ),v.val.2+16*(m:ℤ)+1),by
    have hv := (mem_latticeRectangle (-(5*(m:ℤ)),-(12*(m:ℤ))) v.val (10*m-1) (10*m-1)).mp v.property
    rw [mem_latticeRectangle]
    dsimp at hv ⊢
    omega⟩
  inj' := by
    intro u v huv
    have h := congrArg Subtype.val huv
    apply Subtype.ext
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at hx hy ⊢ <;> omega

theorem generalCGlobalWindow_map_le (m : ℕ) (hm : 1 ≤ m) :
    (rectangleGraph (-(5*(m:ℤ)),-(12*(m:ℤ))) (10*m-1) (10*m-1)).map
      (generalCGlobalWindow m hm) ≤ rectangleGraph (0,0) (32*m+1) (32*m+1) := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
  change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 at huv
  change |(u.val.1+5*(m:ℤ))-(v.val.1+5*(m:ℤ))|+
    |(u.val.2+16*(m:ℤ)+1)-(v.val.2+16*(m:ℤ)+1)|=1
  simpa only [add_sub_add_right_eq_sub] using huv

section GeneralC
variable (m : ℕ) (hm : 1 ≤ m) (D : SquareCrosscutData (32*m+1))
variable (hsecond : ∀ z ∈ D.second.support, z.val.1 ≤ 10*(m:ℤ)-1)
local notation "g" => generalCGlobalWindow m hm
local notation "r" => D.rank ∘ g
local notation "a" => (-(5*(m:ℤ)),-(12*(m:ℤ)))
local notation "N" => 10*m-1
local notation "G" => rectangleGraph a N N

/-- G3 left side is the original global left side. -/
theorem generalCGlobalWindow_left_rank (v : RectangleVertex a N N) (hv : v ∈ Square.squareLeftArc a N) :
    r v ≤ 1 := by
  apply D.rank_le_one_of_x_le_first 0
  · intro z hz
    exact (mem_latticeRectangle (0,0) z.val (32*m+1) (32*m+1)).mp z.property |>.1.1
  · change v.val.1+5*(m:ℤ) ≤ 0
    change v.val.1 = -(5*(m:ℤ)) at hv
    omega

include hsecond in
/-- G3 right side is beyond the entire original right trace. -/
theorem generalCGlobalWindow_right_rank (v : RectangleVertex a N N) (hv : v ∈ Square.squareRightArc a N) :
    3 ≤ r v := by
  apply D.three_le_rank_of_second_x_le (10*(m:ℤ)-1) hsecond
  change 10*(m:ℤ)-1 ≤ v.val.1+5*(m:ℤ)
  change v.val.1 = -(5*(m:ℤ))+((10*m-1:ℕ):ℤ) at hv
  omega

include hsecond in
/-- Exact G3 hboundary, with no dropped original trace piece. -/
theorem generalCGlobalWindow_extremalBoundaryComparison :
    ExtremalBoundaryComparison a N (by omega)
      (edgeRestriction (rankedBandGraph G r) (bandArcBonds G r))
      (rankedBandEmbedding r) (rankedBandBoundary r) :=
  band_active_reference_partition_le G r
    (bandWindow_rank_edges _ _ g (generalCGlobalWindow_map_le m hm) D.rank
      (orderedCutRank_edges D.orderedCuts)) _ _ _
    (generalCGlobalWindow_left_rank m hm D)
    (generalCGlobalWindow_right_rank m hm D hsecond)

include hsecond in
/-- Exact G3 hpaths on the full original-trace attachment sets. -/
theorem generalCGlobalWindow_squareCrossingRestrictsToArcs :
    SquareCrossingRestrictsToArcs a N
      (edgeRestriction (rankedBandGraph G r) (bandArcBonds G r))
      (rankedBandEmbedding r) (bandActive_map_le G r)
      {v | g v.val ∈ D.first.support} {v | g v.val ∈ D.second.support} := by
  intro C hC
  simpa only [rankedBandFirstArc,rankedBandSecondArc,Function.comp_apply,
    D.rank_first_iff,D.rank_second_iff] using
    band_active_reference_crossing_restricts G r
      (bandWindow_rank_edges _ _ g (generalCGlobalWindow_map_le m hm) D.rank
        (orderedCutRank_edges D.orderedCuts)) _ _
      (generalCGlobalWindow_left_rank m hm D)
      (generalCGlobalWindow_right_rank m hm D hsecond) C hC

/-- Exact active inclusion for the source general-C window. -/
theorem generalCGlobalWindow_active_map_le :
    (edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)).map
      (bandWindowEmbedding g D.rank) ≤
        edgeRestriction (rankedBandGraph (rectangleGraph (0,0) (32*m+1) (32*m+1)) D.rank)
          (bandArcBonds _ D.rank) :=
  bandWindow_active_map_le G _ g (generalCGlobalWindow_map_le m hm) D.rank
end GeneralC
end
end PottsContinuity.PlanarMixed
