module

public import PottsContinuity.PD.FK.SubgraphComparison
public import PottsContinuity.PD.Duality.Rectangle
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- Auxiliary square side, leaving room above and to both sides of the source. -/
abbrev sideCollarSize (w h : ℕ) : ℕ := w+h+4

/-- Literal source rectangle embedded two columns inside the auxiliary square. -/
def sideCollarEmbedding (w h : ℕ) :
    RectangleVertex (0,0) w h ↪ RectangleVertex (0,0) (sideCollarSize w h) (sideCollarSize w h) where
  toFun v := ⟨(v.val.1+2,v.val.2),by
    have hv := (mem_latticeRectangle (0,0) v.val w h).mp v.property
    rw [mem_latticeRectangle]
    dsimp [sideCollarSize] at hv ⊢
    constructor <;> constructor <;> omega⟩
  inj' := by
    intro u v huv
    have hx := congrArg (fun z => z.val.1) huv
    have hy := congrArg (fun z => z.val.2) huv
    apply Subtype.ext
    apply Prod.ext
    · change u.val.1+2 = v.val.1+2 at hx
      omega
    · exact hy

/-- The embedding retains every original lattice bond. -/
theorem sideCollarEmbedding_map_le (w h : ℕ) :
    (rectangleGraph (0,0) w h).map (sideCollarEmbedding w h) ≤
      rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro u v huv
  change |u.val.1+2-(v.val.1+2)|+|u.val.2-v.val.2|=1
  change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 at huv
  simpa only [add_sub_add_right_eq_sub] using huv

/-- Fixed open collar: the entire column x=1 and its spokes to the source
left side at heights from zero through h. Every listed bond is auxiliary. -/
def sideCollarOpenEdges (w h : ℕ) :
    Configuration (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)) := by
  classical
  exact Finset.univ.filter fun e => ∃ u v,
    u.val.1 = (1:ℤ) ∧
    (v.val.1 = (1:ℤ) ∨
      (v.val.1 = (2:ℤ) ∧ u.val.2 = v.val.2 ∧ 0 ≤ u.val.2 ∧ u.val.2 ≤ (h:ℤ))) ∧
    e.val = s(u,v)

/-- The deterministic source extension: actual original states, fixed open
collar, and every other auxiliary edge closed. No probability law is changed. -/
def sideCollarExtension (w h : ℕ) (C : Configuration (rectangleGraph (0,0) w h)) :
    Configuration (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)) :=
  embeddedConfigurationEmbedding _ _ (sideCollarEmbedding w h) (sideCollarEmbedding_map_le w h) C ∪
    sideCollarOpenEdges w h

/-- None of the fixed collar bonds is an original source bond. -/
theorem sideCollarOpenEdges_not_source_edge (w h : ℕ)
    (e : (rectangleGraph (0,0) w h).edgeSet) :
    embeddedEdgeEmbedding _ _ (sideCollarEmbedding w h) (sideCollarEmbedding_map_le w h) e ∉
      sideCollarOpenEdges w h := by
  classical
  intro he
  obtain ⟨u,v,hu,_,hpair⟩ := (Finset.mem_filter.mp he).2
  have humem : u ∈ (embeddedEdgeEmbedding _ _ (sideCollarEmbedding w h)
      (sideCollarEmbedding_map_le w h) e).val := by
    rw [hpair]
    exact Sym2.mem_mk_left _ _
  change u ∈ Sym2.map (sideCollarEmbedding w h) e.val at humem
  obtain ⟨a,_,hau⟩ := Sym2.mem_map.mp humem
  have hx := congrArg (fun z => z.val.1) hau
  change a.val.1+2 = u.val.1 at hx
  have ha := (mem_latticeRectangle (0,0) a.val w h).mp a.property
  dsimp at ha
  omega

/-- Reading the embedded source in the collar extension gives exactly the
original configuration, including every originally closed source bond. -/
theorem sideCollarExtension_restriction (w h : ℕ)
    (C : Configuration (rectangleGraph (0,0) w h)) :
    embeddedConfigurationRestriction _ _ (sideCollarEmbedding w h) (sideCollarEmbedding_map_le w h)
      (sideCollarExtension w h C) = C := by
  classical
  ext e
  rw [mem_embeddedConfigurationRestriction]
  have hmap : embeddedEdgeEmbedding _ _ (sideCollarEmbedding w h) (sideCollarEmbedding_map_le w h) e ∈
      embeddedConfigurationEmbedding _ _ (sideCollarEmbedding w h) (sideCollarEmbedding_map_le w h) C ↔ e ∈ C := by
    rw [embeddedConfigurationEmbedding_eq_map]
    exact Finset.mem_map' _
  change _ ∈ _ ∪ sideCollarOpenEdges w h ↔ _
  rw [Finset.mem_union]
  constructor
  · intro he
    rcases he with he | he
    · exact hmap.mp he
    · exact (sideCollarOpenEdges_not_source_edge w h e he).elim
  · intro he
    exact Or.inl (hmap.mpr he)

end
end PottsContinuity.Push
