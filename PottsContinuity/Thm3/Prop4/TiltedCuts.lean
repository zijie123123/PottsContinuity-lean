module

public import PottsContinuity.Thm3.Prop4.TiltedCandidates

/-!
# Actual horizontal edge cuts in tilted windows

A cut between columns k and k+1 consists of precisely the original horizontal
edges at integer heights present in both columns. The carrier is defined at
every slope and truncation, and has at most n+1 edges.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

noncomputable section

local instance tiltedCutEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _

/-- The literal original edges crossing one consecutive pair of columns. -/
def tiltedWindowCutEdges (n M : ℕ) (t : ℝ) (k : ℤ) :
    Finset (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := by
  classical
  exact Finset.univ.filter (fun e => ∃ y : ℤ,
    Sym2.map Subtype.val e.val = s((k,y),(k+1,y)))

/-- Every cut edge has one uniquely determined integer height. -/
theorem tiltedWindowCutEdges_unique_height (n M : ℕ) (t : ℝ) (k : ℤ)
    (e : {e // e ∈ tiltedWindowCutEdges n M t k}) :
    ∃! y : ℤ, Sym2.map Subtype.val e.val.val = s((k,y),(k+1,y)) := by
  classical
  obtain ⟨y,hy⟩ := (Finset.mem_filter.mp e.2).2
  refine ⟨y,hy,?_⟩
  intro z hz
  rcases Sym2.eq_iff.mp (hz.symm.trans hy) with h | h
  · exact congrArg Prod.snd h.1
  · exact congrArg Prod.snd h.1

/-- The actual row of a horizontal cut edge, selected from proved uniqueness. -/
def tiltedCutHeight (n M : ℕ) (t : ℝ) (k : ℤ)
    (e : {e // e ∈ tiltedWindowCutEdges n M t k}) : ℤ :=
  Classical.choose (tiltedWindowCutEdges_unique_height n M t k e)

/-- Full characterization of the selected row on the whole cut-edge carrier. -/
theorem tiltedCutHeight_spec (n M : ℕ) (t : ℝ) (k : ℤ)
    (e : {e // e ∈ tiltedWindowCutEdges n M t k}) :
    Sym2.map Subtype.val e.val.val =
      s((k,tiltedCutHeight n M t k e),(k+1,tiltedCutHeight n M t k e)) :=
  (Classical.choose_spec (tiltedWindowCutEdges_unique_height n M t k e)).1

private theorem cut_left_mem_window (n M : ℕ) (t : ℝ) (k y : ℤ)
    (e : (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet)
    (he : Sym2.map Subtype.val e.val = s((k,y),(k+1,y))) :
    (k,y) ∈ tiltedWindow n M t := by
  let p := e.val.out
  have hp : s(p.1,p.2) = e.val := Quot.out_eq _
  have hpair : s(p.1.val,p.2.val) = s((k,y),(k+1,y)) := by
    simpa only [← hp,Sym2.map_mk] using he
  rcases Sym2.eq_iff.mp hpair with h | h
  · exact h.1 ▸ p.1.property
  · exact h.2 ▸ p.2.property

/-- A cut edge's row lies in the actual left-column height interval. -/
theorem tiltedCutHeight_mem_interval (n M : ℕ) (t : ℝ) (k : ℤ)
    (e : {e // e ∈ tiltedWindowCutEdges n M t k}) :
    tiltedCutHeight n M t k e ∈ Finset.Icc ⌈t*(k : ℝ)⌉ ⌊t*(k : ℝ)+(n : ℝ)⌋ := by
  have hmem := cut_left_mem_window n M t k _ e.val (tiltedCutHeight_spec n M t k e)
  have hstrip := ((mem_tiltedWindow n M t _).mp hmem).2
  apply Finset.mem_Icc.mpr
  constructor
  · apply Int.ceil_le.mpr
    have h := hstrip.1
    dsimp [tiltedHeight] at h
    linarith only [h]
  · apply Int.le_floor.mpr
    have h := hstrip.2
    dsimp [tiltedHeight] at h
    linarith only [h]

/-- Distinct actual cut edges have distinct rows. -/
theorem tiltedCutHeight_injective (n M : ℕ) (t : ℝ) (k : ℤ) :
    Function.Injective (tiltedCutHeight n M t k) := by
  intro e f h
  apply Subtype.ext
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  rw [tiltedCutHeight_spec,tiltedCutHeight_spec,h]

/-- Uniform width bound for every literal tilted cut, including empty cuts. -/
theorem tiltedWindowCutEdges_card_le (n M : ℕ) (t : ℝ) (k : ℤ) :
    (tiltedWindowCutEdges n M t k).card ≤ n+1 := by
  classical
  let f : {e // e ∈ tiltedWindowCutEdges n M t k} →
      {y // y ∈ Finset.Icc ⌈t*(k : ℝ)⌉ ⌊t*(k : ℝ)+(n : ℝ)⌋} :=
    fun e => ⟨tiltedCutHeight n M t k e,tiltedCutHeight_mem_interval n M t k e⟩
  have hinj : Function.Injective f := fun e g h =>
    tiltedCutHeight_injective n M t k (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hinj
  have hc' : (tiltedWindowCutEdges n M t k).card ≤
      (Finset.Icc ⌈t*(k : ℝ)⌉ ⌊t*(k : ℝ)+(n : ℝ)⌋).card := by simpa using hc
  exact hc'.trans (tilted_column_card_le n (t*(k : ℝ)))

end

end PottsContinuity.Thm3.Prop4
