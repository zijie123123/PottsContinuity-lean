module

public import PottsContinuity.Thm3.Prop4.TiltedCuts
public import PottsContinuity.Thm3.Prop4.CutFailure

/-!
# Tilted closed cuts separate actual open paths

The geometric scan bound holds under every finite boundary partition and
at every independent interior parameter, uniformly in the outer truncation.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

noncomputable section

local instance tiltedSeparationEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _

/-- Cuts at distinct column gaps share no actual edge. -/
theorem tiltedWindowCutEdges_disjoint (n M : ℕ) (t : ℝ) (k l : ℤ) (hkl : k ≠ l) :
    Disjoint (tiltedWindowCutEdges n M t k) (tiltedWindowCutEdges n M t l) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hek hel
  obtain ⟨y,hy⟩ := (Finset.mem_filter.mp hek).2
  obtain ⟨z,hz⟩ := (Finset.mem_filter.mp hel).2
  have hpair := hy.symm.trans hz
  rcases Sym2.eq_iff.mp hpair with h | h
  · exact hkl (congrArg Prod.fst h.1)
  · have h1 := congrArg Prod.fst h.1
    have h2 := congrArg Prod.fst h.2
    dsimp at h1 h2
    omega

/-- An original edge crossing from x≤k to x>k belongs to that exact cut. -/
theorem open_edge_crossing_mem_tiltedCut (n M : ℕ) (t : ℝ) (k : ℤ)
    (A : PD.FK.Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))))
    (u v : (tiltedWindow n M t : Set (ℤ × ℤ)))
    (huv : (PD.FK.openGraph _ A).Adj u v) (hu : u.1.1 ≤ k) (hv : k < v.1.1) :
    ∃ e ∈ A, e ∈ tiltedWindowCutEdges n M t k := by
  classical
  obtain ⟨e,he,hval⟩ := (PD.FK.openGraph_adj _ A u v).mp huv
  have hsq : squareLattice.Adj u.val v.val :=
    (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).mem_edgeSet.mp
      (by rw [← hval]; exact e.property)
  change |u.1.1-v.1.1|+|u.1.2-v.1.2|=1 at hsq
  have hux : u.1.1 = k := by simp only [abs_eq_max_neg] at hsq; omega
  have hvx : v.1.1 = k+1 := by simp only [abs_eq_max_neg] at hsq; omega
  have hy : u.1.2 = v.1.2 := by simp only [abs_eq_max_neg] at hsq; omega
  refine ⟨e,he,Finset.mem_filter.mpr ⟨Finset.mem_univ _,u.1.2,?_⟩⟩
  rw [hval,Sym2.map_mk]
  congr 1
  · exact Prod.ext hux rfl
  · exact Prod.ext hvx hy.symm

end

end PottsContinuity.Thm3.Prop4
