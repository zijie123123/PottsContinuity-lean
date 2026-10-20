module

public import PottsContinuity.Thm3.Prop4.TiltedGeometry
public import PottsContinuity.Thm3.Prop4.LocalMinimum

/-!
# The actual lowest top-connected height in each column

DCST, TeX lines 1593–1603 (eq:22 and the local-minimum argument). The
minimum is taken over a proved nonempty finite set of actual connected vertices.
No default height and no boundary-identification path is used.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Actual open graph on all original tilted-strip vertices. -/
def tiltedOpenGraph (n : ℕ) (t : ℝ) (ω : TiltedConfiguration n t) :
    SimpleGraph (tiltedStripVertices n t) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ (tiltedStripGraph n t).edgeSet, ω ⟨e,h⟩ = true}

/-- An original vertex reaches an intrinsic top vertex by an actual open path. -/
def tiltedConnectedToTop (n : ℕ) (t : ℝ) (ω : TiltedConfiguration n t)
    (z : ℤ × ℤ) : Prop :=
  ∃ hz : z ∈ tiltedStripVertices n t, ∃ v : tiltedStripVertices n t,
    tiltedTop n t v.1 ∧ (tiltedOpenGraph n t ω).Reachable ⟨z,hz⟩ v

/-- All top-connected lattice heights in the specified column. -/
noncomputable def topConnectedColumn (n : ℕ) (t : ℝ) (ω : TiltedConfiguration n t)
    (k : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Icc ⌈t*(k : ℝ)⌉ ⌊t*(k : ℝ)+(n : ℝ)⌋).filter
    (fun l => tiltedConnectedToTop n t ω (k,l))

/-- Membership in the finite column is exactly the actual top-connection predicate. -/
theorem mem_topConnectedColumn (n : ℕ) (t : ℝ) (ω : TiltedConfiguration n t)
    (k l : ℤ) : l ∈ topConnectedColumn n t ω k ↔
      tiltedConnectedToTop n t ω (k,l) := by
  classical
  simp only [topConnectedColumn, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact And.right
  · intro h
    obtain ⟨hz, v, hv, hw⟩ := h
    have hlo : t*(k : ℝ) ≤ (l : ℝ) := by
      have hh := hz.1
      dsimp [tiltedHeight] at hh
      linarith only [hh]
    have hhi : (l : ℝ) ≤ t*(k : ℝ)+(n : ℝ) := by
      have hh := hz.2
      dsimp [tiltedHeight] at hh
      linarith only [hh]
    exact ⟨⟨Int.ceil_le.mpr hlo, Int.le_floor.mpr hhi⟩, hz, v, hv, hw⟩

/-- A column is nonempty: its topmost vertex is already connected to itself. -/
theorem topConnectedColumn_nonempty (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration n t) (k : ℤ) : (topConnectedColumn n t ω k).Nonempty := by
  refine ⟨⌊t*(k : ℝ)+(n : ℝ)⌋, (mem_topConnectedColumn _ _ _ _ _).mpr ?_⟩
  have hz := top_column_mem n hn t k
  exact ⟨hz, ⟨_,hz⟩, top_column_isTop n t k, SimpleGraph.Reachable.refl _⟩

/-- The integer coordinate of the actual lowest top-connected vertex. -/
noncomputable def lowestTopConnectedVertex (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration n t) (k : ℤ) : ℤ :=
  (topConnectedColumn n t ω k).min' (topConnectedColumn_nonempty n hn t ω k)

/-- F(k), the source's height above the supporting line. The domain is ℤ. -/
noncomputable def lowestTopConnectedHeight (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration n t) (k : ℤ) : ℝ :=
  (lowestTopConnectedVertex n hn t ω k : ℝ) - t*(k : ℝ)

/-- The chosen vertex genuinely is top-connected. -/
theorem lowestTopConnectedVertex_connected (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration n t) (k : ℤ) :
    tiltedConnectedToTop n t ω (k,lowestTopConnectedVertex n hn t ω k) := by
  apply (mem_topConnectedColumn _ _ _ _ _).mp
  exact Finset.min'_mem _ _

/-- The minimum is no larger than any actual top-connected vertex in its column. -/
theorem lowestTopConnectedVertex_le (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration n t) (k l : ℤ)
    (hl : tiltedConnectedToTop n t ω (k,l)) :
    lowestTopConnectedVertex n hn t ω k ≤ l := by
  exact Finset.min'_le _ _ ((mem_topConnectedColumn _ _ _ _ _).mpr hl)

/-- The source height is in [0,n], for every configuration and column. -/
theorem lowestTopConnectedHeight_mem (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration n t) (k : ℤ) :
    lowestTopConnectedHeight n hn t ω k ∈ Set.Icc (0 : ℝ) n := by
  obtain ⟨hz, _, _, _⟩ := lowestTopConnectedVertex_connected n hn t ω k
  exact hz

/-- If t*m is integral, every lowest height is a nonnegative integer multiple
of 1/m. Negative integral slopes are included. -/
theorem lowestTopConnectedHeight_discrete (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration n t) (m : ℕ) (hm : 1 ≤ m)
    (htm : ∃ a : ℤ, t*(m : ℝ) = a) (k : ℤ) :
    ∃ j : ℕ, lowestTopConnectedHeight n hn t ω k = (j : ℝ)/(m : ℝ) := by
  obtain ⟨a, ha⟩ := htm
  let j : ℤ := lowestTopConnectedVertex n hn t ω k * (m : ℤ) - a*k
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (j : ℝ) = lowestTopConnectedHeight n hn t ω k * (m : ℝ) := by
    dsimp [j, lowestTopConnectedHeight]
    push_cast
    rw [← ha]
    ring
  have hj0 : 0 ≤ j := by
    have h := mul_nonneg (lowestTopConnectedHeight_mem n hn t ω k).1 hmR.le
    rw [← hj] at h
    exact_mod_cast h
  refine ⟨j.toNat, (eq_div_iff hmR.ne').mpr ?_⟩
  rw [← hj]
  exact_mod_cast (Int.toNat_of_nonneg hj0).symm

/-- Actual source local-minimum step at strip height 2n, with the corrected
integer-column domain and the honest integral-slope premise of eq:22. -/
theorem lowestTopConnectedHeight_local_minimum (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (t : ℝ) (htm : ∃ a : ℤ, t*(m : ℝ) = a)
    (ω : TiltedConfiguration (2*n) t)
    (hzero : lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n) :
    ∃ k : ℤ, |k| ≤ (n : ℤ)*(m : ℤ)^2 ∧
      lowestTopConnectedHeight (2*n) (by omega) t ω k ≤ n ∧
      ∀ j : ℤ, |j-k| ≤ (m : ℤ) →
        lowestTopConnectedHeight (2*n) (by omega) t ω k ≤
          lowestTopConnectedHeight (2*n) (by omega) t ω j := by
  exact exists_local_minimum_discrete_height _ n m hm
    (lowestTopConnectedHeight_discrete (2*n) (by omega) t ω m hm htm) hzero

/-- Any top-connected vertex lies at least as high as the lowest height of
its own column. -/
theorem lowestTopConnectedHeight_le_of_connected (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration n t) (z : ℤ × ℤ)
    (hz : tiltedConnectedToTop n t ω z) :
    lowestTopConnectedHeight n hn t ω z.1 ≤ tiltedHeight t z := by
  have h := lowestTopConnectedVertex_le n hn t ω z.1 z.2 hz
  have hR : (lowestTopConnectedVertex n hn t ω z.1 : ℝ) ≤ z.2 := by exact_mod_cast h
  exact sub_le_sub_right hR _

/-- The source local-minimum condition prevents the selected cluster from
reaching any lower tilted height in a neighbouring column. This is the core
no-bottom-exit implication, before restricting to a finite translated window. -/
theorem local_minimum_excludes_lower_cluster (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration n t) (m : ℕ) (k : ℤ)
    (hmin : ∀ j : ℤ, |j-k| ≤ (m : ℤ) →
      lowestTopConnectedHeight n hn t ω k ≤ lowestTopConnectedHeight n hn t ω j)
    (y : tiltedStripVertices n t) (hycol : |y.1.1-k| ≤ (m : ℤ))
    (hylow : tiltedHeight t y.1 < lowestTopConnectedHeight n hn t ω k) :
    ¬ ∃ hx : (k,lowestTopConnectedVertex n hn t ω k) ∈ tiltedStripVertices n t,
      (tiltedOpenGraph n t ω).Reachable
        ⟨(k,lowestTopConnectedVertex n hn t ω k),hx⟩ y := by
  rintro ⟨hx, hxy⟩
  obtain ⟨hx', v, hv, hxv⟩ := lowestTopConnectedVertex_connected n hn t ω k
  have hyTop : tiltedConnectedToTop n t ω y.1 :=
    ⟨y.2, v, hv, hxy.symm.trans hxv⟩
  have hyF := lowestTopConnectedHeight_le_of_connected n hn t ω y.1 hyTop
  have hkF := hmin y.1.1 hycol
  exact (not_le_of_gt hylow) (hkF.trans hyF)

end PottsContinuity.Thm3.Prop4
