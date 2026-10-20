module

public import PottsContinuity.Thm4.SlitCenterLowerBound
public import PottsContinuity.FKC.FiniteFK.SlitBoxFirstHitPathGeometry
public import PottsContinuity.FKC.FiniteFK.SlitBoxBottomCenter
public import PottsContinuity.Foundations.BoxBoundary

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm4Plane

noncomputable section

open PottsContinuity.PD.FK
open PottsContinuity.FKC.FiniteFK

/-- The source event `E` at scale `m`: from `(0,-16m)` the open cluster reaches
the vertex boundary of the box of radius `m` centered at that point. -/
def slitScreenEvent (m : ℕ) :
    Set (PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m))) :=
  {A | ∃ v : SlitBoxVertex (16 * m),
    max |v.val.1| |v.val.2 + (16 * m : ℤ)| = (m : ℤ) ∧
      PottsContinuity.FKC.FiniteFK.ActualConnected
        (slitBoxGraph (16 * m)) A (slitBoxBottomCenterVertex (16 * m)) v}

private theorem int_abs_succ_bounds (z : ℤ) :
    |z| ≤ |z + 1| + 1 ∧ |z + 1| ≤ |z| + 1 := by
  by_cases hz : 0 ≤ z
  · have hz' : 0 ≤ z + 1 := by omega
    rw [abs_of_nonneg hz, abs_of_nonneg hz']
    omega
  · have hz0 : z ≤ 0 := le_of_not_ge hz
    have hz' : z + 1 ≤ 0 := by omega
    rw [abs_of_nonpos hz0, abs_of_nonpos hz']
    omega

private theorem int_abs_adj_bounds {a b : ℤ}
    (h : a + 1 = b ∨ b + 1 = a) :
    |a| ≤ |b| + 1 ∧ |b| ≤ |a| + 1 := by
  rcases h with h | h
  · rw [← h]
    exact int_abs_succ_bounds a
  · rw [← h]
    exact ⟨(int_abs_succ_bounds b).2, (int_abs_succ_bounds b).1⟩

def shiftedRadius (N : ℕ)
    (x : PottsContinuity.FKC.LatticeVertex) : ℤ :=
  max |x.1| |x.2 + (N : ℤ)|

private theorem max_le_add_one_of_components {a b c d : ℤ}
    (ha : a ≤ c + 1) (hb : b ≤ d + 1) :
    max a b ≤ max c d + 1 := by
  apply max_le
  · have hc := le_max_left c d
    omega
  · have hd := le_max_right c d
    omega

private theorem shiftedRadius_adj_bounds (N : ℕ)
    {x y : PottsContinuity.FKC.LatticeVertex}
    (hxy : PottsContinuity.FKC.squareLattice.Adj x y) :
    shiftedRadius N x ≤ shiftedRadius N y + 1 ∧
      shiftedRadius N y ≤ shiftedRadius N x + 1 := by
  rcases (PottsContinuity.FKC.squareLattice_adj_iff x y).mp hxy with
    ⟨horiz | horiz, hy⟩ | ⟨hx, vert | vert⟩
  · simp only [shiftedRadius]
    have habs := int_abs_adj_bounds (Or.inl horiz)
    have hshift : |x.2 + (N : ℤ)| = |y.2 + (N : ℤ)| := by rw [hy]
    constructor
    · apply max_le_add_one_of_components habs.1
      rw [hshift]
      omega
    · apply max_le_add_one_of_components habs.2
      rw [hshift]
      omega
  · simp only [shiftedRadius]
    have habs := int_abs_adj_bounds (Or.inr horiz)
    have hshift : |x.2 + (N : ℤ)| = |y.2 + (N : ℤ)| := by rw [hy]
    constructor
    · apply max_le_add_one_of_components habs.1
      rw [hshift]
      omega
    · apply max_le_add_one_of_components habs.2
      rw [hshift]
      omega
  · simp only [shiftedRadius]
    have habs := int_abs_adj_bounds
      (Or.inl (by omega : x.2 + (N : ℤ) + 1 = y.2 + (N : ℤ)))
    have hfirst : |x.1| = |y.1| := by rw [hx]
    constructor
    · apply max_le_add_one_of_components
      · rw [hfirst]
        omega
      · exact habs.1
    · apply max_le_add_one_of_components
      · rw [hfirst]
        omega
      · exact habs.2
  · simp only [shiftedRadius]
    have habs := int_abs_adj_bounds
      (Or.inr (by omega : y.2 + (N : ℤ) + 1 = x.2 + (N : ℤ)))
    have hfirst : |x.1| = |y.1| := by rw [hx]
    constructor
    · apply max_le_add_one_of_components
      · rw [hfirst]
        omega
      · exact habs.1
    · apply max_le_add_one_of_components
      · rw [hfirst]
        omega
      · exact habs.2

private theorem walk_support_hits_integer_level
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (radius : V → ℤ) (m : ℤ)
    (hstep : ∀ {x y}, G.Adj x y →
      radius x ≤ radius y + 1 ∧ radius y ≤ radius x + 1)
    (hstart : radius u ≤ m) (hend : m ≤ radius v) :
    ∃ x, x ∈ p.support ∧ radius x = m := by
  induction p with
  | @nil u => exact ⟨u, by simp, by omega⟩
  | @cons u v w hadj tail ih =>
      by_cases hu : radius u = m
      · exact ⟨u, by simp, hu⟩
      · have hlt : radius u < m := by omega
        have hnext : radius v ≤ m := by
          have := (hstep hadj).2
          omega
        by_cases hv : radius v = m
        · exact ⟨v, by simp [SimpleGraph.Walk.support_cons], hv⟩
        · have hvlt : radius v < m := by omega
          obtain ⟨x, hx, hxm⟩ := ih (by omega) hend
          exact ⟨x, by simp [SimpleGraph.Walk.support_cons, hx], hxm⟩

/-- A connection from the slit-box bottom center to its wired arc contains an
actual open path that hits the radius-`m` boundary around that center when the
outer slit box has radius `16m`. -/
theorem slitBoxWiredArcConnectionEvent_subset_slitScreenEvent (m : ℕ) :
    slitBoxWiredArcConnectionEvent (16 * m)
        (slitBoxBottomCenterVertex (16 * m)) ⊆ slitScreenEvent m := by
  intro A hA
  obtain ⟨t, ht, p, hp, _hmapPath, _hfirst, _hbox⟩ :=
    slitBoxWiredArcConnectionEvent_firstHit_path_geometry
      (16 * m) A (slitBoxBottomCenterVertex (16 * m)) hA
  let ρ : SlitBoxVertex (16 * m) → ℤ :=
    fun v => shiftedRadius (16 * m) v.val
  have hstep : ∀ {x y},
      (PottsContinuity.FKC.FiniteFK.openGraph
        (slitBoxGraph (16 * m)) A).Adj x y →
        ρ x ≤ ρ y + 1 ∧ ρ y ≤ ρ x + 1 := by
    intro x y hxy
    apply shiftedRadius_adj_bounds (16 * m)
    exact ((slitBoxGraph_adj_iff (16 * m) x y).mp
      (PottsContinuity.FKC.FiniteFK.openGraph_le
        (slitBoxGraph (16 * m)) A hxy)).1
  have hstart : ρ (slitBoxBottomCenterVertex (16 * m)) = 0 := by
    simp [ρ, shiftedRadius, slitBoxBottomCenterVertex_val]
  have htcoords := (mem_slitBoxWiredArc_iff (16 * m) t).mp ht
  have hN : (m : ℤ) ≤ (16 * m : ℤ) := by omega
  have hend : (m : ℤ) ≤ ρ t := by
    dsimp [ρ, shiftedRadius]
    have hy : (m : ℤ) ≤ t.val.2 + (16 * m : ℤ) := by omega
    exact le_trans hy (le_trans (le_abs_self _) (le_max_right _ _))
  obtain ⟨v, hv, hvm⟩ := walk_support_hits_integer_level
    p ρ (m : ℤ) hstep (by omega) hend
  refine ⟨v, ?_, ?_⟩
  · change shiftedRadius (16 * m) v.val = (m : ℤ) at hvm
    simpa [shiftedRadius] using hvm
  · exact (PottsContinuity.FKC.FiniteFK.actualConnected_iff_walk
      (slitBoxGraph (16 * m)) A (slitBoxBottomCenterVertex (16 * m)) v).2
        ⟨p.takeUntil v hv⟩

/-- Lemma 8 implies the first `16m`-scale screen factor on the actual slit
carrier. This is the source's center-to-`∂ₘ` event, expressed through the
translated vertex-boundary equation. -/
theorem slitScreenEvent_probability_lower_bound (q : Set.Icc (1 : ℝ) 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      c / ((16 * m : ℕ) : ℝ)^16 ≤
        (PottsContinuity.PD.FK.measure
          (slitBoxGraph (16 * m))
          (PottsContinuity.Thm4.selfDualParameters ⟨q, q.2.1⟩)
          (PottsContinuity.Thm4.fkcBoundaryToPD
            (slitBoxBoundary (16 * m)))
          (slitScreenEvent m)).toReal := by
  obtain ⟨c, hc, hcenter⟩ :=
    PottsContinuity.Thm4.slit_box_center_arc_polynomial_lower_bound q
  refine ⟨c, hc, ?_⟩
  intro m hm
  have hcenter' := hcenter (16 * m) (by omega)
  let μ := PottsContinuity.PD.FK.measure
    (slitBoxGraph (16 * m))
    (PottsContinuity.Thm4.selfDualParameters ⟨q, q.2.1⟩)
    (PottsContinuity.Thm4.fkcBoundaryToPD (slitBoxBoundary (16 * m)))
  have hsubset := slitBoxWiredArcConnectionEvent_subset_slitScreenEvent m
  have hmono : μ (slitBoxWiredArcConnectionEvent (16 * m)
      (slitBoxBottomCenterVertex (16 * m))) ≤ μ (slitScreenEvent m) :=
    measure_mono hsubset
  have hreal : (μ (slitBoxWiredArcConnectionEvent (16 * m)
      (slitBoxBottomCenterVertex (16 * m)))).toReal ≤ (μ (slitScreenEvent m)).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ _) hmono
  calc
    c / ((16 * m : ℕ) : ℝ)^16 ≤
        (PottsContinuity.Thm4.slitArcConnectionProbability (16 * m)
          ⟨q, q.2.1⟩ (slitBoxBottomCenterVertex (16 * m))) := hcenter'
    _ = (μ (slitBoxWiredArcConnectionEvent (16 * m)
          (slitBoxBottomCenterVertex (16 * m)))).toReal := rfl
    _ ≤ (μ (slitScreenEvent m)).toReal := hreal
    _ = _ := rfl

end
end PottsContinuity.Thm4Plane
