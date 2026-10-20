-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripWindowGeometry.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripBlockerLocality
public import PottsContinuity.FKC.FiniteFK.HorizontalStripConditionalBoundary
public import PottsContinuity.FKC.Rectangle
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial

noncomputable section

private theorem int_bounds_of_natAbs_le {z : ℤ} {m : ℕ} (hz : z.natAbs ≤ m) :
    -(m : ℤ) ≤ z ∧ z ≤ (m : ℤ) := by
  have hcast : (z.natAbs : ℤ) ≤ (m : ℤ) := by exact_mod_cast hz
  by_cases hz0 : 0 ≤ z
  · have habs : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz0
    constructor <;> omega
  · have hneg : 0 ≤ -z := by omega
    have habs : (z.natAbs : ℤ) = -z := by
      calc
        (z.natAbs : ℤ) = ((-z).natAbs : ℤ) := by simp
        _ = -z := Int.natAbs_of_nonneg hneg
    constructor <;> omega

/-- The literal closed window pulled back to the large finite strip rectangle. -/
def horizontalStripWindowRegion (N n m : ℕ) (k : ℤ) (h : ℕ) :
    Set (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)) :=
  {v | horizontalStripClosedWindow n m k h
    (horizontalStripBlockerRectangleToStrip N n v)}

/-- The literal three wired sides pulled back to the large finite rectangle. -/
def horizontalStripWindowWiredRegion (N n m : ℕ) (k : ℤ) (h : ℕ) :
    Set (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)) :=
  {v | horizontalStripWiredSide n m k h
    (horizontalStripBlockerRectangleToStrip N n v)}

theorem horizontalStripWindowWiredRegion_subset
    (N n m : ℕ) (k : ℤ) (h : ℕ) :
    horizontalStripWindowWiredRegion N n m k h ⊆
      horizontalStripWindowRegion N n m k h := by
  intro v hv
  exact hv.1

/-- The distinguished root vertex of the translated window, viewed in the outer rectangle. -/
def horizontalStripWindowRoot
    (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N) :
    RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
  ⟨(k, (h : ℤ)), by
    rw [mem_latticeRectangle]
    have hklo : -((k.natAbs : ℕ) : ℤ) ≤ k := by
      rw [Int.natCast_natAbs]
      exact neg_abs_le k
    have hkhi : k ≤ ((k.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact le_abs_self k
    dsimp [horizontalStripBlockerCollarRadius] at hN
    have hNcast : (k.natAbs : ℤ) + (m : ℤ) + 1 ≤ (N : ℤ) := by
      exact_mod_cast hN
    constructor
    · constructor <;> omega
    · constructor <;> norm_cast <;> omega⟩

@[simp] theorem horizontalStripWindowRoot_val
    (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N) :
    (horizontalStripWindowRoot N n m k h hh hN).val = (k, (h : ℤ)) := rfl

theorem horizontalStripWindow_root_mem
    (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N) :
    horizontalStripWindowRoot N n m k h hh hN ∈
      horizontalStripWindowRegion N n m k h := by
  change horizontalStripClosedWindow n m k h
    (horizontalStripBlockerRectangleToStrip N n
      (horizontalStripWindowRoot N n m k h hh hN))
  simp [horizontalStripClosedWindow, horizontalStripBlockerRectangleToStrip]


private theorem int_natAbs_le_of_bounds {z : ℤ} {m : ℕ}
    (hlo : -(m : ℤ) ≤ z) (hhi : z ≤ (m : ℤ)) : z.natAbs ≤ m := by
  have hcast : (z.natAbs : ℤ) ≤ (m : ℤ) := by
    by_cases hz : 0 ≤ z
    · rw [Int.natAbs_of_nonneg hz]
      exact hhi
    · have hn : 0 ≤ -z := by omega
      have habs : (z.natAbs : ℤ) = -z := by
        calc
          (z.natAbs : ℤ) = ((-z).natAbs : ℤ) := by simp
          _ = -z := Int.natAbs_of_nonneg hn
      rw [habs]
      have hneg := neg_le_neg hlo
      omega
  exact_mod_cast hcast

/-- Literal coordinate equivalence between the translated closed rectangle
and the pullback of its window vertices in the outer rectangle. -/
def horizontalStripWindowVertexEquiv
    (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N) :
    RectangleVertex (k - (m : ℤ), (h : ℤ)) (2 * m) n ≃
      {v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) //
        v ∈ horizontalStripWindowRegion N n m k h} where
  toFun z := ⟨⟨z.val, by
    rw [mem_latticeRectangle]
    have hz := (mem_latticeRectangle (k - (m : ℤ), (h : ℤ)) z.val (2 * m) n).mp z.property
    have hklo : -((k.natAbs : ℕ) : ℤ) ≤ k := by
      rw [Int.natCast_natAbs]
      exact neg_abs_le k
    have hkhi : k ≤ ((k.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact le_abs_self k
    have hNnat : k.natAbs + m + 1 ≤ N := by
      simpa [horizontalStripBlockerCollarRadius] using hN
    have hNcast : (k.natAbs : ℤ) + (m : ℤ) + 1 ≤ (N : ℤ) := by
      exact_mod_cast hNnat
    constructor
    · constructor <;> omega
    · constructor
      · omega
      · have hheight : (h : ℤ) + (n : ℤ) ≤ 2 * (n : ℤ) := by omega
        have hzupper : z.val.2 ≤ (h : ℤ) + (n : ℤ) := by
          have := hz.2.2
          norm_cast at this
        simpa using le_trans hzupper hheight⟩,
    by
      change horizontalStripClosedWindow n m k h
        (horizontalStripBlockerRectangleToStrip N n ⟨z.val, _⟩)
      rw [horizontalStripClosedWindow, horizontalStripBlockerRectangleToStrip_val]
      have hz := (mem_latticeRectangle (k - (m : ℤ), (h : ℤ)) z.val (2 * m) n).mp z.property
      change ((z.val.1 - k).natAbs ≤ m ∧
        (h : ℤ) ≤ z.val.2 ∧ z.val.2 ≤ ((h + n : ℕ) : ℤ))
      constructor
      · apply int_natAbs_le_of_bounds
        · have hxlo : k - (m : ℤ) ≤ z.val.1 := by
            simpa using hz.1.1
          linarith
        · have hxhi : z.val.1 ≤ k + (m : ℤ) := by
            have htmp := hz.1.2
            change z.val.1 ≤ k - (m : ℤ) + ((2 * m : ℕ) : ℤ) at htmp
            norm_num at htmp
            linarith
          linarith
      · constructor
        · exact_mod_cast hz.2.1
        · have hwidth : (h : ℤ) + (n : ℤ) = ((h + n : ℕ) : ℤ) := by norm_cast
          have hzupper : z.val.2 ≤ (h : ℤ) + (n : ℤ) := by
            have hzup := hz.2.2
            change z.val.2 ≤ (h : ℤ) + ((n : ℕ) : ℤ) at hzup
            exact hzup
          exact hwidth ▸ hzupper⟩
  invFun v := ⟨v.val.val, by
    have hv := v.property
    change horizontalStripClosedWindow n m k h
      (horizontalStripBlockerRectangleToStrip N n v.val) at hv
    rw [horizontalStripClosedWindow, horizontalStripBlockerRectangleToStrip_val] at hv
    rw [mem_latticeRectangle]
    constructor
    · have hb := int_bounds_of_natAbs_le hv.1
      constructor
      · have : -(m : ℤ) ≤ v.val.val.1 - k := hb.1
        omega
      · have : v.val.val.1 - k ≤ (m : ℤ) := hb.2
        omega
    · constructor
      · exact_mod_cast hv.2.1
      · exact_mod_cast hv.2.2⟩
  left_inv := by intro z; apply Subtype.ext; rfl
  right_inv := by intro v; apply Subtype.ext; apply Subtype.ext; rfl

@[simp] theorem horizontalStripWindowVertexEquiv_val
    (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N)
    (v : RectangleVertex (k - (m : ℤ), (h : ℤ)) (2 * m) n) :
    (horizontalStripWindowVertexEquiv N n m k h hh hN v).val.val = v.val := rfl

def horizontalStripWindowGraphIso
    (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N) :
    rectangleGraph (k - (m : ℤ), (h : ℤ)) (2 * m) n ≃g
      (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).induce
        (horizontalStripWindowRegion N n m k h) where
  toEquiv := horizontalStripWindowVertexEquiv N n m k h hh hN
  map_rel_iff' := by
    intro u v
    change squareLattice.Adj u.val v.val ↔ squareLattice.Adj
      (horizontalStripWindowVertexEquiv N n m k h hh hN u).val.val
      (horizontalStripWindowVertexEquiv N n m k h hh hN v).val.val
    simp only [horizontalStripWindowVertexEquiv_val]

theorem horizontalStripWindowWiredRegion_iff_sides
    (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N)
    (v : RectangleVertex (k - (m : ℤ), (h : ℤ)) (2 * m) n) :
    (horizontalStripWindowVertexEquiv N n m k h hh hN v).val ∈
      horizontalStripWindowWiredRegion N n m k h ↔
      v.val ∈ rectangleLeftSide (k - (m : ℤ), (h : ℤ)) (2 * m) n ∪
        rectangleRightSide (k - (m : ℤ), (h : ℤ)) (2 * m) n ∪
        rectangleTopSide (k - (m : ℤ), (h : ℤ)) (2 * m) n := by
  simp only [horizontalStripWindowWiredRegion, Set.mem_ofPred_eq,
    horizontalStripWiredSide, horizontalStripClosedWindow,
    horizontalStripBlockerRectangleToStrip_val,
    horizontalStripWindowVertexEquiv_val]
  simp only [rectangleLeftSide, rectangleRightSide, rectangleTopSide,
    Finset.mem_union, Finset.mem_filter, mem_latticeRectangle]
  have hwidth : k - (m : ℤ) + (2 * m : ℕ) = k + (m : ℤ) := by omega
  have hrect := (mem_latticeRectangle (k - (m : ℤ), (h : ℤ)) v.val (2 * m) n).mp v.property
  have hwindow : (v.val.1 - k).natAbs ≤ m ∧
      (h : ℤ) ≤ v.val.2 ∧ v.val.2 ≤ (h + n : ℕ) := by
    constructor
    · apply int_natAbs_le_of_bounds <;> omega
    · exact ⟨hrect.2.1, hrect.2.2⟩
  omega

theorem horizontalStripTopSides_subset_windowComplement_union_wired
    (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N) :
    horizontalStripTopSidesSet N n ⊆
      (horizontalStripWindowRegion N n m k h)ᶜ ∪
        horizontalStripWindowWiredRegion N n m k h := by
  intro v hv
  simp only [horizontalStripTopSidesSet, Set.mem_ofPred_eq] at hv
  rcases hv with htop | hleft | hright
  · by_cases hwin : v ∈ horizontalStripWindowRegion N n m k h
    · right
      change horizontalStripWiredSide n m k h
        (horizontalStripBlockerRectangleToStrip N n v)
      rw [horizontalStripWiredSide, horizontalStripClosedWindow,
        horizontalStripBlockerRectangleToStrip_val]
      refine ⟨hwin, ?_⟩
      right
      right
      have htop' : v.val.2 = (2 * n : ℤ) := by exact_mod_cast htop
      have hwin' : (h : ℤ) ≤ v.val.2 ∧ v.val.2 ≤ (h + n : ℕ) := by
        change horizontalStripClosedWindow n m k h
          (horizontalStripBlockerRectangleToStrip N n v) at hwin
        simpa [horizontalStripClosedWindow, horizontalStripBlockerRectangleToStrip_val] using hwin.2
      have hupper : (h + n : ℤ) ≤ 2 * (n : ℤ) := by omega
      have hlower : 2 * (n : ℤ) ≤ (h + n : ℤ) := by omega
      omega
    · exact Or.inl hwin
  · exact Or.inl (by
      intro hwin
      have hNcast : (k.natAbs : ℤ) + (m : ℤ) + 1 ≤ (N : ℤ) := by
        have hNnat : k.natAbs + m + 1 ≤ N := by
          simpa [horizontalStripBlockerCollarRadius] using hN
        exact_mod_cast hNnat
      have hklo : -((k.natAbs : ℕ) : ℤ) ≤ k := by
        rw [Int.natCast_natAbs]
        exact neg_abs_le k
      have hwindow : ((v.val.1 - k).natAbs) ≤ m := by
        change horizontalStripClosedWindow n m k h
          (horizontalStripBlockerRectangleToStrip N n v) at hwin
        exact hwin.1
      have hb := int_bounds_of_natAbs_le hwindow
      have hleft' : v.val.1 = -(N : ℤ) := by exact_mod_cast hleft
      rw [hleft'] at hb
      omega)
  · exact Or.inl (by
      intro hwin
      have hNcast : (k.natAbs : ℤ) + (m : ℤ) + 1 ≤ (N : ℤ) := by
        have hNnat : k.natAbs + m + 1 ≤ N := by
          simpa [horizontalStripBlockerCollarRadius] using hN
        exact_mod_cast hNnat
      have hkhi : k ≤ ((k.natAbs : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]
        exact le_abs_self k
      have hwindow : ((v.val.1 - k).natAbs) ≤ m := by
        change horizontalStripClosedWindow n m k h
          (horizontalStripBlockerRectangleToStrip N n v) at hwin
        exact hwin.1
      have hb := int_bounds_of_natAbs_le hwindow
      have hright' : v.val.1 = (N : ℤ) := by exact_mod_cast hright
      rw [hright'] at hb
      omega)

end
end PottsContinuity.FKC.FiniteFK
