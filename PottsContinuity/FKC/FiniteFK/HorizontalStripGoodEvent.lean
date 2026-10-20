-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripGoodEvent.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalMinimumPath

@[expose] public section

namespace PottsContinuity.FKC.Medial

/-- The literal closed source rectangle inside the actual finite-height strip. -/
def horizontalStripClosedWindow
    (n m : ℕ) (k : ℤ) (h : ℕ) (z : horizontalStripVertex n) : Prop :=
  (z.val.1 - k).natAbs ≤ m ∧
    (h : ℤ) ≤ z.val.2 ∧ z.val.2 ≤ (h + n : ℕ)

/-- The three wired sides: left, right, and top; the bottom remains free. -/
def horizontalStripWiredSide
    (n m : ℕ) (k : ℤ) (h : ℕ) (z : horizontalStripVertex n) : Prop :=
  horizontalStripClosedWindow n m k h z ∧
    (z.val.1 = k - m ∨ z.val.1 = k + m ∨ z.val.2 = (h + n : ℕ))

/-- The literal source clauses before requiring a confined witness path:
there is a global open connection from the fixed x to a wired side, and every
walk from outside the closed rectangle to this same x hits a wired side. -/
def horizontalStripSourceAEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) : Set LatticeConfiguration :=
  {ω | (∃ v : horizontalStripVertex n,
      ∃ p : (horizontalStripOpenGraph n ω).Walk
        (horizontalStripVertexOfNat n k h (by omega)) v,
        horizontalStripWiredSide n m k h v) ∧
    ∀ u : horizontalStripVertex n,
      ¬ horizontalStripClosedWindow n m k h u →
        ∀ p : (horizontalStripOpenGraph n ω).Walk u
          (horizontalStripVertexOfNat n k h (by omega)),
          ∃ z, z ∈ p.support ∧ horizontalStripWiredSide n m k h z}

/-- The fixed-point source event: the chosen x has a confined open connection
 to the wired sides, and every actual strip walk from outside the closed
 rectangle to this same x hits one of those sides. -/
def horizontalStripGoodEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) : Set LatticeConfiguration :=
  {ω | (∃ v : horizontalStripVertex n,
      ∃ p : (horizontalStripOpenGraph n ω).Walk
        (horizontalStripVertexOfNat n k h (by omega)) v,
        horizontalStripWiredSide n m k h v ∧
          ∀ z ∈ p.support, horizontalStripClosedWindow n m k h z) ∧
    ∀ u : horizontalStripVertex n,
      ¬ horizontalStripClosedWindow n m k h u →
        ∀ p : (horizontalStripOpenGraph n ω).Walk u
          (horizontalStripVertexOfNat n k h (by omega)),
          ∃ z, z ∈ p.support ∧ horizontalStripWiredSide n m k h z}

private theorem exists_index_of_mem_take_support
    {V : Type} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (i : ℕ) (hi : i ≤ p.length) {z : V}
    (hz : z ∈ (p.take i).support) :
    ∃ j ≤ i, p.getVert j = z := by
  rw [SimpleGraph.Walk.support_take] at hz
  obtain ⟨j, hj, hzTake⟩ := List.mem_iff_getElem.mp hz
  have hji : j ≤ i := by
    rw [List.length_take] at hj
    omega
  have hzElem : p.support[j]'(by rw [p.length_support]; omega) = z := by
    simpa using hzTake
  refine ⟨j, hji, ?_⟩
  rw [p.getVert_eq_support_getElem (le_trans hji hi)]
  exact hzElem

private theorem horizontalStrip_height_lower_of_path
    (n m : ℕ) (ω : LatticeConfiguration) (k : ℤ)
    (hk : horizontalStripHeight n ω k ≤ 2 * n)
    (hlocal : ∀ l : ℤ, (l - k).natAbs ≤ m →
      horizontalStripHeight n ω k ≤ horizontalStripHeight n ω l)
    {v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n ω).Walk
      (horizontalStripVertexOfNat n k (horizontalStripHeight n ω k) hk) v)
    (hnear : (v.val.1 - k).natAbs ≤ m) :
    (horizontalStripHeight n ω k : ℤ) ≤ v.val.2 := by
  have hy : v.val.2.toNat ≤ 2 * n := by
    have hcast : (v.val.2.toNat : ℤ) = v.val.2 := Int.toNat_of_nonneg v.property.1
    have hbound : (v.val.2.toNat : ℤ) ≤ 2 * (n : ℤ) := by
      rw [hcast]
      exact v.property.2
    exact_mod_cast hbound
  have hv : horizontalStripVertexOfNat n v.val.1 v.val.2.toNat hy = v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Int.toNat_of_nonneg v.property.1
  have hpath : (horizontalStripOpenGraph n ω).Reachable
      (horizontalStripVertexOfNat n k (horizontalStripHeight n ω k) hk)
      (horizontalStripVertexOfNat n v.val.1 v.val.2.toNat hy) := by
    exact ⟨p.copy rfl hv.symm⟩
  have hlow := horizontalStripHeight_le_of_local_minimum_radius
    n m ω k v.val.1 v.val.2.toNat hk hy hnear hlocal hpath
  have hcast : ((v.val.2.toNat : ℕ) : ℤ) = v.val.2 :=
    Int.toNat_of_nonneg v.property.1
  rw [← hcast]
  exact_mod_cast hlow

/-- A least-height local minimum produces the literal fixed-point good event. -/
theorem horizontalStripLocalMinimum_mem_goodEvent
    (n m : ℕ) (ω : LatticeConfiguration) (k : ℤ)
    (hn : 0 < n) (hm : 0 < m)
    (hk : horizontalStripHeight n ω k ≤ n)
    (hlocal : ∀ l : ℤ, (l - k).natAbs ≤ m →
      horizontalStripHeight n ω k ≤ horizontalStripHeight n ω l) :
    ω ∈ horizontalStripGoodEvent n m k
      (horizontalStripHeight n ω k) hk := by
  classical
  change
    (∃ v : horizontalStripVertex n,
      ∃ p : (horizontalStripOpenGraph n ω).Walk
        (horizontalStripVertexOfNat n k (horizontalStripHeight n ω k) (by omega)) v,
        horizontalStripWiredSide n m k (horizontalStripHeight n ω k) v ∧
          ∀ z ∈ p.support,
            horizontalStripClosedWindow n m k (horizontalStripHeight n ω k) z) ∧
    ∀ u : horizontalStripVertex n,
      ¬ horizontalStripClosedWindow n m k (horizontalStripHeight n ω k) u →
        ∀ p : (horizontalStripOpenGraph n ω).Walk u
          (horizontalStripVertexOfNat n k (horizontalStripHeight n ω k) (by omega)),
          ∃ z, z ∈ p.support ∧
            horizontalStripWiredSide n m k (horizontalStripHeight n ω k) z
  constructor
  · obtain ⟨v, p, hsupport, hside⟩ :=
      horizontalStripLocalMinimum_firstExit n m ω k hn hm hk hlocal
    have hvSupport : v ∈ p.support := by
      simpa only [p.getVert_length] using p.getVert_mem_support p.length
    refine ⟨v, p, ?_, ?_⟩
    · exact ⟨hsupport v hvSupport, hside⟩
    · simpa [horizontalStripClosedWindow] using hsupport
  · intro u houtside p
    let q := p.reverse
    have houtsideOpen : ¬ ((u.val.1 - k).natAbs < m ∧
        u.val.2 < (horizontalStripHeight n ω k + n : ℕ)) := by
      intro hopen
      by_cases hnear : (u.val.1 - k).natAbs ≤ m
      · have hlow : (horizontalStripHeight n ω k : ℤ) ≤ u.val.2 :=
          horizontalStrip_height_lower_of_path n m ω k (by omega) hlocal q hnear
        apply houtside
        exact ⟨hnear, hlow, le_of_lt hopen.2⟩
      · exact hnear (Nat.le_of_lt hopen.1)
    obtain ⟨i, hi, hprefix, hside⟩ := horizontalStripLocalMinimum_walk_firstExit
      n m ω k hn hm hk hlocal q houtsideOpen
    let z := q.getVert i
    have hzPrefix : z ∈ (q.take i).support := by
      have hz := (q.take i).getVert_mem_support i
      simp [z]
    have hzWindow : horizontalStripClosedWindow n m k
        (horizontalStripHeight n ω k) z := hprefix z hzPrefix
    have hzq : z ∈ q.support := by
      rw [SimpleGraph.Walk.support_take] at hzPrefix
      exact List.mem_of_mem_take hzPrefix
    have hqsupport : q.support = p.support.reverse := by
      simp [q, SimpleGraph.Walk.support_reverse]
    have hzp : z ∈ p.support := by
      rw [hqsupport] at hzq
      exact List.mem_reverse.mp hzq
    refine ⟨z, hzp, ?_⟩
    exact ⟨hzWindow, hside⟩

/-- The confined-window formulation is equivalent to the literal source
connection plus the universal blocking clause. The blocking clause forces the
initial portion of any global witness connection to stay inside the window. -/
theorem horizontalStripGoodEvent_iff_sourceAEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (ω : LatticeConfiguration) :
    ω ∈ horizontalStripGoodEvent n m k h hh ↔
      ω ∈ horizontalStripSourceAEvent n m k h hh := by
  classical
  change
    ((∃ v : horizontalStripVertex n,
      ∃ p : (horizontalStripOpenGraph n ω).Walk
        (horizontalStripVertexOfNat n k h (by omega)) v,
        horizontalStripWiredSide n m k h v ∧
          ∀ z ∈ p.support, horizontalStripClosedWindow n m k h z) ∧
      ∀ u : horizontalStripVertex n,
        ¬ horizontalStripClosedWindow n m k h u →
          ∀ p : (horizontalStripOpenGraph n ω).Walk u
            (horizontalStripVertexOfNat n k h (by omega)),
            ∃ z, z ∈ p.support ∧ horizontalStripWiredSide n m k h z) ↔
    ((∃ v : horizontalStripVertex n,
      ∃ p : (horizontalStripOpenGraph n ω).Walk
        (horizontalStripVertexOfNat n k h (by omega)) v,
        horizontalStripWiredSide n m k h v) ∧
      ∀ u : horizontalStripVertex n,
        ¬ horizontalStripClosedWindow n m k h u →
          ∀ p : (horizontalStripOpenGraph n ω).Walk u
            (horizontalStripVertexOfNat n k h (by omega)),
            ∃ z, z ∈ p.support ∧ horizontalStripWiredSide n m k h z)
  constructor
  · rintro ⟨⟨v, p, hside, hwindow⟩, hblock⟩
    exact ⟨⟨v, p, hside⟩, hblock⟩
  · rintro ⟨⟨v, p, hside⟩, hblock⟩
    have hfirst : ∃ i : ℕ, horizontalStripWiredSide n m k h (p.getVert i) := by
      refine ⟨p.length, ?_⟩
      simpa only [p.getVert_length] using hside
    let i := Nat.find hfirst
    have hiSide : horizontalStripWiredSide n m k h (p.getVert i) := Nat.find_spec hfirst
    have hiLe : i ≤ p.length := by
      apply Nat.find_min' hfirst
      simpa only [p.getVert_length] using hside
    have hprefixNoSide (j : ℕ) (hji : j < i) :
        ∀ z ∈ (p.take j).support, ¬ horizontalStripWiredSide n m k h z := by
      intro z hz
      obtain ⟨r, hrj, hrz⟩ := exists_index_of_mem_take_support p j
        (le_trans (Nat.le_of_lt hji) hiLe) hz
      have hri : r < i := lt_of_le_of_lt hrj hji
      have hnot := Nat.find_min hfirst hri
      intro hzside
      apply hnot
      simpa [hrz] using hzside
    refine ⟨⟨p.getVert i, p.take i, hiSide, ?_⟩, hblock⟩
    intro z hz
    obtain ⟨j, hji, hzget⟩ := exists_index_of_mem_take_support p i hiLe hz
    by_cases hzside : horizontalStripWiredSide n m k h z
    · exact hzside.1
    have hjlt : j < i := by
      by_contra hnot
      have hji' : j = i := by omega
      have hzi : z = p.getVert i := by rw [← hzget, hji']
      exact hzside (hzi ▸ hiSide)
    let r := (p.take j).reverse.copy hzget rfl
    have hwindow : horizontalStripClosedWindow n m k h z := by
      by_contra houtside
      obtain ⟨w, hwmem, hwside⟩ := hblock z houtside r
      have hnoSide : ∀ w ∈ (p.take j).support,
          ¬ horizontalStripWiredSide n m k h w := hprefixNoSide j hjlt
      have hwmem' : w ∈ (p.take j).support := by
        have hrev : r.support = (p.take j).support.reverse := by
          simp [r, SimpleGraph.Walk.support_reverse]
        rw [hrev] at hwmem
        exact List.mem_reverse.mp hwmem
      exact (hnoSide w hwmem') hwside
    exact hwindow

end PottsContinuity.FKC.Medial
