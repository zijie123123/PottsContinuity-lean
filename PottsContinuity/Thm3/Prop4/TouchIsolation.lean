module

public import PottsContinuity.Thm3.Prop4.TranslatedWindow

/-!
# The actual A(x) event and the deterministic local-minimum implication

DCST, TeX lines 1590–1604. A(x) requires an actual connection to the translated
wired arc and that every actual path leaving its window meets that arc.
The proof uses exit edges and the proved no-lower-cluster property, not planar
measure duality or an assumed strip comparison.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The source isolation event in an ambient height-N tilted strip, rooted at x. -/
def tiltedTouchIsolationEvent (N n m : ℕ) (t : ℝ) (ω : TiltedConfiguration N t)
    (x : tiltedStripVertices N t) : Prop :=
  (∃ z : tiltedStripVertices N t, translatedTiltedWired n m t x.1 z.1 ∧
    (tiltedOpenGraph N t ω).Reachable x z) ∧
  ∀ y : tiltedStripVertices N t, y.1 ∉ translatedTiltedWindow n m t x.1 →
    ∀ p : (tiltedOpenGraph N t ω).Walk x y,
      ∃ z ∈ p.support, translatedTiltedWired n m t x.1 z.1

private theorem tiltedOpenGraph_le (N : ℕ) (t : ℝ) (ω : TiltedConfiguration N t) :
    tiltedOpenGraph N t ω ≤ tiltedStripGraph N t := by
  intro u v huv
  change (SimpleGraph.fromEdgeSet _).Adj u v at huv
  rw [SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨he, _⟩, _⟩ := huv
  exact (tiltedStripGraph N t).mem_edgeSet.mp he

/-- Every actual path leaving the translated window meets a wired vertex,
provided the root cluster cannot reach a lower height in the horizontal window. -/
theorem walk_meets_translatedWired_of_noLowerCluster
    (N n m : ℕ) (t : ℝ) (ω : TiltedConfiguration N t)
    (x : tiltedStripVertices N t)
    (hno : ∀ y : tiltedStripVertices N t, |y.1.1-x.1.1| ≤ (m : ℤ) →
      tiltedHeight t y.1 < tiltedHeight t x.1 → ¬(tiltedOpenGraph N t ω).Reachable x y)
    (y : tiltedStripVertices N t) (hy : y.1 ∉ translatedTiltedWindow n m t x.1)
    (p : (tiltedOpenGraph N t ω).Walk x y) :
    ∃ z ∈ p.support, translatedTiltedWired n m t x.1 z.1 := by
  have hwalk : ∀ (u v : tiltedStripVertices N t) (w : (tiltedOpenGraph N t ω).Walk u v),
      (tiltedOpenGraph N t ω).Reachable x u →
      u.1 ∈ translatedTiltedWindow n m t x.1 →
      v.1 ∉ translatedTiltedWindow n m t x.1 →
      ∃ z ∈ w.support, translatedTiltedWired n m t x.1 z.1 := by
    intro u v w
    induction w with
    | nil =>
      intro _ hu hv
      exact (hv hu).elim
    | @cons u v w huv p ih =>
      intro hxu hu hw
      by_cases hv : v.1 ∈ translatedTiltedWindow n m t x.1
      · obtain ⟨z, hz, hzw⟩ := ih (hxu.trans huv.reachable) hv hw
        exact ⟨z, List.mem_cons_of_mem u hz, hzw⟩
      · have huv' : squareLattice.Adj u.1 v.1 := tiltedOpenGraph_le N t ω huv
        rcases translatedTiltedWindow_exit_edge n m t x.1 u.1 v.1 hu hv huv' with
          hwire | ⟨hcol, hlow⟩
        · exact ⟨u, List.mem_cons_self, hwire⟩
        · exact (hno v hcol hlow (hxu.trans huv.reachable)).elim
  exact hwalk x y p (SimpleGraph.Reachable.refl x)
    (mem_translatedTiltedWindow_self n m t x.1) hy

/-- Deterministic A(x) assembly from a genuine top connection and the local
no-lower-cluster property. These are geometric premises, not probability bounds. -/
theorem tiltedTouchIsolationEvent_of_noLowerCluster
    (N n m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (ω : TiltedConfiguration N t) (x : tiltedStripVertices N t)
    (hxheight : tiltedHeight t x.1 + (n : ℝ) ≤ N)
    (hxtop : ∃ v : tiltedStripVertices N t, tiltedTop N t v.1 ∧
      (tiltedOpenGraph N t ω).Reachable x v)
    (hno : ∀ y : tiltedStripVertices N t, |y.1.1-x.1.1| ≤ (m : ℤ) →
      tiltedHeight t y.1 < tiltedHeight t x.1 → ¬(tiltedOpenGraph N t ω).Reachable x y) :
    tiltedTouchIsolationEvent N n m t ω x := by
  classical
  have hpaths := walk_meets_translatedWired_of_noLowerCluster N n m t ω x hno
  refine ⟨?_, hpaths⟩
  obtain ⟨v, hvtop, ⟨p⟩⟩ := hxtop
  by_cases hv : v.1 ∈ translatedTiltedWindow n m t x.1
  · refine ⟨v, ⟨hv, Or.inl ?_⟩, ⟨p⟩⟩
    apply (tiltedTop_iff_height n ht (v.1-x.1)).mpr
    have hvH := (tiltedTop_iff_height N ht v.1).mp hvtop
    rw [tiltedHeight_sub]
    linarith only [hxheight, hvH]
  · obtain ⟨z, hz, hzw⟩ := hpaths v hv p
    exact ⟨z, hzw, ⟨p.takeUntil z hz⟩⟩

/-- Actual local minima in the lower half imply the source's A(x), at the
correct lattice point (k, t*k+F(k)) represented by the minimum integer height. -/
theorem local_minimum_implies_touchIsolation (n m : ℕ) (hn : 1 ≤ n)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (ω : TiltedConfiguration (2*n) t) (k : ℤ)
    (hFk : lowestTopConnectedHeight (2*n) (by omega) t ω k ≤ n)
    (hmin : ∀ j : ℤ, |j-k| ≤ (m : ℤ) →
      lowestTopConnectedHeight (2*n) (by omega) t ω k ≤
        lowestTopConnectedHeight (2*n) (by omega) t ω j) :
    ∃ hx : (k,lowestTopConnectedVertex (2*n) (by omega) t ω k) ∈
        tiltedStripVertices (2*n) t,
      tiltedTouchIsolationEvent (2*n) n m t ω
        ⟨(k,lowestTopConnectedVertex (2*n) (by omega) t ω k),hx⟩ := by
  obtain ⟨hx, v, hv, hxv⟩ := lowestTopConnectedVertex_connected (2*n) (by omega) t ω k
  refine ⟨hx, tiltedTouchIsolationEvent_of_noLowerCluster (2*n) n m t ht ω _ ?_
    ⟨v,hv,hxv⟩ ?_⟩
  · change lowestTopConnectedHeight (2*n) (by omega) t ω k + (n : ℝ) ≤ (2*n : ℕ)
    push_cast
    linarith only [hFk]
  · intro y hycol hylow hxy
    exact local_minimum_excludes_lower_cluster (2*n) (by omega) t ω m k hmin y
      hycol hylow ⟨hx,hxy⟩

end PottsContinuity.Thm3.Prop4
