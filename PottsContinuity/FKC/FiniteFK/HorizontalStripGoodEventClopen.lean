-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripGoodEventClopen.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripBlockerLocality
public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleClopenEvents
public import Mathlib.Topology.Clopen
public import Mathlib.Tactic

@[expose] public section

open Set Topology
namespace PottsContinuity.FKC.Medial
noncomputable section

open PottsContinuity.FKC.FiniteFK

local instance stripGoodClopenEdgeFintype (M n : ℕ) :
    Fintype (horizontalStripCutRectangle M n).edgeSet := Fintype.ofFinite _
local instance stripGoodClopenEdgeDecidableEq (M n : ℕ) :
    DecidableEq (horizontalStripCutRectangle M n).edgeSet := Classical.decEq _
local instance stripGoodClopenConfigFintype (M n : ℕ) :
    Fintype (PottsContinuity.FKC.FiniteFK.Configuration (horizontalStripCutRectangle M n)) := Fintype.ofFinite _
local instance stripGoodClopenConfigDecidableEq (M n : ℕ) :
    DecidableEq (PottsContinuity.FKC.FiniteFK.Configuration (horizontalStripCutRectangle M n)) := Classical.decEq _

/-- The actual confined source connection, with a strip walk whose full support
stays in the closed source window. -/
def horizontalStripConfinedConnectionEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) : Set LatticeConfiguration :=
  {ω | ∃ v : horizontalStripVertex n,
    horizontalStripWiredSide n m k h v ∧
      ∃ p : (horizontalStripOpenGraph n ω).Walk
        (horizontalStripVertexOfNat n k h (by omega)) v,
        ∀ z ∈ p.support, horizontalStripClosedWindow n m k h z}

/-- The same confined connection on the literal finite rectangle restriction. -/
def horizontalStripRectangleConfinedConnectionEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) :
    Set (PottsContinuity.FKC.FiniteFK.Configuration
      (horizontalStripCutRectangle (horizontalStripBlockerCollarRadius m k) n)) :=
  {A | ∃ v : RectangleVertex
      (-(horizontalStripBlockerCollarRadius m k : ℤ), 0)
      (2 * horizontalStripBlockerCollarRadius m k) (2 * n),
    horizontalStripWiredSide n m k h
      (horizontalStripBlockerRectangleToStrip (horizontalStripBlockerCollarRadius m k) n v) ∧
      ∃ p : (PottsContinuity.FKC.FiniteFK.openGraph
        (horizontalStripCutRectangle (horizontalStripBlockerCollarRadius m k) n) A).Walk
        (horizontalStripBlockerCollarRoot n m k h hh) v,
        ∀ z ∈ p.support,
          horizontalStripClosedWindow n m k h
            (horizontalStripBlockerRectangleToStrip
              (horizontalStripBlockerCollarRadius m k) n z)}

/-- The rectangle-plane version of the confined source connection. -/
def horizontalStripRectanglePlaneConfinedConnectionEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) : Set LatticeConfiguration :=
  {ω | ∃ v : RectangleVertex
      (-(horizontalStripBlockerCollarRadius m k : ℤ), 0)
      (2 * horizontalStripBlockerCollarRadius m k) (2 * n),
    horizontalStripWiredSide n m k h
      (horizontalStripBlockerRectangleToStrip (horizontalStripBlockerCollarRadius m k) n v) ∧
      ∃ p : (horizontalStripRectangleOpenGraph
        (horizontalStripBlockerCollarRadius m k) n ω).Walk
        (horizontalStripBlockerCollarRoot n m k h hh) v,
        ∀ z ∈ p.support,
          horizontalStripClosedWindow n m k h
            (horizontalStripBlockerRectangleToStrip
              (horizontalStripBlockerCollarRadius m k) n z)}

/-- The finite-coordinate event for failure of the universal outside blocker. -/
def horizontalStripRectangleBlockerFailureEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) :
    Set (PottsContinuity.FKC.FiniteFK.Configuration
      (horizontalStripCutRectangle (horizontalStripBlockerCollarRadius m k) n)) :=
  {A | ∃ u : RectangleVertex
      (-(horizontalStripBlockerCollarRadius m k : ℤ), 0)
      (2 * horizontalStripBlockerCollarRadius m k) (2 * n),
    ¬ horizontalStripClosedWindow n m k h
      (horizontalStripBlockerRectangleToStrip
        (horizontalStripBlockerCollarRadius m k) n u) ∧
    ∃ p : (PottsContinuity.FKC.FiniteFK.openGraph
      (horizontalStripCutRectangle (horizontalStripBlockerCollarRadius m k) n) A).Walk
      u (horizontalStripBlockerCollarRoot n m k h hh),
      (∀ z ∈ p.support, ¬ horizontalStripWiredSide n m k h
        (horizontalStripBlockerRectangleToStrip
          (horizontalStripBlockerCollarRadius m k) n z)) ∧
      (∀ z ∈ p.support,
        horizontalStripClosedWindow n m k h
          (horizontalStripBlockerRectangleToStrip
            (horizontalStripBlockerCollarRadius m k) n z) ∨ z = u)}

private theorem support_induce_strip_mem
    {V : Type*} {G : SimpleGraph V} {S : Set V} {u v : V}
    (p : G.Walk u v) (hs : ∀ z ∈ p.support, z ∈ S)
    {z : S} (hz : z ∈ (p.induce S hs).support) : z.val ∈ p.support := by
  have hmap : List.map Subtype.val (p.induce S hs).support = p.support := by
    rw [SimpleGraph.Walk.support_induce]
    simp
  have : z.val ∈ List.map Subtype.val (p.induce S hs).support :=
    List.mem_map.mpr ⟨z, hz, rfl⟩
  simpa [hmap] using this




private theorem goodEventWindow_abs_bound
    (n m : ℕ) (k : ℤ) (h : ℕ) (v : horizontalStripVertex n)
    (hv : horizontalStripClosedWindow n m k h v) :
    |v.val.1| ≤ (k.natAbs : ℤ) + m := by
  have hdist : |v.val.1 - k| ≤ (m : ℤ) := by
    have hc : ((v.val.1 - k).natAbs : ℤ) ≤ (m : ℤ) := by exact_mod_cast hv.1
    rw [Int.natCast_natAbs] at hc
    exact hc
  calc
    |v.val.1| = |(v.val.1 - k) + k| := by congr 1; ring
    _ ≤ |v.val.1 - k| + |k| := abs_add_le _ _
    _ ≤ (m : ℤ) + (k.natAbs : ℤ) := add_le_add hdist (by rw [Int.natCast_natAbs])
    _ = (k.natAbs : ℤ) + m := by ring

private theorem goodEventWindow_x_bound
    (n m : ℕ) (k : ℤ) (h : ℕ) (v : horizontalStripVertex n)
    (hv : horizontalStripClosedWindow n m k h v) :
    horizontalStripBlockerCollarBound n (horizontalStripBlockerCollarRadius m k) v := by
  have hxabs := goodEventWindow_abs_bound n m k h v hv
  have hxlo := (abs_le.mp hxabs).1
  have hxhi := (abs_le.mp hxabs).2
  constructor
  · dsimp [horizontalStripBlockerCollarRadius]
    omega
  · dsimp [horizontalStripBlockerCollarRadius]
    omega

private theorem goodEventCollarIso_root
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (ω : LatticeConfiguration) :
    horizontalStripBlockerCollarGraphIso (horizontalStripBlockerCollarRadius m k) n ω
      (horizontalStripBlockerCollarRoot n m k h hh) =
        horizontalStripBlockerCollarRootOnStrip n m k h hh := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

private theorem horizontalStripConfinedConnectionEvent_iff_rectanglePlane
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (ω : LatticeConfiguration) :
    ω ∈ horizontalStripConfinedConnectionEvent n m k h hh ↔
      ω ∈ horizontalStripRectanglePlaneConfinedConnectionEvent n m k h hh := by
  classical
  let M := horizontalStripBlockerCollarRadius m k
  let I := horizontalStripBlockerCollarGraphIso M n ω
  have hroot : I (horizontalStripBlockerCollarRoot n m k h hh) =
      horizontalStripBlockerCollarRootOnStrip n m k h hh :=
    goodEventCollarIso_root n m k h hh ω
  have hrootInv : I.symm (horizontalStripBlockerCollarRootOnStrip n m k h hh) =
      horizontalStripBlockerCollarRoot n m k h hh := by
    apply I.injective
    simp [hroot]
  constructor
  · rintro ⟨v, hvside, p, hpwindow⟩
    have hvwindow : horizontalStripClosedWindow n m k h v :=
      hpwindow v p.end_mem_support
    have hbound : ∀ z ∈ p.support, horizontalStripBlockerCollarBound n M z := by
      intro z hz
      exact goodEventWindow_x_bound n m k h z (hpwindow z hz)
    have hxwin : horizontalStripClosedWindow n m k h
        (horizontalStripVertexOfNat n k h (by omega)) := by
      simp [horizontalStripClosedWindow, horizontalStripVertexOfNat]
    let pC : (horizontalStripBlockerCollarGraphOnStrip M n ω).Walk
        ⟨horizontalStripVertexOfNat n k h (by omega),
          goodEventWindow_x_bound n m k h
            (horizontalStripVertexOfNat n k h (by omega)) hxwin⟩
        ⟨v, goodEventWindow_x_bound n m k h v hvwindow⟩ := by
      change ((horizontalStripOpenGraph n ω).induce
        {z : horizontalStripVertex n | horizontalStripBlockerCollarBound n M z}).Walk _ _
      exact p.induce _ hbound
    let vC : horizontalStripBlockerCollarSet M n := ⟨v,
      goodEventWindow_x_bound n m k h v hvwindow⟩
    let xC := horizontalStripBlockerCollarRootOnStrip n m k h hh
    have hstart : (⟨horizontalStripVertexOfNat n k h (by omega),
        goodEventWindow_x_bound n m k h
          (horizontalStripVertexOfNat n k h (by omega)) hxwin⟩ :
          horizontalStripBlockerCollarSet M n) = xC := by
      apply Subtype.ext
      rfl
    let pC' := pC.copy hstart (by apply Subtype.ext; rfl)
    let q := pC'.map I.symm.toHom
    let vRect := I.symm vC
    let q' := q.copy hrootInv rfl
    have hside : horizontalStripWiredSide n m k h
        (horizontalStripBlockerRectangleToStrip M n vRect) := by
      have hvEq : horizontalStripBlockerRectangleToStrip M n vRect = v := by
        apply Subtype.ext
        have hvC : I vRect = vC := by simp [vRect]
        simpa [I, horizontalStripBlockerCollarGraphIso,
          horizontalStripBlockerCollarEquiv, horizontalStripBlockerRectangleToCollar] using
          congrArg Subtype.val (congrArg Subtype.val hvC)
      rw [hvEq]
      exact hvside
    have hsupport : ∀ z ∈ q'.support,
        horizontalStripClosedWindow n m k h
          (horizontalStripBlockerRectangleToStrip M n z) := by
      intro z hz
      simp only [q', SimpleGraph.Walk.support_copy, q] at hz
      rw [SimpleGraph.Walk.support_map] at hz
      rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
      have hwC : w ∈ pC.support := by
        have hw' := hw
        dsimp only [pC'] at hw'
        rw [SimpleGraph.Walk.support_copy] at hw'
        exact hw'
      exact hpwindow w.val (support_induce_strip_mem p hbound hwC)
    exact ⟨vRect, hside, q', hsupport⟩
  · rintro ⟨v, hvside, p, hpwindow⟩
    let f := horizontalStripBlockerRectangleToStripHom M n ω
    let q := p.map f
    have hrootMap : f (horizontalStripBlockerCollarRoot n m k h hh) =
        horizontalStripVertexOfNat n k h (by omega) := rfl
    let q' := q.copy hrootMap rfl
    have hsupport : ∀ z ∈ q'.support,
        horizontalStripClosedWindow n m k h z := by
      intro z hz
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hz
      rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
      exact hpwindow w hw
    exact ⟨horizontalStripBlockerRectangleToStrip M n v, hvside, q', hsupport⟩

private theorem horizontalStripRectanglePlaneConfinedConnectionEvent_restriction_iff
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (ω : LatticeConfiguration) :
    ω ∈ horizontalStripRectanglePlaneConfinedConnectionEvent n m k h hh ↔
      horizontalStripRectangleRestriction (horizontalStripBlockerCollarRadius m k) n ω ∈
        horizontalStripRectangleConfinedConnectionEvent n m k h hh := by
  classical
  simp only [horizontalStripRectanglePlaneConfinedConnectionEvent,
    horizontalStripRectangleConfinedConnectionEvent, Set.mem_ofPred_eq]
  rw [horizontalStripRectangleOpenGraph_eq_openGraph_restriction]

def horizontalStripRectanglePlaneBlockerFailureEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) : Set LatticeConfiguration :=
  {ω | ∃ u : RectangleVertex
      (-(horizontalStripBlockerCollarRadius m k : ℤ), 0)
      (2 * horizontalStripBlockerCollarRadius m k) (2 * n),
    ¬ horizontalStripClosedWindow n m k h
      (horizontalStripBlockerRectangleToStrip (horizontalStripBlockerCollarRadius m k) n u) ∧
    ∃ p : (horizontalStripRectangleOpenGraph
      (horizontalStripBlockerCollarRadius m k) n ω).Walk u
      (horizontalStripBlockerCollarRoot n m k h hh),
      (∀ z ∈ p.support, ¬ horizontalStripWiredSide n m k h
        (horizontalStripBlockerRectangleToStrip
          (horizontalStripBlockerCollarRadius m k) n z)) ∧
      (∀ z ∈ p.support,
        horizontalStripClosedWindow n m k h
          (horizontalStripBlockerRectangleToStrip
            (horizontalStripBlockerCollarRadius m k) n z) ∨ z = u)}

private theorem horizontalStripRectanglePlaneBlockerFailureEvent_restriction_iff
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (ω : LatticeConfiguration) :
    ω ∈ horizontalStripRectanglePlaneBlockerFailureEvent n m k h hh ↔
      horizontalStripRectangleRestriction (horizontalStripBlockerCollarRadius m k) n ω ∈
        horizontalStripRectangleBlockerFailureEvent n m k h hh := by
  classical
  simp only [horizontalStripRectanglePlaneBlockerFailureEvent,
    horizontalStripRectangleBlockerFailureEvent, Set.mem_ofPred_eq]
  rw [horizontalStripRectangleOpenGraph_eq_openGraph_restriction]

private theorem stripGoodRestriction_fiber_eq_biInter
    (M n : ℕ) (A : PottsContinuity.FKC.FiniteFK.Configuration (horizontalStripCutRectangle M n)) :
    {ω : LatticeConfiguration | horizontalStripRectangleRestriction M n ω = A} =
      ⋂ e ∈ (Finset.univ : Finset (horizontalStripCutRectangle M n).edgeSet),
        {ω | ω (horizontalStripRectangleOriginalEdge M n e) = decide (e ∈ A)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_univ, true_implies]
  constructor
  · intro h e
    have hm : (ω (horizontalStripRectangleOriginalEdge M n e) = true) ↔ e ∈ A := by
      have hm := congrArg (fun B : Finset (horizontalStripCutRectangle M n).edgeSet => e ∈ B) h
      simpa [horizontalStripRectangleRestriction] using hm
    by_cases hA : e ∈ A
    · have hs := hm.mpr hA
      simp [hA, hs]
    · have hs : ω (horizontalStripRectangleOriginalEdge M n e) ≠ true := fun ht => hA (hm.mp ht)
      cases hb : ω (horizontalStripRectangleOriginalEdge M n e) <;> simp [hb, hA] at hs ⊢
  · intro h
    apply Finset.ext
    intro e
    have he := h e
    simp [horizontalStripRectangleRestriction, he]

private theorem stripGoodRestriction_coordinate_isClopen
    (M n : ℕ) (A : PottsContinuity.FKC.FiniteFK.Configuration (horizontalStripCutRectangle M n))
    (e : (horizontalStripCutRectangle M n).edgeSet) :
    IsClopen {ω : LatticeConfiguration |
      ω (horizontalStripRectangleOriginalEdge M n e) = decide (e ∈ A)} := by
  by_cases hA : e ∈ A
  · have hc : Continuous (fun ω : LatticeConfiguration =>
        ω (horizontalStripRectangleOriginalEdge M n e)) := continuous_apply _
    convert (isClopen_discrete ({true} : Set Bool)).preimage hc using 1; ext ω; simp [hA]
  · have hc : Continuous (fun ω : LatticeConfiguration =>
        ω (horizontalStripRectangleOriginalEdge M n e)) := continuous_apply _
    convert (isClopen_discrete ({false} : Set Bool)).preimage hc using 1; ext ω; simp [hA]

private theorem stripGoodRestriction_fiber_isClopen
    (M n : ℕ) (A : PottsContinuity.FKC.FiniteFK.Configuration (horizontalStripCutRectangle M n)) :
    IsClopen {ω : LatticeConfiguration | horizontalStripRectangleRestriction M n ω = A} := by
  rw [stripGoodRestriction_fiber_eq_biInter]
  apply isClopen_biInter_finset
  intro e he
  exact stripGoodRestriction_coordinate_isClopen M n A e

theorem isClopen_preimage_horizontalStripRectangleRestriction
    (M n : ℕ) (T : Set (PottsContinuity.FKC.FiniteFK.Configuration (horizontalStripCutRectangle M n))) :
    IsClopen {ω : LatticeConfiguration | horizontalStripRectangleRestriction M n ω ∈ T} := by
  classical
  let S : Finset (PottsContinuity.FKC.FiniteFK.Configuration (horizontalStripCutRectangle M n)) :=
    Finset.univ.filter (fun A => A ∈ T)
  have hEq : {ω | horizontalStripRectangleRestriction M n ω ∈ T} =
      ⋃ A ∈ S, {ω | horizontalStripRectangleRestriction M n ω = A} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨horizontalStripRectangleRestriction M n ω, ?_, rfl⟩
      simp [S, h]
    · rintro ⟨A, hA, hω⟩
      have hA' : A ∈ T := by simpa [S] using hA
      simpa [hω] using hA'
  rw [hEq]
  apply isClopen_biUnion_finset
  intro A hA
  exact stripGoodRestriction_fiber_isClopen M n A

private theorem horizontalStripRectanglePlaneBlockerFailureEvent_iff_blockerFailure
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (ω : LatticeConfiguration) :
    ω ∈ horizontalStripRectanglePlaneBlockerFailureEvent n m k h hh ↔
      ω ∈ horizontalStripBlockerFailureEvent n m k h hh := by
  have hplane : ω ∈ horizontalStripRectanglePlaneBlockerFailureEvent n m k h hh ↔
      ω ∈ horizontalStripBlockerCollarFailureEvent n m k h hh := by
    rfl
  rw [hplane,
    horizontalStripBlockerCollarFailureEvent_iff_finiteFailureEvent,
    ← horizontalStripBlockerFailureEvent_iff_finiteFailureEvent]

theorem horizontalStripGoodEvent_iff_restriction_event
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (ω : LatticeConfiguration) :
    ω ∈ horizontalStripGoodEvent n m k h hh ↔
      horizontalStripRectangleRestriction (horizontalStripBlockerCollarRadius m k) n ω ∈
        {A : PottsContinuity.FKC.FiniteFK.Configuration
          (horizontalStripCutRectangle (horizontalStripBlockerCollarRadius m k) n) |
          A ∈ horizontalStripRectangleConfinedConnectionEvent n m k h hh ∧
            A ∉ horizontalStripRectangleBlockerFailureEvent n m k h hh} := by
  classical
  let M := horizontalStripBlockerCollarRadius m k
  have hconf : ω ∈ horizontalStripConfinedConnectionEvent n m k h hh ↔
      horizontalStripRectangleRestriction M n ω ∈
        horizontalStripRectangleConfinedConnectionEvent n m k h hh := by
    rw [horizontalStripConfinedConnectionEvent_iff_rectanglePlane]
    exact horizontalStripRectanglePlaneConfinedConnectionEvent_restriction_iff n m k h hh ω
  have hfail : ω ∈ horizontalStripBlockerFailureEvent n m k h hh ↔
      horizontalStripRectangleRestriction M n ω ∈
        horizontalStripRectangleBlockerFailureEvent n m k h hh := by
    rw [← horizontalStripRectanglePlaneBlockerFailureEvent_iff_blockerFailure]
    exact horizontalStripRectanglePlaneBlockerFailureEvent_restriction_iff n m k h hh ω
  constructor
  · intro hg
    have hsource := (horizontalStripGoodEvent_iff_sourceAEvent n m k h hh ω).mp hg
    have hnotFail := (not_mem_horizontalStripBlockerFailureEvent_iff_blocking
      n m k h hh ω).mpr hsource.2
    have hgConf : ω ∈ horizontalStripConfinedConnectionEvent n m k h hh := by
      rcases hg.1 with ⟨v, p, hvside, hpwindow⟩
      exact ⟨v, hvside, p, hpwindow⟩
    constructor
    · exact hconf.mp hgConf
    · intro hf
      exact hnotFail (hfail.mpr hf)
  · intro he
    apply (horizontalStripGoodEvent_iff_sourceAEvent n m k h hh ω).mpr
    constructor
    · rcases hconf.mpr he.1 with ⟨v, hvside, p, hp⟩
      exact ⟨v, p, hvside⟩
    · apply (not_mem_horizontalStripBlockerFailureEvent_iff_blocking
        n m k h hh ω).mp
      intro hf
      exact he.2 (hfail.mp hf)

theorem isClopen_horizontalStripGoodEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) :
    IsClopen (horizontalStripGoodEvent n m k h hh) := by
  classical
  let M := horizontalStripBlockerCollarRadius m k
  let T : Set (PottsContinuity.FKC.FiniteFK.Configuration (horizontalStripCutRectangle M n)) :=
    {A | A ∈ horizontalStripRectangleConfinedConnectionEvent n m k h hh ∧
      A ∉ horizontalStripRectangleBlockerFailureEvent n m k h hh}
  have hEq : horizontalStripGoodEvent n m k h hh =
      {ω | horizontalStripRectangleRestriction M n ω ∈ T} := by
    ext ω
    simpa [M, T] using horizontalStripGoodEvent_iff_restriction_event n m k h hh ω
  rw [hEq]
  exact isClopen_preimage_horizontalStripRectangleRestriction M n T


theorem isClopen_horizontalStripSourceAEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) :
    IsClopen (horizontalStripSourceAEvent n m k h hh) := by
  have hEq : horizontalStripSourceAEvent n m k h hh =
      horizontalStripGoodEvent n m k h hh := by
    ext ω
    exact (horizontalStripGoodEvent_iff_sourceAEvent n m k h hh ω).symm
  rw [hEq]
  exact isClopen_horizontalStripGoodEvent n m k h hh

end
end PottsContinuity.FKC.Medial
