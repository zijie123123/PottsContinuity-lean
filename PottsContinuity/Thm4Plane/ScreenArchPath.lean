module

public import PottsContinuity.Thm4Plane.GeneralScreenSetup
public import PottsContinuity.PlanarTopology.SubpathExtraction

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC.Medial

/-- The union of the two side screens and the middle connector rectangle. -/
def generalScreenArchFaceBases (n : ℕ) : Finset LatticeVertex :=
  (generalScreenLeftFaceBases n ∪ generalScreenRightFaceBases n) ∪
    generalScreenMiddleFaceBases n

/-- Every dual face center in the three-piece arch carrier is outside the
target rectangle centered at `(0,-16*m)` with radius `m`. Coordinates are
doubled so the half-integer face-center shift stays exact. -/
theorem generalScreenArchFaceCenters_outside_translatedTargetBox (m : ℕ)
    (hm : 1 ≤ m) :
    ∀ z ∈ generalScreenArchFaceBases (16 * m),
      2 * z.1 + 1 < -(2 * (m : ℤ)) ∨
      2 * (m : ℤ) < 2 * z.1 + 1 ∨
      -(30 * (m : ℤ)) < 2 * z.2 + 1 := by
  intro z hz
  have hm0 : 0 < (m : ℤ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  simp only [generalScreenArchFaceBases, Finset.mem_union] at hz
  rcases hz with hzSides | hzMiddle
  · rcases hzSides with hzLeft | hzRight
    · have hcoords := (generalScreenLeftFaceBases_mem_iff
        (16 * m) z.1 z.2).mp hzLeft
      have hleft : z.1 ≤ -(m : ℤ) - 1 := by omega
      left
      omega
    · have hcoords := (generalScreenRightFaceBases_mem_iff
        (16 * m) z.1 z.2).mp hzRight
      have hright : (m : ℤ) ≤ z.1 := by omega
      right
      left
      omega
  · have hcoords := (generalScreenMiddleFaceBases_mem_iff
      (16 * m) z.1 z.2).mp hzMiddle
    have hyMiddle : -(12 * (m : ℤ)) ≤ z.2 := by omega
    right
    right
    omega

private theorem generalScreenActualClosedDualGraph_mono (n : ℕ)
    (A : Configuration (slitBoxGraph n)) {F G : Finset LatticeVertex}
    (hFG : F ⊆ G) :
    generalScreenActualClosedDualGraph n A F ≤
      generalScreenActualClosedDualGraph n A G := by
  intro u v huv
  rcases huv with ⟨d, e, he, hclosed, hdir, huF, hvF⟩
  exact ⟨d, e, he, hclosed, hdir, hFG huF, hFG hvF⟩

private theorem walk_support_pair_reachable
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) {u v : V}
    (hu : u ∈ p.support) (hv : v ∈ p.support) : G.Reachable u v := by
  induction p generalizing u v with
  | nil =>
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu hv
      subst u
      subst v
      exact SimpleGraph.Reachable.rfl
  | @cons a b c hab tail ih =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hu hv
      rcases hu with hu | hu
      · subst u
        rcases hv with hv | hv
        · subst v
          exact SimpleGraph.Reachable.rfl
        · exact hab.reachable.trans (ih (by simp) hv)
      · rcases hv with hv | hv
        · subst v
          exact (ih hu (by simp)).trans hab.reachable.symm
        · exact ih hu hv

/-- The three source crossings in `generalCEvent` concatenate into one actual
closed-dual arch joining the two bottom sides of the finite slit screen.  This
is the deterministic arch existence step before selecting an outermost arch. -/
theorem generalCEvent_implies_bottomDualArch (n : ℕ)
    (A : Configuration (slitBoxGraph n)) (hC : A ∈ generalCEvent n) :
    ∃ lb ∈ generalScreenBottomTerminals n (generalScreenLeftFaceBases n),
    ∃ rb ∈ generalScreenBottomTerminals n (generalScreenRightFaceBases n),
      (generalScreenActualClosedDualGraph n A
        (generalScreenArchFaceBases n)).Reachable lb rb := by
  rcases hC with ⟨lb, hlb, lt, hlt, pL, rb, hrb, rt, hrt, pR,
    u, v, hu, hv, hmid⟩
  have hleftSubset : generalScreenLeftFaceBases n ⊆
      generalScreenArchFaceBases n := by
    intro x hx
    simp only [generalScreenArchFaceBases, Finset.mem_union]
    exact Or.inl (Or.inl hx)
  have hrightSubset : generalScreenRightFaceBases n ⊆
      generalScreenArchFaceBases n := by
    intro x hx
    simp only [generalScreenArchFaceBases, Finset.mem_union]
    exact Or.inl (Or.inr hx)
  have hmiddleSubset : generalScreenMiddleFaceBases n ⊆
      generalScreenArchFaceBases n := by
    intro x hx
    simp only [generalScreenArchFaceBases, Finset.mem_union]
    exact Or.inr hx
  have hleft := generalScreenActualClosedDualGraph_mono n A hleftSubset
  have hright := generalScreenActualClosedDualGraph_mono n A hrightSubset
  have hmiddle := generalScreenActualClosedDualGraph_mono n A hmiddleSubset
  have hleftPath :
      (generalScreenActualClosedDualGraph n A
        (generalScreenArchFaceBases n)).Reachable lb u := by
    have hlocal := walk_support_pair_reachable pL pL.start_mem_support hu
    exact hlocal.mono hleft
  have hrightPath :
      (generalScreenActualClosedDualGraph n A
        (generalScreenArchFaceBases n)).Reachable v rb := by
    have hlocal := walk_support_pair_reachable pR hv pR.start_mem_support
    exact hlocal.mono hright
  have hmiddlePath := hmid.mono hmiddle
  refine ⟨lb, hlb, rb, hrb, ?_⟩
  exact hleftPath.trans (hmiddlePath.trans hrightPath)

/-- The bottom-to-bottom dual arch supplied by `C` can be chosen simple.
This gives the finite path object needed by an exterior-most arch selector,
while retaining the actual closed-edge graph and its rounded screen carrier. -/
theorem generalCEvent_implies_bottomDualSimpleArch (n : ℕ)
    (A : Configuration (slitBoxGraph n)) (hC : A ∈ generalCEvent n) :
    ∃ lb ∈ generalScreenBottomTerminals n (generalScreenLeftFaceBases n),
    ∃ rb ∈ generalScreenBottomTerminals n (generalScreenRightFaceBases n),
    ∃ p : (generalScreenActualClosedDualGraph n A
      (generalScreenArchFaceBases n)).Walk lb rb, p.IsPath := by
  obtain ⟨lb, hlb, rb, hrb, hreach⟩ :=
    generalCEvent_implies_bottomDualArch n A hC
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  exact ⟨lb, hlb, rb, hrb, p, hp⟩

private theorem screenWalk_support_mem_carrier
    (n : ℕ) (A : Configuration (slitBoxGraph n))
    (F : Finset LatticeVertex) {u v : LatticeVertex}
    (p : (generalScreenActualClosedDualGraph n A F).Walk u v)
    (hu : u ∈ F) : ∀ z ∈ p.support, z ∈ F := by
  induction p with
  | nil =>
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact hu
  | @cons u v w hadj tail ih =>
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · rcases hadj with ⟨d, e, he, hclosed, hdir, huF, hvF⟩
        exact huF
      · rcases hadj with ⟨d, e, he, hclosed, hdir, huF, hvF⟩
        exact ih hvF z hz

/-- The simple arch extracted from `C` has its full walk support inside the
union of the source side and connector screens. This carrier statement is
the finite geometric input needed when an exterior-most selector assigns an
interior to the arch. -/
theorem generalCEvent_implies_bottomDualSimpleArch_withinScreen (n : ℕ)
    (A : Configuration (slitBoxGraph n)) (hC : A ∈ generalCEvent n) :
    ∃ lb ∈ generalScreenBottomTerminals n (generalScreenLeftFaceBases n),
    ∃ rb ∈ generalScreenBottomTerminals n (generalScreenRightFaceBases n),
    ∃ p : (generalScreenActualClosedDualGraph n A
      (generalScreenArchFaceBases n)).Walk lb rb,
      p.IsPath ∧ ∀ z ∈ p.support, z ∈ generalScreenArchFaceBases n := by
  obtain ⟨lb, hlb, rb, hrb, p, hp⟩ :=
    generalCEvent_implies_bottomDualSimpleArch n A hC
  have hlbScreen : lb ∈ generalScreenArchFaceBases n := by
    simp only [generalScreenArchFaceBases, Finset.mem_union]
    exact Or.inl (Or.inl hlb.1)
  exact ⟨lb, hlb, rb, hrb, p, hp,
    screenWalk_support_mem_carrier n A _ p hlbScreen⟩

/-- The simple actual closed-dual bottom arch supplied by `C` stays outside
the translated target box in face-center coordinates. This combines the
source screen carrier with its exact half-integer embedding. -/
theorem generalCEvent_implies_bottomDualSimpleArch_outsideTargetBox
    (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (slitBoxGraph (16 * m)))
    (hC : A ∈ generalCEvent (16 * m)) :
    ∃ lb ∈ generalScreenBottomTerminals (16 * m)
        (generalScreenLeftFaceBases (16 * m)),
    ∃ rb ∈ generalScreenBottomTerminals (16 * m)
        (generalScreenRightFaceBases (16 * m)),
    ∃ p : (generalScreenActualClosedDualGraph (16 * m) A
      (generalScreenArchFaceBases (16 * m))).Walk lb rb,
      p.IsPath ∧ ∀ z ∈ p.support,
        2 * z.1 + 1 < -(2 * (m : ℤ)) ∨
        2 * (m : ℤ) < 2 * z.1 + 1 ∨
        -(30 * (m : ℤ)) < 2 * z.2 + 1 := by
  obtain ⟨lb, hlb, rb, hrb, p, hp, hsupport⟩ :=
    generalCEvent_implies_bottomDualSimpleArch_withinScreen (16 * m) A hC
  exact ⟨lb, hlb, rb, hrb, p, hp, fun z hz =>
    generalScreenArchFaceCenters_outside_translatedTargetBox m hm z
      (hsupport z hz)⟩

end PottsContinuity.Thm4Plane
