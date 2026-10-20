module

public import PottsContinuity.BD12.InfiniteRectangleEvents
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# The path events used by KST

Integer inequalities express the source's rational target widths exactly.
Paths are actual nearest-neighbour lattice walks; the distinguished m-paths
are simple. These definitions contain no planar separation assertion.
-/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK PD.RCInfinite

/-- All bonds of a lattice walk are open in the whole-plane state. -/
def kstPathOpen {u v : LatticeVertex} (ω : LatticeConfiguration)
    (p : PD.squareLattice.Walk u v) : Prop :=
  ∀ e : PD.squareLattice.edgeSet, e.val ∈ p.edges → ω e = true

/-- A walk stays in a closed coordinate rectangle. -/
def kstPathIn {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (left right bottom top : ℤ) : Prop :=
  ∀ z ∈ p.support, left ≤ z.1 ∧ z.1 ≤ right ∧ bottom ≤ z.2 ∧ z.2 ≤ top

/-- KST's m-path: beta=1/12, with no rounding ambiguity in its targets. -/
def kstMPath (m : ℕ) {u v : LatticeVertex} (p : PD.squareLattice.Walk u v) : Prop :=
  p.IsPath ∧ u.2 = (m : ℤ) ∧ v.2 = -(m : ℤ) ∧
    12 * |u.1| ≤ (m : ℤ) ∧ 12 * |v.1| ≤ (m : ℤ) ∧
    ∀ z ∈ p.support, 12 * |z.1| ≤ 13 * (m : ℤ) ∧ |z.2| ≤ (m : ℤ)

/-- KST arm event, alpha=1/64. -/
def kstArm (m : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ (u v : LatticeVertex) (p : PD.squareLattice.Walk u v),
    p.IsPath ∧ kstPathOpen ω p ∧ u.2 = (m : ℤ) ∧ v.2 = -(m : ℤ) ∧
      64 * |u.1| ≤ (m : ℤ) ∧ 64 * |v.1| ≤ (m : ℤ) ∧
      ∀ z ∈ p.support, 64 * |z.1| ≤ 65 * (m : ℤ) ∧ |z.2| ≤ (m : ℤ)}

/-- Left bridge target; the central gap has half-width beta*m. -/
def kstBridgeLeft (m : ℕ) (u : LatticeVertex) : Prop :=
  12 * |u.1| ≤ 13 * (m : ℤ) ∧ |u.2| ≤ (m : ℤ) ∧
    12 * u.1 ≤ -(m : ℤ) ∧ (|u.2| = (m : ℤ) ∨ u.1 = -((13 * m / 12 : ℕ) : ℤ))

def kstBridgeRight (m : ℕ) (u : LatticeVertex) : Prop :=
  12 * |u.1| ≤ 13 * (m : ℤ) ∧ |u.2| ≤ (m : ℤ) ∧
    (m : ℤ) ≤ 12 * u.1 ∧ (|u.2| = (m : ℤ) ∨ u.1 = ((13 * m / 12 : ℕ) : ℤ))

/-- Connection between the left and right three-part bridge targets. -/
def kstBridge (m : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ (u v : LatticeVertex) (p : PD.squareLattice.Walk u v),
    p.IsPath ∧ kstPathOpen ω p ∧ kstBridgeLeft m u ∧ kstBridgeRight m v ∧
      ∀ z ∈ p.support, 12 * |z.1| ≤ 13 * (m : ℤ) ∧ |z.2| ≤ (m : ℤ)}

/-- An open m-path with an open connection to one side of the large box.
Connectors may be walks: their actual connectivity has a simple path representative. -/
def kstAttached (n m : ℕ) (left : Bool) (ω : LatticeConfiguration) : Prop :=
  ∃ (u v z : LatticeVertex) (p : PD.squareLattice.Walk u v)
      (l : PD.squareLattice.Walk z u),
    kstMPath m p ∧ kstPathOpen ω p ∧ kstPathOpen ω l ∧
      (if left then z.1 = -((5 * n / 4 : ℕ) : ℤ)
        else z.1 = ((5 * n / 4 : ℕ) : ℤ)) ∧
      |z.2| ≤ (n : ℤ) ∧
      (∀ x ∈ l.support, 4 * |x.1| ≤ 5 * (n : ℤ) ∧ |x.2| ≤ (n : ℤ)) ∧
      (∀ x ∈ p.support, 4 * |x.1| ≤ 5 * (n : ℤ) ∧ |x.2| ≤ (n : ℤ))

/-- Two open m-paths attached to opposite sides at scale n. -/
def kstQuasiCrossing (n m : ℕ) : Set LatticeConfiguration :=
  {ω | kstAttached n m true ω ∧ kstAttached n m false ω}

/-- The increasing event of an open l-path containing no k-path in either direction. -/
def kstAvoidingPath (l k : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ (u v : LatticeVertex) (p : PD.squareLattice.Walk u v),
    kstMPath l p ∧ kstPathOpen ω p ∧
      ¬ ∃ (x y : LatticeVertex) (q : PD.squareLattice.Walk x y),
        kstMPath k q ∧ (q.IsSubwalk p ∨ q.reverse.IsSubwalk p)}

theorem kstPathOpen_mono {u v : LatticeVertex} {ω η : LatticeConfiguration}
    (hωη : ω ≤ η) (p : PD.squareLattice.Walk u v) (hp : kstPathOpen ω p) :
    kstPathOpen η p := by
  intro e he
  exact hωη e (hp e he)

theorem kstArm_isUpperSet (m : ℕ) : IsUpperSet (kstArm m) := by
  rintro ω η hωη ⟨u, v, p, hp, hopen, hrest⟩
  exact ⟨u, v, p, hp, kstPathOpen_mono hωη p hopen, hrest⟩

theorem kstBridge_isUpperSet (m : ℕ) : IsUpperSet (kstBridge m) := by
  rintro ω η hωη ⟨u, v, p, hp, hopen, hrest⟩
  exact ⟨u, v, p, hp, kstPathOpen_mono hωη p hopen, hrest⟩

theorem kstAvoidingPath_isUpperSet (l k : ℕ) : IsUpperSet (kstAvoidingPath l k) := by
  rintro ω η hωη ⟨u, v, p, hp, hopen, hno⟩
  exact ⟨u, v, p, hp, kstPathOpen_mono hωη p hopen, hno⟩

end PottsContinuity.BD12
