module

public import PottsContinuity.BD12.KSTEvents
public import PottsContinuity.PD.FK.BoxCylinders
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Measurability and monotonicity of the actual KST path events. -/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK PD.FK.LatticeConfiguration

theorem kstPathOpen_isClopen {u v : LatticeVertex}
    (p : PD.squareLattice.Walk u v) :
    IsClopen {ω | kstPathOpen ω p} := by
  classical
  let F := p.edges.toFinset.subtype (· ∈ PD.squareLattice.edgeSet)
  have heq : {ω | kstPathOpen ω p} = allOpen F := by
    ext ω
    simp [kstPathOpen, allOpen, F]
  rw [heq]
  exact allOpen_isClopen F

/-- Arbitrary geometric restrictions on a walk do not affect openness of its
open-path existence event. No countability of the set of witnesses is needed. -/
theorem kst_open_walk_exists
    (P : ∀ u v : LatticeVertex, PD.squareLattice.Walk u v → Prop) :
    IsOpen {ω | ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      P u v p ∧ kstPathOpen ω p} := by
  simp only [Set.ofPred_exists]
  apply isOpen_iUnion
  intro u
  apply isOpen_iUnion
  intro v
  apply isOpen_iUnion
  intro p
  exact isOpen_const.inter (kstPathOpen_isClopen p).isOpen

theorem kstArm_isOpen (m : ℕ) : IsOpen (kstArm m) := by
  convert kst_open_walk_exists (fun u v p => p.IsPath ∧
    u.2 = (m : ℤ) ∧ v.2 = -(m : ℤ) ∧ 64 * |u.1| ≤ (m : ℤ) ∧
    64 * |v.1| ≤ (m : ℤ) ∧
    ∀ z ∈ p.support, 64 * |z.1| ≤ 65 * (m : ℤ) ∧ |z.2| ≤ (m : ℤ)) using 1
  ext ω
  simp only [kstArm, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, v, p, hp, ho, hrest⟩
    exact ⟨u, v, p, ⟨hp, hrest⟩, ho⟩
  · rintro ⟨u, v, p, ⟨hp, hrest⟩, ho⟩
    exact ⟨u, v, p, hp, ho, hrest⟩

theorem kstBridge_isOpen (m : ℕ) : IsOpen (kstBridge m) := by
  convert kst_open_walk_exists (fun u v p => p.IsPath ∧
    kstBridgeLeft m u ∧ kstBridgeRight m v ∧
    ∀ z ∈ p.support, 12 * |z.1| ≤ 13 * (m : ℤ) ∧ |z.2| ≤ (m : ℤ)) using 1
  ext ω
  simp only [kstBridge, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, v, p, hp, ho, hrest⟩
    exact ⟨u, v, p, ⟨hp, hrest⟩, ho⟩
  · rintro ⟨u, v, p, ⟨hp, hrest⟩, ho⟩
    exact ⟨u, v, p, hp, ho, hrest⟩

theorem kstAvoidingPath_isOpen (l k : ℕ) : IsOpen (kstAvoidingPath l k) := by
  convert kst_open_walk_exists (fun _ _ p => kstMPath l p ∧
    ¬ ∃ x y, ∃ q : PD.squareLattice.Walk x y,
      kstMPath k q ∧ (q.IsSubwalk p ∨ q.reverse.IsSubwalk p)) using 1
  ext ω
  simp only [kstAvoidingPath, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, v, p, hp, ho, hrest⟩
    exact ⟨u, v, p, ⟨hp, hrest⟩, ho⟩
  · rintro ⟨u, v, p, ⟨hp, hrest⟩, ho⟩
    exact ⟨u, v, p, hp, ho, hrest⟩

theorem kstAttached_isOpen (n m : ℕ) (left : Bool) :
    IsOpen {ω | kstAttached n m left ω} := by
  simp only [kstAttached, Set.ofPred_exists]
  apply isOpen_iUnion
  intro u
  apply isOpen_iUnion
  intro v
  apply isOpen_iUnion
  intro z
  apply isOpen_iUnion
  intro p
  apply isOpen_iUnion
  intro L
  simp only [Set.ofPred_and]
  exact isOpen_const.inter ((kstPathOpen_isClopen p).isOpen.inter
    ((kstPathOpen_isClopen L).isOpen.inter
      (isOpen_const.inter (isOpen_const.inter (isOpen_const.inter isOpen_const)))))

theorem kstQuasiCrossing_isOpen (n m : ℕ) : IsOpen (kstQuasiCrossing n m) :=
  (kstAttached_isOpen n m true).inter (kstAttached_isOpen n m false)

theorem kstAttached_mono (n m : ℕ) (left : Bool)
    {ω η : LatticeConfiguration} (hωη : ω ≤ η)
    (hω : kstAttached n m left ω) : kstAttached n m left η := by
  obtain ⟨u, v, z, p, L, hp, ho, hL, hrest⟩ := hω
  exact ⟨u, v, z, p, L, hp, kstPathOpen_mono hωη p ho,
    kstPathOpen_mono hωη L hL, hrest⟩

theorem kstQuasiCrossing_isUpperSet (n m : ℕ) : IsUpperSet (kstQuasiCrossing n m) := by
  intro ω η hωη hω
  exact ⟨kstAttached_mono n m true hωη hω.1,
    kstAttached_mono n m false hωη hω.2⟩

end PottsContinuity.BD12
