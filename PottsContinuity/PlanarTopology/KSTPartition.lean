module

public import PottsContinuity.BD12.KSTEvents
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Tactic

/-! The deterministic partition in the KST cascade argument, with original
connectors transported to contiguous smaller paths in either orientation. -/

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12

/-- Every contiguous subwalk of an open walk is open. -/
theorem kstPathOpen_of_subwalk {u v x y : LatticeVertex}
    {ω : LatticeConfiguration} {p : PD.squareLattice.Walk u v}
    {q : PD.squareLattice.Walk x y} (hq : q.IsSubwalk p)
    (hp : kstPathOpen ω p) : kstPathOpen ω q := by
  intro e he
  exact hp e (hq.edges_subset he)

/-- Reversing a path preserves its actual open edges. -/
theorem kstPathOpen_reverse_iff {u v : LatticeVertex}
    (ω : LatticeConfiguration) (p : PD.squareLattice.Walk u v) :
    kstPathOpen ω p.reverse ↔ kstPathOpen ω p := by
  simp only [kstPathOpen, SimpleGraph.Walk.edges_reverse, List.mem_reverse]

/-- Concatenating two open walks preserves openness. -/
theorem kstPathOpen_append {u v w : LatticeVertex}
    {ω : LatticeConfiguration} (p : PD.squareLattice.Walk u v)
    (q : PD.squareLattice.Walk v w) (hp : kstPathOpen ω p)
    (hq : kstPathOpen ω q) : kstPathOpen ω (p.append q) := by
  intro e he
  rw [SimpleGraph.Walk.edges_append] at he
  exact (List.mem_append.mp he).elim (hp e) (hq e)

/-- If an attached path contains a smaller path in either orientation, its
original side connection can be carried to the smaller path's initial vertex. -/
theorem kstAttached_of_contained_path (n k : ℕ) (left : Bool)
    (ω : LatticeConfiguration) {u v z : LatticeVertex}
    (p : PD.squareLattice.Walk u v) (L : PD.squareLattice.Walk z u)
    (hpOpen : kstPathOpen ω p) (hLOpen : kstPathOpen ω L)
    (hzside : if left then z.1 = -((5*n/4 : ℕ) : ℤ)
      else z.1 = ((5*n/4 : ℕ) : ℤ))
    (hz : |z.2| ≤ (n : ℤ))
    (hL : ∀ x ∈ L.support, 4*|x.1| ≤ 5*(n : ℤ) ∧ |x.2| ≤ (n : ℤ))
    (hp : ∀ x ∈ p.support, 4*|x.1| ≤ 5*(n : ℤ) ∧ |x.2| ≤ (n : ℤ))
    {x y : LatticeVertex} (q : PD.squareLattice.Walk x y)
    (hq : kstMPath k q) (hsub : q.IsSubwalk p ∨ q.reverse.IsSubwalk p) :
    kstAttached n k left ω := by
  classical
  have hxs : x ∈ p.support := by
    rcases hsub with h | h
    · exact h.support_subset q.start_mem_support
    · exact h.support_subset q.reverse.end_mem_support
  have hqs : q.support ⊆ p.support := by
    rcases hsub with h | h
    · exact h.support_subset
    · intro x hx
      apply h.support_subset
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hx
  have hqOpen : kstPathOpen ω q := by
    rcases hsub with h | h
    · exact kstPathOpen_of_subwalk h hpOpen
    · exact (kstPathOpen_reverse_iff ω q).mp (kstPathOpen_of_subwalk h hpOpen)
  let lead := p.takeUntil x hxs
  have hlead : lead.IsSubwalk p :=
    SimpleGraph.Walk.isSubwalk_of_append_left (p.take_spec hxs).symm
  refine ⟨x, y, z, q, L.append lead, hq, hqOpen,
    kstPathOpen_append L lead hLOpen (kstPathOpen_of_subwalk hlead hpOpen),
    hzside, hz, ?_, ?_⟩
  · intro x hx
    rw [SimpleGraph.Walk.mem_support_append_iff] at hx
    exact hx.elim (hL x) (fun hx => hp x (hlead.support_subset hx))
  · intro x hx
    exact hp x (hqs hx)

/-- The exact KST quasi-crossing partition, used in `BD12.wired_kst_cascade_of_kstCorridor`.
This inclusion is deterministic and does not use planar separation. -/
theorem kst_quasi_partition (m l k : ℕ)
    (_hml : l ≤ m) (_hlk : k ≤ l) (_hk : 1 ≤ k) :
    kstQuasiCrossing m l ⊆ kstQuasiCrossing m k ∪ kstAvoidingPath l k := by
  classical
  intro ω hω
  obtain ⟨hleft, hright⟩ := hω
  obtain ⟨u, v, z, p, L, hpM, hpO, hLO, hzS, hz, hL, hp⟩ := hleft
  obtain ⟨u', v', z', p', R, hpM', hpO', hRO, hzS', hz', hR, hp'⟩ := hright
  by_cases hsmall : ∃ x y, ∃ q : PD.squareLattice.Walk x y,
      kstMPath k q ∧ (q.IsSubwalk p ∨ q.reverse.IsSubwalk p)
  · by_cases hsmall' : ∃ x y, ∃ q : PD.squareLattice.Walk x y,
        kstMPath k q ∧ (q.IsSubwalk p' ∨ q.reverse.IsSubwalk p')
    · obtain ⟨x, y, q, hq, hsub⟩ := hsmall
      obtain ⟨x', y', q', hq', hsub'⟩ := hsmall'
      exact Or.inl ⟨
        kstAttached_of_contained_path m k true ω p L hpO hLO hzS hz hL hp q hq hsub,
        kstAttached_of_contained_path m k false ω p' R hpO' hRO hzS' hz' hR hp' q' hq' hsub'⟩
    · exact Or.inr ⟨u', v', p', hpM', hpO', hsmall'⟩
  · exact Or.inr ⟨u, v, p, hpM, hpO, hsmall⟩

end PottsContinuity.PlanarTopology
