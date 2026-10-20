module

public import PottsContinuity.Thm3.Push.FirstContactSuffix

@[expose] public section

namespace PottsContinuity.Push
open PlanarMixed.FiniteSlit
noncomputable section

/-- The ordered trace through the first target visit, or none if no vertex
of the trace belongs to the target. Both cases retain their literal meaning. -/
def firstContactTrace {V : Type*} (S : Set V) (trace : List V) : Option (List V) := by
  classical
  exact (trace.findIdx? (fun v => decide (v ∈ S))).map (fun k => trace.take (k+1))

/-- The list search agrees with the walk's exact first-contact characterization. -/
theorem firstContactTrace_eq_support_take {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (S : Set V) (k : ℕ) (hk : IsFirstContact p S k) :
    firstContactTrace S p.support = some (p.take k).support := by
  classical
  have hfind : p.support.findIdx? (fun v => decide (v ∈ S)) = some k := by
    apply List.findIdx?_eq_some_iff_getElem.mpr
    refine ⟨by rw [p.length_support]; exact Nat.lt_add_one_of_le hk.1,?_,?_⟩
    · simpa only [SimpleGraph.Walk.support_getElem_eq_getVert,decide_eq_true_eq] using hk.2.1
    · intro j hj
      simpa only [SimpleGraph.Walk.support_getElem_eq_getVert,decide_eq_true_eq] using hk.2.2 j hj
  simp only [firstContactTrace,hfind,Option.map_some,SimpleGraph.Walk.support_take]

/-- Finding a target in the ordered support gives precisely a first contact
on the walk, with its index inside the actual walk length. -/
theorem support_findIdx_some_iff_firstContact {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (S : Set V) (k : ℕ) :
    (by classical exact p.support.findIdx? (fun v => decide (v ∈ S))) = some k ↔
      IsFirstContact p S k := by
  classical
  rw [List.findIdx?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hk,hhit,hprev⟩
    refine ⟨by rw [p.length_support] at hk; omega,?_,?_⟩
    · simpa only [SimpleGraph.Walk.support_getElem_eq_getVert,decide_eq_true_eq] using hhit
    · intro j hj
      simpa only [SimpleGraph.Walk.support_getElem_eq_getVert,decide_eq_true_eq] using hprev j hj
  · intro hk
    refine ⟨by rw [p.length_support]; exact Nat.lt_add_one_of_le hk.1,?_,?_⟩
    · simpa only [SimpleGraph.Walk.support_getElem_eq_getVert,decide_eq_true_eq] using hk.2.1
    · intro j hj
      simpa only [SimpleGraph.Walk.support_getElem_eq_getVert,decide_eq_true_eq] using hk.2.2 j hj

/-- A walk ending in the target has an actual first-contact index and its
canonical trace is the ordered support of exactly that prefix. -/
theorem firstContactTrace_exists_prefix {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (S : Set V) (hb : b ∈ S) :
    ∃ k, IsFirstContact p S k ∧ firstContactTrace S p.support = some (p.take k).support := by
  classical
  have hex : ∃ v, v ∈ p.support ∧ decide (v ∈ S) :=
    ⟨b,p.end_mem_support,by simpa only [decide_eq_true_eq] using hb⟩
  have hfind := List.findIdx?_eq_some_of_exists hex
  have hk := (support_findIdx_some_iff_firstContact p S _).mp hfind
  exact ⟨_,hk,firstContactTrace_eq_support_take p S _ hk⟩

end
end PottsContinuity.Push
