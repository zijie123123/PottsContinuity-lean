module

public import PottsContinuity.Thm3.Push.FirstContactTrace

@[expose] public section

namespace PottsContinuity.Push
open PlanarMixed.FiniteSlit

/-- A genuine first-contact prefix has no other target vertex. -/
theorem firstContact_prefix_target_unique {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (S : Set V) (k : ℕ) (hk : IsFirstContact p S k)
    (z : V) (hz : z ∈ (p.take k).support) (hzS : z ∈ S) :
    z = p.getVert k := by
  obtain ⟨j,hj,hjk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hjk' : j ≤ k := hjk.trans (by simp only [SimpleGraph.Walk.take_length]; exact Nat.min_le_left _ _)
  have hjp : p.getVert j = z := by
    simpa only [SimpleGraph.Walk.take_getVert,Nat.min_eq_right hjk'] using hj
  by_cases heq : j = k
  · simpa only [heq] using hjp.symm
  · exact False.elim (hk.2.2 j (lt_of_le_of_ne hjk' heq) (hjp ▸ hzS))

end PottsContinuity.Push
