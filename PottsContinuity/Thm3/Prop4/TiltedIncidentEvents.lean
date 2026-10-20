module

public import PottsContinuity.Thm3.Prop4.ArcIsolationLocality
public import PottsContinuity.Thm3.Prop4.TiltedConnectionEvents

/-!
# Finite support and clopenness of tilted-strip isolation

Only the original edges in a one-box collar of the bounded target are needed.
The event still quantifies over every actual escaping walk in the infinite strip.
-/

@[expose] public section

open Topology
namespace PottsContinuity.Thm3.Prop4
noncomputable section
local instance tiltedIncidentEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _

/-- The literal original-edge inclusion of a finite strip window into its infinite strip. -/
def tiltedWindowStripEmbedding (n M : ℕ) (t : ℝ) :
    (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))) ↪g tiltedStripGraph n t where
  toFun z := ⟨z.val,((mem_tiltedWindow n M t z.val).mp z.property).2⟩
  inj' := fun _a _b h => Subtype.ext (congrArg (fun z : tiltedStripVertices n t => z.val) h)
  map_rel_iff' := Iff.rfl

/-- All original strip coordinates sampled in a fixed finite window. -/
def tiltedWindowEdgeCoordinates (n M : ℕ) (t : ℝ) : Finset (tiltedStripGraph n t).edgeSet := by
  classical
  let : Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet :=
    Fintype.ofFinite _
  exact Finset.univ.map (tiltedWindowStripEmbedding n M t).mapEdgeSet

/-- Every event depending on a finite family of original strip edge states is clopen. -/
theorem tilted_isClopen_of_finite_support (n : ℕ) (t : ℝ)
    (F : Finset (tiltedStripGraph n t).edgeSet) (E : Set (TiltedConfiguration n t))
    (hE : ∀ ω η : TiltedConfiguration n t,
      (∀ e ∈ F, ω e = η e) → (ω ∈ E ↔ η ∈ E)) : IsClopen E := by
  let r : TiltedConfiguration n t → (F → Bool) := fun ω e => ω e.val
  have hr : Continuous r := continuous_pi fun _ => continuous_apply _
  have heq : E = r ⁻¹' (r '' E) := by
    ext ω
    constructor
    · exact fun h => ⟨ω,h,rfl⟩
    · rintro ⟨η,hη,hηω⟩
      apply (hE η ω _).mp hη
      intro e he
      exact congrFun hηω ⟨e,he⟩
  rw [heq]
  exact (isClopen_discrete (r '' E)).preimage hr

/-- Every lattice neighbour of the frozen box lies in its one-box collar. -/
theorem neighbour_mem_box_succ (R : ℕ) {u v : ℤ × ℤ}
    (hu : u ∈ box R) (huv : squareLattice.Adj u v) : v ∈ box (R+1) := by
  have hu' := (Foundations.mem_box_iff_interval R u).mp hu
  change |u.1-v.1|+|u.2-v.2|=1 at huv
  apply (Foundations.mem_box_iff_interval (R+1) v).mpr
  simp only [abs_eq_max_neg] at huv
  push_cast
  omega

/-- Agreement on the finite collar determines the entire infinite-strip isolation event. -/
theorem tilted_isolation_finite_support (n : ℕ) (t : ℝ)
    (D W : Set (tiltedStripVertices n t)) (hWD : W ⊆ D)
    (x : tiltedStripVertices n t) (hx : x ∈ D) (R : ℕ)
    (hD : ∀ u ∈ D, u.val ∈ box R)
    (ω η : TiltedConfiguration n t)
    (hagree : ∀ e ∈ tiltedWindowEdgeCoordinates n (R+1) t, ω e = η e) :
    graphArcIsolation (tiltedOpenGraph n t ω) D W x ↔
      graphArcIsolation (tiltedOpenGraph n t η) D W x := by
  apply graphArcIsolation_iff_of_incident_agreement D W hWD x hx
  intro u hu v
  by_cases hbase : (tiltedStripGraph n t).Adj u v
  · have huB : u.val ∈ box (R+1) := by
      have h := (Foundations.mem_box_iff_interval R u.val).mp (hD u hu)
      apply (Foundations.mem_box_iff_interval (R+1) u.val).mpr
      push_cast
      omega
    have hvB := neighbour_mem_box_succ R (hD u hu) hbase
    have huV := (mem_tiltedWindow n (R+1) t u.val).mpr ⟨huB,u.property⟩
    have hvV := (mem_tiltedWindow n (R+1) t v.val).mpr ⟨hvB,v.property⟩
    let e : (squareLattice.induce (tiltedWindow n (R+1) t : Set (ℤ × ℤ))).edgeSet :=
      ⟨s(⟨u.val,huV⟩,⟨v.val,hvV⟩),hbase⟩
    have heq : (tiltedWindowStripEmbedding n (R+1) t).mapEdgeSet e = ⟨s(u,v),hbase⟩ := rfl
    have heF : (⟨s(u,v),hbase⟩ : (tiltedStripGraph n t).edgeSet) ∈
        tiltedWindowEdgeCoordinates n (R+1) t := by
      change _ ∈ Finset.univ.map _
      exact Finset.mem_map.mpr ⟨e,Finset.mem_univ _,heq⟩
    have hstate := hagree _ heF
    simp only [tiltedOpenGraph_adj_iff]
    exact ⟨fun ⟨h,hω⟩ => ⟨h,by rw [← hstate]; exact hω⟩,
      fun ⟨h,hη⟩ => ⟨h,by rw [hstate]; exact hη⟩⟩
  · simp only [tiltedOpenGraph_adj_iff]
    exact ⟨fun ⟨h,_⟩ => False.elim (hbase h),fun ⟨h,_⟩ => False.elim (hbase h)⟩

/-- The source isolation predicate on a bounded target is a clopen cylinder event. -/
theorem isClopen_tilted_graphArcIsolation (n : ℕ) (t : ℝ)
    (D W : Set (tiltedStripVertices n t)) (hWD : W ⊆ D)
    (x : tiltedStripVertices n t) (hx : x ∈ D) (R : ℕ)
    (hD : ∀ u ∈ D, u.val ∈ box R) :
    IsClopen {ω : TiltedConfiguration n t | graphArcIsolation (tiltedOpenGraph n t ω) D W x} :=
  tilted_isClopen_of_finite_support n t (tiltedWindowEdgeCoordinates n (R+1) t) _
    (tilted_isolation_finite_support n t D W hWD x hx R hD)

end
end PottsContinuity.Thm3.Prop4
