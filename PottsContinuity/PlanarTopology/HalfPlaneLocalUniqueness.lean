module

public import PottsContinuity.PlanarTopology.HalfPlaneEvents
public import PottsContinuity.PlanarTopology.LocalUniquenessTranslation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section

/-- All marked roots reaching the boundary line are joined inside the actual
closed half-plane. The marked set may contain any original lattice vertices. -/
def halfPlaneLocalUniquenessEvent (S : Set LatticeVertex) : Set LatticeConfiguration :=
  {ω | ∀ u v : {z : LatticeVertex // 0 ≤ z.1}, u.val ∈ S → v.val ∈ S →
    ω ∈ halfPlaneBoundaryEvent {u.val} → ω ∈ halfPlaneBoundaryEvent {v.val} →
      ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable u v}

theorem halfPlane_singleton_boundary_reachable (ω : LatticeConfiguration)
    (u : {z : LatticeVertex // 0 ≤ z.1}) (hu : ω ∈ halfPlaneBoundaryEvent {u.val}) :
    ∃ z : {z : LatticeVertex // 0 ≤ z.1}, z.val.1 = 0 ∧
      ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable u z := by
  obtain ⟨v,hv,z,hz,hvz⟩ := hu
  have he : v = u := Subtype.ext (Set.mem_singleton_iff.mp hv)
  subst v
  exact ⟨z,hz,hvz⟩

theorem halfPlaneLocalUniquenessEvent_measurableSet (S : Set LatticeVertex) :
    MeasurableSet (halfPlaneLocalUniquenessEvent S) := by
  have hm (u v : {z : LatticeVertex // 0 ≤ z.1}) : MeasurableSet {ω : LatticeConfiguration |
      u.val ∈ S → v.val ∈ S → ω ∈ halfPlaneBoundaryEvent {u.val} →
      ω ∈ halfPlaneBoundaryEvent {v.val} →
        ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable u v} := by
    by_cases hu : u.val ∈ S
    · by_cases hv : v.val ∈ S
      · have hh := ((halfPlaneBoundaryEvent_measurableSet {u.val}).inter
          (halfPlaneBoundaryEvent_measurableSet {v.val})).compl.union
            (measurableSet_domain_open_reachable _ u v)
        convert hh using 1
        ext ω
        simp only [Set.mem_ofPred_eq,hu,hv,Set.mem_union,Set.mem_compl_iff,
          Set.mem_inter_iff,imp_iff_not_or,not_and_or,or_assoc,not_true_eq_false,false_or]
        rfl
      · simp [hv]
    · simp [hu]
  convert MeasurableSet.iInter (fun u => MeasurableSet.iInter (hm u)) using 1
  ext ω
  simp only [halfPlaneLocalUniquenessEvent,Set.mem_ofPred_eq,Set.mem_iInter]

/-- A finite local witness entirely on the positive side connects every marked
pair reaching the boundary, inside the true half-plane induced graph. -/
theorem finite_local_unique_subset_halfplane (S T : Finset LatticeVertex)
    (hT : ∀ z ∈ T, 0 < z.1) :
    finiteLocalUniquenessEvent S T ⊆ halfPlaneLocalUniquenessEvent (S : Set LatticeVertex) := by
  rintro ω ⟨hST,hlocal⟩ u v hu hv huB hvB
  obtain ⟨x,hx,hux⟩ := halfPlane_singleton_boundary_reachable ω u huB
  obtain ⟨y,hy,hvy⟩ := halfPlane_singleton_boundary_reachable ω v hvB
  let uT : {z // z ∈ T} := ⟨u.val,hST hu⟩
  let vT : {z // z ∈ T} := ⟨v.val,hST hv⟩
  have hconn := hlocal uT vT hu hv
    ⟨x.val,(by intro hxT; have := hT x.val hxT; omega),hux.map (SimpleGraph.Embedding.induce _).toHom⟩
    ⟨y.val,(by intro hyT; have := hT y.val hyT; omega),hvy.map (SimpleGraph.Embedding.induce _).toHom⟩
  let e : (PD.rcInfiniteOpenGraph ω).induce (T : Set LatticeVertex) →g
      (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1} :=
    { toFun := fun z => ⟨z.val,(hT z.val z.property).le⟩, map_rel' := fun h => h }
  exact hconn.map e

end
end PottsContinuity.PlanarTopology
