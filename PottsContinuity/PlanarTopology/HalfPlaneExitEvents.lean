module

public import PottsContinuity.PlanarTopology.HalfPlaneEvents
public import PottsContinuity.PlanarTopology.HalfPlaneFirstExit
public import PottsContinuity.PlanarTopology.OpenWalkEmbedding
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section

/-- The right half-plane with exactly one permitted exterior terminal. -/
def halfPlaneExitDomain (y : ℤ) : Set LatticeVertex :=
  {z | 0 ≤ z.1 ∨ z = (-1,y)}

/-- An actual first-exit connection to an exterior terminal whose height lies
in L. Only that terminal may be outside the original half-plane. -/
def halfPlaneExitEvent (S : Set LatticeVertex) (L : Set ℤ) : Set LatticeConfiguration :=
  {ω | ∃ y ∈ L, ∃ u : {z : LatticeVertex // 0 ≤ z.1}, u.val ∈ S ∧
    ((PD.rcInfiniteOpenGraph ω).induce (halfPlaneExitDomain y)).Reachable
      ⟨u.val,Or.inl u.property⟩ ⟨(-1,y),Or.inr rfl⟩}

theorem halfPlaneExitEvent_measurableSet (S : Set LatticeVertex) (L : Set ℤ) :
    MeasurableSet (halfPlaneExitEvent S L) := by
  have hc (p : Prop) : MeasurableSet {ω : LatticeConfiguration | p} := by
    by_cases hp : p <;> simp [hp]
  have hm (y : ℤ) (u : {z : LatticeVertex // 0 ≤ z.1}) : MeasurableSet
      {ω : LatticeConfiguration | y ∈ L ∧ u.val ∈ S ∧
        ((PD.rcInfiniteOpenGraph ω).induce (halfPlaneExitDomain y)).Reachable
          ⟨u.val,Or.inl u.property⟩ ⟨(-1,y),Or.inr rfl⟩} :=
    (hc (y ∈ L)).inter ((hc (u.val ∈ S)).inter (measurableSet_domain_open_reachable _ _ _))
  convert MeasurableSet.iUnion (fun y => MeasurableSet.iUnion (hm y)) using 1
  ext ω
  simp only [halfPlaneExitEvent,Set.mem_ofPred_eq,Set.mem_iUnion]
  constructor
  · rintro ⟨y,hy,u,hu,hconn⟩
    exact ⟨y,u,hy,hu,hconn⟩
  · rintro ⟨y,u,hy,hu,hconn⟩
    exact ⟨y,hy,u,hu,hconn⟩

theorem halfPlaneExitEvent_isUpperSet (S : Set LatticeVertex) (L : Set ℤ) :
    IsUpperSet (halfPlaneExitEvent S L) := by
  rintro ω η hωη ⟨y,hy,u,hu,hconn⟩
  refine ⟨y,hy,u,hu,SimpleGraph.Reachable.mono ?_ hconn⟩
  intro a b hab
  exact rcOpenGraph_monotone hωη hab

theorem halfPlaneExitEvent_union (S : Set LatticeVertex) (L R : Set ℤ) :
    halfPlaneExitEvent S (L ∪ R) = halfPlaneExitEvent S L ∪ halfPlaneExitEvent S R := by
  ext ω
  constructor
  · rintro ⟨y,hy,u,hu,hconn⟩
    rcases hy with hy | hy
    · exact Or.inl ⟨y,hy,u,hu,hconn⟩
    · exact Or.inr ⟨y,hy,u,hu,hconn⟩
  · rintro (⟨y,hy,u,hu,hconn⟩ | ⟨y,hy,u,hu,hconn⟩)
    · exact ⟨y,Or.inl hy,u,hu,hconn⟩
    · exact ⟨y,Or.inr hy,u,hu,hconn⟩

/-- Every event witness yields an original open walk with the exact exterior
terminal and no other negative first coordinate. -/
theorem halfPlaneExitEvent_original_walk (S : Set LatticeVertex) (L : Set ℤ)
    (ω : LatticeConfiguration) (hω : ω ∈ halfPlaneExitEvent S L) :
    ∃ y ∈ L, ∃ u ∈ S, 0 ≤ u.1 ∧
      ∃ p : (PD.rcInfiniteOpenGraph ω).Walk u (-1,y),
        ∀ z ∈ p.support, 0 ≤ z.1 ∨ z = (-1,y) := by
  obtain ⟨y,hy,u,hu,⟨r⟩⟩ := hω
  let p := r.map (SimpleGraph.Embedding.induce (halfPlaneExitDomain y)).toHom
  refine ⟨y,hy,u.val,hu,u.property,p,?_⟩
  intro z hz
  have hs : p.support = r.support.map Subtype.val :=
    SimpleGraph.Walk.support_map (SimpleGraph.Embedding.induce (G := PD.rcInfiniteOpenGraph ω) (halfPlaneExitDomain y)).toHom r
  have hz' : z ∈ r.support.map Subtype.val := Eq.mp (congrArg (fun xs : List LatticeVertex => z ∈ xs) hs) hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz'
  exact w.property

end
end PottsContinuity.PlanarTopology
