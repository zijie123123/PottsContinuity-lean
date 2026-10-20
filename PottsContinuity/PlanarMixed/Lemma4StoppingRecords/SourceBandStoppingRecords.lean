module

public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.ReflectedBottomReveal
public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.SourceAnnulusReveal

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK Exploration Push RSW
noncomputable section
local instance routeSixBandRecordEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

def lemma4SourceBandBase (n : ℕ) (i : Fin 2) : LatticeVertex :=
  if i=0 then (-56*(n:ℤ)-1,2*(n:ℤ)) else (-56*(n:ℤ)-1,-3*(n:ℤ))

def lemma4SourceDualBandRead (n : ℕ) (i : Fin 2)
    (A : Configuration (lemma4AmbientGraph n)) :=
  originalClosedDualRectangleRead (box (56*n)) (lemma4SourceBandBase n i) (112*n+1) (n-1) A

/-- The unchanged upper frontier `Exploration.rectangleTopFrontierReveal`, or its literal
reflected lower frontier, on the exact physical source band. -/
def lemma4SourceDualBandFrontierReveal (n : ℕ) (i : Fin 2) :
    RevealMap (G := rectangleGraph (lemma4SourceBandBase n i) (112*n+1) (n-1)) :=
  if i=0 then Exploration.rectangleTopFrontierReveal (lemma4SourceBandBase n i) (112*n+1) (n-1)
  else rectangleBottomFrontierReveal (lemma4SourceBandBase n i) (112*n+1) (n-1)

def lemma4SourceBandReveal (n : ℕ) (i : Fin 2) : RevealMap (G := lemma4AmbientGraph n) :=
  complementaryStoppingReveal (lemma4AmbientGraph n)
    (rectangleGraph (lemma4SourceBandBase n i) (112*n+1) (n-1))
    (rectangleDualOriginalEdge (box (56*n)) (lemma4SourceBandBase n i) (112*n+1) (n-1))
    (lemma4SourceDualBandFrontierReveal n i)

theorem lemma4SourceDualBandFrontierReveal_stable (n : ℕ) (i : Fin 2)
    (A B : Configuration (rectangleGraph (lemma4SourceBandBase n i) (112*n+1) (n-1)))
    (h : B ∩ lemma4SourceDualBandFrontierReveal n i A=A ∩ lemma4SourceDualBandFrontierReveal n i A) :
    lemma4SourceDualBandFrontierReveal n i B=lemma4SourceDualBandFrontierReveal n i A := by
  unfold lemma4SourceDualBandFrontierReveal at h ⊢
  split_ifs at h ⊢ with hi
  · exact Exploration.rectangleTopFrontierReveal_stable _ _ _ A B h
  · exact rectangleBottomFrontierReveal_stable _ _ _ A B h

theorem lemma4SourceBandReveal_stable (n : ℕ) (i : Fin 2)
    (A B : Configuration (lemma4AmbientGraph n))
    (h : B ∩ lemma4SourceBandReveal n i A=A ∩ lemma4SourceBandReveal n i A) :
    lemma4SourceBandReveal n i B=lemma4SourceBandReveal n i A :=
  complementaryStoppingReveal_stable _ _ _ _ (lemma4SourceDualBandFrontierReveal_stable n i) A B h

theorem lemma4SourceDualBandRead_crossing_iff (n : ℕ) (hn : 1 ≤ n) (i : Fin 2)
    (A : Configuration (lemma4AmbientGraph n)) :
    lemma4SourceDualBandRead n i A ∈
      rectangleHorizontalCrossingEvent (lemma4SourceBandBase n i) (112*n+1) (n-1) ↔
      A ∈ lemma4DualBandEvent n i := by
  have hcross := source_closedDualRectangle_crossing_iff_read (box (56*n)) (lemma4SourceBandBase n i) (112*n+1) (n-1) A
  have hN : ((n-1:ℕ):ℤ)=(n:ℤ)-1 := by omega
  have hW : ((112*n+1:ℕ):ℤ)=112*(n:ℤ)+1 := by omega
  rw [hN,hW] at hcross
  have hright : (lemma4SourceBandBase n i).1+(112*(n:ℤ)+1)=56*(n:ℤ) := by
    unfold lemma4SourceBandBase
    split_ifs <;> dsimp <;> ring
  have htop : (lemma4SourceBandBase n i).2+((n:ℤ)-1)=
      if i=0 then 3*(n:ℤ)-1 else -2*(n:ℤ)-1 := by
    unfold lemma4SourceBandBase
    split_ifs <;> dsimp <;> ring
  rw [hright,htop] at hcross
  fin_cases i
  · change originalClosedDualRectangleRead _ (-56*(n:ℤ)-1,2*(n:ℤ)) _ _ A ∈
      rectangleHorizontalCrossingEvent _ _ _ ↔ A ∈
      finiteClosedDualHorizontalRectangle _ (-56*(n:ℤ)-1) (56*(n:ℤ)) (2*(n:ℤ)) (3*(n:ℤ)-1)
    convert! hcross.symm using 1
  · change originalClosedDualRectangleRead _ (-56*(n:ℤ)-1,-3*(n:ℤ)) _ _ A ∈
      rectangleHorizontalCrossingEvent _ _ _ ↔ A ∈
      finiteClosedDualHorizontalRectangle _ (-56*(n:ℤ)-1) (56*(n:ℤ)) (-3*(n:ℤ)) (-2*(n:ℤ)-1)
    convert! hcross.symm using 1

theorem lemma4DualBandEvent_readFrom_sourceBandReveal (n : ℕ) (hn : 1 ≤ n) (i : Fin 2) :
    ReadFromReveal (lemma4SourceBandReveal n i) (lemma4DualBandEvent n i) := by
  have hread : ReadFromReveal (lemma4SourceDualBandFrontierReveal n i)
      (rectangleHorizontalCrossingEvent (lemma4SourceBandBase n i) (112*n+1) (n-1)) := by
    unfold lemma4SourceDualBandFrontierReveal
    split_ifs
    · exact horizontalCrossing_readFrom_topFrontier _ _ _
    · exact horizontalCrossing_readFrom_bottomFrontier _ _ _
  have h := complementary_readFromReveal (lemma4AmbientGraph n)
    (rectangleGraph (lemma4SourceBandBase n i) (112*n+1) (n-1))
    (rectangleDualOriginalEdge (box (56*n)) (lemma4SourceBandBase n i) (112*n+1) (n-1))
    (lemma4SourceDualBandFrontierReveal n i) (lemma4SourceDualBandFrontierReveal_stable n i) _ hread
  have heq : ((lemma4SourceDualBandRead n i) ⁻¹'
      rectangleHorizontalCrossingEvent (lemma4SourceBandBase n i) (112*n+1) (n-1))=lemma4DualBandEvent n i := by
    ext A
    exact lemma4SourceDualBandRead_crossing_iff n hn i A
  change ReadFromReveal (lemma4SourceBandReveal n i) ((lemma4SourceDualBandRead n i) ⁻¹' _) at h
  rwa [heq] at h

/-- One ACTUAL source stopping set: both one-sided band explorations plus
only the original annulus bonds, including all failure configurations. -/
def lemma4JointSourceReveal (n : ℕ) : RevealMap (G := lemma4AmbientGraph n) :=
  jointReveal (fun _ => lemma4AnnulusBondReveal n)
    (jointReveal (lemma4SourceBandReveal n 0) (lemma4SourceBandReveal n 1))

theorem lemma4JointSourceReveal_stable (n : ℕ)
    (A B : Configuration (lemma4AmbientGraph n))
    (h : B ∩ lemma4JointSourceReveal n A=A ∩ lemma4JointSourceReveal n A) :
    lemma4JointSourceReveal n B=lemma4JointSourceReveal n A :=
  jointReveal_stable _ _ (fun _ _ _ => rfl)
    (jointReveal_stable _ _ (lemma4SourceBandReveal_stable n 0) (lemma4SourceBandReveal_stable n 1)) A B h

theorem lemma4BandConstructionEvent_readFrom_jointSourceReveal (n : ℕ) (hn : 1 ≤ n) :
    ReadFromReveal (lemma4JointSourceReveal n) (lemma4BandConstructionEvent n) :=
  readFromReveal_joint_inter _ _ (fun _ _ _ => rfl)
    (jointReveal_stable _ _ (lemma4SourceBandReveal_stable n 0) (lemma4SourceBandReveal_stable n 1))
    _ _ (lemma4AnnulusPairEvent_read_from_annulusBonds n)
    (readFromReveal_joint_inter _ _ (lemma4SourceBandReveal_stable n 0) (lemma4SourceBandReveal_stable n 1)
      _ _ (lemma4DualBandEvent_readFrom_sourceBandReveal n hn 0) (lemma4DualBandEvent_readFrom_sourceBandReveal n hn 1))

/-- The exact selected observations of the source B_n, not a substitute event. -/
def lemma4SourceBandObservations (n : ℕ) : Set (StoppingObservationRange (lemma4JointSourceReveal n)) :=
  selectedRevealObservations (lemma4JointSourceReveal n) (lemma4BandConstructionEvent n)

theorem lemma4SourceBandObservations_preimage (n : ℕ) (hn : 1 ≤ n) :
    (stoppingObservationMap (lemma4JointSourceReveal n)) ⁻¹' lemma4SourceBandObservations n=
      lemma4BandConstructionEvent n :=
  preimage_selectedRevealObservations _ _ (lemma4BandConstructionEvent_readFrom_jointSourceReveal n hn)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
