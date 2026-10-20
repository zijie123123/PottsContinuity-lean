module

public import PottsContinuity.Thm3.Push.SquareDualReflectionStates
public import PottsContinuity.Thm3.Push.IntervalArmRawRightDetermination

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- The actual reached closed-dual clusters transport with the finite
reflection and its exact complementary port map. -/
theorem squareDualReflection_reached_iff (N : ℕ) (r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N))
    (u : RectangleDualVertex (0,0) N N) :
    squareDualReflectionIso N u ∈ closedClusterReached
      (DualityExt.rectangleDualEdgeEquiv (0,0) N N) (intervalArmRightDualPorts N r)
      (configurationIso (squareArmReflectionIso N) A) ↔
    u ∈ closedClusterReached (DualityExt.rectangleDualEdgeEquiv (0,0) N N)
      (intervalArmLeftDualPorts N ((N:ℤ)-r)) A := by
  classical
  let e := DualityExt.rectangleDualEdgeEquiv (0,0) N N
  let D := squareDualReflectionIso N
  change (∃ t ∈ intervalArmRightDualPorts N r,
    ActualConnected _ (auxiliaryClosedConfiguration e (configurationIso (squareArmReflectionIso N) A)) t (D u)) ↔
    ∃ s ∈ intervalArmLeftDualPorts N ((N:ℤ)-r), ActualConnected _ (auxiliaryClosedConfiguration e A) s u
  rw [← squareDualReflection_left_ports_map N r,← squareDualReflection_closed_configuration N A]
  constructor
  · rintro ⟨t,ht,hconn⟩
    obtain ⟨s,hs,hst⟩ := Finset.mem_map.mp ht
    subst t
    exact ⟨s,hs,(actualConnected_configurationIso D (auxiliaryClosedConfiguration e A) s u).mp hconn⟩
  · rintro ⟨s,hs,hconn⟩
    exact ⟨D s,Finset.mem_map.mpr ⟨s,hs,rfl⟩,
      (actualConnected_configurationIso D (auxiliaryClosedConfiguration e A) s u).mpr hconn⟩

/-- Reflecting the complete actual original-bond reveal gives precisely the
direct right-port reveal. All queried closed and open states are retained. -/
theorem squareDualReflection_closedReveal_map (N : ℕ) (r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :
    configurationIso (squareArmReflectionIso N)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv (0,0) N N)
        (intervalArmLeftDualPorts N ((N:ℤ)-r)) A) =
    closedClusterReveal (DualityExt.rectangleDualEdgeEquiv (0,0) N N)
      (intervalArmRightDualPorts N r) (configurationIso (squareArmReflectionIso N) A) := by
  classical
  let e := DualityExt.rectangleDualEdgeEquiv (0,0) N N
  let P := configurationIsoEdgeEquiv (squareArmReflectionIso N)
  ext f
  obtain ⟨g,rfl⟩ := P.surjective f
  have hl : P g ∈ configurationIso (squareArmReflectionIso N)
      (closedClusterReveal e (intervalArmLeftDualPorts N ((N:ℤ)-r)) A) ↔
      g ∈ closedClusterReveal e (intervalArmLeftDualPorts N ((N:ℤ)-r)) A := by
    change P g ∈ (closedClusterReveal e (intervalArmLeftDualPorts N ((N:ℤ)-r)) A).map P.toEmbedding ↔ _
    simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]
  rw [hl,mem_closedClusterReveal_iff_endpoint,mem_closedClusterReveal_iff_endpoint]
  constructor
  · rintro ⟨u,hu,hreach⟩
    refine ⟨squareDualReflectionIso N u,?_,(squareDualReflection_reached_iff N r A u).mpr hreach⟩
    rw [← squareDualReflection_crossing_pair N g]
    exact Sym2.mem_map.mpr ⟨u,hu,rfl⟩
  · rintro ⟨v,hv,hreach⟩
    rw [← squareDualReflection_crossing_pair N g] at hv
    obtain ⟨u,hu,huv⟩ := Sym2.mem_map.mp hv
    subst v
    exact ⟨u,hu,(squareDualReflection_reached_iff N r A u).mp hreach⟩

/-- The existing reflected right exploration is EXACTLY the direct finite
right/bottom closed-dual cluster reveal on the same sampled square. -/
theorem intervalArmRawRightReveal_eq_direct (N : ℕ) (r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :
    intervalArmRawRightReveal N r A =
      closedClusterReveal (DualityExt.rectangleDualEdgeEquiv (0,0) N N)
        (intervalArmRightDualPorts N r) A := by
  have h := squareDualReflection_closedReveal_map N r ((configurationIso (squareArmReflectionIso N)).symm A)
  simpa only [intervalArmRawRightReveal,isoStoppingReveal,intervalArmLeftReveal,Equiv.apply_symm_apply] using h

end
end PottsContinuity.Push
