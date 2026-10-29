module

public import ASDExplicitGamma.Native.OldSignedRemainderKernel
public import ASDExplicitGamma.Triadic.HilbertHaarCellGeometry

/-! Exact finite cell energy partition of actual Hilbert H1 coordinate
families, for use in joint covariance estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- Coordinate energy partitions commute with the actual normalized cell
average. This applies to values or any fixed derivative family. -/
theorem old_signed_hilbert_coordinate_energy_partition {E A : Type*} [Fintype A]
    [NormedAddCommGroup E] (Q : TriadicCube 2) (j : ℕ) (f : A → Vec 2 → E)
    (hf : ∀ a,MemLp (f a) 2 (normalizedCubeMeasure Q)) :
    descendantsAverage Q j (fun U => ∑ a,hilbertEnergy U (f a))=
      ∑ a,hilbertEnergy Q (f a) := by
  classical
  rw [Homogenization.descendantsAverage_sum Q j Finset.univ (fun U a => hilbertEnergy U (f a))]
  apply Finset.sum_congr rfl
  intro a _
  exact (hilbertEnergy_eq_descendantsAverage Q j (hf a)).symm

/-- Exact complete derivative energy partition for a finite actual H1
family, with no maximum or estimate replacing the cell average. -/
theorem old_signed_hilbert_gradient_energy_partition {E A : Type*} [Fintype A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (j : ℕ) (u : A → HilbertH1Function (openCubeSet Q) E) :
    descendantsAverage Q j (fun U => ∑ a,hilbertGradientEnergy U (u a).grad)=
      ∑ a,hilbertGradientEnergy Q (u a).grad := by
  classical
  simp only [hilbertGradientEnergy]
  rw [Homogenization.descendantsAverage_sum Q j Finset.univ
    (fun U a => ∑ k,hilbertEnergy U (fun x => (u a).grad x k))]
  apply Finset.sum_congr rfl
  intro a _
  apply old_signed_hilbert_coordinate_energy_partition
  intro k
  exact (u a).gradMemL2_normalized Q k

end
end ASDExplicitGamma.Native
