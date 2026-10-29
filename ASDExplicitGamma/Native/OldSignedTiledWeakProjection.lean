module

public import ASDExplicitGamma.Native.OldSignedWeakTraceProxySeries
public import ASDExplicitGamma.Native.OldSignedPartitionSeries
public import ASDExplicitGamma.Triadic.PlanarNeumannBridge

/-! Complete weak-energy identities on the actual source tiling. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- Spatially averaging the actual local weak energies shifts the projection
depth, but leaves the weak geometric weight at the local depth. -/
theorem old_signed_tiled_weak_projection_series {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (mesh : ℕ) (F : ι → Vec 2 → Vec 2)
    (hF : ∀ c i,MemLp (fun x => F c x i) 2 (normalizedCubeMeasure Q)) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*
      ∑ c,∑ i,energy Q (cubeProjection Q (mesh+j) (fun x => F c x i))) ∧
    descendantsAverage Q mesh (fun U => ∑ c,vectorWeakHaarEnergy U (F c))=
      (1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
        ∑ c,∑ i,energy Q (cubeProjection Q (mesh+j) (fun x => F c x i)) := by
  classical
  let f := fun j U => inverseHistoryDiscount^(2*j)*
    ∑ c,∑ i,energy U (cubeProjection U j (fun x => F c x i))
  have hr (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q mesh) :=
    old_signed_finite_weak_projection_series U F
      (fun c i => memLp_on_descendant_of_memLp hU (hF c i))
  have hs := old_signed_partition_series Q mesh f (fun U hU => (hr U hU).1)
  have he (j : ℕ) : descendantsAverage Q mesh (f j)=inverseHistoryDiscount^(2*j)*
      ∑ c,∑ i,energy Q (cubeProjection Q (mesh+j) (fun x => F c x i)) := by
    dsimp only [f]
    rw [descendantsAverage_mul_left,Homogenization.descendantsAverage_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    rw [Homogenization.descendantsAverage_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact descendantsAverage_localProjection_eq Q mesh j _
  simp_rw [he] at hs
  refine ⟨hs.1,?_⟩
  rw [hs.2,←descendantsAverage_mul_left]
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  exact (hr U hU).2

end
end ASDExplicitGamma.Native
