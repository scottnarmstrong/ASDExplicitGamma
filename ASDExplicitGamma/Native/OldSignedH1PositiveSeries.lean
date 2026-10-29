module

public import ASDExplicitGamma.Native.OldSignedQ3SourceEnergy
public import ASDExplicitGamma.Native.OldSignedPairingPartition
public import ASDExplicitGamma.Triadic.PlanarPositiveGradient

/-! Complete positive-norm square convergence of genuine H1 families,
including their restrictions to every actual descendant cell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- A summable actual scalar L2 energy family remains summable on each
fixed descendant cell, using the exact finite normalized partition. -/
theorem old_signed_l2_energy_descendant_series {I : Type*} (Q : TriadicCube 2) (depth : ℕ)
    (f : I → Vec 2 → ℝ) (hf : ∀ n,MemLp (f n) 2 (normalizedCubeMeasure Q))
    (hv : Summable (fun n => energy Q (f n)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n => energy U (f n)) := by
  have havg : Summable (fun n => descendantsAverage Q depth (fun V => energy V (f n))) := by
    apply hv.congr
    intro n
    exact old_signed_pairing_partition Q depth _ _ (hf n) (hf n)
  exact old_signed_summable_of_descendant_average Q depth _
    (fun _ _ _ => energy_nonneg _ _) havg U hU

/-- Summable value and gradient energies give actual square-summability
of the positive Haar norms, with the source's exact planar coefficient. -/
theorem old_signed_h1_positive_series_summable {I : Type*} (Q : TriadicCube 2)
    (f : I → H1Function (openCubeSet Q))
    (hv : Summable (fun n => energy Q (f n).toFun))
    (hg : ∀ j : Fin 2,Summable (fun n => energy Q (fun x => (f n).grad x j))) :
    Summable (fun n => positiveHaarNorm Q (f n).toFun^2) := by
  have hs : Summable (fun n => ∑ j : Fin 2,energy Q (fun x => (f n).grad x j)) :=
    summable_sum (fun j _ => hg j)
  apply (hv.add (hs.mul_left (cubeScaleFactor Q^2*planarC1^2))).of_nonneg_of_le (fun n => sq_nonneg _)
  intro n
  exact positiveHaarNorm_sq_le_l2_add_gradient Q (f n).memL2_normalizedCubeMeasure
    (f n).grad_memL2_normalizedCubeMeasure (f n).hasWeakGradient

/-- The same genuine H1 family has summable cellwise positive squares on
every fixed finite descendant partition, without a new convergence premise. -/
theorem old_signed_h1_positive_descendant_series {I : Type*} (Q : TriadicCube 2) (depth : ℕ)
    (f : I → H1Function (openCubeSet Q))
    (hv : Summable (fun n => energy Q (f n).toFun))
    (hg : ∀ j : Fin 2,Summable (fun n => energy Q (fun x => (f n).grad x j)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n => positiveHaarNorm U (f n).toFun^2) := by
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
  have hvU := old_signed_l2_energy_descendant_series Q depth (fun n => (f n).toFun)
    (fun n => (f n).memL2_normalizedCubeMeasure) hv U hU
  have hgU (j : Fin 2) := old_signed_l2_energy_descendant_series Q depth
    (fun n x => (f n).grad x j) (fun n => (f n).grad_memL2_normalizedCubeMeasure j) (hg j) U hU
  exact old_signed_h1_positive_series_summable U
    (fun n => (f n).restrict (isOpen_openCubeSet U) hsub) hvU hgU

/-- Coordinate aggregation retains complete cellwise positive-norm square
convergence for the actual two-coordinate source vectors. -/
theorem old_signed_h1_vector_positive_descendant_series {I : Type*} (Q : TriadicCube 2) (depth : ℕ)
    (f : I → Fin 2 → H1Function (openCubeSet Q))
    (hv : ∀ i,Summable (fun n => energy Q (f n i).toFun))
    (hg : ∀ i j : Fin 2,Summable (fun n => energy Q (fun x => (f n i).grad x j)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n => vectorPositiveHaarNorm U (fun x i => f n i x)^2) := by
  have hs (i : Fin 2) := old_signed_h1_positive_descendant_series Q depth (fun n => f n i) (hv i) (hg i) U hU
  simpa only [vectorPositiveHaarNorm_sq] using summable_sum (fun i _ => hs i)

end
end ASDExplicitGamma.Native
