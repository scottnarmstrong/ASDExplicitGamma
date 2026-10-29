module

public import ASDExplicitGamma.Gaussian.SquareColumnBound
public import ASDExplicitGamma.Gaussian.SquareSource

/-! Complete actual projected-source energy on arbitrary translated squares. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Model ASDExplicitGamma.Numerics
open scoped BigOperators
noncomputable section

local instance squareEnergyFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem square_q3_generator_covariance_source_bound
    (Q : TriadicCube 2) (m : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (r : H10Function (openCubeSet Q))
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν σ k)
      (openCubeSet Q))
    (w : AHarmonicFunction
      (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet Q))
    (hrep : hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (isOpenBoundedConvexDomain_openCubeSet Q).isOpen.measurableSet
          (square_volume_pos Q)
          ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
        (fun x => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).eval x))
    (hgrad : (lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r).grad =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).potential)
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth Q m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3:ℝ)^(1/4:ℝ)) ≤ B) :
      let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let Y := fun l : whiteBasisIndex =>
      ‖pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
        (square_volume_pos Q) ν σ hν hσ P k
        (squareQ3Directions Q b L
          (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l))‖^2
    Summable Y ∧ (∑' l, Y l) ≤
      B*(|σ⁻¹| * |b| *Numerics.generatorKA (diagMeshRadius Q m/L.1))^2*lemmaVTiledWeakEnergy Q m v.grad := by
  intro v Y
  let R := squareQ3RowEnergy Q b σ L m P.1 r
  let C := |σ⁻¹| * |b| *Numerics.generatorKA (diagMeshRadius Q m/L.1)
  have hrow := square_q3_row_source_trace_bound Q b σ L m P.1 r
  have hRn (l : whiteBasisIndex) : 0 ≤ R l := by
    unfold R squareQ3RowEnergy descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  have hRtotal : (∑' l, R l) ≤ C^2*lemmaVTiledWeakEnergy Q m v.grad := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrow.2 2
    rw [Real.sq_sqrt (tsum_nonneg hRn), mul_pow,
      Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q m v.grad)] at hh
    exact hh
  have hYR (l : whiteBasisIndex) : Y l ≤ B*R l := by
    obtain ⟨hF, hgen, z, hz, he, hb⟩ := square_q3_generator_tiled_source_bound
      Q ν σ b hν hσ L l m k P r u w hrep hgrad B hB hhist
    have hnorm : Y l = (scalarFrameRealization Q ν σ hν hσ k).energyBilin
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) := by
      dsimp only [Y]
      rw [hgen, energyCarrier_norm_sq]
      simp [responseEnergyUp_down, responseFrameEnergyData,
        scalarFrameRealization, scalarFrameEnergyData, responseEnergyHilbertData]
    rw [hnorm]
    convert he using 1
    congr 1
    dsimp only [v, lemmaVTiledPositiveEnergy, R, squareQ3RowEnergy, descendantsAverage]
    congr 1
    apply Finset.sum_congr rfl
    intro U _
    unfold vectorPositiveHaarEnergy
    apply Finset.sum_congr rfl
    intro j _
    exact (primalEnergy_neg U (Real.sqrt 3) _).symm
  have hYn (l : whiteBasisIndex) : 0 ≤ Y l := sq_nonneg _
  have hYsum : Summable Y :=
    Summable.of_nonneg_of_le hYn hYR (hrow.1.mul_left B)
  refine ⟨hYsum, ?_⟩
  calc
    _ ≤ ∑' l, B*R l := hYsum.tsum_le_tsum hYR (hrow.1.mul_left B)
    _ = B*∑' l, R l := tsum_mul_left
    _ ≤ B*(C^2*lemmaVTiledWeakEnergy Q m v.grad) := mul_le_mul_of_nonneg_left hRtotal hB
    _ = _ := by ring

end
end ASDExplicitGamma.Gaussian
