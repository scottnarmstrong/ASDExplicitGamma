module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorActualSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredSource

/-! The full covariance energy of the actual centered pure-flux sources. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

theorem pureFluxMainQ3CenteredGeneratorY_covariance_trace_bound
    (n : ℤ) (q i m : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2)
    (r : H10Function (openCubeSet (originCube 2 n)))
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν σ k)
      (openCubeSet (originCube 2 n)))
    (w : AHarmonicFunction
      (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet (originCube 2 n)))
    (hrep : hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isOpen.measurableSet
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (fun x => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).eval x))
    (hgrad : (lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) P.1 r).grad =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).potential)
    (hρ : cubeScaleFactor (originCube 2 n)/L.1 = pureFluxCovarianceRho q i)
    (hδ : diagMeshRadius (originCube 2 n) m/L.1 = pureFluxCovarianceDelta q i)
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth (originCube 2 n) m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    let Q := originCube 2 n
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let Y := fun l : whiteBasisIndex =>
      ‖pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
        (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P k
        (pureFluxMainCubeQ3CenteredResponseCoefficient n b L
          (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l))‖^2
    Summable Y ∧ (∑' l, Y l) ≤
      B*(|σ⁻¹| * |b| *pureFluxCovarianceA q i)^2*lemmaVTiledWeakEnergy Q m v.grad := by
  intro Q v Y
  let R := pureFluxMainQ3CenteredRowEnergy n b σ L m P.1 r
  let C := |σ⁻¹| * |b| *pureFluxCovarianceA q i
  have hrow := pureFluxMainQ3_centered_row_trace_bound n q i m b σ L hρ hδ P.1 r
  have hRn (l : whiteBasisIndex) : 0 ≤ R l := by
    unfold R pureFluxMainQ3CenteredRowEnergy descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  have hRtotal : (∑' l, R l) ≤ C^2*lemmaVTiledWeakEnergy Q m v.grad := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrow.2 2
    rw [Real.sq_sqrt (tsum_nonneg hRn), mul_pow,
      Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q m v.grad)] at hh
    exact hh
  have hYR (l : whiteBasisIndex) : Y l ≤ B*R l := by
    obtain ⟨hF, hgen, z, hz, he, hb⟩ := pureFluxMainQ3CenteredGeneratorY_tiled_source_bound
      n ν σ b hν hσ L l m k P r u w hrep hgrad B hB hhist
    have hnorm : Y l = (scalarFrameRealization Q ν σ hν hσ k).energyBilin
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) := by
      dsimp only [Y]
      rw [hgen, energyCarrier_norm_sq]
      simp [Q, responseEnergyUp_down, responseFrameEnergyData,
        scalarFrameRealization, scalarFrameEnergyData, responseEnergyHilbertData]
    rw [hnorm]
    convert he using 1
    congr 1
    dsimp only [Q, v, lemmaVTiledPositiveEnergy, R, pureFluxMainQ3CenteredRowEnergy, descendantsAverage]
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
end ASDExplicitGamma.Inverse
