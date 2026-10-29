module

public import ASDExplicitGamma.Gaussian.SquareMinimizer
public import ASDExplicitGamma.Inverse.PureFluxGeneratorMinimizerEnergy

/-! The actual two-channel weak-energy budget on arbitrary translated squares. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section
local instance squareBudgetFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem square_minimizer_pair_tiled_energy_bound (Q : TriadicCube 2) (m : ℕ)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (r : H10Function (openCubeSet Q))
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν σ k) (openCubeSet Q))
    (w : AHarmonicFunction (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet Q))
    (hgrad : (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r).grad =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (blockResponsePairHalfState (responseFramePlanarCoefficientField ν σ k) u w).potential)
    (hEv : responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (square_volume_pos Q) ν σ hν hσ P k - 2*vecDot P.1 P.2 =
      volumeAverage (openCubeSet Q)
        (scalarVariationEnergyIntegrand (adjointCoeffField (responseFramePlanarCoefficientField ν σ k)) w))
    (hEu : responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (square_volume_pos Q) ν σ hν hσ P k + 2*vecDot P.1 P.2 =
      volumeAverage (openCubeSet Q)
        (scalarVariationEnergyIntegrand (responseFramePlanarCoefficientField ν σ k) u))
    (B : ℝ) (hhist : ∀ R ∈ descendantsAtDepth Q m,
      lemmaVInverseHistory R (responseFramePlanarCoefficientField ν σ k) ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    lemmaVTiledWeakEnergy Q m
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r).grad +
      lemmaVTiledWeakEnergy Q m (fun x => (1/2:ℝ) • (w.toH1.grad x-u.toH1.grad x)) ≤
      B * responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (square_volume_pos Q) ν σ hν hσ P k := by
  let a := responseFramePlanarCoefficientField ν σ k
  let V := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
  let f : H1Function (openCubeSet Q) := (1/2:ℝ) • (u.toH1+w.toH1)
  let g : H1Function (openCubeSet Q) := (1/2:ℝ) • (u.toH1-w.toH1)
  have hfirst : f.grad = compatiblePairFirst u w := by rfl
  have hsecond : g.grad = compatiblePairSecondImage u w := by
    funext x i
    simp only [g, compatiblePairSecondImage, H1Function.smul_grad, H1Function.sub_grad,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hV : V.grad =ᵐ[volumeMeasureOn (openCubeSet Q)] f.grad := hgrad
  have hneg : (fun x => (1/2:ℝ) • (w.toH1.grad x-u.toH1.grad x)) = fun x => -g.grad x := by
    funext x i
    simp only [g, H1Function.smul_grad, H1Function.sub_grad, Pi.smul_apply, Pi.sub_apply,
      Pi.neg_apply, smul_eq_mul]
    ring
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hp := pureFlux_paired_tiled_energy_bound Q m hEll u w B hhist
  have hE := compatiblePairState_energy Q hEll u w
  have heq : blockPairingAverage (openCubeSet Q) a (compatiblePairState u w) (compatiblePairState u w) =
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (square_volume_pos Q) ν σ hν hσ P k := by
    rw [hE]
    linarith only [hEv, hEu]
  rw [heq] at hp
  rw [← hfirst, ← hsecond] at hp
  rw [pureFlux_tiledWeakEnergy_h1_congr Q m V f hV, hneg, pureFlux_tiledWeakEnergy_h1_neg]
  exact hp

end
end ASDExplicitGamma.Gaussian
