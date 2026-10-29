module

public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaProfile
public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaPointwise
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurable

/-! The quadratic source row is controlled by the actual correlated bank. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Gaussian Inverse Response Variational Triadic
open MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal NNReal
noncomputable section

private theorem nativeHeatQ3RefinedCarrierBankLeft_le
    (M : ABKModel 2) (n : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (g : ℝ) (d : Fin 9) :
    lemmaVTileHistory (originCube 2 (n - 1))
      (pureFluxBankSourceDepth (d.val + 2))
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (pureFluxOpenResponseRestriction (n - 1)
          (heatRefinedObserverShear (n - 1) n 9 t ω g))) ≤
      heatVHEATDriftBank M n 9 t ω g d := by
  unfold heatVHEATDriftBank
  exact le_max_left _ _

/-- Each actual source-row history is the left branch of the complete
physical bank, after the exact source-observer transport. -/
theorem nativeHeatQ3RefinedCarrierRowHistory_le_bank
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ))
    (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let A := nativeHeat_translateTriadicFieldToOrigin Q
    let x := heatVHEATDriftRefinedChildField m t g z i
    lemmaVTileHistory (originCube 2 Q.scale)
      (pureFluxBankSourceDepth (d.val + 2))
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M (m + 1))
        (pureFluxOpenResponseRestriction Q.scale (A x))) ≤
      heatVHEATDriftBank M (m + 1) 9 t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1)
        (g i z.2) d := by
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  let x := heatVHEATDriftRefinedChildField m t g z i
  have hobs : A x = heatRefinedObserverShear Q.scale (m + 1) 9 t
      (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1)
      (g i z.2) := by
    have hh := heatVHEATDrift_refined_child_observer M m t g z i
    simpa [A, x, Q] using hh
  have hbank := nativeHeatQ3RefinedCarrierBankLeft_le M (m + 1) t
    (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1)
    (g i z.2) d
  have hrow :
      lemmaVTileHistory (originCube 2 Q.scale)
        (pureFluxBankSourceDepth (d.val + 2))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M (m + 1))
          (pureFluxOpenResponseRestriction Q.scale (A x))) =
      lemmaVTileHistory (originCube 2 ((m + 1) - 1))
        (pureFluxBankSourceDepth (d.val + 2))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M (m + 1))
          (pureFluxOpenResponseRestriction ((m + 1) - 1)
            (heatRefinedObserverShear ((m + 1) - 1) (m + 1) 9 t
              (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1)
              (g i z.2)))) := by
    have hscale : Q.scale = m := nativeHeatQ3RefinedCarrierChild_scale m i
    let H : ℤ → ℝ := fun r =>
      lemmaVTileHistory (originCube 2 r) (pureFluxBankSourceDepth (d.val + 2))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M (m + 1))
          (pureFluxOpenResponseRestriction r
            (heatRefinedObserverShear r (m + 1) 9 t
              (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1)
              (g i z.2))))
    have hscale' : Q.scale = (m + 1) - 1 := by omega
    rw [hobs]
    change H Q.scale = H ((m + 1) - 1)
    exact congrArg H hscale'
  dsimp only
  rw [hrow]
  exact hbank

end
end ASDExplicitGamma.Native
