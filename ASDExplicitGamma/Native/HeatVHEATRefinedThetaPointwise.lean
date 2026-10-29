module

public import ASDExplicitGamma.Native.HeatVHEATRefinedFinalAssembly

/-! The source-compatible center-subtracted pointwise VHEAT bracket. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Gaussian Algsuperdiff.Section3 Numerics.Native
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
open scoped ENNReal NNReal
noncomputable section

/-- The actual nine-shell source row, defined at the pointwise interface so
the generator and its expectation use one shared expression. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceRowsForFields
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (fields : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) : ℝ := by
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  exact ∑ d : Fin 9,
    4 * (q3ModelAmplitude M h (m + ((d.val + 2 : ℕ) : ℤ)) ^ 2 / σ ^ 2) *
      q3GridOverlapFactor 10 (d.val + 2) *
      (lemmaVH2Bn
        (cubeScaleFactor (originCube 2 m) /
          (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
        (diagMeshRadius (originCube 2 m)
          (pureFluxBankSourceDepth (d.val + 2)) /
          (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)) ^ 2 *
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          let Qi := nativeHeatQ3RefinedCarrierChild m i
          let A := nativeHeat_translateTriadicFieldToOrigin Qi
          let ki := pureFluxOpenResponseRestriction Qi.scale
            (A (fields i))
          let Bi := lemmaVTileHistory (originCube 2 Qi.scale)
            (pureFluxBankSourceDepth (d.val + 2))
            (responseFramePlanarCoefficientField M.nu σ ki)
          let Ti := modelTraceObservable Qi.scale M.nu σ
            (A (fields i))
          Bi ^ 2 * Ti * (Ti + 4))

noncomputable def nativeHeatQ3RefinedCarrierSourceRows
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  nativeHeatQ3RefinedCarrierSourceRowsForFields M h m
    (fun i => heatVHEATDriftRefinedChildField m t g z i)

end
end ASDExplicitGamma.Native
