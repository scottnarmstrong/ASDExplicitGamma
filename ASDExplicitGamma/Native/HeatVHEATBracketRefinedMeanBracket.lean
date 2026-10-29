module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanAverageProfiles
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanRieszIdentity

/-! The actual common-shell bracket of the refined child mean. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped RealInnerProductSpace Topology

/-- The global mean-gradient bracket for one actual refined common shell. -/
theorem nativeHeatQ3RefinedCarrierMeanRemainderBracket_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (d : Fin 9) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
      fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) :=
      fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal :=
      fun i => volume_cubeSet_toReal_pos (Q i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
      fun i => closure (U i)
    let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
      nativeHeatQ3RefinedCarrierChild_closure_subset m
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let R₀ := childRemainderMap V hV
      (nativeHeatQ3RefinedCarrierCenter m)
    let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
    let s : ℕ := d.val + 2
    let L := q3ModelLength (m + (s : ℤ))
    let profile : nativeHeatQ3RefinedCarrierIndex → ℝ := fun i =>
      let Q := nativeHeatQ3RefinedCarrierChild m i
      let A := nativeHeat_translateTriadicFieldToOrigin Q
      let k := pureFluxOpenResponseRestriction Q.scale (A (x i))
      let B := lemmaVTileHistory (originCube 2 Q.scale) (pureFluxBankSourceDepth s)
        (responseFramePlanarCoefficientField M.nu σ k)
      let T := modelTraceObservable Q.scale M.nu σ (A (x i))
      B ^ 2 * T * (T + 4)
    modelGradientSquareTrace μ
      (fun j => R₀ (F.factor d (F.direction d j))) x ≤
      4 * (q3ModelAmplitude M h (m + (s : ℤ)) ^ 2 / σ ^ 2) *
        q3GridOverlapFactor 10 s *
        (lemmaVH2Bn
          (cubeScaleFactor (originCube 2 m) / L.1)
          (diagMeshRadius (originCube 2 m) (pureFluxBankSourceDepth s) / L.1)) ^ 2 *
        ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
          ∑ i, profile i) := by
  calc
    _ = _ := nativeHeatQ3RefinedCarrierMeanRieszAverageIdentity
      M h hM m d σ hσ x
    _ ≤ _ := nativeHeatQ3RefinedCarrierMeanRieszAverage_sq_le_profiles
      M h hM m d σ hσ x

end ASDExplicitGamma.Native
