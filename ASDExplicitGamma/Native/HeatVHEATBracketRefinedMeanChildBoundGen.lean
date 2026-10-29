module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanChildBound
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurableGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrandGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNormsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedProfileGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedPhysicalGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedBindingGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceObserverGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedActualGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedRowGen
public import ASDExplicitGamma.Native.Q3GridOverlapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSupportGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedObservationGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedParentLawGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSourceMapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanVarianceGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedRemainderGen
import ASDExplicitGamma.Gaussian.HilbertBasisVariance

/-! The `ns`-shell generalization of `HeatVHEATBracketRefinedMeanChildBound`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped RealInnerProductSpace Topology

variable (ns : ℕ) [NeZero ns]

local instance nativeHeatQ3RefinedMeanChildBoundCompact_GenBracketRefinedMeanChildBound (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

/-- A single child's contribution to the averaged Riesz vector is controlled
by the actual child-scale SHEAR history/trace profile. -/
theorem nativeHeatQ3RefinedCarrierChildMeanObservationRiesz_sq_le_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin ns)
    (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ j : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let s : ℕ := d.val + 2
    let b := q3ModelAmplitude M h (Q.scale + (s : ℤ))
    let L := q3ModelLength (Q.scale + (s : ℤ))
    let A := nativeHeat_translateTriadicFieldToOrigin Q
    let B := lemmaVTileHistory (originCube 2 Q.scale) (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField M.nu σ
        (pureFluxOpenResponseRestriction Q.scale (A (x i))))
    let ρ := cubeScaleFactor (originCube 2 Q.scale) / L.1
    let δ := diagMeshRadius (originCube 2 Q.scale)
      (pureFluxBankSourceDepth s) / L.1
    ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
        ((nativeHeatQ3RefinedChildMeanTraceObservation M σ m x i).comp
          (q3RemainderValueFactor
            (cubeCorner Q 0) (cubeCorner Q 0 + cubeScaleFactor Q)
            (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q)
            b L
            ⟨cubeCenter Q,
              nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
                (subset_closure
                  (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet Q))⟩))‖ ^ 2 ≤
      4 * (b ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
        (modelTraceObservable Q.scale M.nu σ (A (x i))) *
          (modelTraceObservable Q.scale M.nu σ (A (x i)) + 4) := by
  classical
  dsimp only
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let s : ℕ := d.val + 2
  let b := q3ModelAmplitude M h (Q.scale + (s : ℤ))
  let L := q3ModelLength (Q.scale + (s : ℤ))
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  let B := lemmaVTileHistory (originCube 2 Q.scale) (pureFluxBankSourceDepth s)
    (responseFramePlanarCoefficientField M.nu σ
      (pureFluxOpenResponseRestriction Q.scale (A (x i))))
  let ρ := cubeScaleFactor (originCube 2 Q.scale) / L.1
  let δ := diagMeshRadius (originCube 2 Q.scale)
    (pureFluxBankSourceDepth s) / L.1
  let Φ := modelTraceObservable Q.scale M.nu σ
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun j => cubeSet (nativeHeatQ3RefinedCarrierChild m j)
  let hU : ∀ j, MeasurableSet (U j) :=
    fun j => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m j)
  let hvol : ∀ j, 0 < (volume (U j)).toReal :=
    fun j => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m j)
  let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j))
  let hV : ∀ j, V j ⊆ nativeHeatQ3RefinedCarrierDomain m :=
    nativeHeatQ3RefinedCarrierChild_closure_subset m
  let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
  let π := ContinuousLinearMap.proj (R := ℝ)
    (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i
  let D := fderiv ℝ
    (childTraceObservable (measurableSet_cubeSet Q)
      (volume_cubeSet_toReal_pos Q) M.nu σ M.nu_pos hσ) (x i)
  let Achild := D.comp (π.comp R₀)
  let r := nativeHeatQ3RefinedCarrierParentRestrict m
  let p := (nativeHeatQ3RefinedCarrierParentSourceGen ns) M h m d
  let O := nativeHeatQ3RefinedChildMeanTraceObservation M σ m x i
  let childFactor := q3RemainderValueFactor
    (cubeCorner Q 0) (cubeCorner Q 0 + cubeScaleFactor Q)
    (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q)
    b L
    ⟨cubeCenter Q,
      nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
        (subset_closure
          (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet Q))⟩
  have hvar := (nativeHeatQ3RefinedCarrierParentObservationRiesz_eq_Gen ns)
    M h hM m Ffam d Achild
  have hsource (u : WhiteNoise) :=
    (nativeHeatQ3RefinedCarrierParentCenteredSource_eq_childRemainders_Gen ns)
      M h m d u
  have hsourcei (u : WhiteNoise) :
      R₀ (r (p u)) i =
        nativeHeatQ3RefinedCarrierChildRectangleToCube m i (childFactor u) := by
    have hi := congrFun (hsource u) i
    simpa [R₀, V, hV, r, p, childFactor, Q, s, b, L,
      nativeHeatQ3RefinedCarrierParentSourceGen,
      nativeHeatQ3RefinedCarrierChild_scale] using hi
  have hmap : (Achild.comp r).comp p = O.comp childFactor := by
    ext u
    change (fderiv ℝ
      (childTraceObservable
        (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q)
        M.nu σ M.nu_pos hσ) (x i))
        ((R₀ (r (p u))) i) = O (childFactor u)
    rw [hsourcei u]
    have hobs := nativeHeatQ3RefinedCarrierChildTrace_fderiv_toOrigin
      Q M.nu σ M.nu_pos hσ (x i)
    rw [hobs]
    rfl
  have hnorm :
      ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm (O.comp childFactor)‖ ^ 2 =
        ∑' j, (Achild (Ffam.factor d (Ffam.direction d j))) ^ 2 := by
    rw [← hmap]
    exact hvar.symm
  let P := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
  let C₀ := centeringMap (pureFluxParentCenter Q.scale)
  have hpoint (j : ℕ) :
      Achild (Ffam.factor d (Ffam.direction d j)) =
        fderiv ℝ Φ (A (x i))
          (C₀ (A (P (Ffam.factor d (Ffam.direction d j))))) := by
    change (fderiv ℝ
      (childTraceObservable
        (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q)
        M.nu σ M.nu_pos hσ) (x i))
        ((R₀ (Ffam.factor d (Ffam.direction d j))) i) = _
    rw [nativeHeatQ3RefinedCarrierChildTrace_fderiv_toOrigin
      Q M.nu σ M.nu_pos hσ (x i)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [nativeHeatQ3RefinedCarrierChildRemainder_translate_eq_centered m i
      (Ffam.factor d (Ffam.direction d j))]
  have hsum :
      (∑' j, (Achild (Ffam.factor d (Ffam.direction d j))) ^ 2) =
        modelGradientSquareTrace Φ
          (fun j => C₀ (A (P (Ffam.factor d (Ffam.direction d j))))) (A (x i)) := by
    unfold modelGradientSquareTrace
    apply tsum_congr
    intro j
    rw [hpoint j]
  have hrow := (nativeHeatQ3RefinedCarrierChildCenteredFreshShellBracket_le_Gen ns)
    M h hM m Ffam i d σ hσ (x i)
  have hrow' :
      modelGradientSquareTrace Φ
        (fun j => C₀ (A (P (Ffam.factor d (Ffam.direction d j))))) (A (x i)) ≤
          4 * (b ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
            Φ (A (x i)) * (Φ (A (x i)) + 4) := by
    simpa only [Q, s, b, L, A, B, ρ, δ, Φ, P, C₀] using hrow
  calc
    _ = ∑' j, (Achild (Ffam.factor d (Ffam.direction d j))) ^ 2 := hnorm
    _ = modelGradientSquareTrace Φ
        (fun j => C₀ (A (P (Ffam.factor d (Ffam.direction d j))))) (A (x i)) := hsum
    _ ≤ 4 * (b ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
        Φ (A (x i)) * (Φ (A (x i)) + 4) := hrow'

end ASDExplicitGamma.Native
