module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanGeometry
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanVariance
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedRemainder
import ASDExplicitGamma.Gaussian.HilbertBasisVariance

/-! The local SHEAR rows bound the Riesz energy of each centered child
observation by its translated history and heat-trace profile. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped RealInnerProductSpace Topology

local instance nativeHeatQ3RefinedMeanChildBoundCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

/-- A single child's contribution to the averaged Riesz vector is controlled
by the actual child-scale SHEAR history/trace profile. -/
theorem nativeHeatQ3RefinedCarrierChildMeanObservationRiesz_sq_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9)
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
  let p := nativeHeatQ3RefinedCarrierParentSource M h m d
  let O := nativeHeatQ3RefinedChildMeanTraceObservation M σ m x i
  let childFactor := q3RemainderValueFactor
    (cubeCorner Q 0) (cubeCorner Q 0 + cubeScaleFactor Q)
    (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q)
    b L
    ⟨cubeCenter Q,
      nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
        (subset_closure
          (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet Q))⟩
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  have hvar := nativeHeatQ3RefinedCarrierParentObservationRiesz_eq
    M h hM m d Achild
  have hsource (u : WhiteNoise) :=
    nativeHeatQ3RefinedCarrierParentCenteredSource_eq_childRemainders
      M h m d u
  have hsourcei (u : WhiteNoise) :
      R₀ (r (p u)) i =
        nativeHeatQ3RefinedCarrierChildRectangleToCube m i (childFactor u) := by
    have hi := congrFun (hsource u) i
    simpa [R₀, V, hV, r, p, childFactor, Q, s, b, L,
      nativeHeatQ3RefinedCarrierParentSource,
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
        ∑' j, (Achild (F.factor d (F.direction d j))) ^ 2 := by
    rw [← hmap]
    exact hvar.symm
  let P := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
  let C₀ := centeringMap (pureFluxParentCenter Q.scale)
  have hpoint (j : ℕ) :
      Achild (F.factor d (F.direction d j)) =
        fderiv ℝ Φ (A (x i))
          (C₀ (A (P (F.factor d (F.direction d j))))) := by
    change (fderiv ℝ
      (childTraceObservable
        (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q)
        M.nu σ M.nu_pos hσ) (x i))
        ((R₀ (F.factor d (F.direction d j))) i) = _
    rw [nativeHeatQ3RefinedCarrierChildTrace_fderiv_toOrigin
      Q M.nu σ M.nu_pos hσ (x i)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [nativeHeatQ3RefinedCarrierChildRemainder_translate_eq_centered m i
      (F.factor d (F.direction d j))]
  have hsum :
      (∑' j, (Achild (F.factor d (F.direction d j))) ^ 2) =
        modelGradientSquareTrace Φ
          (fun j => C₀ (A (P (F.factor d (F.direction d j))))) (A (x i)) := by
    unfold modelGradientSquareTrace
    apply tsum_congr
    intro j
    rw [hpoint j]
  have hrow := nativeHeatQ3RefinedCarrierChildCenteredFreshShellBracket_le
    M h hM m i d σ hσ (x i)
  have hrow' :
      modelGradientSquareTrace Φ
        (fun j => C₀ (A (P (F.factor d (F.direction d j))))) (A (x i)) ≤
          4 * (b ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
            Φ (A (x i)) * (Φ (A (x i)) + 4) := by
    simpa only [Q, s, b, L, A, B, ρ, δ, Φ, F, P, C₀] using hrow
  calc
    _ = ∑' j, (Achild (F.factor d (F.direction d j))) ^ 2 := hnorm
    _ = modelGradientSquareTrace Φ
        (fun j => C₀ (A (P (F.factor d (F.direction d j))))) (A (x i)) := hsum
    _ ≤ 4 * (b ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
        Φ (A (x i)) * (Φ (A (x i)) + 4) := hrow'

end ASDExplicitGamma.Native
