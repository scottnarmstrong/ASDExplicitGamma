module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanObservation
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSourceMap
public import ASDExplicitGamma.Native.HeatVHEATFamily

/-! Named objects for the fixed-shell covariance-to-Riesz identity. -/

@[expose] public section

namespace ASDExplicitGamma.Native

noncomputable section

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped RealInnerProductSpace Topology

local instance nativeHeatQ3RefinedMeanRieszIndexNeZero :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance nativeHeatQ3RefinedMeanRieszChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatQ3RefinedMeanRieszChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn
      (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

noncomputable def nativeHeatQ3RefinedCarrierMeanTrace
    (M : ABKModel 2) (m : ℤ) (σ : ℝ) (hσ : 0 < σ) :
    (∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) → ℝ :=
  childMeanTrace
    (fun i => cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
    M.nu σ M.nu_pos hσ

noncomputable def nativeHeatQ3RefinedCarrierRemainderMap (m : ℤ) :
    C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ]
      (∀ i : nativeHeatQ3RefinedCarrierIndex,
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :=
  childRemainderMap
    (fun i => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)))
    (nativeHeatQ3RefinedCarrierChild_closure_subset m)
    (nativeHeatQ3RefinedCarrierCenter m)

/-- The actual physical child trace derivative composed with that child's
q3 remainder factor. This is definitionally the observation used by the
fixed-shell covariance-to-Riesz interface. -/
noncomputable def nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (d : Fin 9) (σ : ℝ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (i : nativeHeatQ3RefinedCarrierIndex) : WhiteNoise →L[ℝ] ℝ := by
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let s : ℕ := d.val + 2
  exact (nativeHeatQ3RefinedChildMeanTraceObservation M σ m x i).comp
    (q3RemainderValueFactor
      (cubeCorner Q 0) (cubeCorner Q 0 + cubeScaleFactor Q)
      (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q)
      (q3ModelAmplitude M h (m + (s : ℤ)))
      (q3ModelLength (m + (s : ℤ)))
      ⟨cubeCenter Q,
        nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
          (subset_closure
            (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet Q))⟩)

/-- The normalized average of the actual child remainder-observation Riesz
vectors, indexed symbolically by the Cartesian refined grid. -/
noncomputable def nativeHeatQ3RefinedCarrierMeanRieszAverage
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (d : Fin 9) (σ : ℝ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) : WhiteNoise :=
  ((Finset.univ : Finset (Fin (3 ^ 10) × Fin (3 ^ 10))).card : ℝ)⁻¹ •
    ∑ ij : Fin (3 ^ 10) × Fin (3 ^ 10),
      (InnerProductSpace.toDual ℝ WhiteNoise).symm
        (nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
          M h m d σ x (finProdFinEquiv ij))

/-- The actual fresh-shell vector sequence, named once so theorem statements
do not repeatedly elaborate the full carrier-family structure. -/
noncomputable def nativeHeatQ3RefinedCarrierFreshShellVector
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (d : Fin 9) : ℕ → C(nativeHeatQ3RefinedCarrierDomain m, ℝ) :=
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  fun j => F.factor d (F.direction d j)

noncomputable def nativeHeatQ3RefinedCarrierParentSource'
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (d : Fin 9) :
    WhiteNoise →L[ℝ]
      C(closure (cubeSet (originCube 2 (m + 10))), ℝ) := by
  let s : ℕ := d.val + 2
  let β := q3ModelAmplitude M h (m + (s : ℤ))
  let L := q3ModelLength (m + (s : ℤ))
  exact (mainCubeH3Value (m + 10) β L).comp
    (q3H3RangeFactor (-mainCubeHalfSide (m + 10))
      (mainCubeHalfSide (m + 10)) (-mainCubeHalfSide (m + 10))
      (mainCubeHalfSide (m + 10)) β L)

end

end ASDExplicitGamma.Native
