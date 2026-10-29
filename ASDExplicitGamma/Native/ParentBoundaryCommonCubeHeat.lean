module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeCarrier
public import ASDExplicitGamma.Gaussian.BandModelMoments
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Actual common-center descendant heat law on any translated source square. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian Inverse Triadic Response
open scoped ENNReal
noncomputable section

local instance parentCommonCubeObservedCompact (Q : TriadicCube 2) : CompactSpace (closure (openCubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_openCubeSet Q).isCompact_closure

local instance parentCommonCubeResponseMeasurable (Q : TriadicCube 2) :
    MeasurableSpace (ResponseCoefficient (openCubeSet Q)) := borel _

local instance parentCommonCubeResponseBorel (Q : TriadicCube 2) :
    BorelSpace (ResponseCoefficient (openCubeSet Q)) := ⟨rfl⟩

local instance parentCommonCubeHeatCompact (P : TriadicCube 2) : CompactSpace (closure (cubeSet P)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet P).isCompact_closure

local instance parentCommonCubeResponseSecondCountable (Q : TriadicCube 2) :
    SecondCountableTopology (ResponseCoefficient (openCubeSet Q)) := by
  let e : ResponseCoefficient (openCubeSet Q) → C(closure (openCubeSet Q),ℝ) :=
    fun f => f.toContinuousMap
  have he : Isometry e := by
    intro f g
    rw [edist_dist,edist_dist]
    simp [e,BoundedContinuousFunction.dist_eq_iSup,ContinuousMap.dist_eq_iSup]
  exact he.isEmbedding.secondCountableTopology

/-- Actual descendant expectation on the one common source-square band. -/
def parentBoundaryCommonCubeAverage (M : ABKModel 2) {P Q : TriadicCube 2} {d : ℕ}
    (hQ : Q ∈ descendantsAtDepth P d) (n : ℤ) (height : ℕ)
    (Φ : ResponseCoefficient (openCubeSet Q) → ℝ) (t : ℝ) : ℝ :=
  ∫ ω,Φ (parentBoundaryCommonCubeObserved hQ n height t ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- Every polynomial-growth observable has its actual finite moments on
this exact common-center descendant coefficient. -/
theorem parent_boundary_common_cube_test_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (Φ : ResponseCoefficient (openCubeSet Q) → ℝ)
    (hΦ : Measurable Φ) (hgrowth : HasPolynomialGrowth Φ) (t p : ℝ) (hp : 2 ≤ p) :
    MemLp (fun ω => Φ (parentBoundaryCommonCubeObserved hQ n height t ω))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let parentCommonCubeHeightNonzero : NeZero height := ⟨by omega⟩
  let K := closure (cubeSet P)
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K (isBounded_cubeSet P).isCompact_closure
  have hk : Function.Injective (nativeSourceBandIndex n height) := by
    intro i j hij
    apply Fin.ext
    dsimp [nativeSourceBandIndex] at hij
    omega
  obtain ⟨T,v,hA,hlaw⟩ := exists_modelBand_realization K M h hM (nativeSourceBandIndex n height) hk
  exact memLp_bandModel_test K M ell n hK (nativeSourceBandIndex n height) hA T hlaw
    (parentBoundaryCommonOpenCellCoefficient hQ)
    ((parentBoundaryCommonOpenCellCoefficient hQ).comp (centeringMap (parentBoundaryCommonCubeCenter P)))
    Φ hΦ hgrowth t hp

end
end ASDExplicitGamma.Native
