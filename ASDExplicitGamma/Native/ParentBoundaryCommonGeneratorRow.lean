module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorActualSource

/-! Actual projected-source identification for any common-center physical
direction. The center is not required to belong to the observed cube. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Main Triadic Inverse
open scoped ENNReal
noncomputable section

local instance parentBoundaryCommonGeneratorRowFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The actual response generator source is the projected negative DIAG
row. The only identities supplied are the literal coefficient/frame link and
the actual affine minimizer's potential characterization. No source-energy,
generator or history estimate is assumed. -/
theorem parent_boundary_common_generator_row_identity
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (P : BlockVec 2) (k H : ResponseCoefficient (openCubeSet Q))
    (η : PlanarW2Infinity Q) (r : H10Function (openCubeSet Q))
    (hlink : η.value.toFun =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => responseCoefficientExtension H x / σ)
    (hfirst : (fun x => (hilbertBlockL2ToBlockL2
      ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r).grad)
    (m : ℕ) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let F := fun x => -(lemmaVPlanarRowField (diagInterpolant Q m) η.value v x)
    ∃ hrow : MemLp F 2 (normalizedCubeMeasure Q),
      pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ P k H =
      responseEnergyUp (responseFrameEnergyData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k)
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hrow)) := by
  intro v F
  let U := openCubeSet Q
  let hv : 0 < (volume U).toReal := by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  let M := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let X := M.toMuHilbertRealization.minimizerMap P
  let I := diagInterpolant Q m
  let Factual := pureFluxResponseShearSourceField Q σ hσ H X
  have hFactual : MemLp Factual 2 (normalizedCubeMeasure Q) :=
    pureFluxResponseShearSourceField_memLp Q σ hσ H X
  have hactualRaw : Factual =ᵐ[volume.restrict U]
      (fun x => -(η.value.toFun x • matVecMul responsePlanarJ (v.grad x))) := by
    filter_upwards [responseShearL2Operator_toBlockL2_ae σ hσ H X,hfirst,hlink] with x hs hf hη
    change (hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X) x).2 = _
    rw [hs]
    change -((responseCoefficientExtension H x / σ) •
      matVecMul responsePlanarJ ((hilbertBlockL2ToBlockL2 X x).1)) = _
    rw [← hη,hf]
  have hraw : MemLp (fun x => -(η.value.toFun x • matVecMul responsePlanarJ (v.grad x)))
      2 (normalizedCubeMeasure Q) := by
    have hvec : MemVectorL2 U (fun x => -(η.value.toFun x • matVecMul responsePlanarJ (v.grad x))) := by
      change MemLp (-(fun x => η.value.toFun x • matVecMul responsePlanarJ (v.grad x))) 2
        (volumeMeasureOn U)
      exact (lemmaVPlanar_skewGradient_memL2 v η.value_memLp_top).neg
    have hcoord (i : Fin 2) : MemLp
        (fun x => -(η.value.toFun x • matVecMul responsePlanarJ (v.grad x)) i) 2
        (normalizedCubeMeasure Q) :=
      memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hvec i)
    exact memLp_pi_iff.mpr hcoord
  have hzero : IsSolenoidalZeroNormalTraceOn U (fun x =>
      Factual x - -(η.value.toFun x • matVecMul responsePlanarJ (v.grad x))) := by
    intro ψ
    have hdot : (fun x => vecDot
      (Factual x - -(η.value.toFun x • matVecMul responsePlanarJ (v.grad x))) (ψ.grad x)) =ᵐ[volume.restrict U] 0 := by
      filter_upwards [hactualRaw] with x hx
      simp [hx,vecDot]
    rw [integral_congr_ae hdot]
    simp
  have hactualProjection := pureFlux_projectedSource_residual_eq_of_solenoidal_difference
    Q ν σ hν hσ k hFactual hraw hzero
  have hres : MemH10 U (v-I v).toFun := diagInterpolant_affine_residual_memH10 Q m P.1 r
  have hrow : MemLp F 2 (normalizedCubeMeasure Q) := by
    have hvec := lemmaVPlanarRowField_memL2 I η.value v η.value_memLp_top η.gradient_memLp_top_volume
    have hcoord (i : Fin 2) : MemLp (fun x => -(lemmaVPlanarRowField I η.value v x i))
        2 (normalizedCubeMeasure Q) :=
      memLp_normalized_of_memL2On ((memScalarL2_coord_of_memVectorL2 hvec i).neg)
    exact memLp_pi_iff.mpr hcoord
  have hrowProjection := pureFlux_projectedSource_residual_eq_of_lemmaV_lift
    Q ν σ hν hσ k I η.value v hres η.value_memLp_top η.gradient_memLp_top_volume hraw hrow
  refine ⟨hrow,?_⟩
  rw [pureFluxResponseGeneratorY_eq_projectedSourceResidual Q ν σ hν hσ P k H hFactual,
    hactualProjection,hrowProjection]

end
end ASDExplicitGamma.Native
