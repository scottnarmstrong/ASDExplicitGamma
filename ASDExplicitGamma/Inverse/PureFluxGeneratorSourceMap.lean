module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorSource
public import ASDExplicitGamma.Main.LocalizedHessian
public import ASDExplicitGamma.Variational.ProjectedSource
public import ASDExplicitGamma.Scalar.ProjectionRealization

/-! Solenoidal changes of a pure-flux source do not change its weighted
complementary projection. This is the source-side map needed to replace the
raw response shear by the DIAG row field. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Scalar
open ASDExplicitGamma.Main

namespace ASDExplicitGamma.Inverse

local instance pureFluxSourceMapFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The second physical component of an actual response shear. -/
noncomputable def pureFluxResponseShearSourceField (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient (openCubeSet Q))
    (X : HilbertBlockL2 (openCubeSet Q)) : Vec 2 → Vec 2 :=
  fun x => (hilbertBlockL2ToBlockL2
    (responseShearL2Operator σ hσ H X) x).2

/-- A response shear is literally a pure-second source with its second
component as load. -/
theorem pureFlux_responseShear_eq_projectedSourceLoad (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient (openCubeSet Q))
    (X : HilbertBlockL2 (openCubeSet Q))
    (hF : MemLp (pureFluxResponseShearSourceField Q σ hσ H X) 2
      (normalizedCubeMeasure Q)) :
    responseShearL2Operator σ hσ H X = projectedSourceLoad Q hF := by
  let U := openCubeSet Q
  let F := pureFluxResponseShearSourceField Q σ hσ H X
  let hFvec : MemVectorL2 U F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hshear : hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X) =ᵐ[
      volumeMeasureOn U] fun x => (0, F x) := by
    filter_upwards [responseShearL2Operator_toBlockL2_ae σ hσ H X] with x hx
    calc
      hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X) x =
          responseShearCorrection σ (responseCoefficientExtension H x)
            (hilbertBlockL2ToBlockL2 X x) := hx
      _ = (0, (responseShearCorrection σ (responseCoefficientExtension H x)
          (hilbertBlockL2ToBlockL2 X x)).2) := rfl
      _ = (0, F x) := by
        congr 1
        exact congrArg Prod.snd hx.symm
  have hload : hilbertBlockL2ToBlockL2 (projectedSourceLoad Q hF) =ᵐ[
      volumeMeasureOn U] fun x => (0, F x) := by
    filter_upwards [coeFn_hilbertBlockL2ToBlockL2 (F := projectedSourceLoad Q hF),
      (ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn U)
        (L := hilbertPureSecond.toContinuousLinearMap)
        (f := toHilbertVectorL2OfVecField hFvec)),
      coeFn_toHilbertVectorL2OfVecField hFvec] with x htransport hpure hvec
    rw [htransport]
    change (hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hFvec) x).toBlockVec = _
    have hpure' : hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hFvec) x =
        hilbertPureSecond.toContinuousLinearMap (hilbertifyVecField F x) := by
      simpa [hilbertPureSecondL2, hvec] using hpure
    rw [hpure']
    simp [hilbertPureSecond, blockField, HilbertBlockVec.toBlockVec, hilbertifyVecField]
  apply (continuousLinearEquivBlockL2 (U := U)).symm.injective
  apply Lp.ext
  filter_upwards [hshear, hload] with x hxF hxG
  change hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X) x =
    hilbertBlockL2ToBlockL2 (projectedSourceLoad Q hF) x
  rw [hxF, hxG]

/-- If two vector loads differ by a solenoidal zero-normal-trace field, then
their actual weighted projected-source residuals agree. -/
theorem pureFlux_projectedSource_residual_eq_of_solenoidal_difference
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F G : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hG : MemLp G 2 (normalizedCubeMeasure Q))
    (hsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (fun x => F x - G x)) :
    scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF) =
      scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hG) := by
  let U := openCubeSet Q
  let hFvec : MemVectorL2 U F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  let hGvec : MemVectorL2 U G :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hG
  let hΔ : MemVectorL2 U (fun x => F x - G x) := hFvec.sub hGvec
  let D := responseFrameEnergyData (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k
  let V := responseFrameEnergyVariationSpace (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k
  have hsourceDiff :
      projectedSourceLoad Q hF - projectedSourceLoad Q hG =
        hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hΔ) := by
    change hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hFvec) -
      hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hGvec) = _
    rw [← map_sub (hilbertPureSecondL2 U)]
    have hvec : toHilbertVectorL2OfVecField hΔ =
        toHilbertVectorL2OfVecField hFvec - toHilbertVectorL2OfVecField hGvec := by
      change toHilbertVectorL2OfVecField (hFvec.sub hGvec) = _
      exact toHilbertVectorL2OfVecField_sub hFvec hGvec
    rw [hvec]
  have hvar :
      responseEnergyUp D (projectedSourceLoad Q hF - projectedSourceLoad Q hG) ∈
        V.toSubmodule := by
    rw [hsourceDiff]
    exact main_pure_flux_variation_mem Q ν σ hν hσ k (fun x => F x - G x)
      hΔ hsol
  have hproj :
      V.toSubmodule.starProjection (responseEnergyUp D (projectedSourceLoad Q hF)) -
        V.toSubmodule.starProjection (responseEnergyUp D (projectedSourceLoad Q hG)) =
      responseEnergyUp D (projectedSourceLoad Q hF) -
        responseEnergyUp D (projectedSourceLoad Q hG) := by
    rw [← map_sub]
    exact V.toSubmodule.starProjection_mem_subspace_eq_self
      ⟨responseEnergyUp D (projectedSourceLoad Q hF - projectedSourceLoad Q hG), hvar⟩
  change (responseEnergyUp D (projectedSourceLoad Q hF) -
      V.toSubmodule.starProjection (responseEnergyUp D (projectedSourceLoad Q hF))).down =
    (responseEnergyUp D (projectedSourceLoad Q hG) -
      V.toSubmodule.starProjection (responseEnergyUp D (projectedSourceLoad Q hG))).down
  congr 1
  calc
    responseEnergyUp D (projectedSourceLoad Q hF) -
        V.toSubmodule.starProjection (responseEnergyUp D (projectedSourceLoad Q hF)) =
      responseEnergyUp D (projectedSourceLoad Q hF) -
        V.toSubmodule.starProjection (responseEnergyUp D (projectedSourceLoad Q hG)) -
        (responseEnergyUp D (projectedSourceLoad Q hF) -
          responseEnergyUp D (projectedSourceLoad Q hG)) := by
            rw [← hproj]
            abel
    _ = responseEnergyUp D (projectedSourceLoad Q hG) -
        V.toSubmodule.starProjection (responseEnergyUp D (projectedSourceLoad Q hG)) := by
          abel

/-- The abstract Lemma V lift identifies the raw response-shear load with the
negative DIAG row load at the level of the actual weighted projection. -/
theorem pureFlux_projectedSource_residual_eq_of_lemmaV_lift
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q))
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η v : H1Function (openCubeSet Q))
    (hres : MemH10 (openCubeSet Q) (v-I v).toFun)
    (hη : MemLp η.toFun (⊤ : ENNReal) (volume.restrict (openCubeSet Q)))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal)
      (volume.restrict (openCubeSet Q)))
    (hraw : MemLp (fun x => -((η.toFun x) •
      matVecMul responsePlanarJ (v.grad x))) 2 (normalizedCubeMeasure Q))
    (hrow : MemLp (fun x => -(lemmaVPlanarRowField I η v x)) 2
      (normalizedCubeMeasure Q)) :
    scalarProjectionResidual Q ν σ hν hσ k
      (projectedSourceLoad Q hraw) =
    scalarProjectionResidual Q ν σ hν hσ k
      (projectedSourceLoad Q hrow) := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  have hlift := lemmaV_lift_of_interpolant hU I v η hres hη hDη
  have hsol' := isSolenoidalZeroNormalTraceOn_smul hlift (-1 : ℝ)
  have hsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (fun x =>
      -((η.toFun x) • matVecMul responsePlanarJ (v.grad x)) -
        -(lemmaVPlanarRowField I η v x)) := by
    convert hsol' using 1
    ext x i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    ring
  exact pureFlux_projectedSource_residual_eq_of_solenoidal_difference
    Q ν σ hν hσ k hraw hrow hsol

/-- The exact generator field is the weighted projected-source residual of
the actual response shear load. -/
theorem pureFluxResponseGeneratorY_eq_projectedSourceResidual
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (P : BlockVec 2) (k H : ResponseCoefficient (openCubeSet Q))
    (hF : MemLp (pureFluxResponseShearSourceField Q σ hσ H
      ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
        ν σ hν hσ k).toMuHilbertRealization.minimizerMap P)) 2
      (normalizedCubeMeasure Q)) :
    pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      ν σ hν hσ P k H =
    responseEnergyUp
      (responseFrameEnergyData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
        ν σ hν hσ k)
      (scalarProjectionResidual Q ν σ hν hσ k
        (projectedSourceLoad Q hF)) := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let V : ClosedSubmodule ℝ (EnergyCarrier D) :=
    responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let C : ResponseCoefficient (openCubeSet Q) →L[ℝ]
      (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
    responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S : EnergyCarrier D :=
    responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  let X := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.minimizerMap P
  have hshear : responseShearL2Operator σ hσ H X = projectedSourceLoad Q hF := by
    exact pureFlux_responseShear_eq_projectedSourceLoad Q σ hσ H X hF
  have hCS : C H S = responseEnergyUp D (projectedSourceLoad Q hF) := by
    change responseEnergyConjugateOperator D (responseShearL2Operator σ hσ H) S = _
    rw [responseEnergyConjugateOperator_apply]
    have hS : S.down = X := rfl
    rw [hS, hshear]
    rfl
  have hproj (z : EnergyCarrier D) :
      ((V.toSubmodule.orthogonalProjectionOnto z : V.toSubmodule) : EnergyCarrier D) =
        V.toSubmodule.starProjection z :=
    Submodule.coe_orthogonalProjectionOnto_apply V.toSubmodule z
  change C H S -
    (V.toSubmodule.orthogonalProjectionOnto (C H S) : EnergyCarrier D) = _
  rw [hCS, hproj]
  change responseEnergyUp D (projectedSourceLoad Q hF) -
      V.toSubmodule.starProjection (responseEnergyUp D (projectedSourceLoad Q hF)) =
    responseEnergyUp D (scalarProjectionResidual Q ν σ hν hσ k
      (projectedSourceLoad Q hF))
  rfl

end ASDExplicitGamma.Inverse
