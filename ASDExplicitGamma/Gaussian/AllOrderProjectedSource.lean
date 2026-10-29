module

public import ASDExplicitGamma.Main.Q3FiniteColumn
public import ASDExplicitGamma.Main.HilbertTensorProduct
public import ASDExplicitGamma.Main.HilbertFiniteCoordinates
public import ASDExplicitGamma.Main.Q3ValueDerivatives
public import ASDExplicitGamma.Gaussian.GeneratorBounds
public import ASDExplicitGamma.Variational.LemmaVDiagEstimates
public import ASDExplicitGamma.Variational.ForcedSourceFeedback

/-! The DIAG row with coordinatewise projected-source potentials. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian

open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ASDExplicitGamma.Main ASDExplicitGamma.Numerics ASDExplicitGamma.Response
open scoped BigOperators

noncomputable section

local instance projectedSourceFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-! The scalar source residual is the literal response-energy orthogonal
complement projection of its pure-second load. -/

/-- Adding an admissible response variation does not change the orthogonal
complement component of a load. -/
theorem carrier_complement_projection_eq_of_diff_mem {Q : TriadicCube 2}
    (hU : MeasurableSet (openCubeSet Q))
    (hv : 0 < (volume (openCubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q))
    (z z' : EnergyCarrier (responseFrameEnergyData hU hv ν σ hν hσ k))
    (hDiff : z - z' ∈
      (responseFrameEnergyVariationSpace hU hv ν σ hν hσ k).toSubmodule) :
    ((responseFrameEnergyVariationSpace hU hv ν σ hν hσ k).toSubmoduleᗮ.starProjection z) =
      ((responseFrameEnergyVariationSpace hU hv ν σ hν hσ k).toSubmoduleᗮ.starProjection z') := by
  let V := responseFrameEnergyVariationSpace hU hv ν σ hν hσ k
  have hself := V.toSubmodule.starProjection_mem_subspace_eq_self
    (⟨z - z', hDiff⟩ : V.toSubmodule)
  have hsum := V.toSubmodule.starProjection_add_starProjection_orthogonal (z - z')
  have hzero : V.toSubmoduleᗮ.starProjection (z - z') = 0 := by
    rw [hself] at hsum
    exact (add_eq_left.mp hsum)
  calc
    V.toSubmoduleᗮ.starProjection z =
        V.toSubmoduleᗮ.starProjection (z' + (z - z')) := by congr 1; abel
    _ = V.toSubmoduleᗮ.starProjection z' +
        V.toSubmoduleᗮ.starProjection (z - z') := map_add _ _ _
    _ = V.toSubmoduleᗮ.starProjection z' := by rw [hzero, add_zero]

/-- When a response minimizer has a prescribed first field, its shear image
is the pure-second load with the literal physical `H/σ` factor. -/
theorem response_shear_eq_pureSecond_of_field (Q : TriadicCube 2)
    (hU : MeasurableSet (openCubeSet Q))
    (hv : 0 < (volume (openCubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k H : ResponseCoefficient (openCubeSet Q))
    (S : EnergyCarrier (responseFrameEnergyData hU hv ν σ hν hσ k))
    {F : Vec 2 → Vec 2} (hF : MemVectorL2 (openCubeSet Q) F)
    (hFae : F =ᵐ[volumeMeasureOn (openCubeSet Q)] (fun x =>
      -((responseCoefficientExtension H x / σ) • matVecMul responsePlanarJ
        (hilbertBlockL2ToBlockL2 S.down x).1))) :
    responseFrameEnergyShearFamily hU hv ν σ hν hσ k H S =
      responseEnergyUp (responseFrameEnergyData hU hv ν σ hν hσ k)
        (hilbertPureSecondL2 (openCubeSet Q) (toHilbertVectorL2OfVecField hF)) := by
  let U := openCubeSet Q
  let D := responseFrameEnergyData hU hv ν σ hν hσ k
  change responseEnergyUp D (responseShearL2Operator σ hσ H S.down) =
    responseEnergyUp D (hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hF))
  congr 1
  have hrep : hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H S.down) =
      hilbertBlockL2ToBlockL2
        (hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hF)) := by
    apply MeasureTheory.Lp.ext
    filter_upwards [responseShearL2Operator_toBlockL2_ae σ hσ H S.down,
      coeFn_hilbertBlockL2ToBlockL2
        (F := hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hF)),
      (ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn U)
        (L := hilbertPureSecond.toContinuousLinearMap)
        (f := toHilbertVectorL2OfVecField hF)),
      coeFn_toHilbertVectorL2OfVecField hF, hFae] with x hshear hpure htransport hvec hfield
    rw [hshear, hpure]
    change responseShearCorrection σ (responseCoefficientExtension H x)
        (hilbertBlockL2ToBlockL2 S.down x) = _
    have hpure' : hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hF) x =
        hilbertPureSecond.toContinuousLinearMap (hilbertifyVecField F x) := by
      simpa [hilbertPureSecondL2, hvec] using htransport
    rw [hpure']
    simp [responseShearCorrection, hfield, responsePlanarJ, hilbertPureSecond,
      HilbertVec.toVec, HilbertVec.toVec_ofVec, hilbertifyVecField]
    constructor
    · rfl
    · rw [← HilbertVec.continuousLinearEquivVec_apply]
      simp only [map_neg, map_smul, HilbertVec.continuousLinearEquivVec_apply,
        HilbertVec.toVec_ofVec]
  exact (continuousLinearEquivBlockL2 (U := U)).symm.injective hrep

/-- Re-expressing the projected-source residual in the response energy carrier
gives exactly the complementary projection used by the nilpotent Hessian
identity. -/
theorem projectedSource_carrier_complement_eq (Q : TriadicCube 2)
    (hU : MeasurableSet (openCubeSet Q))
    (hv : 0 < (volume (openCubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    let D := responseFrameEnergyData hU hv ν σ hν hσ k
    let V := responseFrameEnergyVariationSpace hU hv ν σ hν hσ k
    (V.toSubmoduleᗮ.starProjection
      (responseEnergyUp D (projectedSourceLoad Q hF)) : EnergyCarrier D) =
      responseEnergyUp D
        (Scalar.scalarProjectionResidual Q ν σ hν hσ k
          (projectedSourceLoad Q hF)) := by
  change (Scalar.scalarFrameVariationSpace Q ν σ hν hσ k).toSubmoduleᗮ.starProjection
      (responseEnergyUp (Scalar.scalarFrameEnergyData Q ν σ hν hσ k)
        (projectedSourceLoad Q hF)) =
    responseEnergyUp (Scalar.scalarFrameEnergyData Q ν σ hν hσ k)
      (Scalar.scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
  let D := Scalar.scalarFrameEnergyData Q ν σ hν hσ k
  let V := Scalar.scalarFrameVariationSpace Q ν σ hν hσ k
  let z := responseEnergyUp D (projectedSourceLoad Q hF)
  have hsum := V.toSubmodule.starProjection_add_starProjection_orthogonal z
  unfold Scalar.scalarProjectionResidual
  change V.toSubmoduleᗮ.starProjection z =
    responseEnergyUp D ((z - V.toSubmodule.starProjection z).down)
  have hResidual : V.toSubmoduleᗮ.starProjection z = z - V.toSubmodule.starProjection z := by
    calc
      V.toSubmoduleᗮ.starProjection z =
          (V.toSubmodule.starProjection z + V.toSubmoduleᗮ.starProjection z) -
            V.toSubmodule.starProjection z := by abel
      _ = z - V.toSubmodule.starProjection z := by rw [hsum]
  rw [hResidual]
  rfl

/-- The pure-shear source coordinate associated with a planar interpolant row. -/
noncomputable def planarShearSourceField {Q : TriadicCube 2}
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η : PlanarW2Infinity Q) (v : H1Function (openCubeSet Q)) : Vec 2 → Vec 2 :=
  fun x i => -planarQuarterTurn
    (fun a => η.value.toFun x * (I v).grad x a -
      η.value.grad x a * (v-I v).toFun x) i

/-- The actual physical response shear and the DIAG pure-shear source have the
same complementary response-energy projection. Their difference is the
localized column-divergence lift, which is an admissible solenoidal flux. -/
theorem planar_response_shear_complement_eq (Q : TriadicCube 2)
    (hU : MeasurableSet (openCubeSet Q))
    (hv : 0 < (volume (openCubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k H : ResponseCoefficient (openCubeSet Q))
    (S : EnergyCarrier (responseFrameEnergyData hU hv ν σ hν hσ k))
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η : PlanarW2Infinity Q) (v : H1Function (openCubeSet Q))
    (hres : MemH10 (openCubeSet Q) (v-I v).toFun)
    (F : Vec 2 → Vec 2)
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hsource : F = planarShearSourceField I η v)
    (hlink : η.value.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => responseCoefficientExtension H x / σ)
    (hfirst : (fun x =>
      (hilbertBlockL2ToBlockL2 S.down x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)] v.grad) :
    let D := responseFrameEnergyData hU hv ν σ hν hσ k
    let V := responseFrameEnergyVariationSpace hU hv ν σ hν hσ k
    V.toSubmoduleᗮ.starProjection (responseFrameEnergyShearFamily hU hv ν σ hν hσ k H S) =
      V.toSubmoduleᗮ.starProjection
        (responseEnergyUp D (projectedSourceLoad Q hF)) := by
  let U := openCubeSet Q
  let M := responseFrameMuOperatorSystemData hU hv ν σ hν hσ k
  let D := responseEnergyHilbertData M.toMuHilbertRealization
  let V := responseEnergyCorrectionSpace M.toMuHilbertRealization D
  let d := localizedColumnProductDivergence η.value (v-I v)
  have hη : MemLp η.value.toFun ⊤ (volume.restrict U) := η.value_memLp_top
  have hDη : ∀ i, MemLp (fun x => η.value.grad x i) ⊤ (volume.restrict U) :=
    fun i => PlanarW2Infinity.gradient_memLp_top_volume η i
  have hlift := lemmaV_interpolant_lift_source
    (isOpenBoundedConvexDomain_openCubeSet Q) I v η.value v hres hη hDη
  have hrowSource : planarShearSourceField I η v =
      fun x => -lemmaVPlanarRowField I η.value v x := by
    funext x i
    rw [lemmaVH2_rowField_eq]
    simp [planarShearSourceField, planarQuarterTurn]
  have hsumField : (fun x i => F x i + d x i) =
      fun x i => -(η.value.toFun x • matVecMul responsePlanarJ (v.grad x)) i := by
    funext x i
    rw [show F x = -lemmaVPlanarRowField I η.value v x by
      rw [hsource]
      exact congrFun hrowSource x]
    rw [← congrFun (localizedColumnProductDivergence_row_identity I η.value v) x]
    simp only [Pi.neg_apply, Pi.add_apply]
    simp [lemmaVPlanarRowField, Pi.smul_apply, smul_eq_mul,
      matVecMul, responsePlanarJ, Fin.sum_univ_two]
    ring
  have hFvec : MemVectorL2 U F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hd : MemVectorL2 U d := hlift.1
  have hsol : IsSolenoidalZeroNormalTraceOn U d := hlift.2.1
  let hG : MemVectorL2 U (fun x => F x + d x) := hFvec.add hd
  have hGae : (fun x i => (F x + d x) i) =ᵐ[volumeMeasureOn U]
      fun x => -((responseCoefficientExtension H x / σ) • matVecMul responsePlanarJ
        (hilbertBlockL2ToBlockL2 S.down x).1) := by
    filter_upwards [hlink, hfirst] with x hηH hS
    have hpoint := congrFun (congrFun hsumField x)
    funext i
    calc
      (F x + d x) i = -(η.value.toFun x • matVecMul responsePlanarJ (v.grad x)) i :=
        hpoint i
      _ = -((responseCoefficientExtension H x / σ) • matVecMul responsePlanarJ
          (hilbertBlockL2ToBlockL2 S.down x).1) i := by rw [hηH, hS]
  have hShear := response_shear_eq_pureSecond_of_field Q hU hv ν σ hν hσ k H S hG hGae
  have hLoadDiff : hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hG) -
      projectedSourceLoad Q hF =
      hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hd) := by
    rw [toHilbertVectorL2OfVecField_add hFvec hd]
    have hload : projectedSourceLoad Q hF =
        hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hFvec) := rfl
    rw [hload]
    simp only [map_add]
    exact add_sub_cancel_left _ _
  have hShear' : responseFrameEnergyShearFamily hU hv ν σ hν hσ k H S =
      responseEnergyUp D (hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hG)) := by
    simpa only [D, responseFrameEnergyData] using hShear
  have hCarrierDiff :
      (responseFrameEnergyShearFamily hU hv ν σ hν hσ k H S) -
        responseEnergyUp D (projectedSourceLoad Q hF) =
      responseEnergyUp D (hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hd)) := by
    calc
      _ = responseEnergyUp D (hilbertPureSecondL2 U
          (toHilbertVectorL2OfVecField hG)) -
            responseEnergyUp D (projectedSourceLoad Q hF) := by rw [hShear']
      _ = responseEnergyUp D
          (hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hd)) := by
        change responseEnergyUpLinear D
          (hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hG) -
            projectedSourceLoad Q hF) = _
        rw [hLoadDiff]
        rfl
  have hvariation : responseEnergyUp D
      (hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hd)) ∈ V.toSubmodule := by
    exact main_pure_flux_variation_mem Q ν σ hν hσ k d hd hsol
  have hDiff :
      (responseFrameEnergyShearFamily hU hv ν σ hν hσ k H S) -
        responseEnergyUp D (projectedSourceLoad Q hF) ∈ V.toSubmodule :=
    hCarrierDiff.symm ▸ hvariation
  have hproj := carrier_complement_projection_eq_of_diff_mem
    hU hv ν σ hν hσ k
    (responseFrameEnergyShearFamily hU hv ν σ hν hσ k H S)
    (responseEnergyUp D (projectedSourceLoad Q hF)) hDiff
  exact hproj

end
end ASDExplicitGamma.Gaussian
