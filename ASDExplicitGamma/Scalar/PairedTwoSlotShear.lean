module

public import ASDExplicitGamma.Scalar.PhysicalResolventIdentity

/-! The physical positive shear acts pointwise (public copy of the private lemma). -/

@[expose] public section

open Homogenization
open ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped InnerProduct InnerProductSpace

namespace ASDExplicitGamma.Scalar
noncomputable section

theorem shear_hilbertSecondProjection_toBlock_ae (U : Set (Vec 2))
    (X : HilbertBlockL2 U) :
    hilbertVectorL2ToVectorL2 (hilbertSecondProjection U X) =ᵐ[volumeMeasureOn U]
      fun x => (hilbertBlockL2ToBlockL2 X x).2 := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2)
      (μ := volumeMeasureOn U)
      (L := hilbertBlockSecondProjectionVec) (f := X),
    coeFn_hilbertVectorL2ToVectorL2 (hilbertSecondProjection U X),
    coeFn_hilbertBlockL2ToBlockL2 X] with x hproj hvector hblock
  rw [hvector]
  change ((hilbertBlockSecondProjectionVec.compLpL 2 (volumeMeasureOn U) X) x).toVec = _
  rw [hproj, hblock]
  simp [hilbertBlockSecondProjectionVec, HilbertBlockVec.flux]

theorem shear_hilbertBlock_firstInsert_toBlock_ae (U : Set (Vec 2))
    (p : HilbertVectorL2 U) :
    hilbertBlockL2ToBlockL2 (hilbertPureFirstL2 U p) =ᵐ[volumeMeasureOn U]
      fun x => (hilbertVectorL2ToVectorL2 p x, 0) := by
  filter_upwards [coeFn_hilbertBlockL2ToBlockL2 (hilbertPureFirstL2 U p),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn U)
      (L := pureFirst.toContinuousLinearMap) (f := p),
    coeFn_hilbertVectorL2ToVectorL2 p] with x hblock hinsert hp
  rw [hblock]
  change ((pureFirst.toContinuousLinearMap.compLpL 2 (volumeMeasureOn U) p) x).toBlockVec = _
  rw [hinsert, hp]
  apply Prod.ext
  · ext i
    simp [pureFirst, HilbertVec.toVec]
  · ext i
    simp [pureFirst, HilbertVec.toVec]

theorem positiveShear_toPlain_ae
    (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (H : ResponseCoefficient (openCubeSet Q))
    (p : HilbertVectorL2 (openCubeSet Q)) :
    hilbertVectorL2ToVectorL2
        (physicalPositiveShear Q σ hσ H p) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => (responseCoefficientExtension H x / σ) •
        matVecMul responsePlanarJ (hilbertVectorL2ToVectorL2 p x) := by
  let U := openCubeSet Q
  let S := responseShearL2Operator σ hσ H (hilbertPureFirstL2 U p)
  have hp : hilbertBlockL2ToBlockL2 (hilbertPureFirstL2 U p) =ᵐ[volumeMeasureOn U]
      fun x => (hilbertVectorL2ToVectorL2 p x, 0) :=
    shear_hilbertBlock_firstInsert_toBlock_ae U p
  have hS := responseShearL2Operator_toBlockL2_ae σ hσ H (hilbertPureFirstL2 U p)
  have hP := shear_hilbertSecondProjection_toBlock_ae U S
  have hmap : hilbertVectorL2ToVectorL2
      (physicalPositiveShear Q σ hσ H p) =
        -hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S) := by
    change hilbertVectorL2ToVectorL2 (-(hilbertSecondProjection U S)) = _
    exact map_neg (hilbertVectorL2ToVectorL2 (U := U)) _
  have hneg := MeasureTheory.Lp.coeFn_neg
    (hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S))
  change hilbertVectorL2ToVectorL2 (-(hilbertSecondProjection U S)) =ᵐ[volumeMeasureOn U] _
  filter_upwards [hP, hS, hp, hneg] with x hproj hshear hinsert hnegative
  calc
    hilbertVectorL2ToVectorL2 (physicalPositiveShear Q σ hσ H p) x =
        (-hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S)) x :=
      congrArg (fun f : VectorL2 U => f x) hmap
    _ = -hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S) x := hnegative
    _ = -((hilbertBlockL2ToBlockL2 S x).2) := by rw [hproj]
    _ = (responseCoefficientExtension H x / σ) •
        matVecMul responsePlanarJ (hilbertVectorL2ToVectorL2 p x) := by
      have hsecond := congrArg Prod.snd hshear
      rw [hinsert] at hsecond
      rw [hsecond]
      simp [responseShearCorrection]

end
end ASDExplicitGamma.Scalar
