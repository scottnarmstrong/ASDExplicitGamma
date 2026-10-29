module

public import ASDExplicitGamma.Scalar.PhysicalResolventIdentity
public import ASDExplicitGamma.Scalar.CoefficientFlux

/-! T4 support: public copies of private transport lemmas, and the explicit second
component of the doubled planar coefficient action. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Triadic
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem fw_hilbertSecondProjection_toBlock_ae (U : Set (Vec 2))
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

theorem fw_hilbertBlock_firstInsert_toBlock_ae (U : Set (Vec 2))
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

theorem fw_hilbertVectorL2_norm_sq_integral (U : Set (Vec 2))
    (f : Vec 2 → Vec 2) (hf : MemVectorL2 U f) :
    ‖toHilbertVectorL2OfVecField hf‖ ^ 2 =
      ∫ x in U, vecNormSq (f x) ∂MeasureTheory.volume := by
  rw [← real_inner_self_eq_norm_sq,
    inner_toHilbertVectorL2OfVecField_eq_integral hf hf]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  simp [vecDot, vecNormSq]

theorem fw_shear_toPlain_ae
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
    fw_hilbertBlock_firstInsert_toBlock_ae U p
  have hS := responseShearL2Operator_toBlockL2_ae σ hσ H (hilbertPureFirstL2 U p)
  have hP := fw_hilbertSecondProjection_toBlock_ae U S
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

theorem fw_toHilbertVectorL2OfVecField_hilbertVectorL2ToVectorL2
    {U : Set (Vec 2)} (p : HilbertVectorL2 U) :
    toHilbertVectorL2OfVecField
        (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 p)) = p := by
  let f := hilbertVectorL2ToVectorL2 p
  let hf : MemVectorL2 U f := MeasureTheory.Lp.memLp f
  calc
    toHilbertVectorL2OfVecField hf =
        vectorL2ToHilbertVectorL2 (toVectorL2 hf) :=
          (vectorL2ToHilbertVectorL2_toVectorL2 hf).symm
    _ = vectorL2ToHilbertVectorL2 (hilbertVectorL2ToVectorL2 p) := by
      congr 1
      exact MeasureTheory.Lp.toLp_coeFn (hilbertVectorL2ToVectorL2 p)
        (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 p))
    _ = p := vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 p

theorem fw_physicalField_memPotentialSpace
    (Q : TriadicCube 2) {f : Vec 2 → Vec 2}
    (hf : MemVectorL2 (openCubeSet Q) f)
    (hpot : IsPotentialZeroTraceOn (openCubeSet Q) f) :
    toHilbertVectorL2OfVecField hf ∈
      (physicalPotentialSpace Q).toSubmodule := by
  change toHilbertVectorL2OfVecField hf ∈
    PotentialSolenoidalExact.potentialZeroTrace (openCubeSet Q)
  rw [PotentialSolenoidalExact.mem_potentialZeroTrace_iff]
  rcases hpot with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_toHilbertVectorL2OfVecField hf,
    u.toH1Function.coeFn_gradToHilbertVectorL2] with x hfield hgrad
  rw [hfield, hgrad]
  simp [hilbertifyVecField, ← hu]

theorem fw_physicalField_memSolenoidalSpace
    (Q : TriadicCube 2) {g : Vec 2 → Vec 2}
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) g) :
    toHilbertVectorL2OfVecField hg ∈
      (physicalSolenoidalSpace Q).toSubmodule := by
  change toHilbertVectorL2OfVecField hg ∈
    PotentialSolenoidalExact.solenoidalZeroNormalTrace (openCubeSet Q)
  rw [PotentialSolenoidalExact.mem_solenoidalZeroNormalTrace_iff]
  intro u
  rw [show u.gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField u.grad_memVectorL2 from rfl]
  rw [inner_toHilbertVectorL2OfVecField_eq_integral hg u.grad_memVectorL2]
  exact hsol u

theorem fw_symm (c κ : ℝ) :
    symmPart (responsePlanarCoefficient c κ) = c • (1 : Mat 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [responsePlanarCoefficient, responsePlanarJ, symmPart,
      Matrix.smul_apply, smul_eq_mul]

theorem fw_skew (c κ : ℝ) :
    skewPart (responsePlanarCoefficient c κ) = κ • responsePlanarJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [responsePlanarCoefficient, responsePlanarJ, skewPart,
      Matrix.smul_apply, smul_eq_mul]
  all_goals ring

theorem fw_symm_inv (c : ℝ) (hc : c ≠ 0) :
    (c • (1 : Mat 2))⁻¹ = c⁻¹ • (1 : Mat 2) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  <;> field_simp

/-- The reciprocal-gradient component of the doubled coefficient action. -/
theorem fw_flux_snd (c κ : ℝ) (hc : 0 < c) (p q : Vec 2) :
    (blockMatVecMul (blockMatrixOfCoeff (responsePlanarCoefficient c κ)) (p, q)).2 =
      c⁻¹ • (q - κ • matVecMul responsePlanarJ p) := by
  rw [blockMatVecMul_snd]
  unfold blockMatrixOfCoeff
  simp only [fw_symm, fw_skew, fw_symm_inv c hc.ne']
  ext i
  fin_cases i <;>
    simp [matVecMul, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_two,
      responsePlanarJ, Pi.smul_apply, Pi.sub_apply] <;> ring

end

end ASDExplicitGamma.Scalar
