module

public import ASDExplicitGamma.Response.FrameAlgebra
public import Homogenization.CoarseGraining.MuOperator.CoeffOperator
public import Mathlib.Topology.TietzeExtension

@[expose] public section

namespace ASDExplicitGamma.Response

open Homogenization

noncomputable section

/-- Bounded continuous physical skew coefficients on the closed response domain. -/
abbrev ResponseCoefficient (U : Set (Vec 2)) :=
  BoundedContinuousFunction (closure U) ℝ

/-- Extend a coefficient from the closed response domain to the plane without
increasing its sup norm. The extension is only used to present measurable
pointwise fields; its values off `U` do not affect the `L²` operators. -/
noncomputable def responseCoefficientExtension {U : Set (Vec 2)}
    (H : ResponseCoefficient U) : BoundedContinuousFunction (Vec 2) ℝ := by
  let e : C(closure U, Vec 2) := ⟨Subtype.val, continuous_subtype_val⟩
  exact Classical.choose
    (BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding'
      H e isClosed_closure.isClosedEmbedding_subtypeVal)

theorem responseCoefficientExtension_norm {U : Set (Vec 2)}
    (H : ResponseCoefficient U) :
    ‖responseCoefficientExtension H‖ = ‖H‖ := by
  unfold responseCoefficientExtension
  exact (Classical.choose_spec
    (BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding'
      H ⟨Subtype.val, continuous_subtype_val⟩
      isClosed_closure.isClosedEmbedding_subtypeVal)).1

theorem responseCoefficientExtension_eq {U : Set (Vec 2)}
    (H : ResponseCoefficient U) {x : Vec 2} (hx : x ∈ U) :
    responseCoefficientExtension H x = H ⟨x, subset_closure hx⟩ := by
  unfold responseCoefficientExtension
  have hext := (Classical.choose_spec
    (BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding'
      H ⟨Subtype.val, continuous_subtype_val⟩
      isClosed_closure.isClosedEmbedding_subtypeVal)).2
  have h := congrArg (fun G : ResponseCoefficient U =>
    G ⟨x, subset_closure hx⟩) hext
  simpa using h

theorem responseCoefficientExtension_add_on {U : Set (Vec 2)}
    (H K : ResponseCoefficient U) {x : Vec 2} (hx : x ∈ U) :
    responseCoefficientExtension (H + K) x =
      responseCoefficientExtension H x + responseCoefficientExtension K x := by
  rw [responseCoefficientExtension_eq (H + K) hx,
    responseCoefficientExtension_eq H hx, responseCoefficientExtension_eq K hx]
  rfl

theorem responseCoefficientExtension_smul_on {U : Set (Vec 2)}
    (c : ℝ) (H : ResponseCoefficient U) {x : Vec 2} (hx : x ∈ U) :
    responseCoefficientExtension (c • H) x =
      c * responseCoefficientExtension H x := by
  rw [responseCoefficientExtension_eq (c • H) hx,
    responseCoefficientExtension_eq H hx]
  rfl

/-- The physical nilpotent shear as a bounded operator on the pointwise
four-dimensional Euclidean carrier. -/
def responseShearBlockMatrix (σ η : ℝ) : BlockMat 2 :=
  { upperLeft := 0
    upperRight := 0
    lowerLeft := -((η / σ) • responsePlanarJ)
    lowerRight := 0 }

noncomputable def responseShearMatrixOperator (σ η : ℝ) :
    HilbertBlockVec 2 →L[ℝ] HilbertBlockVec 2 :=
  HilbertBlockVec.applyBlockMat (responseShearBlockMatrix σ η)

noncomputable def responseShearPointwiseOperator (σ η : ℝ) :
    HilbertBlockVec 2 →L[ℝ] HilbertBlockVec 2 :=
  η • responseShearMatrixOperator σ 1

@[simp] theorem responseShearPointwiseOperator_apply (σ η : ℝ)
    (X : HilbertBlockVec 2) :
    responseShearPointwiseOperator σ η X =
      HilbertBlockVec.ofBlockVec (0,
        -((η / σ) • matVecMul responsePlanarJ X.toBlockVec.1)) := by
  apply HilbertBlockVec.ext
  · apply HilbertVec.ext
    intro i
    simp [responseShearPointwiseOperator, responseShearMatrixOperator,
      responseShearBlockMatrix, HilbertBlockVec.applyBlockMat_apply,
      blockMatVecMul, matVecMul]
  · ext i
    simp [responseShearPointwiseOperator, responseShearMatrixOperator,
      responseShearBlockMatrix, HilbertBlockVec.applyBlockMat_apply,
      blockMatVecMul, matVecMul, div_eq_mul_inv]
    ring_nf

theorem responseShearPointwiseOperator_smul (σ η : ℝ) :
    responseShearPointwiseOperator σ η =
      η • responseShearPointwiseOperator σ 1 := by
  simp [responseShearPointwiseOperator]

private theorem responseShearMatrixOperator_norm_le (σ η : ℝ) :
    ‖responseShearMatrixOperator σ η‖ ≤ |η / σ| := by
  apply HilbertBlockVec.opNorm_applyBlockMat_le_of_block_bound
  · positivity
  · intro X
    rcases X with ⟨p, q⟩
    have hout : blockMatVecMul (responseShearBlockMatrix σ η) (p, q) =
        (0, -((η / σ) • matVecMul responsePlanarJ p)) := by
      apply Prod.ext
      · funext i
        simp [responseShearBlockMatrix, blockMatVecMul, matVecMul]
      · funext i
        simp [responseShearBlockMatrix, blockMatVecMul, matVecMul,
          Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
        ring
    have hJ := responsePlanarJ_vecNormSq p
    rw [hout]
    have houtnorm : blockVecDot (0, -((η / σ) • matVecMul responsePlanarJ p))
        (0, -((η / σ) • matVecMul responsePlanarJ p)) =
        (η / σ) ^ 2 * vecNormSq p := by
      calc
        _ = (η / σ) ^ 2 * vecNormSq (matVecMul responsePlanarJ p) := by
          simp [blockVecDot, vecDot, vecNormSq, Pi.neg_apply,
            Pi.smul_apply, Fin.sum_univ_two]
          ring_nf
        _ = _ := by rw [hJ]
    rw [houtnorm]
    have hp : 0 ≤ vecNormSq p := vecNormSq_nonneg p
    have hq : 0 ≤ vecNormSq q := vecNormSq_nonneg q
    rw [sq_abs]
    simp only [blockVecDot, vecNormSq, vecDot] at *
    nlinarith

theorem responseShearPointwiseOperator_norm_le (σ η : ℝ) :
    ‖responseShearPointwiseOperator σ η‖ ≤ |η / σ| := by
  calc
    ‖responseShearPointwiseOperator σ η‖ =
        |η| * ‖responseShearMatrixOperator σ 1‖ := by
          simp [responseShearPointwiseOperator, norm_smul]
    _ ≤ |η| * |1 / σ| := by
          exact mul_le_mul_of_nonneg_left
            (responseShearMatrixOperator_norm_le σ 1) (abs_nonneg _)
    _ = |η / σ| := by
      rw [div_eq_mul_inv, abs_mul, abs_inv]
      simp only [abs_one]
      rw [abs_div, div_eq_mul_inv]
      ring

theorem responseShearPointwiseOperator_pairwise_nilpotent (σ η θ : ℝ) :
    responseShearPointwiseOperator σ η ∘L
      responseShearPointwiseOperator σ θ = 0 := by
  apply ContinuousLinearMap.ext
  intro X
  rw [ContinuousLinearMap.comp_apply,
    responseShearPointwiseOperator_apply,
    responseShearPointwiseOperator_apply]
  have hzero : matVecMul responsePlanarJ
      (HilbertVec.toVec (0 : HilbertVec 2)) = 0 := by
    ext i
    simp [matVecMul, HilbertVec.toVec]
  simp [hzero]

/-- The measurable pointwise field for a physical coefficient direction. -/
noncomputable def responseShearOperatorField {U : Set (Vec 2)}
    (σ : ℝ) (hσ : 0 < σ)
    (H : ResponseCoefficient U) : PointwiseHilbertBlockOperatorField U where
  field := fun x => responseCoefficientExtension H x •
    responseShearPointwiseOperator σ 1
  measurable_field := by
    have hcont : Continuous (fun x : Vec 2 => responseCoefficientExtension H x •
        responseShearPointwiseOperator σ 1) := by
      fun_prop
    exact hcont.measurable
  opNormBound := ‖H‖ / σ
  opNormBound_nonneg := div_nonneg (norm_nonneg _) hσ.le
  le_opNormBound := by
    intro x
    calc
      ‖responseCoefficientExtension H x • responseShearPointwiseOperator σ 1‖ ≤
          |responseCoefficientExtension H x| * |1 / σ| := by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left
          (responseShearPointwiseOperator_norm_le σ 1)
          (abs_nonneg _)
      _ = |responseCoefficientExtension H x| / σ := by
        rw [abs_div, abs_of_pos hσ]
        ring
      _ ≤ ‖H‖ / σ := by
        apply div_le_div_of_nonneg_right ?_ hσ.le
        calc
          |responseCoefficientExtension H x| =
              ‖responseCoefficientExtension H x‖ := by simp
          _ ≤ ‖responseCoefficientExtension H‖ :=
              (responseCoefficientExtension H).norm_coe_le_norm x
          _ = ‖H‖ := responseCoefficientExtension_norm H

noncomputable def responseShearL2Operator {U : Set (Vec 2)}
    (σ : ℝ) (hσ : 0 < σ)
    (H : ResponseCoefficient U) : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U :=
  (responseShearOperatorField σ hσ H).toContinuousLinearMap

theorem responseShearL2Operator_add {U : Set (Vec 2)}
    (hU : MeasurableSet U) (σ : ℝ) (hσ : 0 < σ)
    (H K : ResponseCoefficient U) :
    responseShearL2Operator σ hσ (H + K) =
      responseShearL2Operator σ hσ H + responseShearL2Operator σ hσ K := by
  apply ContinuousLinearMap.ext
  intro F
  apply MeasureTheory.Lp.ext
  let MHK := responseShearOperatorField σ hσ (H + K)
  let MH := responseShearOperatorField σ hσ H
  let MK := responseShearOperatorField σ hσ K
  have hUae : ∀ᵐ x ∂volumeMeasureOn U, x ∈ U :=
    MeasureTheory.ae_restrict_of_forall_mem hU (fun x hx => hx)
  filter_upwards [MHK.coeFn_toContinuousLinearMap F,
    MH.coeFn_toContinuousLinearMap F, MK.coeFn_toContinuousLinearMap F,
    MeasureTheory.Lp.coeFn_add (responseShearL2Operator σ hσ H F)
      (responseShearL2Operator σ hσ K F), hUae] with x hHK hH hK hadd hx
  calc
    responseShearL2Operator σ hσ (H + K) F x = MHK.applyFn F x := hHK
    _ = MH.applyFn F x + MK.applyFn F x := by
      change MHK.field x (F x) = MH.field x (F x) + MK.field x (F x)
      have hc := responseCoefficientExtension_add_on H K hx
      simp [MHK, MH, MK, responseShearOperatorField, hc, add_smul]
    _ = responseShearL2Operator σ hσ H F x +
        responseShearL2Operator σ hσ K F x := by
      change MH.applyFn F x + MK.applyFn F x =
        (MH.toContinuousLinearMap F) x + (MK.toContinuousLinearMap F) x
      exact congrArg₂ (fun a b => a + b) hH.symm hK.symm
    _ = (responseShearL2Operator σ hσ H F +
        responseShearL2Operator σ hσ K F) x := hadd.symm

theorem responseShearL2Operator_smul {U : Set (Vec 2)}
    (hU : MeasurableSet U) (σ : ℝ) (hσ : 0 < σ)
    (c : ℝ) (H : ResponseCoefficient U) :
    responseShearL2Operator σ hσ (c • H) =
      c • responseShearL2Operator σ hσ H := by
  apply ContinuousLinearMap.ext
  intro F
  apply MeasureTheory.Lp.ext
  let MCH := responseShearOperatorField σ hσ (c • H)
  let MH := responseShearOperatorField σ hσ H
  have hUae : ∀ᵐ x ∂volumeMeasureOn U, x ∈ U :=
    MeasureTheory.ae_restrict_of_forall_mem hU (fun x hx => hx)
  filter_upwards [MCH.coeFn_toContinuousLinearMap F,
    MH.coeFn_toContinuousLinearMap F,
    MeasureTheory.Lp.coeFn_smul c (responseShearL2Operator σ hσ H F), hUae]
      with x hCH hH hsmul hx
  calc
    responseShearL2Operator σ hσ (c • H) F x = MCH.applyFn F x := hCH
    _ = c • MH.applyFn F x := by
      change MCH.field x (F x) = c • MH.field x (F x)
      have hc := responseCoefficientExtension_smul_on c H hx
      simp [MCH, MH, responseShearOperatorField, hc, smul_smul]
    _ = c • (responseShearL2Operator σ hσ H F x) := by
      change c • MH.applyFn F x = c • (MH.toContinuousLinearMap F) x
      exact congrArg (fun a => c • a) hH.symm
    _ = (c • responseShearL2Operator σ hσ H F) x := hsmul.symm

/-- The coefficient-to-operator family on standard `L²`; the physical shear
is continuous and pairwise nilpotent. -/
noncomputable def responseShearL2FamilyLinear {U : Set (Vec 2)}
    (hU : MeasurableSet U) (σ : ℝ) (hσ : 0 < σ) :
    ResponseCoefficient U →ₗ[ℝ]
      (HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) where
  toFun := responseShearL2Operator σ hσ
  map_add' := responseShearL2Operator_add hU σ hσ
  map_smul' := responseShearL2Operator_smul hU σ hσ

theorem responseShearL2Operator_opNorm_le {U : Set (Vec 2)}
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient U) :
    ‖responseShearL2Operator σ hσ H‖ ≤ ‖H‖ / σ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hσ.le)
  intro F
  exact (responseShearOperatorField σ hσ H).norm_apply_le F

noncomputable def responseShearL2Family {U : Set (Vec 2)}
    (hU : MeasurableSet U) (σ : ℝ) (hσ : 0 < σ) :
    ResponseCoefficient U →L[ℝ]
      (HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) :=
  (responseShearL2FamilyLinear hU σ hσ).mkContinuous (1 / σ) (by
    intro H
    calc
      ‖responseShearL2Operator σ hσ H‖ ≤ ‖H‖ / σ :=
        responseShearL2Operator_opNorm_le σ hσ H
      _ = (1 / σ) * ‖H‖ := by ring)

private theorem responseShearOperatorField_pairwise_nilpotent {U : Set (Vec 2)}
    (σ : ℝ) (hσ : 0 < σ) (H K : ResponseCoefficient U) (x : Vec 2) :
    (responseShearOperatorField σ hσ H).field x ∘L
        (responseShearOperatorField σ hσ K).field x = 0 := by
  change (responseCoefficientExtension H x • responseShearPointwiseOperator σ 1) ∘L
      (responseCoefficientExtension K x • responseShearPointwiseOperator σ 1) = 0
  rw [← responseShearPointwiseOperator_smul σ (responseCoefficientExtension H x),
    ← responseShearPointwiseOperator_smul σ (responseCoefficientExtension K x)]
  exact responseShearPointwiseOperator_pairwise_nilpotent σ _ _

theorem responseShearL2Operator_pairwise_nilpotent {U : Set (Vec 2)}
    (σ : ℝ) (hσ : 0 < σ) (H K : ResponseCoefficient U) :
    responseShearL2Operator σ hσ H ∘L responseShearL2Operator σ hσ K = 0 := by
  apply ContinuousLinearMap.ext
  intro F
  apply MeasureTheory.Lp.ext
  let MH := responseShearOperatorField σ hσ H
  let MK := responseShearOperatorField σ hσ K
  let hzeroAe := MeasureTheory.Lp.coeFn_zero
    (E := HilbertBlockVec 2) (p := (2 : ENNReal)) (μ := volumeMeasureOn U)
  filter_upwards [MH.coeFn_toContinuousLinearMap
      (responseShearL2Operator σ hσ K F),
    MK.coeFn_toContinuousLinearMap F, hzeroAe] with x hH hK hzero
  calc
    (responseShearL2Operator σ hσ H ∘L responseShearL2Operator σ hσ K) F x =
        MH.applyFn (responseShearL2Operator σ hσ K F) x := hH
    _ = MH.field x (MK.field x (F x)) := by
      change MH.field x (responseShearL2Operator σ hσ K F x) = _
      have hK' : responseShearL2Operator σ hσ K F x = MK.field x (F x) := by
        simpa [responseShearL2Operator,
          PointwiseHilbertBlockOperatorField.applyFn] using hK
      rw [hK']
    _ = 0 := by
      have hp := responseShearOperatorField_pairwise_nilpotent σ hσ H K x
      have hpX := congrArg (fun T : HilbertBlockVec 2 →L[ℝ] HilbertBlockVec 2 =>
        T (F x)) hp
      simpa [ContinuousLinearMap.comp_apply] using hpX
    _ = (0 : HilbertBlockL2 U) x := by simpa using hzero.symm

end

end ASDExplicitGamma.Response
