module

public import ASDExplicitGamma.Variational.LocalizedInterpolantOperators
public import ASDExplicitGamma.Triadic.HilbertSkewMultipliers
public import ASDExplicitGamma.Variational.LocalizedShearWeak

/-! The literal localized row as a bounded operator on the closed affine-gradient space. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

 theorem weakColumnDivergence_memLp_top {U : Set (Vec 2)} (η : H1Function U)
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict U)) :
    MemLp (fun x => HilbertVec.ofVec (lemmaVPlanarWeakColumnDivergence η x)) ⊤ (volume.restrict U) := by
  have hg : MemLp η.grad ⊤ (volume.restrict U) := MemLp.of_eval hDη
  have hh := (HilbertVec.continuousLinearEquivVec 2).symm.toContinuousLinearMap.comp_memLp' hg
  have h := (-hilbertPlanarJ.toContinuousLinearMap).comp_memLp' hh
  simpa [hilbertPlanarJ, lemmaVPlanarWeakColumnDivergence, Function.comp_def, HilbertVec.toVec] using! h


 def weakColumnDivergenceLp {U : Set (Vec 2)} (η : H1Function U)
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict U)) : Lp (HilbertVec 2) ⊤ (volume.restrict U) :=
  (weakColumnDivergence_memLp_top η hDη).toLp (fun x => HilbertVec.ofVec (lemmaVPlanarWeakColumnDivergence η x))

 def localizedRowOperator (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict (openCubeSet Q)))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hI : ∀ v ∈ affinePotentialSubmodule Q, ‖(I v).gradToHilbertVectorL2‖ ≤ A*‖v.gradToHilbertVectorL2‖)
    (hR : ∀ v ∈ affinePotentialSubmodule Q, ‖(v-I v).toScalarL2‖ ≤ B*‖v.gradToHilbertVectorL2‖) :
    affineGradientClosedSubmodule Q →L[ℝ] HilbertVectorL2 (openCubeSet Q) :=
  ((lpScalarMultiplication (volume.restrict (openCubeSet Q)) (hη.toLp η.toFun)).comp
    (hilbertPlanarJ.toContinuousLinearMap.compLpL 2 (volume.restrict (openCubeSet Q)))).comp
      (interpolantGradientOperator Q I hA hI) +
  (lpVectorMultiplication (volume.restrict (openCubeSet Q)) (weakColumnDivergenceLp η hDη)).comp
      (interpolantResidualOperator Q I hB hR)

 theorem localizedRowOperator_norm_le (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict (openCubeSet Q)))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hI : ∀ v ∈ affinePotentialSubmodule Q, ‖(I v).gradToHilbertVectorL2‖ ≤ A*‖v.gradToHilbertVectorL2‖)
    (hR : ∀ v ∈ affinePotentialSubmodule Q, ‖(v-I v).toScalarL2‖ ≤ B*‖v.gradToHilbertVectorL2‖) :
    ‖localizedRowOperator Q I η hη hDη hA hB hI hR‖ ≤
      A*‖hη.toLp η.toFun‖+B*‖weakColumnDivergenceLp η hDη‖ := by
  let μ := volume.restrict (openCubeSet Q)
  have hM := lpScalarMultiplication_norm_le (E := HilbertVec 2) μ (hη.toLp η.toFun)
  have hN := lpVectorMultiplication_norm_le μ (weakColumnDivergenceLp η hDη)
  have hJ : ‖hilbertPlanarJ.toContinuousLinearMap.compLpL 2 μ‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans (LinearIsometry.norm_toContinuousLinearMap_le _)
  have hG := (interpolantGradientOperator_spec Q I hA hI).1
  have hV := (interpolantResidualOperator_spec Q I hB hR).1
  unfold localizedRowOperator
  apply (ContinuousLinearMap.opNorm_add_le _ _).trans
  apply add_le_add
  · apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans
    have hMJ := mul_le_mul hM hJ (norm_nonneg _) (norm_nonneg _)
    have hfull := mul_le_mul hMJ hG (ContinuousLinearMap.opNorm_nonneg _) (by positivity : 0 ≤ ‖hη.toLp η.toFun‖*1)
    convert hfull using 1
    ring
  · apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    have hfull := mul_le_mul hN hV (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _)
    convert hfull using 1
    ring

end
end ASDExplicitGamma.Variational
