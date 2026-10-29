module

public import ASDExplicitGamma.Scalar.StationaryTrial
public import ASDExplicitGamma.Scalar.CutoffMeasurability
public import ASDExplicitGamma.Scalar.ViscosityCutoff
public import Algsuperdiff.Section3.Provider.Annealed.CubeScalar

/-! The parent comparison for arbitrary source potential loading. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Algsuperdiff.Section3
open ASDExplicitGamma.Variational
noncomputable section

/-- The literal terminal cutoff stream on the compact closure of a half-open cell. -/
def cutoffCubeSkew (N : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    ResponseCoefficient (cubeSet Q) := by
  let compactClosedCell : CompactSpace (closure (cubeSet Q)) :=
    isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Cutoff.cutoff N ω x.1 1 0,
      (Cutoff.continuous_cutoffValue_entry N ω 1 0).comp continuous_subtype_val⟩

theorem frame_top_quadratic_le_trial (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (cubeSet Q))
    (e : Vec 2) (F : Vec 2 → BlockVec 2)
    (hF : ScalarVariation (openCubeSet Q) F) :
    vecDot e (matVecMul (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
      (responsePlanarCoefficientField ν k))).upperLeft e) ≤
      volumeAverage (openCubeSet Q) (fun x => responseFrameEnergyDensity ν σ
        (responseCoefficientExtension k x) ((stateOfVariation (e,0) F).eval x)) := by
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_cubeSet Q) ν σ hν hσ k
  have hEllOpen := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hbound := mu_le_cell_patch_trial hEllOpen (e,0) F hF
  rw [← cube_Mu_eq_open Q (e,0)] at hbound
  rw [mu_eq_half_coarseBlockMatrix_elliptic_triCube (div_pos hν hσ) hEll (e,0),
    response_coarseMatrix_frame_eq (measurableSet_cubeSet Q) ν σ hν hσ k] at hbound
  have hquad (A : BlockMat 2) : blockVecDot (e,0) (blockMatVecMul A (e,0)) =
      vecDot e (matVecMul A.upperLeft e) := by
    simp only [blockVecDot, blockMatVecMul, matVecMul_zero, add_zero,
      vecDot_zero_left]
  rw [hquad] at hbound
  have heq : (fun x => responseFrameEnergyDensity ν σ (responseCoefficientExtension k x)
      ((stateOfVariation (e,0) F).eval x)) =
      fun x => 2*blockEnergyDensity (responseFramePlanarCoefficientField ν σ k)
        (stateOfVariation (e,0) F) x := by
    funext x
    exact responseFrameEnergyDensity_eq_twice_blockEnergyDensity ν σ hν hσ k _ x
  rw [heq]
  rw [show (fun x => 2*blockEnergyDensity (responseFramePlanarCoefficientField ν σ k)
      (stateOfVariation (e,0) F) x) =
      (2:ℝ) • (fun x => blockEnergyDensity (responseFramePlanarCoefficientField ν σ k)
        (stateOfVariation (e,0) F) x) from rfl, volumeAverage_smul]
  change _ ≤ 2*_
  linarith only [hbound]

/-- In the actual terminal coefficient, an arbitrary admissible source trial
bounds the physical top quadratic divided by the old true scalar. -/
theorem cutoff_top_quadratic_le_trial (M : ABKModel 2) (N : ℤ) (σ : ℝ)
    (hσ : 0 < σ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2)
    (e : Vec 2) (F : Vec 2 → BlockVec 2)
    (hF : ScalarVariation (openCubeSet Q) (F-constantBlockLoad (e,0))) :
    σ⁻¹*vecDot e (matVecMul (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu N ω).toFun).upperLeft e) ≤
      volumeAverage (openCubeSet Q) (fun x => responseFrameEnergyDensity M.nu σ
        (Cutoff.cutoff N ω x 1 0) (F x)) := by
  let k := cutoffCubeSkew N Q ω
  have hvalue {x : Vec 2} (hx : x ∈ cubeSet Q) :
      responseCoefficientExtension k x = Cutoff.cutoff N ω x 1 0 := by
    rw [responseCoefficientExtension_eq k hx]
    rfl
  have hcoeff : responsePlanarCoefficientField M.nu k =ᵐ[volume.restrict (cubeSet Q)]
      (Cutoff.coefficientCutoff M.nu N ω).toFun := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
    change responsePlanarCoefficient M.nu (responseCoefficientExtension k x) = _
    rw [hvalue hx]
    exact old_cutoff_coefficient_planar M.nu N ω x
  have hbound := frame_top_quadratic_le_trial Q M.nu σ M.nu_pos hσ k e
    (F-constantBlockLoad (e,0)) hF
  rw [coarseBlockMatrix_congr_of_ae_eq hcoeff] at hbound
  have hstate (x : Vec 2) :
      (stateOfVariation (e,0) (F-constantBlockLoad (e,0))).eval x = F x := by
    change (e,0)+(F x-(e,0)) = F x
    abel
  have heq : (fun x => responseFrameEnergyDensity M.nu σ (responseCoefficientExtension k x)
      ((stateOfVariation (e,0) (F-constantBlockLoad (e,0))).eval x)) =ᵐ[
      volume.restrict (openCubeSet Q)] fun x => responseFrameEnergyDensity M.nu σ
        (Cutoff.cutoff N ω x 1 0) (F x) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    rw [hstate, hvalue (openCubeSet_subset_cubeSet Q hx)]
  have havg := congrArg (fun t => (volume (openCubeSet Q)).toReal⁻¹*t) (integral_congr_ae heq)
  change volumeAverage (openCubeSet Q) _ = volumeAverage (openCubeSet Q) _ at havg
  rw [havg] at hbound
  simpa only [frameMatrix, smul_matVecMul, vecDot_smul_right] using hbound

/-- The expected physical top quadratic is exactly the annealed quadratic. -/
theorem integral_cutoff_top_quadratic (M : ABKModel 2) (N k : ℤ) (e : Vec 2) :
    (∫ ω, vecDot e (matVecMul (coarseBlockMatrix (cubeSet (originCube 2 k))
      (Cutoff.coefficientCutoff M.nu N ω).toFun).upperLeft e)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      vecDot e (matVecMul (Homogenization.Book.Ch04.annealedBlockMatrixAtScale
        (Cutoff.coefficientCutoffLaw M N) k).upperLeft e) := by
  unfold vecDot matVecMul
  rw [integral_finsetSum _ (fun i _ => (integrable_finsetSum Finset.univ
    (fun j _ => ((integrable_cutoff_top_entry M N k i j).mul_const (e j)))).const_mul (e i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, integral_finsetSum _
    (fun j _ => (integrable_cutoff_top_entry M N k i j).mul_const (e j))]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_mul_const, ← annealed_top_entry_cutoff_samples]

/-- Square symmetry identifies every unit potential loading with the same
annealed diagonal; no rotational invariance of the kernel is assumed. -/
theorem integral_cutoff_unit_top_quadratic (M : ABKModel 2) (N k : ℤ)
    (e : Vec 2) (he : vecDot e e=1) :
    (∫ ω, vecDot e (matVecMul (coarseBlockMatrix (cubeSet (originCube 2 k))
      (Cutoff.coefficientCutoff M.nu N ω).toFun).upperLeft e)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      (Homogenization.Book.Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M N) k).upperLeft 0 0 := by
  rw [integral_cutoff_top_quadratic]
  obtain ⟨a,b,hmean⟩ :=
    Provider.Annealed.coefficientCutoffLaw_exists_annealedBlockMatrixAtScale_eq_blockDiag_smul_one M N k
  rw [hmean]
  simp [Homogenization.Book.Ch02.blockDiag, smul_matVecMul, vecDot_smul_right]
  rw [show matVecMul (1 : Mat 2) e=e from Matrix.one_mulVec e, he, mul_one]

end
end ASDExplicitGamma.Scalar
