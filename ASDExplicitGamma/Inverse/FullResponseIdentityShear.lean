module

public import ASDExplicitGamma.Inverse.FullResponseCellSensitivity
public import ASDExplicitGamma.Inverse.AssemblyShearSign
public import ASDExplicitGamma.Inverse.AssemblyPhysicalBand

/-! Exact full-response identity shear, adapted from the identity assembly.
The generic shear algebra and physical-band identification are reused. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Gaussian
noncomputable section

/-- The actual attenuated trace is bounded by the exactly sheared actual old
matrix, retaining the full paired-load sensitivity rather than a Young bound. -/
theorem good_cell_exact_shear_trace (M : ABKModel 2)
    (Q : TriadicCube 2) (r : RootRow) (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r) (waveGateEta (rootWaveTuple r)) Q) :
    let n := Q.scale+40
    let μ := cubeAverage Q (laterBandW2 Q n J (sourceBandWeights m weights) ω).value.toFun
    let σ := (Annealed.sigmaBar M n:ℝ)
    let B := coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun
    let R := constantSkewMatrix (μ/σ)
    Matrix.trace (toFullBlockMat (frameMatrix σ
      (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω))))/4 ≤
        rootEdelta r*(Matrix.trace (R.transpose*toFullBlockMat (frameMatrix σ B)*R)/4) := by
  dsimp only
  let n := Q.scale + 40
  let a := sourceBandWeights m weights
  let k := oldResponseCoefficient Q n ω
  let kH := laterResponseCoefficient Q n J a ω
  let h := laterBandW2 Q n J a ω
  let μ := cubeAverage Q h.value.toFun
  let kH0 := kH + BoundedContinuousFunction.const (closure (openCubeSet Q)) (-μ)
  let kC := sensitivityResponseCoefficientPath k kH0 1
  let kClosed := responseCoefficientOnClosedCube Q kC
  let σ := (Annealed.sigmaBar M n : ℝ)
  let g := μ / σ
  let B := coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hrep := later_response_coefficient_represents Q n J a ω
  have hcenter := good_cell_centered_full_pair_response M Q r m J weights hw ω hgood
  have hcenterField : (fun x => responsePlanarCoefficientField M.nu kClosed x) =ᵐ[
      volume.restrict (openCubeSet Q)] (sensitivityBaseRegField M.nu kC).toFun := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    have hxQ : x ∈ cubeSet Q := openCubeSet_subset_cubeSet Q hx
    have hext := responseCoefficientOnClosedCube_extension_eq Q kC hxQ
    have h := congrArg (fun z : ℝ => responsePlanarCoefficient M.nu z) hext
    simpa [sensitivityBaseRegField, responseFramePlanarCoefficientField,
      responsePlanarCoefficientField] using h
  have hcenterMatrix :
      coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu kClosed) =
        coarseBlockMatrix (cubeSet Q) (sensitivityBaseRegField M.nu kC).toFun := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q]
    exact coarseBlockMatrix_congr_of_ae_eq hcenterField
  have hpair : ∀ P : BlockVec 2,
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu kClosed)) P) ≤
      rootEdelta r * blockVecDot P (blockMatVecMul B P) := by
    intro P
    rw [hcenterMatrix]
    simpa only [B] using hcenter P
  have hmeanShift : σ * g = μ := by
    dsimp only [g]
    field_simp [hσ.ne']
  have hcenterLoad (x : Vec 2) (hx : x ∈ openCubeSet Q) :
      responseCoefficientExtension kC x =
        responseCoefficientExtension k x + responseCoefficientExtension kH x - μ := by
    change responseCoefficientExtension
      (sensitivityResponseCoefficientPath k kH0 1) x = _
    rw [sensitivityResponseCoefficientPath,
      responseCoefficientExtension_add_on k (1 • kH0) hx,
      responseCoefficientExtension_smul_on 1 kH0 hx]
    simp only [one_mul]
    dsimp only [kH0]
    rw [responseCoefficientExtension_add_on kH
      (BoundedContinuousFunction.const (closure (openCubeSet Q)) (-μ)) hx,
      responseCoefficientExtension_eq
        (BoundedContinuousFunction.const (closure (openCubeSet Q)) (-μ)) hx]
    simp only [BoundedContinuousFunction.const_apply]
    ring
  have hfield : (fun x => responsePlanarCoefficient M.nu
      (responseCoefficientExtension kClosed x + σ * g)) =ᵐ[
        volume.restrict (openCubeSet Q)] attenuatedCoefficient M m J weights ω := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    have hxQ : x ∈ cubeSet Q := openCubeSet_subset_cubeSet Q hx
    have hext := responseCoefficientOnClosedCube_extension_eq Q kC hxQ
    have hsum : responseCoefficientExtension kClosed x + σ * g =
        responseCoefficientExtension k x + responseCoefficientExtension kH x := by
      rw [hext, hmeanShift, hcenterLoad x hx]
      ring
    have hpath := sensitivity_path_represents_attenuated M Q n m J (by omega)
      hm weights ω hx
    simp only [sensitivityBaseRegField, responseFramePlanarCoefficientField,
      div_one] at hpath
    rw [responseCoefficientExtension_add_on k kH hx] at hpath
    rw [hsum]
    exact hpath
  have hactualMatrix :
      coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω) =
        coarseBlockMatrix (cubeSet Q) (fun x => responsePlanarCoefficient M.nu
          (responseCoefficientExtension kClosed x + σ * g)) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q]
    exact coarseBlockMatrix_congr_of_ae_eq hfield.symm
  rw [hactualMatrix,response_coarseBlockMatrix_constantSkew Q M.nu M.nu_pos kClosed]
  have htrace := assembly_shear_trace_domination
    (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu kClosed)) B
    (rootEdelta r) σ (σ*g) hσ hpair
  rw [hmeanShift] at htrace
  rw [hmeanShift]
  exact htrace

/-- On the actual good event, clipping preserves the complete old matrix. -/
theorem good_cell_clipped_exact_shear_trace (M : ABKModel 2)
    (Q : TriadicCube 2) (r : RootRow) (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r) (waveGateEta (rootWaveTuple r)) Q) :
    let n := Q.scale+40
    let μ := cubeAverage Q (laterBandW2 Q n J (sourceBandWeights m weights) ω).value.toFun
    let σ := (Annealed.sigmaBar M n:ℝ)
    let R := constantSkewMatrix (μ/σ)
    Matrix.trace (toFullBlockMat (frameMatrix σ
      (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω))))/4 ≤
        rootEdelta r*(Matrix.trace (R.transpose*clippedCellMatrix M n Q (rootTau r) ω*R)/4) := by
  have hraw := good_cell_raw_history M Q (rootTau r) (waveGateEta (rootWaveTuple r)) ω hgood
  dsimp only
  rw [clippedCellMatrix,Set.indicator_of_mem hraw,clippedSourceMatrix]
  exact good_cell_exact_shear_trace M Q r m J hn hm weights hw ω hgood

/-- The exact good-cell trace uses the same physical Gaussian added-stream
conjugator whose complete-family concentration is proved separately. -/
theorem good_cell_physical_shear_trace (M : ABKModel 2)
    (Q : TriadicCube 2) (r : RootRow) (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r) (waveGateEta (rootWaveTuple r)) Q) :
    let n := Q.scale+40
    let σ := (Annealed.sigmaBar M n:ℝ)
    let R := assemblyPhysicalShearMatrix M n Q.scale J
      (((Q.index 0:ℝ)-1/2)*(3:ℝ)^Q.scale)
      (((Q.index 1:ℝ)-1/2)*(3:ℝ)^Q.scale) (sourceBandWeights m weights) ω
    Matrix.trace (toFullBlockMat (frameMatrix σ
      (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω))))/4 ≤
        rootEdelta r*(Matrix.trace (R.transpose*clippedCellMatrix M n Q (rootTau r) ω*R)/4) := by
  dsimp only
  rw [assemblyPhysicalShearMatrix,assembly_physical_average_eq_cubeAverage]
  exact good_cell_clipped_exact_shear_trace M Q r m J hn hm weights hw ω hgood

end
end ASDExplicitGamma.Inverse
