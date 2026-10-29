module

public import ASDExplicitGamma.Inverse.RawShellMixedShearIdentity
public import ASDExplicitGamma.Variational.LemmaVTrace

/-! Load polarization for the OLD coarse shear coefficient. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian
noncomputable section

local instance rawTraceMixedShearFiniteMeasure (n : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 n))) :=
  (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isFiniteMeasure_restrict_volume

/-- A unit mixed primal/flux load, with the sign on its flux component. -/
def rawTraceMixedShearLoad (i j : Fin 2) (b : Bool) : BlockVec 2 :=
  (Real.sqrt (1 / 2 : ℝ) • Pi.single i (1 : ℝ),
    (if b then 1 else -1) * Real.sqrt (1 / 2 : ℝ) • Pi.single j (1 : ℝ))

/-- The actual framed response energy of a mixed load, pulled back to the
compact scalar coefficient carrier used by the OLD trace observable. -/
noncomputable def rawTraceMixedShearEnergy
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2) :
    C(closure (cubeSet (originCube 2 n)), ℝ) → ℝ := fun x =>
  responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
    (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P
    (pureFluxOpenResponseRestriction n x)

private theorem rawTraceMixedShear_response_energy_eq_quadratic
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (P : BlockVec 2) (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let K := closure (cubeSet Q)
    let k : ResponseCoefficient (cubeSet Q) :=
      ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ x
    let kOpen : ResponseCoefficient (openCubeSet Q) :=
      pureFluxOpenResponseRestriction n x
    responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P kOpen =
      blockVecDot P (blockMatVecMul
        (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField ν k))) P) := by
  intro Q K k kOpen
  let U := openCubeSet Q
  let hU := measurableSet_openCubeSet Q
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let aOpen := responseFramePlanarCoefficientField ν σ kOpen
  let aClosed := responseFramePlanarCoefficientField ν σ k
  have hEllOpen := responseFramePlanarCoefficientField_isElliptic hU ν σ hν hσ kOpen
  have hEllClosed := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_cubeSet Q) ν σ hν hσ k
  have hE : responseFrameEnergyObservable hU hv ν σ hν hσ P kOpen =
      2 * Mu U P aOpen := by
    rw [lemmaV_observable_eq_twice_muCandidate, ← lemmaV_responseSystem_eq_canonical]
    congr 1
    exact lemmaV_canonical_muCandidate_eq_Mu
      (isOpenBoundedConvexDomain_openCubeSet Q) hEllOpen hv P
  have hframeClosed (y : Vec 2) : aClosed y = σ⁻¹ •
      responsePlanarCoefficientField ν k y := by
    dsimp [aClosed]
    rw [responseFramePlanarCoefficientField_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [responsePlanarCoefficientField, responsePlanarCoefficient,
        responsePlanarJ, Matrix.smul_apply, smul_eq_mul] <;>
      field_simp [hσ.ne']
  have haeOpen : aOpen =ᵐ[volume.restrict U] aClosed := by
    have hrestr := pureFluxOpenResponseRestriction_frame_ae n ν σ x hσ
    filter_upwards [hrestr] with y hy
    calc
      aOpen y = σ⁻¹ • responsePlanarCoefficientField ν k y := hy
      _ = aClosed y := (hframeClosed y).symm
  have haeCube : aOpen =ᵐ[volume.restrict (cubeSet Q)] aClosed := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact haeOpen
  calc
    responseFrameEnergyObservable hU hv ν σ hν hσ P kOpen = 2 * Mu U P aOpen := hE
    _ = 2 * Mu U P aClosed := by rw [Mu_congr_of_ae_eq haeOpen P]
    _ = 2 * Mu (cubeSet Q) P aClosed := by
      rw [(Mu_cubeSet_originCube_eq_openCubeSet n P aClosed).symm]
    _ = blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet Q) aClosed) P) := by
      rw [mu_eq_half_coarseBlockMatrix_elliptic_triCube (div_pos hν hσ) hEllClosed]
      ring
    _ = blockVecDot P (blockMatVecMul
        (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField ν k))) P) := by
      rw [response_coarseMatrix_frame_eq (measurableSet_cubeSet Q) ν σ hν hσ k]

private theorem rawTraceMixedShearLoad_energy_formula
    (σ : ℝ) (A : BlockMat 2) (hA : IsSymmetricBlockMat A)
    (i j : Fin 2) (b : Bool) :
    blockVecDot (rawTraceMixedShearLoad i j b)
        (blockMatVecMul (frameMatrix σ A) (rawTraceMixedShearLoad i j b)) =
      (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight j j) / 2 +
        (if b then 1 else -1) * A.upperRight i j := by
  have hc : (Real.sqrt 2)⁻¹ ^ 2 = 1 / 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    calc
      (Real.sqrt 2)⁻¹ ^ 2 = ((Real.sqrt 2) ^ 2)⁻¹ := by rw [inv_pow]
      _ = 1 / 2 := by rw [hs]; norm_num
  have hsign : (if b then (1 : ℝ) else -1) ^ 2 = 1 := by
    cases b <;> norm_num
  have hsym := hA (Sum.inl i) (Sum.inr j)
  change A.upperRight i j = A.lowerLeft j i at hsym
  cases b <;>
    simp [rawTraceMixedShearLoad, blockVecDot, blockMatVecMul, vecDot, matVecMul,
      frameMatrix, Matrix.smul_apply, smul_eq_mul, Pi.single_apply] <;>
    rw [← hsym] <;> ring_nf <;> rw [hc] <;> ring

/-- The actual OLD shear coefficient is the signed polarization of four
mixed response-load energies. The response frame changes only the diagonal
block weights, which cancel in this combination. -/
theorem raw_trace_model_shear_linear_eq_mixed_load_energies
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let kOpen : ResponseCoefficient (openCubeSet Q) :=
      pureFluxOpenResponseRestriction n x
    let E (i j : Fin 2) (b : Bool) :=
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
        (rawTraceMixedShearLoad i j b) kOpen
    rawTraceModelShearLinear n ν x =
      ((E 1 0 true - E 1 0 false) - (E 0 1 true - E 0 1 false)) / 2 := by
  intro Q kOpen E
  let K := closure (cubeSet Q)
  let k : ResponseCoefficient (cubeSet Q) :=
    ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ x
  let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)
  have hA : IsSymmetricBlockMat A := coarseBlockMatrix_symmetric _ _
  have hEnergy (i j : Fin 2) (b : Bool) : E i j b =
      (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight j j) / 2 +
        (if b then 1 else -1) * A.upperRight i j := by
    dsimp [E]
    rw [rawTraceMixedShear_response_energy_eq_quadratic n ν σ hν hσ
      (rawTraceMixedShearLoad i j b) x]
    exact rawTraceMixedShearLoad_energy_formula σ A hA i j b
  rw [hEnergy 1 0 true, hEnergy 1 0 false,
    hEnergy 0 1 true, hEnergy 0 1 false]
  simp [rawTraceModelShearLinear, Variational.shearTraceLinear, A, k]
  ring

/-- The four mixed loads form an orthonormal frame, so their total energy is
the OLD trace defect plus four. -/
theorem raw_trace_model_mixed_loads_sum_eq_trace_plus_four
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    rawTraceMixedShearEnergy n ν σ hν hσ (rawTraceMixedShearLoad 1 0 true) x +
      rawTraceMixedShearEnergy n ν σ hν hσ (rawTraceMixedShearLoad 1 0 false) x +
      rawTraceMixedShearEnergy n ν σ hν hσ (rawTraceMixedShearLoad 0 1 true) x +
      rawTraceMixedShearEnergy n ν σ hν hσ (rawTraceMixedShearLoad 0 1 false) x =
        modelTraceObservable n ν σ x + 4 := by
  let Q := originCube 2 n
  let K := closure (cubeSet Q)
  let k : ResponseCoefficient (cubeSet Q) :=
    ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ x
  let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)
  let E (i j : Fin 2) (b : Bool) :=
    rawTraceMixedShearEnergy n ν σ hν hσ (rawTraceMixedShearLoad i j b) x
  have hA : IsSymmetricBlockMat A := coarseBlockMatrix_symmetric _ _
  have hEnergy (i j : Fin 2) (b : Bool) : E i j b =
      (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight j j) / 2 +
        (if b then 1 else -1) * A.upperRight i j := by
    dsimp [E, rawTraceMixedShearEnergy]
    rw [rawTraceMixedShear_response_energy_eq_quadratic n ν σ hν hσ
      (rawTraceMixedShearLoad i j b) x]
    exact rawTraceMixedShearLoad_energy_formula σ A hA i j b
  change E 1 0 true + E 1 0 false + E 0 1 true + E 0 1 false = _
  rw [hEnergy 1 0 true, hEnergy 1 0 false,
    hEnergy 0 1 true, hEnergy 0 1 false]
  simp [modelTraceObservable, traceDefect, A, k, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two]
  ring

end
end ASDExplicitGamma.Inverse
