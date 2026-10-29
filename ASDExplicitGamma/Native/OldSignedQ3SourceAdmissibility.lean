module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredSource
public import ASDExplicitGamma.Native.OldSignedOldErrorSource

/-! Genuine cellwise positive-Haar convergence of the uncentered physical
q3 localized row. Both residual and cell-mean columns are retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
noncomputable section

/-- Every actual uncentered q3 row has the required complete spatial Haar
series on each DIAG cell. This retains the fresh constant column. -/
theorem old_signed_q3_row_positive (n : ℤ) (b : ℝ) (L : {l : ℝ // 0<l}) (mesh : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) mesh)
    (l : whiteBasisIndex) (i : Fin 2) :
    Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => -lemmaVPlanarRowField
        (diagInterpolant (originCube 2 n) mesh)
        (mainQ3DirectionW2 (originCube 2 n) b L (whiteBasis l)).value
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u) x i))) := by
  classical
  let Q := originCube 2 n
  let phi := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q mesh
  let R := fun x k => mainQ3ResidualCoordinate whiteBasis b L Q mesh phi U l x k
  let M := fun x k => cubeAverage U
    (fun y => q3Convolution b L h3Zero (whiteBasis l) y)*(I phi).grad x k
  have hRmem (k : Fin 2) : MemLp (fun x => R x k) 2 (normalizedCubeMeasure U) :=
    main_q3_residual_coordinate_memLp whiteBasis b L Q mesh phi U hU l k
  have hMmem (k : Fin 2) : MemLp (fun x => M x k) 2 (normalizedCubeMeasure U) :=
    (memLp_on_descendant_of_memLp hU ((I phi).grad_memL2_normalizedCubeMeasure k)).const_mul _
  have hRpos (k : Fin 2) : Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => R x k))) := by
    let s : Finset whiteBasisIndex := {l}
    let F := mainQ3DiagResidualColumn whiteBasis s b L Q mesh phi U
    have hF : MemLp F 2 (normalizedCubeMeasure U) := by
      apply memLp_piLp_iff.mpr
      rintro ⟨l',k'⟩
      simpa only [F,mainQ3DiagResidualColumn_coordinate] using
        main_q3_residual_coordinate_memLp whiteBasis b L Q mesh phi U hU l'.1 k'
    have hp := (main_q3_diag_residual_local whiteBasis s b L Q mesh p u U hU).1
    let li : s := ⟨l,Finset.mem_singleton_self l⟩
    simpa only [F,mainQ3DiagResidualColumn_coordinate,li,s] using
      main_hilbert_coordinate_summable U hF hp (li,k)
  have hMpos (k : Fin 2) : Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => M x k))) :=
    pureFlux_positive_series_smul U _ _ (diagInterpolant_gradient_summable Q mesh p u U hU k)
  have hadd := (vectorPositiveHaar_add_le U R M hRmem hMmem hRpos hMpos).1
  have hrow : lemmaVPlanarRowField I (mainQ3DirectionW2 Q b L (whiteBasis l)).value phi=
      fun x => planarQuarterTurn (fun k => R x k+M x k) := by
    funext x
    simpa only [pureFluxMainQ3BasisFrameMultiplier,inv_one,one_smul,one_mul] using
      pureFluxMainQ3Row_decomposition n b 1 (by norm_num) L mesh l p u U hU x
  change Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
    (cubeIncrement U (j+1) (fun x => -lemmaVPlanarRowField I
      (mainQ3DirectionW2 Q b L (whiteBasis l)).value phi x i)))
  rw [hrow]
  fin_cases i
  · change Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => -(-(R x 1+M x 1)))))
    simpa only [neg_neg] using hadd 1
  · change Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => -(R x 0+M x 0))))
    simp_rw [cubeIncrement_neg,energy_neg]
    exact hadd 0

/-- Zero affine load adds no value or gradient to an actual H10 potential. -/
theorem old_signed_zero_affine_potential (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) :
    lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) 0 u=u.toH1Function := by
  apply H1Function.ext
  · funext x
    change H1Function.affineOnIsSobolevRegularDomain
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain 0 x+u.toH1Function x=u.toH1Function x
    rw [H1Function.affineOnIsSobolevRegularDomain_apply]
    simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_add]
  · funext x
    change (H1Function.affineOnIsSobolevRegularDomain
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain 0).grad x+
        u.toH1Function.grad x=u.toH1Function.grad x
    rw [H1Function.affineOnIsSobolevRegularDomain_grad,zero_add]

/-- The actual canonical OLD-error source has every cell's positive Haar
series. Neither its convergence nor an auxiliary potential is assumed. -/
theorem old_signed_old_error_source_positive (n : ℤ) (mesh : ℕ) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube 2 n)) a)
    (P : BlockVec 2) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) mesh)
    (l : whiteBasisIndex) (i : Fin 2) :
    Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => (oldSignedOldErrorSource (originCube 2 n) mesh a hEll b L l P x).2 i))) := by
  have h := old_signed_q3_row_positive n b L mesh 0
    (oldSignedCanonicalFirstCorrector (originCube 2 n) a hEll P) U hU l i
  rw [old_signed_zero_affine_potential] at h
  exact h

end
end ASDExplicitGamma.Native
