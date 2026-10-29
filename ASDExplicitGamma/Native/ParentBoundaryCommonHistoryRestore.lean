module

public import ASDExplicitGamma.Native.ParentBoundaryCommonProtectedHistory
public import ASDExplicitGamma.Native.ParentBoundaryBandMaxTraceMoment
public import ASDExplicitGamma.Native.HeatRemainderControlGaussianMoments
public import ASDExplicitGamma.Native.ParentBoundaryCommonSingletonBank
public import ASDExplicitGamma.Native.ParentBoundaryCommonShearYoung
public import ASDExplicitGamma.Native.ParentBoundaryCommonPhysicalYoung
public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeGauge
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandBank
public import ASDExplicitGamma.Native.ParentBoundaryBandRegular
public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeFrame
public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledProjected
public import ASDExplicitGamma.Inverse.PureFluxFeedbackCoefficient
public import ASDExplicitGamma.Gaussian.CovarianceRow
public import ASDExplicitGamma.Triadic.HaarNormTriangle
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Restore the physical trace history from the complete common-centered history. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
open scoped ENNReal Nat
noncomputable section

private theorem parent_common_shear_scalar_sqrt
    (T D z g sigma : ℝ) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hz : z^2 ≤ D*T) :
    T+2*(g/sigma)*z+(g/sigma)^2*D ≤
      (Real.sqrt T + |g / sigma| * Real.sqrt D)^2 := by
  have habs : |z| ≤ Real.sqrt T*Real.sqrt D := by
    have hs : (Real.sqrt T*Real.sqrt D)^2=T*D := by
      rw [mul_pow,Real.sq_sqrt hT,Real.sq_sqrt hD]
    have hn : 0 ≤ Real.sqrt T*Real.sqrt D := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith only [hz,hs,sq_abs z,abs_nonneg z,hn]
  have hcross : (g/sigma)*z ≤ |g / sigma| * (Real.sqrt T*Real.sqrt D) :=
    (le_abs_self ((g/sigma)*z)).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left habs (abs_nonneg _))
  have hsT := Real.sq_sqrt hT
  have hsD := Real.sq_sqrt hD
  nlinarith only [hcross,hsT,hsD,sq_abs (g/sigma)]

/-- Sharp square-root restoration for one translated physical cell. -/
theorem parent_boundary_common_cell_sqrt_restore
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (f : C(closure (cubeSet P),ℝ)) (g : ℝ) :
    traceDefect (cubeSet Q)
      (responsePlanarCoefficientField nu (parentBoundaryCellCoefficient hQ (f+ContinuousMap.const _ g))) sigma ≤
      (Real.sqrt (traceDefect (cubeSet Q)
        (responsePlanarCoefficientField nu (parentBoundaryCellCoefficient hQ f)) sigma)+
        |g / sigma| * Real.sqrt (Matrix.trace (frameMatrix sigma
          (coarseBlockMatrix (cubeSet Q)
            (responsePlanarCoefficientField nu (parentBoundaryCellCoefficient hQ f)))).lowerRight))^2 := by
  let k := parentBoundaryCellCoefficient hQ f
  let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField nu k)
  let T := traceDefect (cubeSet Q) (responsePlanarCoefficientField nu k) sigma
  let D := Matrix.trace (frameMatrix sigma A).lowerRight
  let z := Variational.shearTraceLinear A
  have hshift : responsePlanarCoefficientField nu
      (parentBoundaryCellCoefficient hQ (f+ContinuousMap.const _ g)) =ᵐ[volume.restrict (cubeSet Q)]
      (fun x => responsePlanarCoefficient nu (responseCoefficientExtension k x+g)) := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
    change responsePlanarCoefficient nu
        (responseCoefficientExtension (parentBoundaryCellCoefficient hQ (f+ContinuousMap.const _ g)) x) = _
    rw [parent_boundary_cell_coefficient_value hQ (f+ContinuousMap.const _ g) hx,
      parent_boundary_cell_coefficient_value hQ f hx]
    simp only [ContinuousMap.add_apply,ContinuousMap.const_apply]
  have hmat := coarseBlockMatrix_congr_of_ae_eq hshift
  have hrows := nativeTraceShearDefectRows Q nu sigma hnu hsigma k
  have hT0 : 0 ≤ T := by dsimp [T]; exact hrows.1
  have hD0 : 0 ≤ D := by
    have hp := hrows.2.1
    have hh := mul_pos hp (sq_pos_of_pos hsigma)
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hsigma).ne'] at hh
    exact hh.le
  have hsq : z^2 ≤ D*T := by
    have hh := hrows.2.2.1
    have hscale := mul_le_mul_of_nonneg_left hh (sq_nonneg sigma)
    have hleft : (Variational.shearTraceLinear
        (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField nu k))/sigma)^2*sigma^2 =
        Variational.shearTraceLinear
          (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField nu k))^2 := by
      field_simp [hsigma.ne']
    have hright : (Matrix.trace (frameMatrix sigma
        (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField nu k))).lowerRight/sigma^2*T)*sigma^2 =
        Matrix.trace (frameMatrix sigma
          (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField nu k))).lowerRight*T := by
      field_simp [hsigma.ne']
    dsimp [z,D,A,T]
    nlinarith only [hscale,hleft,hright]
  have hid := hrows.2.2.2 g
  have hphysical : traceDefect (cubeSet Q)
      (responsePlanarCoefficientField nu (parentBoundaryCellCoefficient hQ (f+ContinuousMap.const _ g))) sigma =
      traceDefect (cubeSet Q) (fun x => responsePlanarCoefficient nu (responseCoefficientExtension k x+g)) sigma := by
    unfold traceDefect
    rw [hmat]
  calc
    _ = T+2*(g/sigma)*z+(g/sigma)^2*D := by
      rw [hphysical,hid]
      dsimp [T,D,z,A]
      field_simp [hsigma.ne']
    _ ≤ _ := parent_common_shear_scalar_sqrt T D z g sigma hT0 hD0 hsq

private def parentCommonPhysicalFrame (M : ABKModel 2) (P : TriadicCube 2)
    (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : CoeffField 2 :=
  responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
    (parentBoundaryCommonOpenCubeCoefficient P
      (parentBoundaryCommonCubeBand P n height t ω))

private def parentCommonCenteredFrame (M : ABKModel 2) (P : TriadicCube 2)
    (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : CoeffField 2 :=
  responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
    (parentBoundaryCommonOpenCubeCoefficient P
      (parentBoundaryCommonCubeCentered P n height t ω))

private theorem parent_common_frame_cell_matrix
    (M : ABKModel 2) {P R : TriadicCube 2} {j : ℕ}
    (hR : R ∈ descendantsAtDepth P j) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (centered : Bool) :
    coarseBlockMatrix (openCubeSet R)
        (if centered then parentCommonCenteredFrame M P n height t ω
          else parentCommonPhysicalFrame M P n height t ω) =
      frameMatrix (Annealed.sigmaBar M n)
        (coarseBlockMatrix (cubeSet R)
          (responsePlanarCoefficientField M.nu
            (if centered then parentBoundaryCellCoefficient hR
                (parentBoundaryCommonCubeCentered P n height t ω)
              else parentBoundaryCellCoefficient hR
                (parentBoundaryCommonCubeBand P n height t ω)))) := by
  have hσ : 0 < (Annealed.sigmaBar M n : ℝ) :=
    (Annealed.sigmaBar_characterization M n).1
  have hrestr (f : C(closure (cubeSet P), ℝ)) :
      responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (parentBoundaryCommonOpenCubeCoefficient P f) =ᵐ[volume.restrict (openCubeSet R)]
      responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (parentBoundaryCellCoefficient hR f) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    rw [responseFramePlanarCoefficientField_apply,
      responseFramePlanarCoefficientField_apply,
      parent_boundary_common_open_cube_coefficient_value P f
        (openCubeSet_subset_of_mem_descendantsAtDepth hR hx),
      parent_boundary_cell_coefficient_value hR f
        (openCubeSet_subset_cubeSet R hx)]
  cases centered with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      change coarseBlockMatrix (openCubeSet R)
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
            (parentBoundaryCommonOpenCubeCoefficient P
              (parentBoundaryCommonCubeBand P n height t ω))) = _
      rw [coarseBlockMatrix_congr_of_ae_eq (hrestr _)]
      rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
          (parentBoundaryCellCoefficient hR
            (parentBoundaryCommonCubeBand P n height t ω)))]
      exact response_coarseMatrix_frame_eq (measurableSet_cubeSet R) M.nu
        (Annealed.sigmaBar M n) M.nu_pos hσ
        (parentBoundaryCellCoefficient hR
          (parentBoundaryCommonCubeBand P n height t ω))
  | true =>
      simp only [ite_true]
      change coarseBlockMatrix (openCubeSet R)
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
            (parentBoundaryCommonOpenCubeCoefficient P
              (parentBoundaryCommonCubeCentered P n height t ω))) = _
      rw [coarseBlockMatrix_congr_of_ae_eq (hrestr _)]
      rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
          (parentBoundaryCellCoefficient hR
            (parentBoundaryCommonCubeCentered P n height t ω)))]
      exact response_coarseMatrix_frame_eq (measurableSet_cubeSet R) M.nu
        (Annealed.sigmaBar M n) M.nu_pos hσ
        (parentBoundaryCellCoefficient hR
          (parentBoundaryCommonCubeCentered P n height t ω))

private theorem parent_common_centered_cell_trace
    (M : ABKModel 2) {P R : TriadicCube 2} {j : ℕ}
    (hR : R ∈ descendantsAtDepth P j) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    squareTrace R M.nu (Annealed.sigmaBar M n)
        (parentBoundaryCommonCubeObserved hR n height t ω) =
      traceDefect (openCubeSet R)
        (parentCommonCenteredFrame M P n height t ω) 1 := by
  have hcell := parent_boundary_common_cell_trace_eq hR M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (parentBoundaryCommonCubeCentered P n height t ω)
  have hm := parent_common_frame_cell_matrix M hR n height t ω true
  have hm' : coarseBlockMatrix (openCubeSet R)
        (parentCommonCenteredFrame M P n height t ω) =
      frameMatrix (Annealed.sigmaBar M n)
        (coarseBlockMatrix (cubeSet R)
          (responsePlanarCoefficientField M.nu
            (parentBoundaryCellCoefficient hR
              (parentBoundaryCommonCubeCentered P n height t ω)))) := by
    exact hm
  have hnorm : traceDefect (openCubeSet R)
      (parentCommonCenteredFrame M P n height t ω) 1 =
      traceDefect (cubeSet R)
        (responsePlanarCoefficientField M.nu
          (parentBoundaryCellCoefficient hR
            (parentBoundaryCommonCubeCentered P n height t ω)))
        (Annealed.sigmaBar M n) := by
    unfold traceDefect
    rw [hm']
    simp [frameMatrix, Matrix.trace_smul, smul_eq_mul]
  simpa only [parentBoundaryCommonCubeObserved] using hcell.trans hnorm.symm

private theorem parent_common_cell_inverse_trace_le
    (M : ABKModel 2) (P R : TriadicCube 2) (j : ℕ)
    (hR : R ∈ descendantsAtDepth P j) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    Matrix.trace (frameMatrix (Annealed.sigmaBar M n)
      (coarseBlockMatrix (cubeSet R)
        (responsePlanarCoefficientField M.nu
          (parentBoundaryCellCoefficient hR
            (parentBoundaryCommonCubeCentered P n height t ω))))).lowerRight ≤
      2 * lemmaVInverseDepthMax P (parentCommonPhysicalFrame M P n height t ω) j := by
  classical
  let σ : ℝ := Annealed.sigmaBar M n
  let fc := parentBoundaryCommonCubeCentered P n height t ω
  let g := parentBoundaryCommonCubeCenterValue P n height t ω
  let af := parentCommonPhysicalFrame M P n height t ω
  let ac := parentCommonCenteredFrame M P n height t ω
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hsplit := parent_boundary_common_cube_split P n height t ω
  have hcoef : parentBoundaryCommonOpenCubeCoefficient P
      (parentBoundaryCommonCubeBand P n height t ω) =
      parentBoundaryCommonOpenCubeCoefficient P (fc + ContinuousMap.const _ g) :=
    congrArg (parentBoundaryCommonOpenCubeCoefficient P) hsplit
  have hgauge := parent_boundary_common_descendant_inverse_block_gauge P M.nu σ
    M.nu_pos hσ fc g R j hR
  have hLRcube : (coarseBlockMatrix (cubeSet R) af).lowerRight =
      (coarseBlockMatrix (cubeSet R) ac).lowerRight := by
    dsimp only [af, ac, parentCommonPhysicalFrame, parentCommonCenteredFrame]
    rw [hcoef]
    exact hgauge
  have hLRopen : (coarseBlockMatrix (openCubeSet R) ac).lowerRight =
      (coarseBlockMatrix (openCubeSet R) af).lowerRight := by
    calc
      _ = (coarseBlockMatrix (cubeSet R) ac).lowerRight :=
        congrArg (fun A : BlockMat 2 => A.lowerRight)
          (coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R ac).symm
      _ = (coarseBlockMatrix (cubeSet R) af).lowerRight := hLRcube.symm
      _ = _ := congrArg (fun A : BlockMat 2 => A.lowerRight)
        (coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R af)
  have hmatC := parent_common_frame_cell_matrix M hR n height t ω true
  have hmatC' : coarseBlockMatrix (openCubeSet R) ac =
      frameMatrix σ (coarseBlockMatrix (cubeSet R)
        (responsePlanarCoefficientField M.nu (parentBoundaryCellCoefficient hR fc))) := by
    simpa [ac, parentCommonCenteredFrame, σ] using hmatC
  have hD : Matrix.trace (frameMatrix σ
      (coarseBlockMatrix (cubeSet R)
        (responsePlanarCoefficientField M.nu (parentBoundaryCellCoefficient hR fc)))).lowerRight =
      Matrix.trace (coarseBlockMatrix (openCubeSet R) ac).lowerRight := by
    rw [← hmatC']
  have htraceLR : Matrix.trace (coarseBlockMatrix (openCubeSet R) ac).lowerRight =
      Matrix.trace (coarseBlockMatrix (openCubeSet R) af).lowerRight := by
    rw [hLRopen]
  have hEll : IsEllipticFieldOn (M.nu / σ)
      (((M.nu / σ)^2 +
        (‖parentBoundaryCommonOpenCubeCoefficient P
          (parentBoundaryCommonCubeBand P n height t ω)‖ / σ)^2) / (M.nu / σ))
      (openCubeSet P) af := by
    exact responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet P) M.nu σ M.nu_pos hσ
      (parentBoundaryCommonOpenCubeCoefficient P
        (parentBoundaryCommonCubeBand P n height t ω))
  have hEllR := hEll.mono (measurableSet_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth hR)
  have hmatNorm : Book.Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) af).lowerRight ≤
      lemmaVInverseDepthMax P af j := by
    unfold lemmaVInverseDepthMax
    have hinv := Scalar.inverse_history_lowerRight R af hEllR
    apply le_csSup ((Set.toFinite _).image _).bddAbove
      ⟨R, hR, congrArg Book.Ch02.matrixNorm hinv⟩
  have htraceNorm : Matrix.trace (coarseBlockMatrix (openCubeSet R) af).lowerRight ≤
      2 * Book.Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) af).lowerRight := by
    let B := (coarseBlockMatrix (cubeSet R) af).lowerRight
    have h0 := (le_abs_self (B 0 0)).trans (clipped_matrix_entry_abs_le_norm B 0 0)
    have h1 := (le_abs_self (B 1 1)).trans (clipped_matrix_entry_abs_le_norm B 1 1)
    have h0' : B 0 0 ≤ Book.Ch02.matrixNorm B := by
      simpa only [Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
        Book.Ch02.matrixOperatorNorm] using h0
    have h1' : B 1 1 ≤ Book.Ch02.matrixNorm B := by
      simpa only [Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
        Book.Ch02.matrixOperatorNorm] using h1
    have hcoarse : coarseBlockMatrix (openCubeSet R) af = coarseBlockMatrix (cubeSet R) af :=
      (coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R af).symm
    rw [hcoarse]
    simp only [Matrix.trace, Fin.sum_univ_two]
    dsimp [B]
    nlinarith only [h0', h1']
  calc
    _ = Matrix.trace (coarseBlockMatrix (openCubeSet R) ac).lowerRight := hD
    _ = Matrix.trace (coarseBlockMatrix (openCubeSet R) af).lowerRight := htraceLR
    _ ≤ 2 * Book.Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) af).lowerRight := htraceNorm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmatNorm (by norm_num)

private theorem parent_common_cell_trace_restore_depth
    (M : ABKModel 2) (P R : TriadicCube 2) (j : ℕ)
    (hR : R ∈ descendantsAtDepth P j) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    traceDefect (cubeSet R)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)
        (Annealed.sigmaBar M n) ≤
      (Real.sqrt (traceDefect (openCubeSet R)
          (parentCommonCenteredFrame M P n height t ω) 1) +
        |parentBoundaryCommonCubeCenterValue P n height t ω /
          (Annealed.sigmaBar M n:ℝ)| *
          Real.sqrt (2*lemmaVInverseDepthMax P
            (parentCommonPhysicalFrame M P n height t ω) j))^2 := by
  let σ : ℝ := Annealed.sigmaBar M n
  let fc := parentBoundaryCommonCubeCentered P n height t ω
  let g := parentBoundaryCommonCubeCenterValue P n height t ω
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hsplit := parent_boundary_common_cube_split P n height t ω
  have hmap : parentBoundaryCellCoefficient hR
      (parentBoundaryCommonCubeBand P n height t ω) =
      parentBoundaryCellCoefficient hR (fc + ContinuousMap.const _ g) :=
    congrArg (parentBoundaryCellCoefficient hR) hsplit
  have hphys := parent_boundary_common_cell_physical_coarse M hR n height t ω
  rw [hmap] at hphys
  have hphysical : traceDefect (cubeSet R)
      (responsePlanarCoefficientField M.nu
        (parentBoundaryCellCoefficient hR (fc + ContinuousMap.const _ g))) σ =
      traceDefect (cubeSet R)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω) σ := by
    unfold traceDefect
    rw [hphys]
  have hrestore := parent_boundary_common_cell_sqrt_restore hR M.nu σ
    M.nu_pos hσ fc g
  have hcenterTrace : traceDefect (cubeSet R)
      (responsePlanarCoefficientField M.nu
        (parentBoundaryCellCoefficient hR fc)) σ =
      traceDefect (openCubeSet R)
        (parentCommonCenteredFrame M P n height t ω) 1 := by
    have h1 := parent_boundary_common_cell_trace_eq hR M.nu σ M.nu_pos hσ fc
    have h2 := parent_common_centered_cell_trace M hR n height t ω
    exact h1.symm.trans h2
  rw [hcenterTrace] at hrestore
  have hD := parent_common_cell_inverse_trace_le M P R j hR n height t ω
  have hDroot := Real.sqrt_le_sqrt hD
  let A := Real.sqrt (traceDefect (openCubeSet R)
      (parentCommonCenteredFrame M P n height t ω) 1) +
      |g / σ| * Real.sqrt (Matrix.trace (frameMatrix σ
        (coarseBlockMatrix (cubeSet R)
          (responsePlanarCoefficientField M.nu (parentBoundaryCellCoefficient hR fc)))).lowerRight)
  let B := Real.sqrt (traceDefect (openCubeSet R)
      (parentCommonCenteredFrame M P n height t ω) 1) +
      |g / σ| * Real.sqrt (2*lemmaVInverseDepthMax P
        (parentCommonPhysicalFrame M P n height t ω) j)
  have hAB : A ≤ B := by
    dsimp [A, B, g, σ]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hDroot (abs_nonneg _))
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsq : A^2 ≤ B^2 := by
    nlinarith [sq_nonneg (B-A)]
  rw [← hphysical]
  change traceDefect (cubeSet R)
      (responsePlanarCoefficientField M.nu
        (parentBoundaryCellCoefficient hR (fc + ContinuousMap.const _ g))) σ ≤ B^2
  exact hrestore.trans (by simpa only [A] using hsq)

/-- The actual physical trace on one descendant cell is restored from the
common-centered trace with the true source-frame inverse-depth maximum.
This is the per-cell interface for the discounted history aggregation. -/
theorem parent_boundary_common_cell_physical_trace_restore
    (M : ABKModel 2) (P R : TriadicCube 2) (j : ℕ)
    (hR : R ∈ descendantsAtDepth P j) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    traceDefect (cubeSet R)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)
        (Annealed.sigmaBar M n) ≤
      (Real.sqrt (traceDefect (openCubeSet R)
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
            (parentBoundaryCommonOpenCubeCoefficient P
              (parentBoundaryCommonCubeCentered P n height t ω))) 1) +
        |parentBoundaryCommonCubeCenterValue P n height t ω /
          (Annealed.sigmaBar M n:ℝ)| *
          Real.sqrt (2*lemmaVInverseDepthMax P
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
              (parentBoundaryCommonOpenCubeCoefficient P
                (parentBoundaryCommonCubeBand P n height t ω))) j))^2 := by
  simpa only [parentCommonPhysicalFrame, parentCommonCenteredFrame] using
    parent_common_cell_trace_restore_depth M P R j hR n height t ω

theorem parent_common_singleton_history_rare_inputs
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (P : TriadicCube 2) (n : ℤ)
    (r : ℕ) (hr : r ≤ 5) (hP : P.scale=n-(r:ℤ))
    (height : ℕ) (hpast : ∀ k<n,nativeInductionState M h k)
    (t : ℝ) (ht : t ≤ 1) :
    (∀ ω, 0 ≤ parentBoundaryCommonSingletonHistory M P n n height t ω) ∧
    eLpNorm (inverseBankPopulationRemainder .localInverse ({P}:Finset (TriadicCube 2)) M n
      (n+(height:ℤ)) (parentBoundaryObserverBandWeights n t)) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (3/10^46:ℝ) ∧
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      parentBoundaryCommonSingletonHistory M P n n height t ω ≤
        (3683/2500:ℝ)+inverseBankPopulationRemainder .localInverse
          ({P}:Finset (TriadicCube 2)) M n (n+(height:ℤ))
            (parentBoundaryObserverBandWeights n t) ω := by
  let Y := bankFiniteRootHistoryMax ({P}:Finset (TriadicCube 2)) M n
    (n+(height:ℤ)) (parentBoundaryObserverBandWeights n t)
  let R := inverseBankPopulationRemainder .localInverse ({P}:Finset (TriadicCube 2)) M n
    (n+(height:ℤ)) (parentBoundaryObserverBandWeights n t)
  let B := parentBoundaryCommonSingletonHistory M P n n height t
  have hb := parent_boundary_common_singleton_bank M h hM hg P n n
    (by rw [hP]; omega) (by rw [hP]; omega) le_rfl height hpast t ht
  have hA0 : 0 ≤ (inverseBankCap .localInverse:ℝ) := by norm_num [inverseBankCap]
  have hR0 : ∀ ω, 0 ≤ R ω := by
    intro ω
    exact hb.remainder_nonneg ω
  have hcap : (inverseBankCap .localInverse:ℝ)=(3683/2500:ℝ) := by
    norm_num [inverseBankCap]
  refine ⟨?_, ?_, ?_⟩
  · intro ω
    exact ENNReal.toReal_nonneg
  · simpa [inverseBankReserve] using hb.remainder_L128
  · filter_upwards [hb.history_finite, hb.history_le] with ω hfinite hsplit
    have hsplit' := ENNReal.toReal_mono (by finiteness) hsplit
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hA0, ENNReal.toReal_ofReal (hR0 ω)] at hsplit'
    have hY : (Y ω).toReal = B ω := by rfl
    rw [hY,hcap] at hsplit'
    exact hsplit'

local instance parentCommonHistoryRestoreCompact (P : TriadicCube 2) :
    CompactSpace (closure (cubeSet P)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet P).isCompact_closure

private theorem parent_common_center_gaussian_norm_sq
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (k : ℕ) (hk : 1 ≤ k) :
    (eLpNorm (fun ω => parentBoundaryCommonCubeCenterValue P n height t ω /
      (Annealed.sigmaBar M n:ℝ)) (ENNReal.ofReal (2*(k:ℝ)))
      (Cutoff.cutoffSampleLaw M).toMeasure).toReal^2 =
      t*parentBoundaryCommonBandVariance M h n height*
      Real.rpow ((2*k-1)‼:ℝ) ((k:ℝ)⁻¹) := by
  let K := closure (cubeSet P)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := fun ω => modelBand K (nativeSourceBandIndex n height) ω
    (parentBoundaryCommonCubeCenter P)
  let σ : ℝ := Annealed.sigmaBar M n
  let c : ℝ := Real.sqrt t / σ
  let G0 := fun ω => parentBoundaryCommonCubeCenterValue P n height t ω / σ
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hc : 0 ≤ c := div_nonneg (Real.sqrt_nonneg _) hσ.le
  have hkindex : Function.Injective (nativeSourceBandIndex n height) := by
    intro i j hij
    apply Fin.ext
    dsimp [nativeSourceBandIndex] at hij
    omega
  have hXmeas : Measurable X := by
    exact (ContinuousMap.evalCLM ℝ (parentBoundaryCommonCubeCenter P)).continuous.measurable.comp
      (measurable_modelBand K (nativeSourceBandIndex n height))
  have hXlaw := parent_boundary_band_point_law K M h hM
    (nativeSourceBandIndex n height) hkindex (parentBoundaryCommonCubeCenter P)
  have hXnorm : eLpNorm X (ENNReal.ofReal (2*(k:ℝ))) μ =
      eLpNorm (id:ℝ→ℝ) (ENNReal.ofReal (2*(k:ℝ)))
        (gaussianReal 0 (Real.toNNReal (∑ i : Fin height,
          (q3ModelAmplitude M h (nativeSourceBandIndex n height i))^2))) := by
    have hm := eLpNorm_map_measure (p:=ENNReal.ofReal (2*(k:ℝ)))
      (f:=X) (μ:=μ) (by fun_prop : AEStronglyMeasurable (id:ℝ→ℝ) (μ.map X))
      hXmeas.aemeasurable
    rw [hXlaw] at hm
    simpa only [Function.id_comp] using hm.symm
  have hG0eq : G0 = c • X := by
    funext ω
    dsimp [G0,c,X,K,σ]
    simp only [parentBoundaryCommonCubeCenterValue]
    ring
  have hnormScale : eLpNorm G0 (ENNReal.ofReal (2*(k:ℝ))) μ =
      ENNReal.ofReal c * eLpNorm X (ENNReal.ofReal (2*(k:ℝ))) μ := by
    rw [hG0eq,eLpNorm_const_smul,Real.enorm_eq_ofReal hc]
  have hnormSq : (eLpNorm X (ENNReal.ofReal (2*(k:ℝ))) μ).toReal^2 =
      (∑ i : Fin height,(q3ModelAmplitude M h (nativeSourceBandIndex n height i))^2) *
        Real.rpow ((2*k-1)‼:ℝ) ((k:ℝ)⁻¹) := by
    rw [hXnorm]
    have hsum0 : 0 ≤ ∑ i : Fin height,(q3ModelAmplitude M h
        (nativeSourceBandIndex n height i))^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hgauss := nativeHeat_gaussian_even_norm_sq
      (Real.toNNReal (∑ i : Fin height,
        (q3ModelAmplitude M h (nativeSourceBandIndex n height i))^2)) k hk
    rw [Real.coe_toNNReal _ hsum0] at hgauss
    exact hgauss
  have hvariance :
      (∑ i : Fin height,(q3ModelAmplitude M h (nativeSourceBandIndex n height i))^2)/σ^2 =
        parentBoundaryCommonBandVariance M h n height := by
    have hi (i : Fin height) : nativeSourceBandIndex n height i=n+((i.val+1:ℕ):ℤ) := by
      dsimp only [nativeSourceBandIndex]
      push_cast
      ring
    unfold parentBoundaryCommonBandVariance
    rw [Finset.sum_div]
  rw [hnormScale,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,mul_pow,hnormSq]
  have hs : c^2=t/σ^2 := by
    dsimp [c]
    rw [div_pow,Real.sq_sqrt ht0]
  have hcoeff : 0 ≤ Real.rpow ((2*k-1)‼:ℝ) ((k:ℝ)⁻¹) :=
    Real.rpow_nonneg (by positivity) _
  rw [hs]
  let S : ℝ := ∑ i : Fin height,(q3ModelAmplitude M h (nativeSourceBandIndex n height i))^2
  let C : ℝ := Real.rpow ((2*k-1)‼:ℝ) ((k:ℝ)⁻¹)
  change (t/σ^2)*(S*C)=t*parentBoundaryCommonBandVariance M h n height*C
  calc
    (t/σ^2)*(S*C) = (S/σ^2)*(t*C) := by ring
    _ = parentBoundaryCommonBandVariance M h n height*(t*C) := by rw [←hvariance]
    _ = _ := by ring

theorem parent_common_center_L4_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    eLpNorm (fun ω => parentBoundaryCommonCubeCenterValue P n height t ω /
      (Annealed.sigmaBar M n:ℝ)) 4 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.rpow 3 (1/4:ℝ) *
        Real.sqrt (t*parentBoundaryCommonBandVariance M h n height)) := by
  let G := fun ω => parentBoundaryCommonCubeCenterValue P n height t ω /
    (Annealed.sigmaBar M n:ℝ)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hmem : MemLp G 4 μ := by
    simpa only [G] using parent_boundary_common_cube_center_memLp M h hM P n height t 4 (by finiteness)
  have hsq := parent_common_center_gaussian_norm_sq M h hM P n height t ht0 2 (by norm_num)
  have hV0 : 0 ≤ parentBoundaryCommonBandVariance M h n height :=
    parent_boundary_common_band_variance_nonneg M h n height
  have hcoeff : Real.rpow ((2*2-1)‼:ℝ) ((2:ℝ)⁻¹)=Real.sqrt 3 := by
    norm_num [Nat.doubleFactorial]
    rw [Real.sqrt_eq_rpow]
  have hx : 0 ≤ t*parentBoundaryCommonBandVariance M h n height :=
    mul_nonneg ht0 hV0
  have hnorm : (eLpNorm G 4 μ).toReal ≤
      Real.rpow 3 (1/4:ℝ)*Real.sqrt (t*parentBoundaryCommonBandVariance M h n height) := by
    have hn0 : 0 ≤ (eLpNorm G 4 μ).toReal := ENNReal.toReal_nonneg
    have hsqBase : (eLpNorm G 4 μ).toReal^2 =
        t*parentBoundaryCommonBandVariance M h n height*
          Real.rpow ((2*2-1)‼:ℝ) ((2:ℝ)⁻¹) := by
      have he := hsq
      norm_num only [ENNReal.ofReal_ofNat] at he
      have hnat : (2*2-1:ℕ)=3 := by norm_num
      have hexp : (2:ℝ)⁻¹=(1/2:ℝ) := by norm_num
      simpa only [G,μ,hnat,hexp] using he
    have hsq' : (eLpNorm G 4 μ).toReal^2 =
        Real.sqrt 3*(t*parentBoundaryCommonBandVariance M h n height) := by
      calc
        _ = t*parentBoundaryCommonBandVariance M h n height*
            Real.rpow ((2*2-1)‼:ℝ) ((2:ℝ)⁻¹) := by
          exact hsqBase
        _ = _ := by rw [hcoeff]; ring
    have hsqrt := Real.sqrt_le_sqrt hsq'.le
    have hself : Real.sqrt ((eLpNorm G 4 μ).toReal^2)=(eLpNorm G 4 μ).toReal := by
      rw [Real.sqrt_sq_eq_abs,abs_of_nonneg hn0]
    have hcoeffNorm : Real.sqrt (Real.sqrt 3)=Real.rpow 3 (1/4:ℝ) := by
      rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow]
      rw [←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
      norm_num
    have htarget : Real.sqrt (Real.sqrt 3*(t*parentBoundaryCommonBandVariance M h n height)) =
        Real.rpow 3 (1/4:ℝ)*Real.sqrt (t*parentBoundaryCommonBandVariance M h n height) := by
      rw [Real.sqrt_mul (Real.sqrt_nonneg _),hcoeffNorm]
    calc
      (eLpNorm G 4 μ).toReal = Real.sqrt ((eLpNorm G 4 μ).toReal^2) := hself.symm
      _ ≤ Real.sqrt (Real.sqrt 3*(t*parentBoundaryCommonBandVariance M h n height)) := hsqrt
      _ = _ := htarget
  rw [←ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hnorm

theorem parent_common_center_L8_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    eLpNorm (fun ω => parentBoundaryCommonCubeCenterValue P n height t ω /
      (Annealed.sigmaBar M n:ℝ)) 8 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.rpow 105 (1/8:ℝ) *
        Real.sqrt (t*parentBoundaryCommonBandVariance M h n height)) := by
  let G := fun ω => parentBoundaryCommonCubeCenterValue P n height t ω /
    (Annealed.sigmaBar M n:ℝ)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hmem : MemLp G 8 μ := by
    simpa only [G] using parent_boundary_common_cube_center_memLp M h hM P n height t 8 (by finiteness)
  have hsq := parent_common_center_gaussian_norm_sq M h hM P n height t ht0 4 (by norm_num)
  have hV0 : 0 ≤ parentBoundaryCommonBandVariance M h n height :=
    parent_boundary_common_band_variance_nonneg M h n height
  have hcoeff : Real.rpow ((2*4-1)‼:ℝ) ((4:ℝ)⁻¹)=Real.sqrt (Real.sqrt 105) := by
    norm_num [Nat.doubleFactorial]
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow]
    rw [←Real.rpow_mul (by norm_num : (0:ℝ)≤105)]
    norm_num
  have hx : 0 ≤ t*parentBoundaryCommonBandVariance M h n height :=
    mul_nonneg ht0 hV0
  have hnorm : (eLpNorm G 8 μ).toReal ≤
      Real.rpow 105 (1/8:ℝ)*Real.sqrt (t*parentBoundaryCommonBandVariance M h n height) := by
    have hn0 : 0 ≤ (eLpNorm G 8 μ).toReal := ENNReal.toReal_nonneg
    have hsqBase : (eLpNorm G 8 μ).toReal^2 =
        t*parentBoundaryCommonBandVariance M h n height*
          Real.rpow ((2*4-1)‼:ℝ) ((4:ℝ)⁻¹) := by
      have he := hsq
      norm_num only [ENNReal.ofReal_ofNat] at he
      have hnat : (2*4-1:ℕ)=7 := by norm_num
      have hexp : (4:ℝ)⁻¹=(1/4:ℝ) := by norm_num
      simpa only [G,μ,hnat,hexp] using he
    have hsq' : (eLpNorm G 8 μ).toReal^2 =
        Real.sqrt (Real.sqrt 105)*(t*parentBoundaryCommonBandVariance M h n height) := by
      calc
        _ = t*parentBoundaryCommonBandVariance M h n height*
            Real.rpow ((2*4-1)‼:ℝ) ((4:ℝ)⁻¹) := by
          exact hsqBase
        _ = _ := by rw [hcoeff]; ring
    have hsqrt := Real.sqrt_le_sqrt hsq'.le
    have hself : Real.sqrt ((eLpNorm G 8 μ).toReal^2)=(eLpNorm G 8 μ).toReal := by
      rw [Real.sqrt_sq_eq_abs,abs_of_nonneg hn0]
    have hcoeffNorm : Real.sqrt (Real.sqrt (Real.sqrt 105))=Real.rpow 105 (1/8:ℝ) := by
      rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow]
      rw [←Real.rpow_mul (by norm_num : (0:ℝ)≤105),←Real.rpow_mul (by norm_num : (0:ℝ)≤105)]
      norm_num
    have htarget : Real.sqrt (Real.sqrt (Real.sqrt 105)*(t*parentBoundaryCommonBandVariance M h n height)) =
        Real.rpow 105 (1/8:ℝ)*Real.sqrt (t*parentBoundaryCommonBandVariance M h n height) := by
      rw [Real.sqrt_mul (Real.sqrt_nonneg _),hcoeffNorm]
    calc
      (eLpNorm G 8 μ).toReal = Real.sqrt ((eLpNorm G 8 μ).toReal^2) := hself.symm
      _ ≤ Real.sqrt (Real.sqrt (Real.sqrt 105)*(t*parentBoundaryCommonBandVariance M h n height)) := hsqrt
      _ = _ := htarget
  rw [←ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hnorm

end
end ASDExplicitGamma.Native
