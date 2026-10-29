module

public import ASDExplicitGamma.Inverse.ContainedTriangleRootResponse
public import ASDExplicitGamma.Inverse.TriangleHistoryBudget
public import ASDExplicitGamma.Inverse.TriangleResponseBudget
public import ASDExplicitGamma.Inverse.FullResponseMatrixError
public import ASDExplicitGamma.Inverse.ClippedMatrixResponseBound
public import ASDExplicitGamma.Inverse.HistoryResponse
public import ASDExplicitGamma.Inverse.FullResponseTrace
public import ASDExplicitGamma.Inverse.RestrictedResponseCoefficients

/-! The full old-response trace on a physical triangle is paid by the same
literal raw history that controls the inverse block. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- The complete framed response trace of a physical triangle is bounded by
the exact volume weighted sum of the framed traces on its contained cubes.
This is the trace-level consequence of the full paired-load variational
comparison, before any probabilistic or history estimate. -/
theorem triangle_root_full_trace_le_weighted_cube_traces (Q : TriadicCube 2)
    (pi : Equiv.Perm (Fin 2)) (a : Book.Ch02.CoeffOn (kuhnCellDomain ⟨Q, pi⟩))
    (σ : ℝ) (hσ : 0 < σ) :
    ENNReal.ofReal (Matrix.trace (toFullBlockMat
      (frameMatrix σ (Book.Ch02.coarseBlockMatrix (kuhnCellDomain ⟨Q, pi⟩) a))) / 4) ≤
      ∑' P : ↥(triangleCubePartition Q.scale pi), ENNReal.ofReal
        (((volume (openCubeSet (triangleRootCube Q pi P))).toReal /
          (volume (Whitney.KuhnCell.mk Q pi).openCarrier).toReal) *
          (Matrix.trace (toFullBlockMat (frameMatrix σ
            (Book.Ch02.coarseBlockMatrix
              (Book.Ch02.cubeDomain (triangleRootCube Q pi P))
              (triangleRootCubeCoeff Q pi a P)))) / 4)) := by
  classical
  let T := kuhnCellDomain (Whitney.KuhnCell.mk Q pi)
  let A := Book.Ch02.coarseBlockMatrix T a
  let s := Real.sqrt σ
  let E (j : Fin 2 × Bool) : BlockVec 2 :=
    orthonormalFrameLoad j.1 (if j.2 then 1 else -1)
  let Eσ (j : Fin 2 × Bool) : BlockVec 2 :=
    (s⁻¹ • (E j).1, s • (E j).2)
  let w (P : ↥(triangleCubePartition Q.scale pi)) : ℝ :=
    (volume (openCubeSet (triangleRootCube Q pi P))).toReal /
      (volume (Whitney.KuhnCell.mk Q pi).openCarrier).toReal
  let AP (P : ↥(triangleCubePartition Q.scale pi)) :=
    Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain (triangleRootCube Q pi P))
      (triangleRootCubeCoeff Q pi a P)
  let qT (j : Fin 2 × Bool) :=
    blockVecDot (E j) (blockMatVecMul (frameMatrix σ A) (E j))
  let qC (P : ↥(triangleCubePartition Q.scale pi)) (j : Fin 2 × Bool) :=
    blockVecDot (E j) (blockMatVecMul (frameMatrix σ (AP P)) (E j))
  have hs : 0 < s := Real.sqrt_pos.mpr hσ
  have hs2 : s^2 = σ := Real.sq_sqrt hσ.le
  have hframeT (j : Fin 2 × Bool) :
      qT j = blockVecDot (Eσ j) (blockMatVecMul A (Eσ j)) := by
    have hh := Variational.frame_load_quadratic A (E j) s hs.ne'
    rw [hs2] at hh
    exact hh.symm
  have hframeC (P : ↥(triangleCubePartition Q.scale pi)) (j : Fin 2 × Bool) :
      qC P j = blockVecDot (Eσ j) (blockMatVecMul (AP P) (Eσ j)) := by
    have hh := Variational.frame_load_quadratic (AP P) (E j) s hs.ne'
    rw [hs2] at hh
    exact hh.symm
  have hquad_nonneg (V : Book.Ch02.Domain 2) (c : Book.Ch02.CoeffOn V)
      (P : BlockVec 2) :
      0 ≤ blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix V c) P) := by
    by_cases hP : P = 0
    · rw [hP]
      simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
    · exact (Book.Ch02.blockCoarseMatrixTheory V c).block_matrix_posDef P hP |>.le
  have hqT0 (j : Fin 2 × Bool) : 0 ≤ qT j := by
    rw [hframeT]
    exact hquad_nonneg T a (Eσ j)
  have hqC0 (P : ↥(triangleCubePartition Q.scale pi)) (j : Fin 2 × Bool) :
      0 ≤ qC P j := by
    rw [hframeC]
    exact hquad_nonneg _ _ (Eσ j)
  have htraceT :
      Matrix.trace (toFullBlockMat (frameMatrix σ A)) = ∑ j : Fin 2 × Bool, qT j := by
    have hh := full_response_frame_trace_eq_scaled_loads σ A hσ
    have hh' : Matrix.trace (toFullBlockMat (frameMatrix σ A)) =
        ∑ j : Fin 2 × Bool, blockVecDot (Eσ j) (blockMatVecMul A (Eσ j)) := by
      simpa only [Eσ, s, fullResponseTraceLoad] using hh
    calc
      _ = ∑ j : Fin 2 × Bool, blockVecDot (Eσ j) (blockMatVecMul A (Eσ j)) := hh'
      _ = ∑ j : Fin 2 × Bool, qT j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (hframeT j).symm
  have htraceC (P : ↥(triangleCubePartition Q.scale pi)) :
      Matrix.trace (toFullBlockMat (frameMatrix σ (AP P))) = ∑ j : Fin 2 × Bool, qC P j := by
    have hh := full_response_frame_trace_eq_scaled_loads σ (AP P) hσ
    have hh' : Matrix.trace (toFullBlockMat (frameMatrix σ (AP P))) =
        ∑ j : Fin 2 × Bool, blockVecDot (Eσ j) (blockMatVecMul (AP P) (Eσ j)) := by
      simpa only [Eσ, s, fullResponseTraceLoad] using hh
    calc
      _ = ∑ j : Fin 2 × Bool, blockVecDot (Eσ j) (blockMatVecMul (AP P) (Eσ j)) := hh'
      _ = ∑ j : Fin 2 × Bool, qC P j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (hframeC P j).symm
  have hcmp (j : Fin 2 × Bool) :
      ENNReal.ofReal (blockVecDot (Eσ j) (blockMatVecMul A (Eσ j))) ≤
        ∑' P : ↥(triangleCubePartition Q.scale pi), ENNReal.ofReal
          (w P * qC P j) := by
    have hh := triangle_root_full_response_le Q pi a (Eσ j).1 (Eσ j).2
    have hh' : ENNReal.ofReal (blockVecDot (Eσ j)
        (blockMatVecMul A (Eσ j))) ≤
        ∑' P : ↥(triangleCubePartition Q.scale pi), ENNReal.ofReal
          (w P * blockVecDot (Eσ j) (blockMatVecMul (AP P) (Eσ j))) := by
      simpa [A, T, w, AP, Eσ, triangleRootCubeCoeff, kuhnCellDomain] using hh
    have heq : (∑' P : ↥(triangleCubePartition Q.scale pi), ENNReal.ofReal
        (w P * qC P j)) =
        ∑' P : ↥(triangleCubePartition Q.scale pi), ENNReal.ofReal
          (w P * blockVecDot (Eσ j) (blockMatVecMul (AP P) (Eσ j))) := by
      apply tsum_congr
      intro P
      rw [hframeC P j]
    exact hh'.trans_eq heq.symm
  have hquarter : 0 ≤ (1/4:ℝ) := by norm_num
  have hcmp' (j : Fin 2 × Bool) :
      ENNReal.ofReal ((1/4:ℝ)*qT j) ≤
        ∑' P : ↥(triangleCubePartition Q.scale pi),
          ENNReal.ofReal (w P*((1/4:ℝ)*qC P j)) := by
    have hh := hcmp j
    rw [← hframeT j] at hh
    have hmul := mul_le_mul_right hh (ENNReal.ofReal (1/4:ℝ))
    rw [← ENNReal.ofReal_mul hquarter, ← ENNReal.tsum_mul_left] at hmul
    apply hmul.trans_eq
    apply tsum_congr
    intro P
    rw [← ENNReal.ofReal_mul hquarter]
    congr 1
    ring
  have hsumT : Matrix.trace (toFullBlockMat (frameMatrix σ A))/4 =
      ∑ j : Fin 2 × Bool, (1/4:ℝ)*qT j := by
    rw [htraceT]
    rw [← Finset.mul_sum]
    ring_nf
  have hsumC (P : ↥(triangleCubePartition Q.scale pi)) :
      w P*(Matrix.trace (toFullBlockMat (frameMatrix σ (AP P)))/4) =
        ∑ j : Fin 2 × Bool, w P*((1/4:ℝ)*qC P j) := by
    rw [htraceC P]
    calc
      w P * ((∑ j : Fin 2 × Bool, qC P j)/4) =
          (w P/4) * ∑ j : Fin 2 × Bool, qC P j := by ring
      _ = ∑ j : Fin 2 × Bool, (w P/4)*qC P j := by rw [← Finset.mul_sum]
      _ = ∑ j : Fin 2 × Bool, w P*((1/4:ℝ)*qC P j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hchild (P : ↥(triangleCubePartition Q.scale pi)) :
      (∑ j : Fin 2 × Bool, ENNReal.ofReal (w P*((1/4:ℝ)*qC P j))) =
        ENNReal.ofReal (w P*(Matrix.trace (toFullBlockMat
          (frameMatrix σ (AP P)))/4)) := by
    rw [hsumC P]
    exact (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun j : Fin 2 × Bool => w P*((1/4:ℝ)*qC P j))
      (fun j _ => mul_nonneg
        (show 0 ≤ w P from div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        (mul_nonneg hquarter (hqC0 P j)))).symm
  have hdouble :
      (∑ j : Fin 2 × Bool, ∑' P : ↥(triangleCubePartition Q.scale pi),
        ENNReal.ofReal (w P*((1/4:ℝ)*qC P j))) =
      ∑' P : ↥(triangleCubePartition Q.scale pi),
        ENNReal.ofReal (w P*(Matrix.trace (toFullBlockMat
          (frameMatrix σ (AP P)))/4)) := by
    calc
      _ = ∑' P : ↥(triangleCubePartition Q.scale pi),
          ∑ j : Fin 2 × Bool, ENNReal.ofReal (w P*((1/4:ℝ)*qC P j)) := by
        simpa only [tsum_fintype] using
          (ENNReal.tsum_comm (f := fun j P =>
            ENNReal.ofReal (w P*((1/4:ℝ)*qC P j))))
      _ = _ := by
        apply tsum_congr
        exact hchild
  calc
    _ = ∑ j : Fin 2 × Bool, ENNReal.ofReal ((1/4:ℝ)*qT j) := by
      rw [hsumT, ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg hquarter (hqT0 j))]
    _ ≤ ∑ j : Fin 2 × Bool, ∑' P : ↥(triangleCubePartition Q.scale pi),
        ENNReal.ofReal (w P*((1/4:ℝ)*qC P j)) :=
      Finset.sum_le_sum (fun j _ => hcmp' j)
    _ = _ := hdouble

/-- The normalized full trace of an actual old response cell is nonnegative,
as follows from positivity of each of its four normalized response loads. -/
theorem old_full_normalized_trace_nonneg (M : ABKModel 2) (n : ℤ)
    (R : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    0 ≤ Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M n : ℝ)
      (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 4 := by
  have hsource := clipped_source_quadratic_nonneg M n R ω
  have htrace := full_response_trace_eq_four_orthonormal_loads 1
    (ofFullBlockMat (clippedSourceMatrix M n R ω))
  have hframe : frameMatrix 1 (ofFullBlockMat (clippedSourceMatrix M n R ω)) =
      ofFullBlockMat (clippedSourceMatrix M n R ω) := by
    cases ofFullBlockMat (clippedSourceMatrix M n R ω)
    simp [frameMatrix]
  rw [hframe, toFullBlockMat_ofFullBlockMat] at htrace
  have hload (j : Fin 2) (ε : ℝ) (he : ε = 1 ∨ ε = -1) :
      0 ≤ blockVecDot (orthonormalFrameLoad j ε)
        (blockMatVecMul (ofFullBlockMat (clippedSourceMatrix M n R ω))
          (orthonormalFrameLoad j ε)) := by
    have hh := hsource (toFullBlockVec (orthonormalFrameLoad j ε))
    simpa only [clippedSourceMatrix, fullMatrixQuadratic_block,
      toFullBlockMat_ofFullBlockMat, ofFullBlockMat_toFullBlockMat] using hh
  rw [Matrix.trace, Fin.sum_univ_two] at htrace
  have hp := hload 0 1 (Or.inl rfl)
  have hm := hload 0 (-1) (Or.inr rfl)
  have hp' := hload 1 1 (Or.inl rfl)
  have hm' := hload 1 (-1) (Or.inr rfl)
  have hsum : 0 ≤
      blockVecDot (orthonormalFrameLoad 0 1)
        (blockMatVecMul (ofFullBlockMat (clippedSourceMatrix M n R ω))
          (orthonormalFrameLoad 0 1)) +
      blockVecDot (orthonormalFrameLoad 0 (-1))
        (blockMatVecMul (ofFullBlockMat (clippedSourceMatrix M n R ω))
          (orthonormalFrameLoad 0 (-1))) +
      (blockVecDot (orthonormalFrameLoad 1 1)
        (blockMatVecMul (ofFullBlockMat (clippedSourceMatrix M n R ω))
          (orthonormalFrameLoad 1 1)) +
      blockVecDot (orthonormalFrameLoad 1 (-1))
        (blockMatVecMul (ofFullBlockMat (clippedSourceMatrix M n R ω))
          (orthonormalFrameLoad 1 (-1)))) := by
    positivity
  have htrace' : 0 ≤ Matrix.trace (clippedSourceMatrix M n R ω) := by
    calc
      0 ≤ blockVecDot (orthonormalFrameLoad 0 1)
            (blockMatVecMul (ofFullBlockMat (clippedSourceMatrix M n R ω))
              (orthonormalFrameLoad 0 1)) +
          blockVecDot (orthonormalFrameLoad 0 (-1))
            (blockMatVecMul (ofFullBlockMat (clippedSourceMatrix M n R ω))
              (orthonormalFrameLoad 0 (-1))) +
          (blockVecDot (orthonormalFrameLoad 1 1)
            (blockMatVecMul (ofFullBlockMat (clippedSourceMatrix M n R ω))
              (orthonormalFrameLoad 1 1)) +
          blockVecDot (orthonormalFrameLoad 1 (-1))
            (blockMatVecMul (ofFullBlockMat (clippedSourceMatrix M n R ω))
              (orthonormalFrameLoad 1 (-1)))) := hsum
      _ = Matrix.trace (clippedSourceMatrix M n R ω) := htrace.symm
  have htrace'' : Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M n : ℝ)
      (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun))) =
      Matrix.trace (clippedSourceMatrix M n R ω) := rfl
  rw [← htrace''] at htrace'
  exact div_nonneg htrace' (by norm_num)

/-- The normalized old full trace is exactly one plus the normalized trace
defect, and the latter is bounded by the history operator defect. -/
theorem old_full_normalized_trace_le_one_add_defect (M : ABKModel 2) (n : ℤ)
    (R : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M n : ℝ)
      (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 4 ≤
      1 + historyOperatorDefect M n R ω := by
  let A := coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun
  let H := historyDefectMatrix (frameMatrix (Annealed.sigmaBar M n : ℝ) A)
  have hdef := history_defect_trace (Annealed.sigmaBar M n : ℝ) A
  have hbook : Book.Ch02.fullBlockTrace H = Matrix.trace H := by
    simp only [Book.Ch02.fullBlockTrace, H]
    rfl
  rw [hbook] at hdef
  have hframe : Matrix.trace (toFullBlockMat (frameMatrix
      (Annealed.sigmaBar M n : ℝ) A)) =
      (Annealed.sigmaBar M n : ℝ)⁻¹*Matrix.trace A.upperLeft +
        (Annealed.sigmaBar M n : ℝ)*Matrix.trace A.lowerRight := by
    simp [Matrix.trace, toFullBlockMat, frameMatrix, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.diag_apply]
    ring
  have htrace : Matrix.trace H =
      Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M n : ℝ) A))-4 := by
    rw [hdef, hframe]
  have hrelation : Matrix.trace (toFullBlockMat
      (frameMatrix (Annealed.sigmaBar M n : ℝ) A)) / 4 = 1 + Matrix.trace H/4 := by
    rw [htrace]
    ring
  have hnorm := full_block_normalized_trace_abs_le_euclidean_opNorm H
  have hnorm' : |Matrix.trace H/4| ≤ historyOperatorDefect M n R ω := by
    simpa only [A, H, historyOperatorDefect] using hnorm
  have hupper : Matrix.trace H/4 ≤ historyOperatorDefect M n R ω :=
    (le_abs_self _).trans hnorm'
  rw [hrelation]
  linarith only [hupper]

/-- On a good parent, the complete physical contained-cube family has a
summable normalized old full trace. The planar raw-history payment is
`1+2*sqrt(3)*tau`, before the later shear and wave terms. -/
theorem good_parent_triangle_old_full_trace_budget (M : ABKModel 2)
    {Q U : TriadicCube 2} {a : ℕ} (hU : U ∈ descendantsAtDepth Q a) (ha : a ≤ 2)
    (pi : Equiv.Perm (Fin 2)) (r : RootRow)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) Q) :
    let C := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i,
      ((volume (openCubeSet (rootTranslateCube U P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
        (Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M (Q.scale+40) : ℝ)
          (coarseBlockMatrix (cubeSet (rootTranslateCube U P))
            (Cutoff.coefficientCutoff M.nu (Q.scale+40) ω).toFun))) / 4)
    Summable C ∧ (∑' i, C i) ≤ 1+2*Real.sqrt 3*rootTau r := by
  classical
  let n := Q.scale+40
  let w := fun P : TriadicCube 2 =>
    (volume (openCubeSet (rootTranslateCube U P))).toReal /
      (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal
  let D := fun P : TriadicCube 2 => historyOperatorDefect M n (rootTranslateCube U P) ω
  let B := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i, w P*D P
  let C := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i,
    w P*(Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M n : ℝ)
      (coarseBlockMatrix (cubeSet (rootTranslateCube U P))
        (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 4)
  let mass := fun i : ℕ => 2*(1/3:ℝ)^(i+1)
  have hτ : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hB := triangle_good_parent_history_budget M n hU ha pi (rootTau r) hτ ω
    (good_cell_raw_history M Q (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω hgood)
  have hw0 (P : TriadicCube 2) : 0 ≤ w P := by
    dsimp only [w]
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hC0 (i : ℕ) : 0 ≤ C i := by
    apply Finset.sum_nonneg
    intro P hP
    exact mul_nonneg (hw0 P)
      (old_full_normalized_trace_nonneg M n (rootTranslateCube U P) ω)
  have hC (i : ℕ) : C i ≤ mass i+B i := by
    let S := triangleFirstCubes U.scale pi i
    have hsum : (∑ P ∈ S, w P*(1+D P)) =
        (∑ P ∈ S, w P)+(∑ P ∈ S, w P*D P) := by
      calc
        _ = ∑ P ∈ S, (w P+w P*D P) := by
          apply Finset.sum_congr rfl
          intro P hP
          ring
        _ = _ := Finset.sum_add_distrib
    calc
      C i ≤ ∑ P ∈ S, w P*(1+D P) := by
        apply Finset.sum_le_sum
        intro P hP
        have hh := old_full_normalized_trace_le_one_add_defect M n
          (rootTranslateCube U P) ω
        have hlin :
            Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M n : ℝ)
              (coarseBlockMatrix (cubeSet (rootTranslateCube U P))
                (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 4 ≤ 1+D P := by
          simpa only [D,n] using hh
        exact mul_le_mul_of_nonneg_left hlin (hw0 P)
      _ = mass i+B i := by
        dsimp only [B,D,mass]
        rw [hsum, triangle_root_first_weights]
  have hmaj : Summable (fun i : ℕ => mass i+B i) :=
    triangle_first_masses_hasSum.summable.add hB.1
  have hCs := hmaj.of_nonneg_of_le hC0 hC
  refine ⟨hCs, ?_⟩
  calc
    (∑' i : ℕ, C i) ≤ ∑' i : ℕ, (mass i+B i) := hCs.tsum_le_tsum hC hmaj
    _ = 1+∑' i : ℕ, B i := by
      dsimp only [mass]
      rw [triangle_first_masses_hasSum.summable.tsum_add hB.1,
        triangle_first_masses_hasSum.tsum_eq]
    _ ≤ 1+2*Real.sqrt 3*rootTau r := by linarith only [hB.2]

end
end ASDExplicitGamma.Inverse
