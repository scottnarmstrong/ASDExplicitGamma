module

public import ASDExplicitGamma.Inverse.AssemblyTriangleTrace

/-! Actual active-triangle trace and its complete contained-cube means. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- On a good parent, the actual full normalized trace of an attenuated
coefficient on a physical Kuhn simplex is bounded by the weighted sum of
its contained-cube bounds. Each cube uses its own later-wave mean in the
shear payment. The result is the active-simplex input to the wave and
selected-height aggregation of the source. -/
theorem assembly_active_triangle_trace_cube_majorant
    (M : ABKModel 2) {Q U : TriadicCube 2} {a : ℕ}
    (hU : U ∈ descendantsAtDepth Q a) (pi : Equiv.Perm (Fin 2))
    (m J : ℤ) (hn : Q.scale + 40 ≤ m) (hm : m ≤ J)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (resetAllOrderTau)
      (ASDExplicitGamma.Gaussian.waveGateEta .allOrder) Q) :
    let n := Q.scale + 40
    let σ := (Annealed.sigmaBar M n : ℝ)
    let h := laterBandW2 Q n J (sourceBandWeights m weights) ω
    ENNReal.ofReal (Matrix.trace (toFullBlockMat (frameMatrix σ
      (coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
        (attenuatedCoefficient M m J weights ω)))) / 4) ≤
      ∑' P : ↥(triangleCubePartition U.scale pi), ENNReal.ofReal
        (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
          (rootAssemblySensitivity * Matrix.trace (toFullBlockMat (frameMatrix σ
            (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
              (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 2 +
            (cubeAverage (triangleRootCube U pi P)
              ((h.restrict (triangle_root_cube_descendant_of_parent hU pi P)).value.toFun) / σ)^2 *
              rootAssemblySensitivity * Matrix.trace ((frameMatrix σ
                (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
                  (Cutoff.coefficientCutoff M.nu n ω).toFun)).lowerRight) / 2)) := by
  classical
  dsimp only
  let n := Q.scale + 40
  let σ := (Annealed.sigmaBar M n : ℝ)
  let h := laterBandW2 Q n J (sourceBandWeights m weights) ω
  let k := oldResponseCoefficient Q n ω +
    laterResponseCoefficient Q n J (sourceBandWeights m weights) ω
  let aQ := sensitivityBookCoeffOn Q M.nu M.nu_pos k
  let T := kuhnCellDomain (Whitney.KuhnCell.mk U pi)
  have hT : (T : Set (Vec 2)) ⊆ openCubeSet Q := by
    exact (Whitney.KuhnCell.openCarrier_subset_openCubeSet _).trans
      (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  let aT := restrictCoeffOn aQ hT
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hcmp := triangle_root_full_trace_le_weighted_cube_traces U pi aT σ hσ
  have hTe : Book.Ch02.coarseBlockMatrix T aT =
      coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
        (attenuatedCoefficient M m J weights ω) := by
    simpa only [aT, aQ, k, n, T, kuhnCellDomain] using
      attenuated_domain_matrix_eq M Q n m J hn hm weights ω T hT
  have hCe (P : ↥(triangleCubePartition U.scale pi)) :
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain (triangleRootCube U pi P))
        (triangleRootCubeCoeff U pi aT P) =
      coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
        (attenuatedCoefficient M m J weights ω) := by
    have hP : openCubeSet (triangleRootCube U pi P) ⊆ openCubeSet Q :=
      (triangle_root_cube_subset U pi P).trans hT
    have hh := attenuated_domain_matrix_eq M Q n m J hn hm weights ω
      (Book.Ch02.cubeDomain (triangleRootCube U pi P)) hP
    change Book.Ch02.coarseBlockMatrix _ (restrictCoeffOn aQ hP) = _ at hh
    change Book.Ch02.coarseBlockMatrix _
      (restrictCoeffOn (restrictCoeffOn aQ hT)
        (triangle_root_cube_subset U pi P)) = _
    rw [show restrictCoeffOn (restrictCoeffOn aQ hT)
      (triangle_root_cube_subset U pi P) = restrictCoeffOn aQ hP from rfl, hh]
    exact (coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube _ _).symm
  have hcmp' : ENNReal.ofReal (Matrix.trace (toFullBlockMat (frameMatrix σ
      (coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
        (attenuatedCoefficient M m J weights ω)))) / 4) ≤
      ∑' P : ↥(triangleCubePartition U.scale pi), ENNReal.ofReal
        (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
          (Matrix.trace (toFullBlockMat (frameMatrix σ
            (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
              (attenuatedCoefficient M m J weights ω)))) / 4)) := by
    rw [hTe] at hcmp
    simpa only [hCe] using hcmp
  have hterm (P : ↥(triangleCubePartition U.scale pi)) :
      ENNReal.ofReal (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
        (Matrix.trace (toFullBlockMat (frameMatrix σ
          (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
            (attenuatedCoefficient M m J weights ω)))) / 4)) ≤
      ENNReal.ofReal (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
        (rootAssemblySensitivity * Matrix.trace (toFullBlockMat (frameMatrix σ
          (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
            (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 2 +
        (cubeAverage (triangleRootCube U pi P)
          ((h.restrict (triangle_root_cube_descendant_of_parent hU pi P)).value.toFun) / σ)^2 *
          rootAssemblySensitivity * Matrix.trace ((frameMatrix σ
            (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
              (Cutoff.coefficientCutoff M.nu n ω).toFun)).lowerRight) / 2)) := by
    let R := triangleRootCube U pi P
    let j := a + (triangleRootPartitionDepth U pi P + 1)
    let w := (volume (openCubeSet R)).toReal /
      (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal
    let B := coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun
    let μ := cubeAverage R
      ((h.restrict (triangle_root_cube_descendant_of_parent hU pi P)).value.toFun)
    let g := μ / σ
    have hR : R ∈ descendantsAtDepth Q j := by
      dsimp only [R, j]
      exact triangle_root_cube_descendant_of_parent hU pi P
    have hdesc := reset_good_parent_descendant_actual_full_normalized_trace
      M hR m J hn hm weights hw ω hgood
    have hdesc' : Matrix.trace (toFullBlockMat (frameMatrix σ
        (coarseBlockMatrix (cubeSet R) (attenuatedCoefficient M m J weights ω)))) / 4 ≤
        rootAssemblySensitivity * Matrix.trace (toFullBlockMat (frameMatrix σ B)) / 2 +
          g^2 * rootAssemblySensitivity * Matrix.trace ((frameMatrix σ B).lowerRight) / 2 := by
      dsimp only [σ, B, h, n, μ, g] at hdesc ⊢
      linarith
    have hw0 : 0 ≤ w := by
      dsimp only [w]
      exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have hmul := mul_le_mul_of_nonneg_left hdesc' hw0
    exact ENNReal.ofReal_le_ofReal hmul
  calc
    _ ≤ ∑' P : ↥(triangleCubePartition U.scale pi), ENNReal.ofReal
        (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
          (Matrix.trace (toFullBlockMat (frameMatrix σ
            (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
              (attenuatedCoefficient M m J weights ω)))) / 4)) := hcmp'
    _ ≤ ∑' P : ↥(triangleCubePartition U.scale pi), ENNReal.ofReal (
        ((volume (openCubeSet (triangleRootCube U pi P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
        (rootAssemblySensitivity * Matrix.trace (toFullBlockMat (frameMatrix σ
          (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
            (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 2 +
        (cubeAverage (triangleRootCube U pi P)
          ((h.restrict (triangle_root_cube_descendant_of_parent hU pi P)).value.toFun) / σ)^2 *
          rootAssemblySensitivity * Matrix.trace ((frameMatrix σ
            (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
              (Cutoff.coefficientCutoff M.nu n ω).toFun)).lowerRight) / 2)) := by
      exact ENNReal.tsum_le_tsum hterm

/-- A uniform cap on each contained cube's later-wave mean turns the
cube-by-cube actual trace estimate into a scalar active-simplex cap. The
complete old-trace history budget supplies `1+2√3 τ`; the two shear terms
are kept as the explicit factor `1+W²`. -/
theorem assembly_active_triangle_trace_of_uniform_mean
    (M : ABKModel 2) {Q U : TriadicCube 2} {a : ℕ}
    (hU : U ∈ descendantsAtDepth Q a) (ha : a ≤ 2)
    (pi : Equiv.Perm (Fin 2))
    (m J : ℤ) (hn : Q.scale + 40 ≤ m) (hm : m ≤ J)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (resetAllOrderTau)
      (ASDExplicitGamma.Gaussian.waveGateEta .allOrder) Q)
    (W : ℝ) (hW : 0 ≤ W)
    (hmean : ∀ P : ↥(triangleCubePartition U.scale pi),
      |cubeAverage (triangleRootCube U pi P)
        ((laterBandW2 Q (Q.scale + 40) J (sourceBandWeights m weights) ω).restrict
          (triangle_root_cube_descendant_of_parent hU pi P)).value.toFun /
          (Annealed.sigmaBar M (Q.scale + 40) : ℝ)| ≤ W) :
    ENNReal.ofReal (Matrix.trace (toFullBlockMat (frameMatrix
      (Annealed.sigmaBar M (Q.scale + 40) : ℝ)
      (coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
        (attenuatedCoefficient M m J weights ω)))) / 4) ≤
      ENNReal.ofReal (2 * rootAssemblySensitivity * (1 + W^2) *
        (1 + 2 * Real.sqrt 3 * resetAllOrderTau)) := by
  classical
  let n := Q.scale + 40
  let σ := (Annealed.sigmaBar M n : ℝ)
  let h := laterBandW2 Q n J (sourceBandWeights m weights) ω
  let w (P : ↥(triangleCubePartition U.scale pi)) : ℝ :=
    (volume (openCubeSet (triangleRootCube U pi P))).toReal /
      (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal
  let t (P : ↥(triangleCubePartition U.scale pi)) : ℝ :=
    Matrix.trace (toFullBlockMat (frameMatrix σ
      (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
        (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 4
  let b := 2 * rootAssemblySensitivity * (1 + W^2)
  let f (P : ↥(triangleCubePartition U.scale pi)) : ℝ :=
    w P * b * t P
  let Csrc (i : ℕ) : ℝ :=
    ∑ P ∈ triangleFirstCubes U.scale pi i,
      ((volume (openCubeSet (rootTranslateCube U P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
        (Matrix.trace (toFullBlockMat (frameMatrix σ
          (coarseBlockMatrix (cubeSet (rootTranslateCube U P))
            (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 4)
  let c (P : TriadicCube 2) : ℝ :=
    ((volume (openCubeSet (rootTranslateCube U P))).toReal /
      (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
      (Matrix.trace (toFullBlockMat (frameMatrix σ
        (coarseBlockMatrix (cubeSet (rootTranslateCube U P))
          (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 4)
  have hb : 0 ≤ b := by dsimp only [b, rootAssemblySensitivity]; positivity
  have hbudget := assembly_parent_triangle_old_trace_budget
    M hU ha pi ω hgood
  have hbudget' : Summable Csrc ∧ (∑' i, Csrc i) ≤
      1 + 2 * Real.sqrt 3 * resetAllOrderTau := by
    simpa only [Csrc, n, σ] using hbudget
  have ht0 (P : ↥(triangleCubePartition U.scale pi)) : 0 ≤ t P := by
    dsimp only [t]
    exact old_full_normalized_trace_nonneg M n
      (triangleRootCube U pi P) ω
  have hw0 (P : ↥(triangleCubePartition U.scale pi)) : 0 ≤ w P := by
    dsimp only [w]
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hterm (P : ↥(triangleCubePartition U.scale pi)) :
      ENNReal.ofReal (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
        (rootAssemblySensitivity * Matrix.trace (toFullBlockMat (frameMatrix σ
          (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
            (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 2 +
        (cubeAverage (triangleRootCube U pi P)
          ((h.restrict (triangle_root_cube_descendant_of_parent hU pi P)).value.toFun) /
            σ)^2 * rootAssemblySensitivity * Matrix.trace ((frameMatrix σ
              (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
                (Cutoff.coefficientCutoff M.nu n ω).toFun)).lowerRight) / 2)) ≤
      ENNReal.ofReal (f P) := by
    let R := triangleRootCube U pi P
    let B := coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun
    let μ := cubeAverage R ((h.restrict
      (triangle_root_cube_descendant_of_parent hU pi P)).value.toFun)
    let g := μ / σ
    have hR : R ∈ descendantsAtDepth Q
        (a + (triangleRootPartitionDepth U pi P + 1)) :=
      triangle_root_cube_descendant_of_parent hU pi P
    have hdesc := reset_good_parent_descendant_actual_full_normalized_trace
      M hR m J hn hm weights hw ω hgood
    have hg : |g| ≤ W := by
      dsimp only [g, μ, σ, h, n, R]
      exact hmean P
    have hgsq : g^2 ≤ W^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg g) hW).2 hg
      simpa only [sq_abs] using hh
    have hfull0 : 0 ≤ Matrix.trace (toFullBlockMat (frameMatrix σ B)) := by
      have hh := old_full_normalized_trace_nonneg M n R ω
      dsimp only [σ] at hh ⊢
      dsimp only [B] at hh ⊢
      nlinarith only [hh]
    have hLRle := old_full_framed_lower_right_trace_le M n R ω
    have hprod : g^2 * Matrix.trace (frameMatrix σ B).lowerRight ≤
        W^2 * Matrix.trace (toFullBlockMat (frameMatrix σ B)) := by
      by_cases hLR0 : Matrix.trace (frameMatrix σ B).lowerRight ≤ 0
      · have hleft : g^2 * Matrix.trace (frameMatrix σ B).lowerRight ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sq_nonneg g) hLR0
        have hright : 0 ≤ W^2 * Matrix.trace (toFullBlockMat (frameMatrix σ B)) :=
          mul_nonneg (sq_nonneg W) hfull0
        linarith
      · have hLRpos : 0 ≤ Matrix.trace (frameMatrix σ B).lowerRight := le_of_not_ge hLR0
        calc
          _ ≤ W^2 * Matrix.trace (frameMatrix σ B).lowerRight :=
            mul_le_mul_of_nonneg_right hgsq hLRpos
          _ ≤ _ := mul_le_mul_of_nonneg_left hLRle (sq_nonneg W)
    have hδ : 0 ≤ rootAssemblySensitivity := (Real.exp_pos _).le
    have hbase :
        rootAssemblySensitivity * Matrix.trace (toFullBlockMat (frameMatrix σ B)) / 2 +
          g^2 * rootAssemblySensitivity * Matrix.trace (frameMatrix σ B).lowerRight / 2 ≤
        b * (Matrix.trace (toFullBlockMat (frameMatrix σ B)) / 4) := by
      dsimp only [b]
      nlinarith only [hprod, hδ]
    have hwbase := mul_le_mul_of_nonneg_left hbase (hw0 P)
    have htermReal :
        ((volume (openCubeSet R)).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
          (rootAssemblySensitivity * Matrix.trace (toFullBlockMat (frameMatrix σ B)) / 2 +
            (μ / σ)^2 * rootAssemblySensitivity *
              Matrix.trace (frameMatrix σ B).lowerRight / 2) ≤ f P := by
      dsimp only [f, t, w, R, B, μ, σ, h, n] at hwbase ⊢
      convert hwbase using 1
      ring
    exact ENNReal.ofReal_le_ofReal htermReal
  have Csrc0 (i : ℕ) : 0 ≤ Csrc i := by
    dsimp only [Csrc]
    apply Finset.sum_nonneg
    intro P hP
    exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (old_full_normalized_trace_nonneg M n (rootTranslateCube U P) ω)
  have hCscaled (i : ℕ) : 0 ≤ b * Csrc i := mul_nonneg hb (Csrc0 i)
  have hCscaled_sum : Summable (fun i : ℕ => b * Csrc i) :=
    hbudget'.1.mul_left b
  have hpartition_sum :
      (∑' P : ↥(triangleCubePartition U.scale pi), ENNReal.ofReal (f P)) =
        ENNReal.ofReal (∑' i : ℕ, b * Csrc i) := by
    rw [← (triangleFirstEquiv U.scale pi).tsum_eq (fun P => ENNReal.ofReal (f P)),
      ENNReal.tsum_sigma']
    rw [ENNReal.ofReal_tsum_of_nonneg hCscaled hCscaled_sum]
    apply tsum_congr
    intro i
    have hsumReal : (∑ P ∈ triangleFirstCubes U.scale pi i, b * c P) =
        b * Csrc i := by
      dsimp only [Csrc, c]
      rw [← Finset.mul_sum]
    have hmap (P : ↥(triangleFirstCubes U.scale pi i)) :
        f ((triangleFirstEquiv U.scale pi) ⟨i, P⟩) = b * c P.val := by
      dsimp only [f, w, t, c]
      simp only [triangleFirstEquiv, Equiv.ofBijective_apply,
        triangleRootCube, rootTranslatedCube, rootTranslateCube]
      ring
    have hnonneg (P : TriadicCube 2) (hP : P ∈ triangleFirstCubes U.scale pi i) :
        0 ≤ b * c P := by
      dsimp only [c]
      have hP0 : 0 ≤ (volume (openCubeSet (rootTranslateCube U P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal :=
        div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      have htP : 0 ≤ Matrix.trace (toFullBlockMat (frameMatrix σ
          (coarseBlockMatrix (cubeSet (rootTranslateCube U P))
            (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 4 :=
        old_full_normalized_trace_nonneg M n (rootTranslateCube U P) ω
      exact mul_nonneg hb (mul_nonneg hP0 htP)
    rw [← hsumReal, ENNReal.ofReal_sum_of_nonneg hnonneg]
    have hh := Finset.sum_coe_sort (triangleFirstCubes U.scale pi i)
      (fun P => ENNReal.ofReal (b * c P))
    calc
      _ = ∑' P : ↥(triangleFirstCubes U.scale pi i),
          ENNReal.ofReal (b * c P.val) := by
        apply tsum_congr
        intro P
        exact congrArg ENNReal.ofReal (hmap P)
      _ = ∑ P ∈ triangleFirstCubes U.scale pi i,
          ENNReal.ofReal (b * c P) := by
        rw [tsum_fintype]
        exact hh
  have hsum_le : (∑' i : ℕ, b * Csrc i) ≤
      b * (1 + 2 * Real.sqrt 3 * resetAllOrderTau) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hbudget'.2 hb
  have hfinal : (∑' P : ↥(triangleCubePartition U.scale pi),
      ENNReal.ofReal (f P)) ≤
      ENNReal.ofReal (b * (1 + 2 * Real.sqrt 3 * resetAllOrderTau)) := by
    rw [hpartition_sum]
    exact ENNReal.ofReal_le_ofReal hsum_le
  have hcube := assembly_active_triangle_trace_cube_majorant
    M hU pi m J hn hm weights hw ω hgood
  calc
    _ ≤ ∑' P : ↥(triangleCubePartition U.scale pi), ENNReal.ofReal
        (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
          (rootAssemblySensitivity * Matrix.trace (toFullBlockMat (frameMatrix σ
            (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
              (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 2 +
          (cubeAverage (triangleRootCube U pi P)
            ((h.restrict (triangle_root_cube_descendant_of_parent hU pi P)).value.toFun) /
              σ)^2 * rootAssemblySensitivity * Matrix.trace ((frameMatrix σ
                (coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
                  (Cutoff.coefficientCutoff M.nu n ω).toFun)).lowerRight) / 2)) := hcube
    _ ≤ ∑' P : ↥(triangleCubePartition U.scale pi), ENNReal.ofReal (f P) :=
      ENNReal.tsum_le_tsum hterm
    _ ≤ ENNReal.ofReal (b * (1 + 2 * Real.sqrt 3 * resetAllOrderTau)) := hfinal

end
end ASDExplicitGamma.Inverse
