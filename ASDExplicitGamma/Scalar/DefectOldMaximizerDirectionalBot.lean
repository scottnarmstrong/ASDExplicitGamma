module

public import ASDExplicitGamma.Scalar.DefectOldMaximizerDirectional
public import ASDExplicitGamma.Native.OldSignedDirectionalDepthMatrix

/-! The flux-affine (bottom-load) directional tiled weak energy: the primal potential of the
canonical field of the load `(0, e)` plus its reciprocal defect `(a S)_2 - e`, bounded
pathwise by the same directional pair-charge series as the top load, hence
`E[B² (V_e² + G_e²)] <= β² ξ / 2` for the flux-affine problem. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Triadic Variational Native Inverse Gaussian
  Algsuperdiff.Section3 Numerics.Inverse ASDExplicitGamma.Main
open scoped ENNReal BigOperators
attribute [local irreducible] Homogenization.descendantsAtDepth
noncomputable section

/-- Cellwise: the directional pair charge is the coarse quadratic form of the actual cell
matrix at the two pure loads, minus `2|e|²`. -/
theorem cell_charge (M : ABKModel 2) (m : ℤ) (Q R : TriadicCube 2) (depth : ℕ)
    (hR : R ∈ descendantsAtDepth Q depth) (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    let k := oldCutoffSkewCoefficient m Q ω
    let σ := (Annealed.sigmaBar M m : ℝ)
    let a := responseFramePlanarCoefficientField M.nu σ k
    blockVecDot ((e, 0) : BlockVec 2) (blockMatVecMul
        (coarseBlockMatrix (openCubeSet R) a) ((e, 0) : BlockVec 2)) +
      blockVecDot ((0, e) : BlockVec 2) (blockMatVecMul
        (coarseBlockMatrix (openCubeSet R) a) ((0, e) : BlockVec 2)) - 2 * vecNormSq e =
      smoothFeedbackPairCharge M m R e ω := by
  intro k σ a
  let Ptop : BlockVec 2 := (e, 0)
  let Pbot : BlockVec 2 := (0, e)
  let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
  let kR := oldSignedCellCoefficient Q R hRQ k
  let aR := responseFramePlanarCoefficientField M.nu σ kR
  have hCoeff : a =ᵐ[volumeMeasureOn (openCubeSet R)] aR := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    simp only [a, aR, responseFramePlanarCoefficientField]
    rw [old_signed_cell_coefficient_extension_eq Q R hRQ k hx]
  have hCellMatrix :
      coarseBlockMatrix (openCubeSet R) a =
        smoothFeedbackCellA M m R ω := by
    calc
      coarseBlockMatrix (openCubeSet R) a =
          coarseBlockMatrix (openCubeSet R) aR :=
        coarseBlockMatrix_congr_of_ae_eq hCoeff
      _ = smoothFeedbackCellA M m R ω := by
        let aCube := responseFramePlanarCoefficientField M.nu σ
          (smoothFeedbackCellCubeCoefficient m R ω)
        have hCube : coarseBlockMatrix (cubeSet R) aCube =
            smoothFeedbackCellA M m R ω := by
          have hframe := Variational.response_coarseMatrix_frame_eq
            (measurableSet_cubeSet R) M.nu σ M.nu_pos
            (Annealed.sigmaBar M m).property
            (smoothFeedbackCellCubeCoefficient m R ω)
          rw [hframe, coarseBlockMatrix_congr_of_ae_eq
            (smooth_feedback_cube_physical_coefficient M m R ω)]
          rfl
        calc
          coarseBlockMatrix (openCubeSet R) aR =
              coarseBlockMatrix (openCubeSet R) aCube :=
            coarseBlockMatrix_congr_of_ae_eq
              (smooth_feedback_open_frame_coefficients_ae M m R ω)
          _ = coarseBlockMatrix (cubeSet R) aCube :=
            (Variational.cube_coarseMatrix_eq_open R _).symm
          _ = smoothFeedbackCellA M m R ω := hCube
  rw [hCellMatrix]
  simp [Ptop, Pbot, smoothFeedbackPairCharge,
    smoothFeedbackCellK, smoothFeedbackCellD,
    blockVecDot, blockMatVecMul, matVecMul, vecDot]

/-- The primal part `p_0` of the actual OLD canonical field of the flux load `(0, e)`. -/
def botPrimal (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) : Vec 2 → Vec 2 :=
  fun x => (oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω) ((0, e) : BlockVec 2) x).1

/-- The reciprocal defect `(a S)_2 - e` of the same field. -/
def botRecip (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) : Vec 2 → Vec 2 :=
  fun x => (oldSignedDualReflection Q M.nu (Annealed.sigmaBar M m : ℝ)
    (oldCutoffSkewCoefficient m Q ω)
    (oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω) ((0, e) : BlockVec 2)) x).1 - e

/-- The tiled depth-134 weak energy of the flux-affine pair `V² + G²`. -/
def dirTiledBot (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  descendantsAverage Q 134 (fun U =>
    vectorWeakHaarEnergy U (botPrimal M m Q e ω) +
      vectorWeakHaarEnergy U (botRecip M m Q e ω))

theorem botPrimal_memLp (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (i : Fin 2) :
    MemLp (fun x => botPrimal M m Q e ω x i) 2 (normalizedCubeMeasure Q) :=
  memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
    (memVectorL2_fst_of_memBlockL2 (Lp.memLp (oldSignedFrameCanonicalField Q M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
      (oldCutoffSkewCoefficient m Q ω) ((0, e) : BlockVec 2)))) i)

theorem botRecip_memLp (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (i : Fin 2) :
    MemLp (fun x => botRecip M m Q e ω x i) 2 (normalizedCubeMeasure Q) := by
  have hJ := (memVectorL2_fst_of_memBlockL2
    (old_signed_dual_reflection_memL2 Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
      (Lp.memLp (oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
        ((0, e) : BlockVec 2))))).sub (memVectorL2_const e)
  exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hJ i)

/-- The flux-affine per-depth projection bound against the directional pair charge. -/
theorem bot_depth_le_charge (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    (∑ i, energy Q (cubeProjection Q depth (fun x => botPrimal M m Q e ω x i))) +
      (∑ i, energy Q (cubeProjection Q depth (fun x => botRecip M m Q e ω x i))) ≤
      depthMax M m Q ω depth * descendantsAverage Q depth (fun R =>
        smoothFeedbackPairCharge M m R e ω) := by
  have hh := old_signed_paired_projection_exact_bound Q depth M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
    ((0, e) : BlockVec 2) ((e, 0) : BlockVec 2)
  dsimp only at hh
  have hc : blockVecDot ((0, e) : BlockVec 2) ((e, 0) : BlockVec 2).swap = vecNormSq e := by
    simp [blockVecDot, vecNormSq, vecDot]
  rw [hc] at hh
  have hav : descendantsAverage Q depth (fun R => smoothFeedbackPairCharge M m R e ω) =
      descendantsAverage Q depth (fun U => blockVecDot ((0, e) : BlockVec 2)
          (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
              (oldCutoffSkewCoefficient m Q ω))) ((0, e) : BlockVec 2))) +
        descendantsAverage Q depth (fun U => blockVecDot ((e, 0) : BlockVec 2)
          (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
              (oldCutoffSkewCoefficient m Q ω))) ((e, 0) : BlockVec 2))) - 2 * vecNormSq e := by
    have h1 : descendantsAverage Q depth (fun R => smoothFeedbackPairCharge M m R e ω) =
        descendantsAverage Q depth (fun U =>
          (blockVecDot ((e, 0) : BlockVec 2) (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
              (oldCutoffSkewCoefficient m Q ω))) ((e, 0) : BlockVec 2)) +
          blockVecDot ((0, e) : BlockVec 2) (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
              (oldCutoffSkewCoefficient m Q ω))) ((0, e) : BlockVec 2))) - 2 * vecNormSq e) := by
      change ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * (descendantsAtDepth Q depth).sum
          (fun R => smoothFeedbackPairCharge M m R e ω) = _
      apply congrArg (fun z : ℝ => ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * z)
      refine Finset.sum_congr rfl fun R hR => ?_
      exact (cell_charge M m Q R depth hR e ω).symm
    rw [h1, old_signed_descendants_average_sub, descendantsAverage_add, descendantsAverage_const]
    ring
  rw [hav]
  simpa [oldSignedPrimalProjectionEnergy, oldSignedReciprocalProjectionEnergy, botPrimal,
    botRecip, depthMax] using hh

/-- The directional tiled energy is bounded pathwise by the correlated directional
inverse-weighted pair-charge series. -/
theorem dirTiledBot_le_series (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) :
    dirTiledBot M m Q e ω ≤ ∑' j : ℕ, (1 - Scalar.inverseHistoryDiscount ^ 2) *
      Scalar.inverseHistoryDiscount ^ (2 * j) * depthMax M m Q ω (134 + j) *
        dirX M m Q e ω j := by
  classical
  have hα := Scalar.inverse_history_discount_range
  have hΔ0 : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 :=
    sub_nonneg.mpr (pow_le_one₀ hα.1.le hα.2.le)
  let F : Bool → Vec 2 → Vec 2 := fun c =>
    if c then botPrimal M m Q e ω
    else botRecip M m Q e ω
  have hF : ∀ c i, MemLp (fun x => F c x i) 2 (normalizedCubeMeasure Q) := by
    intro c i
    cases c
    · simpa [F] using botRecip_memLp M m Q e ω i
    · simpa [F] using botPrimal_memLp M m Q e ω i
  obtain ⟨hs1, hid⟩ := old_signed_tiled_weak_projection_series Q 134 F hF
  have hsumF (U : TriadicCube 2) : ∑ c : Bool, vectorWeakHaarEnergy U (F c) =
      vectorWeakHaarEnergy U (botPrimal M m Q e ω) +
        vectorWeakHaarEnergy U (botRecip M m Q e ω) := by
    simp [Fintype.sum_bool, F]
  have hL : dirTiledBot M m Q e ω =
      descendantsAverage Q 134 (fun U => ∑ c : Bool, vectorWeakHaarEnergy U (F c)) := by
    unfold dirTiledBot
    congr 1
    funext U
    rw [hsumF]
  rw [hL, hid]
  -- RHS summability
  have hB := alpha_depth_le_B M m Q ω
  have hTs := traceSeries_summable M m Q ω
  have hRHS : Summable (fun j : ℕ => (1 - Scalar.inverseHistoryDiscount ^ 2) *
      Scalar.inverseHistoryDiscount ^ (2 * j) * depthMax M m Q ω (134 + j) *
        dirX M m Q e ω j) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      (hTs.mul_left ((1 - Scalar.inverseHistoryDiscount ^ 2) *
        bhist M m Q 134 ω * vecNormSq e))
    · exact mul_nonneg (mul_nonneg (mul_nonneg hΔ0 (pow_nonneg hα.1.le _))
        (lemmaVInverseDepthMax_nonneg _ _ _)) (dirX_nonneg M m Q e ω j)
    · have h1 := hB j
      have h2 := dirX_le M m Q e ω j
      have hD0 : 0  ≤ depthMax M m Q ω (134 + j) := lemmaVInverseDepthMax_nonneg _ _ _
      have hX0 := dirX_nonneg M m Q e ω j
      have hp : 0 ≤ Scalar.inverseHistoryDiscount ^ j := pow_nonneg hα.1.le j
      have hsq : Scalar.inverseHistoryDiscount ^ (2 * j) =
          Scalar.inverseHistoryDiscount ^ j * Scalar.inverseHistoryDiscount ^ j := by
        rw [show 2 * j = j + j by omega, pow_add]
      calc (1 - Scalar.inverseHistoryDiscount ^ 2) *
            Scalar.inverseHistoryDiscount ^ (2 * j) * depthMax M m Q ω (134 + j) *
              dirX M m Q e ω j
          = (1 - Scalar.inverseHistoryDiscount ^ 2) *
            (Scalar.inverseHistoryDiscount ^ j * depthMax M m Q ω (134 + j)) *
              (Scalar.inverseHistoryDiscount ^ j * dirX M m Q e ω j) := by
            rw [hsq]; ring
        _ ≤ (1 - Scalar.inverseHistoryDiscount ^ 2) * bhist M m Q 134 ω *
              (Scalar.inverseHistoryDiscount ^ j *
                (vecNormSq e * rawWeakTraceSequence M m Q 0 ω (134 + j))) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left h1 hΔ0
            · exact mul_le_mul_of_nonneg_left h2 hp
            · exact mul_nonneg hp hX0
            · exact mul_nonneg hΔ0 ((mul_nonneg hp hD0).trans h1)
        _ = _ := by ring
  have hmain : (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) * ∑ c : Bool, ∑ i : Fin 2,
      energy Q (cubeProjection Q (134 + j) (fun x => F c x i))) ≤
      ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) * (depthMax M m Q ω (134 + j) *
        dirX M m Q e ω j) := by
    refine hs1.tsum_le_tsum (fun j => ?_) ?_
    · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hα.1.le _)
      have h := bot_depth_le_charge M m Q (134 + j) e ω
      simpa [Fintype.sum_bool, F, depthMax, dirX, add_comm] using h
    · simpa only [mul_assoc] using hRHS.mul_left ((1 - Scalar.inverseHistoryDiscount ^ 2)⁻¹) |>.congr
        (fun j => by
          have : (1 - Scalar.inverseHistoryDiscount ^ 2) ≠ 0 := by
            have := pow_lt_one₀ hα.1.le hα.2 (by norm_num : 2 ≠ 0)
            linarith
          field_simp)
  calc (1 - Scalar.inverseHistoryDiscount ^ 2) * ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
        ∑ c : Bool, ∑ i : Fin 2, energy Q (cubeProjection Q (134 + j) (fun x => F c x i))
      ≤ (1 - Scalar.inverseHistoryDiscount ^ 2) * ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
        (depthMax M m Q ω (134 + j) * dirX M m Q e ω j) :=
        mul_le_mul_of_nonneg_left hmain hΔ0
    _ = _ := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro j
        ring

end
end ASDExplicitGamma.Scalar
