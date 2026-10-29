module

public import ASDExplicitGamma.Main.ThetaGeneratorELinearProxyTranslate
public import ASDExplicitGamma.Main.ELinearObsBridge
public import ASDExplicitGamma.Main.HotCovCellBound

/-! MA-E-COVARIANCE, expectation step 1: the cell frame of the hot patch (the restricted
observer-root coefficient) has the same directional proxy as the cell's own skew coefficient,
and the proxy payment `E proxy <= (xi/2) sum |nu_i|^2` for a deterministic vector family. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

local instance hotCovProxyCompact_Th (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

/-- The proxy of the restricted observer coefficient on a cell is the proxy of the cell's own
skew coefficient. -/
theorem hotCov_proxy_cell_bridge_Th (M : ABKModel 2) (Q : TriadicCube 2) (d : ℕ) (m : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (U : OldSignedCellIndex Q d) (e : Vec 2) :
    oldSignedDirectionalProxy U.val
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (hotCovCellCoef Q d (mainAffineOpenResponseRestriction Q
          (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω)) U)) e =
    oldSignedDirectionalProxy U.val (responseFramePlanarCoefficientField M.nu
      (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U.val ω)) e := by
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  have hσ := (Annealed.sigmaBar_characterization M m).1
  have hEllQ := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
    (mainAffineOpenResponseRestriction Q
      (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω))
  have hEllC := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U.val) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
    (hotCovCellCoef Q d (mainAffineOpenResponseRestriction Q
      (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω)) U)
  have h1 := old_signed_directional_proxy_congr U.val _ _ hEllC
    (hEllQ.mono (measurableSet_openCubeSet U.val) hsub)
    (old_signed_cell_frame_coefficient_ae Q U.val hsub M.nu (Annealed.sigmaBar M m : ℝ)
      (mainAffineOpenResponseRestriction Q
        (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω))) e
  refine h1.trans ?_
  exact main_e_linear_obs_proxy_bridge M Q m t ω U.val hsub e

theorem hotCov_proxy_zero_Th (U : TriadicCube 2) (a : CoeffField 2) :
    oldSignedDirectionalProxy U a 0 = 0 := by
  unfold oldSignedDirectionalProxy ASDExplicitGamma.Inverse.rawWeakTraceProxy
  simp [vecDot]

/-- The proxy payment for one deterministic vector family. -/
theorem hotCov_proxy_payment_Th {I : Type*} [Countable I]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (hscale : U.scale = m - 5)
    (ν : I → Vec 2) (hν : Summable (fun i => vecNormSq (ν i))) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let xi := mainEnvelopeXi
      ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
      M.gamma (theta M * mainSourceInversePrefix) (theta M) t
    Integrable (fun ω => ∑' i, oldSignedDirectionalProxy U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t U ω)) (ν i)) μ ∧
    (∫ ω, ∑' i, oldSignedDirectionalProxy U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t U ω)) (ν i) ∂μ) ≤
      xi / 2 * ∑' i, vecNormSq (ν i) := by
  intro μ xi
  let E : I → Fin 2 → Vec 2 := fun i c => if c = 0 then ν i else 0
  have hE : Summable (fun i => ∑ c : Fin 2, vecNormSq (E i c)) := by
    refine hν.congr (fun i => ?_)
    simp [E, Fin.sum_univ_two, vecNormSq, vecDot]
  have hp := main_e_linear_obs_proxy_modes_payment_Th M h hM hγ N hpast m hm t ht U hscale E hE
  have hP : (fun ω => ∑' i, ∑ c : Fin 2, oldSignedDirectionalProxy U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t U ω)) (E i c)) = fun ω => ∑' i,
      oldSignedDirectionalProxy U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) (ν i) := by
    funext ω
    apply tsum_congr
    intro i
    simp [E, Fin.sum_univ_two, hotCov_proxy_zero_Th]
  have hS : ∑' i, ∑ c : Fin 2, vecNormSq (E i c) = ∑' i, vecNormSq (ν i) := by
    apply tsum_congr
    intro i
    simp [E, Fin.sum_univ_two, vecNormSq, vecDot]
  dsimp only at hp
  rw [hP, hS] at hp
  exact hp

end

end ASDExplicitGamma.Main
