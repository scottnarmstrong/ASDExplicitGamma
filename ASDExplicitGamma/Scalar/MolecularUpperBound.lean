module

public import ASDExplicitGamma.Scalar.Molecular
public import ASDExplicitGamma.Scalar.MolecularUpper
public import ASDExplicitGamma.Scalar.MolecularUpperVariational
public import ASDExplicitGamma.Model.CutoffProjectedEnergy

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Corrector
open ASDExplicitGamma.Model
open Filter

namespace ASDExplicitGamma.Scalar

/-- The actual cutoff lower-right entry dominates the reciprocal molecular
trial denominator, with no small-disorder hypothesis. -/
theorem cutoff_coarseLowerRight_molecular_lower (M : ABKModel 2) (m n : ℤ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (M.nu + cutoffProjectedEnergy M planarBasis0 m n ω / M.nu)⁻¹ ≤
        (Homogenization.coarseBlockMatrix (cubeSet (originCube 2 n))
          (Cutoff.coefficientCutoff M.nu m ω).toFun).lowerRight 0 0 := by
  filter_upwards [cutoffProjectedField_residual M planarBasis0 m n] with ω hω
  have hcoef (x : Vec 2) : matVecMul (Cutoff.coefficientCutoff M.nu m ω x) planarBasis0 -
      M.nu • planarBasis0 = matVecMul (Cutoff.cutoffValue m ω x) planarBasis0 := by
    change matVecMul (M.nu • (1 : Mat 2) + Cutoff.cutoffValue m ω x) planarBasis0 - _ = _
    rw [add_matVecMul, Internal.Ch02.BookCh02.matVecMul_smul_one]
    abel
  have hres : IsSolenoidalOn (openCubeSet (originCube 2 n)) (fun x =>
      matVecMul (Cutoff.coefficientCutoff M.nu m ω x) planarBasis0 - M.nu • planarBasis0 -
        (cutoffProjectedField M planarBasis0 m ω x).toVec) := by
    simpa only [hcoef] using hω.2
  have he : vecNormSq planarBasis0 = 1 := by
    simp [planarBasis0, vecNormSq, vecDot, Pi.single_apply]
  have hb := molecular_lowerRight_of_physical_projection
    (Ch02.cubeDomain (originCube 2 n))
    (Cutoff.coefficientCutoffCoeffOn M m ω (originCube 2 n))
    (Cutoff.isEllipticFieldOn_coefficientCutoff_cube M m ω (originCube 2 n)) M.nu_pos
    (Cutoff.symmPart_coefficientCutoff M.nu m ω) he hω.1 hres
  have hnorm (x : Vec 2) : vecNormSq (cutoffProjectedField M planarBasis0 m ω x).toVec =
      ‖cutoffProjectedField M planarBasis0 m ω x‖ ^ 2 :=
    (HilbertVec.inner_def _ _).symm.trans (real_inner_self_eq_norm_sq _)
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  change (M.nu + volumeAverage (openCubeSet (originCube 2 n))
    (fun x => ‖cutoffProjectedField M planarBasis0 m ω x‖ ^ 2) / M.nu)⁻¹ ≤ _
  change (M.nu + volumeAverage (openCubeSet (originCube 2 n))
    (fun x => vecNormSq (cutoffProjectedField M planarBasis0 m ω x).toVec) / M.nu)⁻¹ ≤
    vecDot planarBasis0 (matVecMul (Homogenization.coarseBlockMatrix
      (openCubeSet (originCube 2 n)) (Cutoff.coefficientCutoff M.nu m ω).toFun).lowerRight planarBasis0) at hb
  simp_rw [hnorm] at hb
  simpa [planarBasis0, vecDot, matVecMul, Fin.sum_univ_two, Pi.single_apply] using hb

/-- Reciprocal integrability from a positive deterministic lower bound. -/
theorem integrable_inv_of_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} {a : ℝ}
    (ha : 0 < a) (hf : AEStronglyMeasurable f μ) (hlower : ∀ᵐ ω ∂μ, a ≤ f ω) :
    Integrable (fun ω => (f ω)⁻¹) μ := by
  refine (integrable_const a⁻¹).mono' hf.inv₀ ?_
  filter_upwards [hlower] with ω hω
  have hpos := ha.trans_le hω
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact (inv_le_inv₀ hpos ha).mpr hω

/-- Jensen and the physical J4 estimate bound each genuine annealed lower-right
entry. The frame here is Annealed.sigmaBar; ν remains the molecular parameter. -/
theorem annealed_coarseLowerRight_molecular_lower
    (M : ABKModel 2) (h : ℝ) (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (m n : ℤ) :
    (M.nu + shellVarianceSum h M.gamma m / (2 * M.nu))⁻¹ ≤
      (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n).lowerRight 0 0 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    M.nu + cutoffProjectedEnergy M planarBasis0 m n ω / M.nu
  have hf : Integrable f μ :=
    (integrable_const M.nu).add ((integrable_cutoffProjectedEnergy M planarBasis0 m n).div_const M.nu)
  have hlower : ∀ᵐ ω ∂μ, M.nu ≤ f ω := Eventually.of_forall fun ω => by
    dsimp [f]
    exact le_add_of_nonneg_right (div_nonneg (cutoffProjectedEnergy_nonneg M _ _ _ ω) M.nu_pos.le)
  have havg : (∫ ω, f ω ∂μ) = M.nu + shellVarianceSum h M.gamma m / (2 * M.nu) := by
    rw [integral_add (integrable_const M.nu)
      ((integrable_cutoffProjectedEnergy M planarBasis0 m n).div_const M.nu),
      integral_const, probReal_univ, one_smul, integral_div,
      integral_cutoffProjectedEnergy M h hM planarBasis0_unit m n]
    ring
  have hj := inv_integral_le_integral_inv μ M.nu_pos hf hlower
  rw [havg] at hj
  have hi := Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
    M m (originCube 2 n) (Sum.inr (0 : Fin 2)) (Sum.inr (0 : Fin 2))
  change Integrable (fun a : RegCoeffField 2 =>
    (Homogenization.coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).lowerRight 0 0)
    (Cutoff.coefficientCutoffLaw M m) at hi
  change _ ≤ ∫ a : RegCoeffField 2,
    (Homogenization.coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).lowerRight 0 0
    ∂(Cutoff.coefficientCutoffLaw M m)
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hi ⊢
  rw [integral_map (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable hi.aestronglyMeasurable]
  have hiSample := (integrable_map_measure hi.aestronglyMeasurable
    (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable).mp hi
  exact hj.trans (integral_mono_ae
    (integrable_inv_of_lower_bound M.nu_pos hf.aestronglyMeasurable hlower)
    hiSample (cutoff_coarseLowerRight_molecular_lower M m n))

/-- SC-MOLECULAR-UPPER for the true running diffusivity, unconditionally in B. -/
theorem sigmaBar_le_molecular_upper
    (M : ABKModel 2) (h : ℝ) (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (m : ℤ) :
    (Annealed.sigmaBar M m : ℝ) ≤ M.nu + shellVarianceSum h M.gamma m / (2 * M.nu) := by
  have hlim := (Annealed.sigmaBar_characterization M m).2.1
  have hentry := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim (Sum.inr (0 : Fin 2))))
    (Sum.inr (0 : Fin 2))
  have hentry' : Tendsto
      (fun n : ℕ => (Ch04.annealedBlockMatrixAtScale
        (Cutoff.coefficientCutoffLaw M m) (n : ℤ)).lowerRight 0 0)
      atTop (nhds (Annealed.sigmaBar M m : ℝ)⁻¹) := by
    simpa [toFullBlockMat, Ch02.blockDiag] using hentry
  have hbound := ge_of_tendsto hentry' (Eventually.of_forall fun n : ℕ =>
    annealed_coarseLowerRight_molecular_lower M h hM m (n : ℤ))
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := M.nu_pos.trans_le (nu_le_sigmaBar M m)
  have hBhalf : 0 ≤ ∫ ω, cutoffProjectedEnergy M planarBasis0 m m ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
    integral_nonneg (fun ω => cutoffProjectedEnergy_nonneg M planarBasis0 m m ω)
  rw [integral_cutoffProjectedEnergy M h hM planarBasis0_unit m m] at hBhalf
  have hB : 0 ≤ shellVarianceSum h M.gamma m := by linarith only [hBhalf]
  have hC : 0 < M.nu + shellVarianceSum h M.gamma m / (2 * M.nu) :=
    add_pos_of_pos_of_nonneg M.nu_pos (div_nonneg hB (mul_nonneg (by norm_num) M.nu_pos.le))
  exact (inv_le_inv₀ hC hσ).mp hbound

end ASDExplicitGamma.Scalar
