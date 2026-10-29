module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalPrincipalComparison
public import ASDExplicitGamma.Scalar.UpperCellEnergyOldPrincipalPayment
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalSensitivityPayment
public import ASDExplicitGamma.Scalar.UpperCellEnergyTrial

/-! Integrated principal-energy estimate on the actual physical Hilbert carrier. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Algsuperdiff.Section3
noncomputable section

/-- Positivity of the actual scalar-frame energy on arbitrary Hilbert loads. -/
theorem upper_cell_frame_energy_nonneg
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (X : HilbertBlockL2 (openCubeSet Q)) :
    0 ≤ (scalarFrameRealization Q nu sigma hnu hsigma k).energyBilin X X := by
  obtain ⟨c,hc,hbound⟩ := (scalarFrameRealization Q nu sigma hnu hsigma k).energyCoercive
  exact (by positivity : 0 ≤ c*‖X‖*‖X‖).trans (hbound X)

/-- The actual principal projected mean is integrable and paid by the source
principal expression. The two load premises describe the measurable physical
representative and are supplied by upper_cell_measurable_band_load. -/
theorem upper_cell_physical_principal_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (n : ℤ) (hn : n < N)
    {e : Vec 2} (he : Book.Ch02.vecNorm e = 1)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet (originCube 2 (n-14))))
    (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∃ hω : MemBlockL2 (openCubeSet (originCube 2 (n-14)))
        (bandLoad M n (n+⌊(17/50:ℝ)/M.gamma⌋.toNat) (Annealed.sigmaBar M n:ℝ) e ω),
        F ω = toHilbertBlockL2OfBlockField hω) :
    let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
    let Q := originCube 2 (n-14)
    let sigma := (Annealed.sigmaBar M n:ℝ)
    let k := fun ω => oldCutoffSkewCoefficient (n+height) Q ω
    let S := fun ω => scalarProjectionResidual Q M.nu sigma M.nu_pos (Annealed.sigmaBar M n).property
      (k ω) (upperCellResetMeanField Q (F ω))
    let E := fun ω => (scalarFrameRealization Q M.nu sigma M.nu_pos
      (Annealed.sigmaBar M n).property (k ω)).energyBilin (S ω) (S ω)
    let z := (shellVarianceSum h M.gamma (n+height)-shellVarianceSum h M.gamma n)/(2*sigma^2)
    Integrable E (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, E ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        1+z+safeDepth14EndpointCap/2+upperCellSensitivityProfile M.gamma := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
  let Q := originCube 2 (n-14)
  let sigma := (Annealed.sigmaBar M n:ℝ)
  let k := fun ω => oldCutoffSkewCoefficient (n+height) Q ω
  let S := fun ω => scalarProjectionResidual Q M.nu sigma M.nu_pos (Annealed.sigmaBar M n).property
    (k ω) (upperCellResetMeanField Q (F ω))
  let E := fun ω => (scalarFrameRealization Q M.nu sigma M.nu_pos
    (Annealed.sigmaBar M n).property (k ω)).energyBilin (S ω) (S ω)
  let P := fun ω => (e,upperCellPhysicalPotentialMean M n (n+height) sigma⁻¹ e Q ω)
  let O := fun ω => blockVecDot (P ω) (blockMatVecMul (frameMatrix sigma
    (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun)) (P ω))
  let A := fun ω => 1+2*(lagTraceHistory M n 14 ω).toReal+Real.sqrt (2*(lagTraceHistory M n 14 ω).toReal)
  let D := upperCellPhysicalEnvelope M n height (cubeCenter Q)
  let L := upperCellPhysicalLoadMagnitude M n (n+height) sigma⁻¹ e Q
  let T := fun ω => 6*A ω^2*D ω*(1+2*D ω+4*D ω^2)*L ω^2
  have ho := upper_cell_old_principal_payment M h hM hg N hpast n hn he
  have ht := upper_cell_physical_sensitivity_payment M h hM hg N hpast n hn he
  have hbound : ∀ᵐ ω ∂μ, E ω ≤ O ω+T ω :=
    upper_cell_physical_principal_comparison M n height he F hF
  have hSm : Measurable S := upper_cell_principal_projection_measurable
    (n+height) Q M.nu sigma M.nu_pos (Annealed.sigmaBar M n).property F hFm
  have hEm : Measurable E := upper_cell_random_energy_measurable
    M (n+height) sigma (Annealed.sigmaBar M n).property Q S hSm
  have hE0 (ω) : 0 ≤ E ω := upper_cell_frame_energy_nonneg Q M.nu sigma M.nu_pos
    (Annealed.sigmaBar M n).property (k ω) (S ω)
  have hsum : Integrable (fun ω => O ω+T ω) μ := ho.1.add ht.1
  have hEi : Integrable E μ := hsum.mono' hEm.aestronglyMeasurable
    (hbound.mono (fun ω hh => by rwa [Real.norm_of_nonneg (hE0 ω)]))
  refine ⟨hEi, ?_⟩
  have hh := integral_mono_ae hEi hsum hbound
  rw [integral_add ho.1 ht.1] at hh
  exact hh.trans (add_le_add ho.2 ht.2)

end
end ASDExplicitGamma.Scalar
