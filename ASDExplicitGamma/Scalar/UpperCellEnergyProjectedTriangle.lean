module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalPrincipalPayment
public import ASDExplicitGamma.Scalar.UpperCellEnergyIntegratedCross
public import ASDExplicitGamma.Scalar.UpperCellEnergyProjection

/-! Integration of the actual terminal-coefficient projection split. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Algsuperdiff.Section3
noncomputable section

/-- Actual energy of the projected Hilbert load at a terminal cutoff. -/
def upperCellProjectedEnergy (M : ABKModel 2) (terminal : ℤ) (Q : TriadicCube 2)
    (sigma : ℝ) (hsigma : 0<sigma)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q))
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  let k := oldCutoffSkewCoefficient terminal Q ω
  let Z := scalarProjectionResidual Q M.nu sigma M.nu_pos hsigma k (F ω)
  (scalarFrameRealization Q M.nu sigma M.nu_pos hsigma k).energyBilin Z Z

theorem upper_cell_projected_energy_measurable
    (M : ABKModel 2) (terminal : ℤ) (Q : TriadicCube 2) (sigma : ℝ) (hsigma : 0<sigma)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q)) (hF : Measurable F) :
    Measurable (upperCellProjectedEnergy M terminal Q sigma hsigma F) :=
  upper_cell_random_energy_measurable M terminal sigma hsigma Q _
    (upper_cell_random_projection_measurable terminal Q M.nu sigma M.nu_pos hsigma F hF)

theorem upper_cell_projected_energy_nonneg
    (M : ABKModel 2) (terminal : ℤ) (Q : TriadicCube 2) (sigma : ℝ) (hsigma : 0<sigma)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q)) (ω : Cutoff.CutoffSample 2) :
    0 ≤ upperCellProjectedEnergy M terminal Q sigma hsigma F ω :=
  upper_cell_frame_energy_nonneg Q M.nu sigma M.nu_pos hsigma _ _

/-- The genuine random weighted projection obeys the integrated triangle.
The component integrability inputs are supplied by the principal and RESET
payments; no cross-term estimate or independence premise is needed. -/
theorem upper_cell_projected_energy_triangle
    (M : ABKModel 2) (terminal : ℤ) (Q : TriadicCube 2) (sigma : ℝ) (hsigma : 0<sigma)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q)) (hF : Measurable F)
    (hP : Integrable (upperCellProjectedEnergy M terminal Q sigma hsigma
      (fun ω => upperCellResetMeanField Q (F ω))) (Cutoff.cutoffSampleLaw M).toMeasure)
    (hR : Integrable (upperCellProjectedEnergy M terminal Q sigma hsigma
      (fun ω => F ω-upperCellResetMeanField Q (F ω))) (Cutoff.cutoffSampleLaw M).toMeasure) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let T := upperCellProjectedEnergy M terminal Q sigma hsigma F
    let E := upperCellProjectedEnergy M terminal Q sigma hsigma
      (fun ω => upperCellResetMeanField Q (F ω))
    let R := upperCellProjectedEnergy M terminal Q sigma hsigma
      (fun ω => F ω-upperCellResetMeanField Q (F ω))
    Integrable T μ ∧ (∫ ω,T ω ∂μ) ≤
      (∫ ω,E ω ∂μ)+2*Real.sqrt ((∫ ω,E ω ∂μ)*(∫ ω,R ω ∂μ))+(∫ ω,R ω ∂μ) := by
  apply upper_cell_integrated_triangle
    (Cutoff.cutoffSampleLaw M).toMeasure _ _ _
    (upper_cell_projected_energy_measurable M terminal Q sigma hsigma F hF).aestronglyMeasurable
    hP hR
    (upper_cell_projected_energy_nonneg M terminal Q sigma hsigma F)
    (upper_cell_projected_energy_nonneg M terminal Q sigma hsigma _)
    (upper_cell_projected_energy_nonneg M terminal Q sigma hsigma _)
  exact Filter.Eventually.of_forall (fun ω => upper_cell_projection_energy_le
    Q M.nu sigma M.nu_pos hsigma (oldCutoffSkewCoefficient terminal Q ω)
    (F ω) (upperCellResetMeanField Q (F ω)))

end
end ASDExplicitGamma.Scalar
