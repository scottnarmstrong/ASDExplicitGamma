module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPotentialGaussian
public import ASDExplicitGamma.Scalar.UpperCellEnergyBandSobolevTensor
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetBandProjection
public import ASDExplicitGamma.Scalar.Lambda8CovarianceAdapter

/-! The physical band forcing lies in the actual scalar band's closed Gaussian
orbit. The identification is on the original cutoff carrier. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
noncomputable section

/-- Pointwise scalar-coordinate formula for the literal finite-band forcing. -/
theorem upper_cell_band_forcing_point
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (i : Fin 2) :
    (valuePathForcing (c • e) (shellSumValuePath n (n+height) ω.val)).ofLp i =
      matVecMul Response.responsePlanarJ e i *
        upperCellBandJet (upperCellPhysicalBandLabel n height)
          (fun _ => c) (.value 0) ω := by
  change matVecMul (shellSumValuePath n (n+height) ω.val 0) (c • e) i = _
  rw [shellSumValuePath_apply,matVecMul_finiteShellIncrement_apply]
  have hp (k : ℤ) : shellRowForcing (c • e) 0 i k ω.val =
      matVecMul Response.responsePlanarJ e i * (c*shellDerivativeEval (.value 0) (ω.val k)) := by
    change matVecMul (ω.val k 0) (c • e) i = _
    rw [lambda8Q3ShellMatVec_eq_scalarJ]
    change (ω.val k 0 1 0) * matVecMul Response.responsePlanarJ (c • e) i =
      matVecMul Response.responsePlanarJ e i * (c * (ω.val k 0 1 0))
    simp only [matVecMul,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul]
    ring
  simp_rw [hp]
  rw [←Finset.mul_sum]
  congr 1
  exact (upper_cell_physical_band_sum' n height
    (fun k => c*shellDerivativeEval (.value 0) (ω.val k))).symm

/-- Exact stationary L2 coordinates of the physical forcing, before projection. -/
theorem upper_cell_band_forcing_coord
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (i : Fin 2) :
    vectorL2Coord i (upperCellResetBandForcing M n (n+height) c e) =
      matVecMul Response.responsePlanarJ e i •
        upperCellResetBandJetClass M (upperCellPhysicalBandLabel n height)
          (fun _ => c) (upper_cell_band_jets_gaussian M h hM _
            (upper_cell_physical_band_label_injective n height) _) (.value 0) := by
  let F := upperCellResetBandForcing M n (n+height) c e
  let v := upperCellResetBandJetClass M (upperCellPhysicalBandLabel n height)
    (fun _ => c) (upper_cell_band_jets_gaussian M h hM _
      (upper_cell_physical_band_label_injective n height) _) (.value 0)
  let hp := measurePreserving_shellSumValuePath_cutoffSample M n (n+height)
  have hc := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).coeFn_compLpL F
  have ht := coeFn_carrierTransport hp (shellSumForcingL2 M (c • e) n (n+height))
  have hf := hp.quasiMeasurePreserving.ae
    (memLp_two_valuePathForcing_shellSum M (c • e) n (n+height)).coeFn_toLp
  have hv := (upper_cell_reset_band_jet_memLp M (upperCellPhysicalBandLabel n height)
    (fun _ => c) (upper_cell_band_jets_gaussian M h hM _
      (upper_cell_physical_band_label_injective n height) _) (.value 0)).coeFn_toLp
  have hs := Lp.coeFn_smul (matVecMul Response.responsePlanarJ e i) v
  apply Lp.ext
  filter_upwards [hc,ht,hf,hv,hs] with ω hc ht hf hv hs
  change vectorL2Coord i F ω = (F ω).ofLp i at hc
  change F ω = shellSumForcingL2 M (c • e) n (n+height)
    (shellSumValuePath n (n+height) ω.val) at ht
  change shellSumForcingL2 M (c • e) n (n+height)
    (shellSumValuePath n (n+height) ω.val) = _ at hf
  change v ω = upperCellBandJet (upperCellPhysicalBandLabel n height)
    (fun _ => c) (.value 0) ω at hv
  change vectorL2Coord i F ω = (matVecMul Response.responsePlanarJ e i • v) ω
  rw [hc,ht,hf,hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hv]
  exact upper_cell_band_forcing_point n height c e ω i

end
end ASDExplicitGamma.Scalar
