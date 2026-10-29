module

public import ASDExplicitGamma.Model.SpectralProjectionTransport
public import Algsuperdiff.Section3.Disorder.Cstar

@[expose] public section

open MeasureTheory Homogenization

namespace ASDExplicitGamma.Model

/-- The literal J4 corrector energy in the first coordinate direction. The
source-sign corrector is the negative potential projection, with the same norm. -/
theorem q3J4_origin_energy
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector
      M.P
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
        M.P M.J1.stationary)
      planarBasis0
      (Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
        M.P M.J2.gaussian_tail planarBasis0 planarBasis0_unit)‖ ^ 2 = h ^ 2 / 2 := by
  change ‖-Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
    (μ := planarRegLaw M) (d := 2) (q3OriginForcingL2 M)‖ ^ 2 = _
  rw [norm_neg]
  exact q3OriginPotentialProjection_energy M h hM

/-- The q3 model's canonical J4 constant, with the source's exact normalization. -/
theorem q3_cstar_exact
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    Algsuperdiff.Section3.Disorder.cstar M = h ^ 2 / (2 * Real.log 3) := by
  have hc := (Algsuperdiff.Section3.Disorder.cstar_characterization M).2.1
    ⟨planarBasis0, planarBasis0_unit⟩
  rw [q3J4_origin_energy M h hM] at hc
  have hl : Real.log (3 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  apply (eq_div_iff (mul_ne_zero (by norm_num) hl)).mpr
  nlinarith only [hc]

/-- The exact energy identity on every unit direction in the frozen J4 carrier. -/
theorem q3J4_directional_energy
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    (e : {e : Vec 2 // Homogenization.Book.Ch02.vecNorm e = 1}) :
    ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector
      M.P
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
        M.P M.J1.stationary)
      e.1
      (Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
        M.P M.J2.gaussian_tail e.1 e.2)‖ ^ 2 = h ^ 2 / 2 := by
  rw [(Algsuperdiff.Section3.Disorder.cstar_characterization M).2.1 e, q3_cstar_exact M h hM]
  have hl : Real.log (3 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hl]

end ASDExplicitGamma.Model
