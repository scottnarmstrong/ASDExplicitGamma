module

public import ASDExplicitGamma.Inverse.RootMatrixDeviation

/-! Measurability of the complete positive root series, independently of
its moments or any response comparison. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- The actual density excess is measurable with no concentration input. -/
theorem reset_density_excess_measurable (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ)
    (τ η q T : ℝ) (m : ℕ) (hk : ℕ × ℕ) (e : Fin 3) :
    Measurable (resetDensityExcess M Q H0 τ η q T m hk e) := by
  let R := resetDensityDepth H0 hk e
  let B := q3PlanarMarks M (rootFineLabel Q R) τ η
  have hb := root_diameter_average_measurable B
    (q3_local_mark_measurable M _ τ η) (q3_positive_mark_measurable M _ τ η)
    Q R (localizationWhitneyLayer Q (H0+hk.1) hk.2)
    (localization_whitney_layer_measurable Q _ _) (localization_whitney_layer_subset Q _ _) m
  exact (hb.sub_const _).max measurable_const

/-- The literal nonnegative double series (8.7) is measurable before any
finite-energy estimate, without defining it as a difference of norms. -/
theorem positive_root_error_measurable (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow) :
    Measurable (positiveRootError M Q r) := by
  apply Measurable.const_mul
  apply Measurable.tsum
  intro hk
  apply Measurable.const_mul
  have hD : Measurable (fun ω => ∑ e : Fin 3, ENNReal.ofReal
      (resetDensityExcess M Q (rootH0 r) (rootTau r)
        (waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r) 2 hk e ω)) := by
    apply Finset.measurable_sum
    intro e _
    exact (reset_density_excess_measurable M Q (rootH0 r) (rootTau r)
      (waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r) 2 hk e).ennreal_ofReal
  exact (root_matrix_positive_error_measurable M Q r hk).ennreal_ofReal.add
    (hD.const_mul _)

end
end ASDExplicitGamma.Inverse
