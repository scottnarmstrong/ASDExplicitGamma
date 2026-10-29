module

public import ASDExplicitGamma.Scalar.DefectCoupling
public import ASDExplicitGamma.Gaussian.Q3ModelH3Realization
public import ASDExplicitGamma.Gaussian.ModelHeatLaw

/-! Gaussian coordinates for the actual fresh shell of the cutoff model. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian Homogenization
  Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal

/-- The q3 series value on the source rectangle, as a map of the Gaussian coordinates. -/
noncomputable def shellSeries (a b c d : ℝ) (M : ABKModel 2) (h : ℝ) (k : ℤ)
    (z : ℕ → ℝ) : C(closedRectangle a b c d, ℝ) :=
  q3C1Series a b c d (q3ModelAmplitude M h k) (q3ModelLength k) whiteBasis z 0

theorem shell_coupling (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (ell m : ℤ)
    (hK : closedRectangle a b c d ⊆ openCubeSet (originCube 2 ell)) :
    ∃ μ' : Measure (Cutoff.CutoffSample 2 × (ℕ → ℝ)), IsProbabilityMeasure μ' ∧
      μ'.map Prod.fst = (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∀ᵐ p ∂μ', shellSeries a b c d M h (m + 1) p.2 =
        shellFieldScalarRestriction (closedRectangle a b c d) (p.1.1 (m + 1))) ∧
      μ'.map (fun p => (olderField (closedRectangle a b c d) m p.1, p.2)) =
        ((Cutoff.cutoffSampleLaw M).toMeasure.map
          (olderField (closedRectangle a b c d) m)).prod standardGaussianInfinitePi := by
  have hlaw := actualShellLaw_eq_h3Series a b c d hab hcd M h hM (m + 1)
  have hZ : Measurable (shellSeries a b c d M h (m + 1)) :=
    ((measurable_pi_apply (0 : Fin 3)).comp
      (stronglyMeasurable_q3C1Series a b c d _ _ whiteBasis).measurable)
  have hf : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction (closedRectangle a b c d) (ω.1 (m + 1))) :=
    (measurable_shellFieldScalarRestriction _).comp
      ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  exact coordinate_extension (Cutoff.cutoffSampleLaw M).toMeasure
    (olderField (closedRectangle a b c d) m)
    (fun ω => shellFieldScalarRestriction (closedRectangle a b c d) (ω.1 (m + 1)))
    (measurable_olderField _ ell m hK) hf
    (indepFun_olderField_freshShell _ M ell m hK) (shellSeries a b c d M h (m + 1)) hZ
    hlaw.symm

end ASDExplicitGamma.Scalar
