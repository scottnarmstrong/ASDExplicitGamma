module

public import ASDExplicitGamma.Scalar.CutoffMeasurability

/-! Joint measurability of the actual weighted projection in both the cutoff
sample and the cell load. Fixed-load measurability alone does not suffice for
UPPER's correlated band load. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The terminal-coefficient projection is jointly measurable in sample and
load, so a correlated measurable load may be inserted without independence. -/
theorem upper_cell_projection_joint_measurable
    (N : ℤ) (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma) :
    Measurable (fun p : Cutoff.CutoffSample 2 × HilbertBlockL2 (openCubeSet Q) =>
      scalarProjectionResidual Q nu sigma hnu hsigma (oldCutoffSkewCoefficient N Q p.1) p.2) := by
  let finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let : IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance
  let : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  let : SecondCountableTopology (HilbertBlockL2 (openCubeSet Q)) := inferInstance
  have hc (ω : Cutoff.CutoffSample 2) : Continuous (fun F : HilbertBlockL2 (openCubeSet Q) =>
      scalarProjectionResidual Q nu sigma hnu hsigma (oldCutoffSkewCoefficient N Q ω) F) := by
    simp only [scalarProjectionResidual_eq_affineMinimizer]
    exact ContinuousLinearMap.continuous _
  have hm := measurable_uncurry_of_continuous_of_measurable hc
    (fun F => measurable_oldCutoff_scalarProjectionResidual N Q nu sigma hnu hsigma F)
  exact hm.comp (f := Prod.swap) measurable_swap

/-- The actual projection of a measurable random load is measurable, even
when the load and coefficient are correlated. -/
theorem upper_cell_random_projection_measurable
    (N : ℤ) (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q)) (hF : Measurable F) :
    Measurable (fun ω => scalarProjectionResidual Q nu sigma hnu hsigma
      (oldCutoffSkewCoefficient N Q ω) (F ω)) :=
  (upper_cell_projection_joint_measurable N Q nu sigma hnu hsigma).comp
    (f := fun ω => (ω, F ω)) (measurable_id.prodMk hF)

end
end ASDExplicitGamma.Scalar
