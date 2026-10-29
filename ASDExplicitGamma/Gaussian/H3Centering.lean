module

public import ASDExplicitGamma.Gaussian.H3Constant
public import ASDExplicitGamma.Gaussian.Q3H3Range
public import ASDExplicitGamma.Gaussian.GaussCentering

/-! # Literal remainder centering in ordinary H³ and in the full C¹ first jet -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- Center only the value component; genuine spatial derivatives stay unchanged. -/
noncomputable def c1CenteringMap {K : Set (Vec 2)} [CompactSpace K] (x₀ : K) :
    C1Jet K →L[ℝ] C1Jet K :=
  ContinuousLinearMap.pi fun i => if i = 0 then
    (centeringMap x₀).comp (ContinuousLinearMap.proj 0) else ContinuousLinearMap.proj i

theorem c1CenteringMap_value {K : Set (Vec 2)} [CompactSpace K] (x₀ : K)
    (j : C1Jet K) (x : K) : c1CenteringMap x₀ j 0 x = j 0 x - j 0 x₀ := by
  simp only [c1CenteringMap, ContinuousLinearMap.pi_apply, ↓reduceIte,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, centeringMap_apply]

/-- Evaluation of the actual continuous representative is bounded on the ordinary H³ range. -/
noncomputable def q3H3RangeEvaluation (a b c d β : ℝ) (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle a b c d) : Q3H3Range a b c d β L →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x₀).comp
    ((ContinuousLinearMap.proj 0).comp (q3H3RangeC1 a b c d β L))

/-- This is literal point subtraction in ordinary weak H³, using only the fresh field. -/
noncomputable def q3H3RemainderMap (a b c d β : ℝ) (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle a b c d) :
    Q3H3Range a b c d β L →L[ℝ] h3Space (openRectangle a b c d) :=
  (hilbertRange (q3SobolevOperator (openRectangle a b c d) β L)).subtypeL -
    (h3Constant (openRectangle a b c d)).comp (q3H3RangeEvaluation a b c d β L x₀)

/-- The remainder first jet is obtained from the same fresh-field Hilbert realization. -/
noncomputable def q3C1RemainderMap (a b c d β : ℝ) (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle a b c d) :
    Q3H3Range a b c d β L →L[ℝ] C1Jet (closedRectangle a b c d) :=
  (c1CenteringMap x₀).comp (q3H3RangeC1 a b c d β L)

/-- A bounded image of a Hilbert–Schmidt family is square summable. -/
theorem summable_sq_bounded_image {ι V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ι → V) (hv : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) :
    Summable (fun j => ‖T (v j)‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hv.mul_left (‖T‖ ^ 2))
  intro j
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (v j)) 2

end ASDExplicitGamma.Gaussian
