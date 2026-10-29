module

public import ASDExplicitGamma.Triadic.SensitivityODEPath
public import Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CrudeBound

/-! A fixed microscopic ellipticity witness gives a uniform path bound. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response
open Homogenization.Book.Ch02 Homogenization.Book.Ch04

noncomputable section

/-- The path coefficient on an arbitrary cube, with the actual source lower
ellipticity constant retained as the Chapter 2 witness. -/
def sensitivityFixedPathCoeffOn {Q : TriadicCube 2} (R : TriadicCube 2)
    (ν : ℝ) (hν : 0 < ν) (k : ResponseCoefficient (openCubeSet Q)) :
    Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R) := by
  let a := sensitivityBaseRegField (Q₀ := Q) ν k
  have hEll' : IsEllipticFieldOn ν ((ν ^ 2 + ‖k‖ ^ 2) / ν)
      (openCubeSet R) a.toFun := by
    refine ⟨?_, ?_⟩
    · apply measurable_pi_iff.2
      intro i
      apply measurable_pi_iff.2
      intro j
      exact Measurable.ite (measurableSet_openCubeSet R)
        (a.entry_measurable i j) measurable_const
    · intro x hx
      have hkx : |responseCoefficientExtension k x| ≤ ‖k‖ := by
        calc
          |responseCoefficientExtension k x| =
              ‖responseCoefficientExtension k x‖ := by simp
          _ ≤ ‖responseCoefficientExtension k‖ :=
            (responseCoefficientExtension k).norm_coe_le_norm x
          _ = ‖k‖ := responseCoefficientExtension_norm k
      have hpoint := responsePlanarCoefficient_isElliptic ν ‖k‖
        (responseCoefficientExtension k x) hν hkx
      simpa [a, sensitivityBaseRegField, responseFramePlanarCoefficientField,
        responsePlanarCoefficientField, div_one] using hpoint
  refine ⟨a.toFun, ν, (ν ^ 2 + ‖k‖ ^ 2) / ν, hν, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hν).mpr
    nlinarith [sq_nonneg ‖k‖]
  · intro i j
    have h := ((measurable_pi_iff.mp (measurable_pi_iff.mp hEll'.1 i)) j)
    apply (h.aestronglyMeasurable (μ := volumeMeasureOn (openCubeSet R))).congr
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ openCubeSet R <;>
        simp [Book.Ch02.cubeDomain_coe, restrictCoeffField, hx]
  · filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact hEll'.2 x hx

/-- The path family whose local coefficient objects all record lower
ellipticity exactly `ν`. -/
def sensitivityFixedPathFamily {Q : TriadicCube 2} (ν : ℝ) (hν : 0 < ν)
    (k kH : ResponseCoefficient (openCubeSet Q)) (t : ℝ) :
    TriadicCoeffFamily 2 where
  coeffOn R := sensitivityFixedPathCoeffOn R ν hν
    (sensitivityResponseCoefficientPath k kH t)
  restrictsTo_of_subset := by
    intro R S hRS
    exact Filter.EventuallyEq.rfl

@[simp] theorem sensitivityFixedPathFamily_lam {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (t : ℝ) (R : TriadicCube 2) :
    ((sensitivityFixedPathFamily ν hν k kH t).coeffOn R).lam = ν := rfl

/-- The fixed-witness family and the canonical path family have the same
finite multiscale history. -/
theorem sensitivityFixedPathFamily_lambdaSqFinite_eq {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (u t : ℝ) :
    Book.Ch02.lambdaSqFinite Q u 2
        (sensitivityFixedPathFamily ν hν k kH t) =
      Book.Ch02.lambdaSqFinite Q u 2
        (sensitivityPathFamily ν hν k kH t) := by
  apply sensitivity_lambdaSqFinite_eq_of_descendant_aeeq
  intro j R hR
  change Book.Ch02.CoeffOn.AEEq
    (sensitivityFixedPathCoeffOn R ν hν
      (sensitivityResponseCoefficientPath k kH t))
    ((sensitivityPathFamily ν hν k kH t).coeffOn R)
  change responseFramePlanarCoefficientField ν 1
      (sensitivityResponseCoefficientPath k kH t) =ᵐ[
        volumeMeasureOn (openCubeSet R)]
    responseFramePlanarCoefficientField ν 1
      (sensitivityResponseCoefficientPath k kH t)
  exact Filter.EventuallyEq.rfl

/-- Every finite inverse-lambda along the path is bounded by the deterministic
two-dimensional ellipticity estimate. -/
theorem sensitivityPath_lambdaSqFinite_inv_le_uniform {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    {u : ℝ} (hu : 0 < u) (t : ℝ) :
    (Book.Ch02.lambdaSqFinite Q u 2
      (sensitivityPathFamily ν hν k kH t))⁻¹ ≤ 8 * ν⁻¹ := by
  let F := sensitivityFixedPathFamily ν hν k kH t
  have hmax : ∀ n : ℕ,
      Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) F ≤ 8 * ν⁻¹ := by
    intro n
    have h := Algsuperdiff.Section24.Sensitivity.Provider.Lambda.maxDescendantSigmaStarInvMatrixNormAtScale_le_uniform Q F n
    have h' : Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) F ≤ 4 * 2 * ν⁻¹ := by
      simpa [F, sensitivityFixedPathFamily_lam] using h
    nlinarith [h']
  have hF := Algsuperdiff.Section24.Sensitivity.Provider.Lambda.lambdaSqFinite_inv_le_of_uniform_maxDescendant
      Q F (s := u) (q := 2) (M := 8 * ν⁻¹) hu
      (by norm_num : (1 : ℝ) ≤ 2) (by positivity) hmax
  have hF' : (Book.Ch02.lambdaSqFinite Q u 2 F)⁻¹ ≤ 8 * ν⁻¹ := by
    simpa [Book.Ch02.lambdaSqFinite] using hF
  rw [← sensitivityFixedPathFamily_lambdaSqFinite_eq ν hν k kH u t]
  exact hF'

end

end ASDExplicitGamma.Triadic
