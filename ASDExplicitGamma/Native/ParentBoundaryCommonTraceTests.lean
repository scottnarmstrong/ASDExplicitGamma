module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeHeat
public import ASDExplicitGamma.Native.ParentBoundaryCommonGaussianMap
public import ASDExplicitGamma.Native.ParentBoundaryCommonTraceGenerator
public import ASDExplicitGamma.Gaussian.PolynomialTests
public import ASDExplicitGamma.Gaussian.ModelHeatPower

/-! Actual trace regularity, power trace and integrability on common-centered descendants. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

local instance parentCommonTraceTestMeasurable (Q : TriadicCube 2) :
    MeasurableSpace (ResponseCoefficient (openCubeSet Q)) := borel _
local instance parentCommonTraceTestBorel (Q : TriadicCube 2) :
    BorelSpace (ResponseCoefficient (openCubeSet Q)) := ⟨rfl⟩

/-- The actual translated-square trace has the full Gaussian-test C2 bounds. -/
theorem parent_boundary_common_square_trace_polynomial
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) :
    HasPolynomiallyBoundedC2Derivatives (squareTrace Q ν σ) := by
  let E := squareLoadEnergy Q ν σ hν hσ
  have hE (p : Fin 2 × Bool) : HasPolynomiallyBoundedC2Derivatives (E p) :=
    responseFrameEnergyObservable_hasPolynomiallyBoundedC2Derivatives _ _ ν σ hν hσ _
  have heq : squareTrace Q ν σ = fun z => (∑ p : Fin 2 × Bool,E p z)-4 := by
    funext z
    exact squareTrace_eq_load_sum Q ν σ hν hσ z
  rw [heq]
  exact hasPolynomiallyBoundedC2Derivatives_sub_const
    (c2_polynomial_sum Finset.univ E (fun p _ => hE p)) 4

/-- Nonnegativity belongs to the actual physical trace, including zeros. -/
theorem parent_boundary_common_square_trace_nonneg
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) : 0 ≤ squareTrace Q ν σ k :=
  traceDefect_nonneg_of_ellipticFieldOn_triCube (div_pos hν hσ)
    (lemmaV_frameCoefficient_isEllipticOn (measurableSet_cubeSet Q) ν σ hν hσ k) (by norm_num)

/-- Exact p20 power trace for the actual physical common-center response
family, identified through its genuine enclosing Gaussian Hilbert factor. -/
theorem parent_boundary_common_response_power_identity
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l})
    (x : ResponseCoefficient (openCubeSet Q)) :
    let Φ := squareTrace Q ν σ
    let H := parentBoundaryCommonResponseDirections P Q b L
    (1/2:ℝ)*modelCovarianceTrace (fun y => Φ y^(20:ℝ)) H x=modelPowerHeatGenerator Φ H 20 x := by
  intro Φ H
  obtain ⟨ell,hP⟩ := exists_originCube_containing_compact (closure (cubeSet P))
    (isBounded_cubeSet P).isCompact_closure
  obtain ⟨T,hT⟩ := parent_boundary_common_gaussian_factor hQ ell hP b L
  have heq : (fun j => T (mainCubeQ3Directions ell b L j))=H := funext hT
  rw [←heq]
  exact @modelCovarianceTrace_rpow (MainCubeH3 ell b L) (ResponseCoefficient (openCubeSet Q))
    inferInstance (mainCubeH3InnerProductSpace ell b L) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (mainCubeQ3Directions ell b L) (mainCubeQ3Directions_summable ell b L) T Φ
    (parent_boundary_common_square_trace_polynomial Q ν σ hν hσ)
    (parent_boundary_common_square_trace_nonneg Q ν σ hν hσ) 20 (by norm_num) x

/-- The actual common-center p20 generator is Bochner integrable on the
original cutoff sample law, before any quantitative generator estimate. -/
theorem parent_boundary_common_cube_power_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) (t b : ℝ) (L : {l : ℝ // 0 < l}) :
    Integrable (fun ω => modelPowerHeatGenerator (squareTrace Q M.nu (Annealed.sigmaBar M n))
      (parentBoundaryCommonResponseDirections P Q b L) 20
      (parentBoundaryCommonCubeObserved hQ n height t ω)) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let σ : ℝ := Annealed.sigmaBar M n
  let Φ := squareTrace Q M.nu σ
  let H := parentBoundaryCommonResponseDirections P Q b L
  have hσ := (Annealed.sigmaBar_characterization M n).1
  have hΦ := parent_boundary_common_square_trace_polynomial Q M.nu σ M.nu_pos hσ
  have hΦ0 := parent_boundary_common_square_trace_nonneg Q M.nu σ M.nu_pos hσ
  have hp := hasPolynomiallyBoundedC2Derivatives_rpow hΦ hΦ0 (by norm_num : (2:ℝ) ≤ 20)
  have hH := parent_boundary_common_response_directions_summable P Q b L
  have hm := measurable_modelCovarianceTrace (fun x => Φ x^(20:ℝ)) hp.1 H
  have hg := polynomial_modelCovarianceTrace H hH (fun x => Φ x^(20:ℝ)) hp
  have hi := (parent_boundary_common_cube_test_memLp M h hM hQ n height hheight _ hm hg t 2
    (by norm_num)).integrable (by norm_num : (1:ℝ≥0∞) ≤ ENNReal.ofReal (2:ℝ))
  have he : (fun ω => modelPowerHeatGenerator Φ H 20 (parentBoundaryCommonCubeObserved hQ n height t ω)) =
      fun ω => (1/2:ℝ)*modelCovarianceTrace (fun x => Φ x^(20:ℝ)) H
        (parentBoundaryCommonCubeObserved hQ n height t ω) := by
    funext ω
    exact (parent_boundary_common_response_power_identity hQ M.nu σ b M.nu_pos hσ L _).symm
  rw [he]
  exact hi.const_mul _

end
end ASDExplicitGamma.Native
