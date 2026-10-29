module

public import ASDExplicitGamma.Main.Q3ResidualProduct
public import ASDExplicitGamma.Triadic.DiagEstimates

/-! Actual centered covariance residual on each affine-data DIAG cell. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
open scoped BigOperators

local instance mainQ3DiagResidualFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Literal residual columns, defined on every cell without a restriction fallback. -/
noncomputable def mainQ3DiagResidualColumn {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (j : ℕ)
    (φ : H1Function (openCubeSet Q)) (U : TriadicCube 2) (x : Vec 2) : EuclideanSpace ℝ (s × Fin 2) :=
  mainEuclideanTensor
    (mainQ3FiniteValue e s b L x-hilbertCubeAverage U (mainQ3FiniteValue e s b L))
      (WithLp.toLp 2 ((diagInterpolant Q j φ).grad x))+
    (-(φ-diagInterpolant Q j φ).toFun x) • mainQ3FiniteColumn e s b L x

/-- The actual affine-data residual has genuine cellwise positive membership
and the three-term local product bound used by the broken-norm aggregation. -/
theorem main_q3_diag_residual_local {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (j : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q j) :
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy U
      (hilbertCubeIncrement U (k+1) (mainQ3DiagResidualColumn e s b L Q j φ U))) ∧
    hilbertPositiveHaarNorm U (Real.sqrt 3) (mainQ3DiagResidualColumn e s b L Q j φ U) ≤
      (diagMeshRadius Q j*(1/Real.sqrt 3+planarC1)*Real.sqrt ((156/5)*b^2/L.1^2))*
        vectorPositiveHaarNorm U (I φ).grad+
      Real.sqrt ((156/5)*b^2/L.1^2)*positiveHaarNorm U (φ-I φ).toFun+
      diagMeshRadius Q j*planarC1*Real.sqrt ((46488/25)*b^2/L.1^4)*
        Real.sqrt (energy U (φ-I φ).toFun) := by
  intro φ I
  let rU := (φ-I φ).restrictToOpenSubcube hU
  let F := fun x => WithLp.toLp 2 ((I φ).grad x)
  have hF (i : Fin 2) : MemLp (fun x => (I φ).grad x i) 2 (normalizedCubeMeasure U) :=
    memLp_on_descendant_of_memLp hU ((I φ).grad_memL2_normalizedCubeMeasure i)
  have hP (i : Fin 2) := diagInterpolant_gradient_summable Q j p u U hU i
  have hm : MemLp F 2 (normalizedCubeMeasure U) := memLp_piLp_iff.mpr hF
  have hp := main_hilbert_summable_of_coordinates U hm hP
  have h := main_q3_residual_product e s b L U hm hp rU
  have he : mainQ3ResidualColumn e s b L U F rU = mainQ3DiagResidualColumn e s b L Q j φ U := rfl
  rw [he, main_hilbertPositive_eq_vectorPositive U hF hP] at h
  simpa only [rU, H1Function.restrictToOpenSubcube_toFun, cubeScaleFactor_descendant_eq_div_pow hU,
    diagMeshRadius] using h

end ASDExplicitGamma.Main
