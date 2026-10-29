module

public import ASDExplicitGamma.Main.Q3DiagResidualLocal

/-! Literal coordinates of the actual covariance receiver residual. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
open scoped BigOperators

local instance mainQ3ResidualCoordinatesFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- One actual Gaussian coordinate of the source receiver residual. -/
noncomputable def mainQ3ResidualCoordinate {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (j : ℕ)
    (φ : H1Function (openCubeSet Q)) (U : TriadicCube 2) (l : ι) (x : Vec 2) (i : Fin 2) : ℝ :=
  (q3Convolution b L h3Zero (e l) x-cubeAverage U (q3Convolution b L h3Zero (e l)))*
    (diagInterpolant Q j φ).grad x i-
    (φ-diagInterpolant Q j φ).toFun x*
      (fderiv ℝ (q3Convolution b L h3Zero (e l)) x) (basisVec i)

/-- The finite Hilbert mean's coordinates are exactly the actual scalar cell means. -/
theorem mainQ3FiniteValue_average_coordinate {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (U : TriadicCube 2) (l : s) :
    (hilbertCubeAverage U (mainQ3FiniteValue e s b L)).ofLp l =
      cubeAverage U (q3Convolution b L h3Zero (e l)) := by
  let pr : EuclideanSpace ℝ s →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) l
  have hm : MemLp (mainQ3FiniteValue e s b L) 2 (normalizedCubeMeasure U) :=
    (main_continuous_memLp_top U (mainQ3FiniteValue_contDiff e s b L).continuous).mono_exponent
      (by simp : (2:ENNReal) ≤ ⊤)
  have h := hilbertCubeAverage_map U pr hm
  change hilbertCubeAverage U (q3Convolution b L h3Zero (e l)) =
    (hilbertCubeAverage U (mainQ3FiniteValue e s b L)).ofLp l at h
  rw [hilbertCubeAverage_real] at h
  exact h.symm

/-- Exact coordinates, retaining the physical centering and the residual sign. -/
theorem mainQ3DiagResidualColumn_coordinate {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (j : ℕ)
    (φ : H1Function (openCubeSet Q)) (U : TriadicCube 2) (l : s) (x : Vec 2) (i : Fin 2) :
    (mainQ3DiagResidualColumn e s b L Q j φ U x).ofLp (l,i) =
      mainQ3ResidualCoordinate e b L Q j φ U l x i := by
  simp only [mainQ3DiagResidualColumn, mainEuclideanTensor, PiLp.add_apply,
    PiLp.smul_apply, PiLp.sub_apply, mainQ3FiniteValue, mainQ3FiniteColumn,
    mainQ3FiniteValue_average_coordinate, smul_eq_mul, mainQ3ResidualCoordinate]
  ring

/-- Each actual receiver residual coordinate is genuinely L2 on its tile. -/
theorem main_q3_residual_coordinate_memLp {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (j : ℕ)
    (φ : H1Function (openCubeSet Q)) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q j)
    (l : ι) (i : Fin 2) :
    MemLp (fun x => mainQ3ResidualCoordinate e b L Q j φ U l x i) 2 (normalizedCubeMeasure U) := by
  have hg := memLp_on_descendant_of_memLp hU ((diagInterpolant Q j φ).grad_memL2_normalizedCubeMeasure i)
  have hz := memLp_on_descendant_of_memLp hU (φ-diagInterpolant Q j φ).memL2_normalizedCubeMeasure
  have hv := main_q3_direction_memLp_top (normalizedCubeMeasure U) b L h3Zero (e l)
  have hd : MemLp (fun x => (fderiv ℝ (q3Convolution b L h3Zero (e l)) x) (basisVec i))
      ⊤ (normalizedCubeMeasure U) := by
    simp_rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
    exact main_q3_direction_memLp_top _ b L _ (e l)
  exact ((hv.sub (memLp_const _)).mul hg).sub (hz.mul hd)

/-- The actual finite Hilbert residual energy is its full scalar coordinate sum. -/
theorem main_q3_residual_energy_coordinates {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (j : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q j) :
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    hilbertPrimalEnergy U (Real.sqrt 3) (mainQ3DiagResidualColumn e s b L Q j φ U) =
      ∑ l ∈ s, ∑ i : Fin 2, primalEnergy U (Real.sqrt 3)
        (fun x => mainQ3ResidualCoordinate e b L Q j φ U l x i) := by
  intro φ
  have hm : MemLp (mainQ3DiagResidualColumn e s b L Q j φ U) 2 (normalizedCubeMeasure U) := by
    apply memLp_piLp_iff.mpr
    rintro ⟨l,i⟩
    simpa only [mainQ3DiagResidualColumn_coordinate] using
      main_q3_residual_coordinate_memLp e b L Q j φ U hU l i
  have hp := (main_q3_diag_residual_local e s b L Q j p u U hU).1
  rw [main_hilbertPrimalEnergy_euclidean U hm hp, Fintype.sum_prod_type]
  simp_rw [mainQ3DiagResidualColumn_coordinate]
  exact Finset.sum_coe_sort s (fun l => ∑ i : Fin 2, primalEnergy U (Real.sqrt 3)
    (fun x => mainQ3ResidualCoordinate e b L Q j φ U l x i))

end ASDExplicitGamma.Main
