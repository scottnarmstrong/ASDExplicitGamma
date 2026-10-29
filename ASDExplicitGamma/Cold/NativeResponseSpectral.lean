module

public import ASDExplicitGamma.Cold.NativeFourColor
public import ASDExplicitGamma.Cold.CoarseGramQuadratic
public import ASDExplicitGamma.Cold.FiniteSpectralPair
public import ASDExplicitGamma.Cold.MatrixFrobeniusMoment
public import ASDExplicitGamma.Cold.NativeTraceMoments

/-! # Spectral estimates for the genuine fixed-frame response -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
open scoped BigOperators RealInnerProductSpace
namespace ASDExplicitGamma.Cold

/-- The native response is strictly positive at every sample. -/
theorem coldNativeResponse_posDef (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : (coldNativeResponse M m Q ω).PosDef := by
  rw [coldNativeResponse_eq_normalized]
  obtain ⟨Λ,hEll⟩ := coldNativeCoefficient_elliptic M m Q ω
  exact coarse_square_full_posDef Q (hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q))

/-- Native inverse/reflection order is a consequence of actual variational positivity. -/
theorem coldNativeResponse_duality (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    (coarseGramSwap*coldNativeResponse M m Q ω*coarseGramSwap-(coldNativeResponse M m Q ω)⁻¹).PosSemidef := by
  rw [coldNativeResponse_eq_normalized]
  obtain ⟨Λ,hEll⟩ := coldNativeCoefficient_elliptic M m Q ω
  have hO := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  let A := toFullBlockMat (coarseBlockMatrix (openCubeSet Q) (coldNativeCoefficient M m ω).toFun)
  have hA := (coarse_square_full_posDef Q hO).isHermitian
  have hR := coarseGramSwap_isHermitian
  have hRAR : (coarseGramSwap*A*coarseGramSwap).IsHermitian := by
    simpa only [hR.eq] using Matrix.isHermitian_conjTranspose_mul_mul coarseGramSwap hA
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  constructor
  · exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (hRAR.sub hA.inv)
  · intro x
    have h := coarse_square_inverse_reflection_order Q hO x
    change ⟪x,A⁻¹.toEuclideanLin x⟫ ≤ ⟪x,coarseGramSwap.toEuclideanLin (A.toEuclideanLin (coarseGramSwap.toEuclideanLin x))⟫ at h
    simp only [Matrix.toEuclideanLin,map_sub,Matrix.toLpLin_mul_same,LinearMap.sub_apply,
      LinearMap.comp_apply,inner_sub_left,real_inner_comm]
    exact sub_nonneg.mpr h

/-- The literal matrix trace excess equals the genuine fixed-frame cell trace. -/
theorem coldNativeResponse_trace (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    (coldNativeResponse M m Q ω).trace-4 = coldNativeCellTrace M m Q ω := by
  simp only [coldNativeResponse,coldNativeCellTrace,traceDefect,Variational.frameMatrix,
    Matrix.trace,Matrix.diag_apply,Fintype.sum_sum_type,toFullBlockMat,Matrix.smul_apply,smul_eq_mul,
    ← Finset.mul_sum]

/-- The sharp source spectral bound holds for the actual response, without spectral premises. -/
theorem coldNativeResponse_spectral (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    matrixFrobeniusSq (coldNativeResponse M m Q ω-1) ≤
      2*coldNativeCellTrace M m Q ω+(coldNativeCellTrace M m Q ω)^2 := by
  have hh := (matrix_spectral_pair_finite (d := 2) (by simp [BlockCoord]) _ coarseGramSwap
    (coldNativeResponse_posDef M m Q ω) coarseGramSwap_isHermitian coarseGramSwap_sq
    (coldNativeResponse_duality M m Q ω)).2
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  simpa only [coldNativeResponse_trace] using hh

end ASDExplicitGamma.Cold
