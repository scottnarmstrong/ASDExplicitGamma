module

public import ASDExplicitGamma.Cold.NativeSelectedGraph
public import ASDExplicitGamma.Cold.MatchedGraphIdentity

/-! # The actual own-cell four-load graph expectations -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Measurability of the exact source twice-Frobenius-square observable. -/
theorem cold_graph_observable_measurable : Measurable (fun A : FullBlockMat 2 => 2*matrixFrobeniusSq (A-1)) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  change Measurable (fun A : FullBlockMat 2 => (A i j-(1:FullBlockMat 2) i j)^2)
  have he : Measurable (fun A : FullBlockMat 2 => A i j) := (measurable_pi_apply j).comp (measurable_pi_apply i)
  exact (he.sub_const _).pow_const 2

/-- Actual native matched optimizers have exactly the twice-Frobenius-square graph energy. -/
theorem coldNativeMatched_graph (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    squareFourGraphEnergy Q (coldNativeMatchedOptimizers M m Q ω).primal (coldNativeMatchedOptimizers M m Q ω).adjoint =
      2*matrixFrobeniusSq (coldNativeResponse M m Q ω-1) := by
  rw [coldNativeResponse_eq_normalized]
  obtain ⟨Λ,hE⟩ := coldNativeCoefficient_elliptic M m Q ω
  exact square_matched_graph_identity Q (hE.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)) _

/-- Own-cell graph expectations are integrable and obey the actual selected native source cap. -/
theorem cold_native_own_graph_cap (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hroot : root20 M m ≤ ENNReal.ofReal (θ*(coldR20:ℝ)))
    (Q : TriadicCube 2) (r : ℕ) {n ell : ℕ} (hn : n ≤ 128) (hell : ell < n) (hell126 : ell ≤ 126)
    (hscale : Q.scale-(r:ℤ) = m+(ell:ℤ))
    (hmean : ∀ i < n, coldNativeMean M m i ≤ θ*(coldMeanAt i:ℝ)) :
    let F := coldNativePlateauFamily M m Q
    Integrable (fun ω => squareOwnGraphEnergy Q (F.cells r ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, squareOwnGraphEnergy Q (F.cells r ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ coldSelectedGraphCap θ ell := by
  dsimp only
  let μprob := (Cutoff.cutoffSampleLaw M).toMeasure
  have he (ω : Cutoff.CutoffSample 2) :
      squareOwnGraphEnergy Q ((coldNativePlateauFamily M m Q).cells r ω) =
        squareCellMean Q r (fun C => 2*matrixFrobeniusSq (coldNativeResponse M m C.val ω-1)) := by
    unfold squareOwnGraphEnergy
    congr 1
    funext C
    exact coldNativeMatched_graph M m C.val ω
  have hInt (C : SquareCells Q r) : Integrable (fun ω => 2*matrixFrobeniusSq (coldNativeResponse M m C.val ω-1)) μprob := by
    have hc : C.val.scale = m+(ell:ℤ) := (scale_eq_sub_of_mem_descendantsAtDepth C.property).trans hscale
    have hT : MemLp (coldNativeCellTrace M m C.val) 2 μprob := by
      apply (coldNativeCellTrace_memLp_iff M m C.val 2).mpr
      rw [hc]
      exact (coldNativeTrace_memLp hroot ell).mono_exponent (by norm_num)
    have hA := coldNativeResponse_memLp_of_trace M m C.val hT
    exact (integrable_matrixFrobeniusSq (fun i j => (hA i j).sub (memLp_const _))).const_mul 2
  have hSame (C : SquareCells Q r) : (∫ ω, 2*matrixFrobeniusSq (coldNativeResponse M m C.val ω-1) ∂μprob) =
      ∫ ω, 2*matrixFrobeniusSq (coldNativeResponse M m (originCube 2 (m+(ell:ℤ))) ω-1) ∂μprob := by
    have hh := ((coldNativeResponse_identDistrib M m C.val).comp cold_graph_observable_measurable).integral_eq
    rw [scale_eq_sub_of_mem_descendantsAtDepth C.property,hscale] at hh
    exact hh
  simp_rw [he]
  refine ⟨integrable_squareCellMean Q r hInt,?_⟩
  rw [integral_squareCellMean Q r hInt]
  simp_rw [hSame]
  rw [squareCellMean_const,integral_const_mul]
  exact cold_native_selected_graph M h hM m hθ hroot hn hell hell126 hmean

end ASDExplicitGamma.Cold
