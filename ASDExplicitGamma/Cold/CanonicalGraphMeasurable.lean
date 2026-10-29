module

public import ASDExplicitGamma.Cold.CanonicalAverageMeasurable
public import ASDExplicitGamma.Cold.ProjectedGraphEnergy
public import ASDExplicitGamma.Cold.NativeMatchedFamily

/-! # Actual projected canonical graph means are measurable -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Restricting the actual harmonic function preserves its true flux/gradient cell averages. -/
theorem coarseGraphMean_restriction (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : AHarmonicFunction a (openCubeSet Q))
    {r : ℕ} (R : SquareCells Q r) :
    coarseGraphMean R.val (squareCellRestriction Q hEll v R) =
      (cubeAverageVec R.val (fun x => matVecMul (a x) (v.toH1.grad x)),cubeAverageVec R.val v.toH1.grad) := by
  apply Prod.ext
  · funext i
    change volumeAverage (openCubeSet R.val) (fun x => matVecMul (a x) (v.toH1.grad x) i) = _
    rw [square_volumeAverage_eq_cubeAverage]
    rfl
  · funext i
    change volumeAverage (openCubeSet R.val) (fun x => v.toH1.grad x i) = _
    rw [square_volumeAverage_eq_cubeAverage]
    rfl

/-- The squared graph mean of each actual restricted canonical solution is a.e. measurable. -/
theorem cold_canonical_restricted_graph_measurable {Ω : Type*} [MeasurableSpace Ω]
    (μprob : Measure Ω) [IsProbabilityMeasure μprob] (a : Ω → RegCoeffField 2)
    (hm : Measurable a) (ha : ∀ ω, Ch04.AELocallyUniformlyEllipticField (a ω))
    (Q : TriadicCube 2) {lam Lam : Ω → ℝ}
    (hEll : ∀ ω, IsEllipticFieldOn (lam ω) (Lam ω) (openCubeSet Q) (a ω).toFun)
    {r : ℕ} (R : SquareCells Q r) (p q : Vec 2) :
    AEMeasurable (fun ω => blockVecDot
      (coarseGraphMean R.val (squareCellRestriction Q (hEll ω) (coldCanonicalOptimizer (a ω) (ha ω) Q p q) R))
      (coarseGraphMean R.val (squareCellRestriction Q (hEll ω) (coldCanonicalOptimizer (a ω) (ha ω) Q p q) R))) μprob := by
  have hg := cold_canonical_gradient_average_measurable μprob a hm ha Q R.val R.property p q
  have hf := cold_canonical_flux_average_measurable μprob a hm ha Q R.val R.property p q
  simp_rw [coarseGraphMean_restriction]
  unfold blockVecDot vecDot
  apply AEMeasurable.add
  · exact Finset.aemeasurable_sum Finset.univ (fun i _ => ((aemeasurable_pi_iff.mp hf) i).mul ((aemeasurable_pi_iff.mp hf) i))
  · exact Finset.aemeasurable_sum Finset.univ (fun i _ => ((aemeasurable_pi_iff.mp hg) i).mul ((aemeasurable_pi_iff.mp hg) i))

/-- The actual native projected graph has no additional solution-measurability premise. -/
theorem coldNativePlateauFamily_projectedGraph_measurable (M : Algsuperdiff.Section3.ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (r : ℕ) :
    AEStronglyMeasurable ((coldNativePlateauFamily M m Q).projectedGraph r)
      (Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure := by
  let F := coldNativePlateauFamily M m Q
  let μprob := (Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure
  have hp (R : SquareCells Q r) (i : Fin 2) := cold_canonical_restricted_graph_measurable μprob
    (coldNativeCoefficient M m) (coldNativeCoefficient_measurable M m) (coldNativeCoefficient_locallyElliptic M m)
    Q F.elliptic R (Pi.single i 1) (Pi.single i 1)
  have ha (R : SquareCells Q r) (i : Fin 2) := cold_canonical_restricted_graph_measurable μprob
    (fun ω => adjointReg (coldNativeCoefficient M m ω)) (measurable_adjointReg.comp (coldNativeCoefficient_measurable M m))
    (coldNativeAdjoint_locallyElliptic M m) Q
    (fun ω => isEllipticFieldOn_adjointCoeffField (F.elliptic ω)) R (Pi.single i 1) (Pi.single i 1)
  have hh := (Finset.aemeasurable_sum Finset.univ (fun R _ =>
    Finset.aemeasurable_sum Finset.univ (fun i _ => (hp R i).add (ha R i)))).const_mul
      (((descendantsAtDepth Q r).card:ℝ)⁻¹)
  simp only [Finset.sum_apply,Pi.add_apply] at hh
  exact hh.aestronglyMeasurable

end ASDExplicitGamma.Cold
