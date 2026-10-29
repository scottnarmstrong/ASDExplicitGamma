module

public import ASDExplicitGamma.Gaussian.CovarianceTrace
public import ASDExplicitGamma.Gaussian.FiniteFactorLaw
public import ASDExplicitGamma.Gaussian.ModelHeatPower
public import ASDExplicitGamma.Native.HeatInitialDescendants
public import ASDExplicitGamma.Native.HeatShearMoment
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.BankLocal
public import ASDExplicitGamma.Inverse.ClippedMatrixLocal
public import ASDExplicitGamma.Model.CutoffGaussian
public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Variational.TraceDefect
public import ASDExplicitGamma.Cold.NativeGraphTraceAverage
public import ASDExplicitGamma.Cold.SquareCellMean
public import ASDExplicitGamma.Native.HeatVHEATChild
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Inverse.AnchorAdapter
public import ASDExplicitGamma.Gaussian.ChildResponse
public import ASDExplicitGamma.Native.HeatTrueFrameCooperativeCurve
public import ASDExplicitGamma.Main.CubeFactor
public import ASDExplicitGamma.Gaussian.BasisIndependence

/-! Exact assembly of the actual nine-shell carrier generator into its
proved source-shell generator rows. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ProbabilityTheory

/-- Bilinear covariance traces split over the exact finite direct-sum basis
used by the heterogeneous shell realization. -/
theorem finiteFactor_bilinearTrace_eq_sum
    {b : ℕ} [NeZero b] {V : Fin b → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ∀ i, ℕ → V i)
    (hv : ∀ i, Summable (fun j => ‖v i j‖ ^ 2))
    (T : ∀ i, V i →L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ∑' j, B (finiteFactor V T (finiteDirections V v j))
        (finiteFactor V T (finiteDirections V v j)) =
      ∑ i, ∑' j, B (T i (v i j)) (T i (v i j)) := by
  classical
  have hs (i : Fin b) : Summable (fun j => B (T i (v i j)) (T i (v i j))) :=
    summable_bilinear_images (hv i) B (T i) (T i)
  have hp : Summable (fun p : Fin b × ℕ =>
      B (T p.1 (v p.1 p.2)) (T p.1 (v p.1 p.2))) := by
    apply Summable.of_norm
    rw [summable_prod_of_nonneg (fun p => norm_nonneg
      (B (T p.1 (v p.1 p.2)) (T p.1 (v p.1 p.2)) ))]
    exact ⟨fun i => (hs i).norm, Summable.of_finite⟩
  simp only [finiteDirections, finiteFactor_single]
  rw [(bandIndex b).tsum_eq
      (fun p : Fin b × ℕ => B (T p.1 (v p.1 p.2)) (T p.1 (v p.1 p.2))),
    hp.tsum_prod' hs]
  exact tsum_fintype _

end ASDExplicitGamma.Native

end
