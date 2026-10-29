module

public import ASDExplicitGamma.Scalar.ChaosInfiniteInputMap
public import ASDExplicitGamma.Scalar.ChaosHilbertSymmetrization
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! The actual trace centering and finite cutoffs of a quadratic Gaussian Hilbert series. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Source trace centering of the quadratic Gaussian series. -/
noncomputable def gaussianBilinearTrace (B : V →L[ℝ] V →L[ℝ] W) (v : ℕ → V) : W :=
  ∑' i,B (v i) (v i)

/-- The trace series is genuinely summable under the source Hilbert-Schmidt condition. -/
theorem gaussian_bilinear_trace_summable [CompleteSpace W]
    (B : V →L[ℝ] V →L[ℝ] W) (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) :
    Summable (fun i => B (v i) (v i)) := by
  apply (hA.mul_left ‖B‖).of_norm_bounded
  intro i
  simpa only [pow_two,mul_assoc] using B.le_opNorm₂ (v i) (v i)

/-- Uniform deterministic control of the finite trace centerings. -/
theorem gaussian_bilinear_partial_trace_norm_le (B : V →L[ℝ] V →L[ℝ] W)
    (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) (n : ℕ) :
    ‖∑ i ∈ Finset.range n,B (v i) (v i)‖≤‖B‖*(∑' i,‖v i‖^2) := by
  have hB0 : 0≤‖B‖ := by convert norm_nonneg B using 1
  calc
    _ ≤ ∑ i ∈ Finset.range n,‖B (v i) (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n,‖B‖*‖v i‖^2 := Finset.sum_le_sum (fun i hi => by
      simpa only [pow_two,mul_assoc] using B.le_opNorm₂ (v i) (v i))
    _ = ‖B‖*(∑ i ∈ Finset.range n,‖v i‖^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hA.sum_le_tsum (Finset.range n) (fun i hi => sq_nonneg _)) hB0

/-- The actual centered quadratic cutoff, with its true finite trace. -/
noncomputable def gaussianBilinearPartial (B : V →L[ℝ] V →L[ℝ] W) (v : ℕ → V)
    (n : ℕ) (omega : ℕ → ℝ) : W :=
  B (Gaussian.gaussianPartialSum v n omega) (Gaussian.gaussianPartialSum v n omega)-
    ∑ i ∈ Finset.range n,B (v i) (v i)

/-- The Hilbert-series Gaussian quadratic with its trace centering. -/
noncomputable def gaussianBilinearChaos [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    (B : V →L[ℝ] V →L[ℝ] W) (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2))
    (omega : ℕ → ℝ) : W :=
  B (Gaussian.gaussianSeriesLimit v hA omega) (Gaussian.gaussianSeriesLimit v hA omega)-gaussianBilinearTrace B v

/-- The source infinite-input Hilbert-valued norm-squared envelope. -/
noncomputable def gaussianHilbertEnvelope [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    (m : W) (B : V →L[ℝ] V →L[ℝ] W) (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2))
    (omega : ℕ → ℝ) : ℝ := ‖m+gaussianBilinearChaos B v hA omega‖^2

end ASDExplicitGamma.Scalar
