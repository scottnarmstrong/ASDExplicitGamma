module

public import ASDExplicitGamma.Scalar.UpperSourceCaps
public import ASDExplicitGamma.Variational.TrueFrame

/-! The two OLD mean excesses share one half-trace charge. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Homogenization.Book MeasureTheory Algsuperdiff.Section3 Native
open scoped ENNReal
noncomputable section

/-- The accepted depth-fourteen source cap bounds the actual coefficient-law
mean trace, in sigmaBar at the completed left endpoint. -/
theorem upper_cell_old_mean_trace
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (n : ℤ) (hn : n < N) :
    (∫ a : RegCoeffField 2, traceDefect (cubeSet (originCube 2 (n-14))) a.toFun
      (Annealed.sigmaBar M n:ℝ) ∂(Cutoff.coefficientCutoffLaw M n)) ≤
      safeDepth14EndpointCap := by
  have hcap := (scalar_upper_source_caps M h hM hg N hpast n hn).2.2.1
  have hi := Cold.integrable_cutoffTraceDefect M n (n-14)
  have heq : (∫ ω,cutoffTraceDefect M n (n-14) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      (nativeCompletedSourceMean M n 14).toReal := by
    simpa only [nativeCompletedSourceMean,Nat.cast_ofNat] using
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (Variational.cutoffTraceDefect_nonneg M n (n-14)))
        hi.aestronglyMeasurable
  have hcapReal : (nativeCompletedSourceMean M n 14).toReal ≤ safeDepth14EndpointCap :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hcap).trans_eq
      (ENNReal.toReal_ofReal (by unfold safeDepth14EndpointCap; positivity))
  have hiLaw := Variational.integrable_traceDefect_cutoffLaw M n
    (originCube 2 (n-14)) (Annealed.sigmaBar M n:ℝ)
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hiLaw ⊢
  rw [integral_map (Cutoff.measurable_coefficientCutoff M.nu n).aemeasurable
    hiLaw.aestronglyMeasurable]
  exact heq ▸ hcapReal

/-- The actual OLD annealed matrix has nonnegative block excesses A,B whose
SUM is at most the single half-trace cap, uniformly over real translations.
This is stronger than separately bounding each block by that cap. -/
theorem upper_cell_old_mean_excesses
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (n : ℤ) (hn : n < N) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ A+B ≤ safeDepth14EndpointCap/2 ∧
      ∀ x : Vec 2,
        Variational.frameMatrix (Annealed.sigmaBar M n:ℝ)
          (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M n)
            (translateSet x (cubeSet (originCube 2 (n-14))))) =
          Ch02.blockDiag ((1+A) • (1:Mat 2)) ((1+B) • (1:Mat 2)) := by
  obtain ⟨a,b,ha,hb,heq⟩ := Variational.exists_trueFrame_mean_scalars M n (n-14)
  have htrace := upper_cell_old_mean_trace M h hM hg N hpast n hn
  rw [Variational.integral_traceDefect_eq_annealed_trace] at htrace
  have hzero := heq 0
  rw [translateSet_zero] at hzero
  have hUL := congrArg (fun C : BlockMat 2 => Matrix.trace C.upperLeft) hzero
  have hLR := congrArg (fun C : BlockMat 2 => Matrix.trace C.lowerRight) hzero
  simp only [Variational.frameMatrix,Ch02.blockDiag,Matrix.trace_smul,smul_eq_mul,
    Matrix.trace_one,Fintype.card_fin] at hUL hLR
  rw [hUL,hLR] at htrace
  norm_num only [Nat.cast_ofNat] at htrace
  refine ⟨a-1,b-1,sub_nonneg.mpr ha,sub_nonneg.mpr hb,?_,?_⟩
  · linarith only [htrace]
  · intro x
    simpa only [add_sub_cancel] using heq x

/-- The positive trial's OLD charge retains its block weight; no extra
factor 1+z is paid against the half-trace cap. -/
theorem upper_cell_old_weighted_excess_le (A B z t : ℝ)
    (hB : 0 ≤ B) (hz : z ≤ 1) (htrace : A+B ≤ t/2) :
    A+z*B ≤ t/2 := by
  have hh := mul_le_mul_of_nonneg_right hz hB
  linarith only [hh,htrace]

end
end ASDExplicitGamma.Scalar
