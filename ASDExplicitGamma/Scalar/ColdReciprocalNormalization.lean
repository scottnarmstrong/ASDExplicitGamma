module

public import ASDExplicitGamma.Cold.GraphMeanOrder
public import ASDExplicitGamma.Cold.NativeResponseLaw
public import ASDExplicitGamma.Cold.NativeResponseMoment
public import ASDExplicitGamma.Cold.NativeTriangular
public import ASDExplicitGamma.Cold.NativeSubadditivity
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Scalar.TrueFrameNormalization
public import ASDExplicitGamma.Numerics.Cold.Certificate

/-! Cold trace to physical reciprocal response normalization. -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Homogenization.Book Algsuperdiff.Section3 Matrix
open scoped ENNReal
open ASDExplicitGamma.Cold ASDExplicitGamma.Numerics.Cold
namespace ASDExplicitGamma.Scalar

/-- SC-COLD-RECIPROCAL-NORMALIZATION for the actual OLD coefficient and true frame. -/
theorem cold_reciprocal_normalization (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (i : ℤ)
    (hordinary : ordinaryMean M i ≤ ENNReal.ofReal (3/50 * theta M))
    (hstrong : strong20 M i ≤ ENNReal.ofReal (2379/2500 * theta M))
    (hroot : root20 M i ≤ ENNReal.ofReal (2013/10000 * theta M))
    (e : Vec 2) (he : vecDot e e = 1) :
    2 * ((Annealed.sigmaBar M i : ℝ) * physicalInverseResponse M i
      (originCube 2 (i + 128)) e - 1) ≤ coldNativeMean M i 128 ∧
    1 ≤ (Annealed.sigmaBar M i : ℝ) * physicalInverseResponse M i
      (originCube 2 (i + 128)) e ∧
    (Annealed.sigmaBar M i : ℝ) * physicalInverseResponse M i
      (originCube 2 (i + 128)) e ≤ 1 + (coldD128Target : ℝ) / 2 := by
  have htheta : theta M ≤ 1 := by
    rw [theta]
    apply (div_le_iff₀ (by norm_num [gammaZero] : (0:ℝ) < gammaZero)).2
    nlinarith [hγ]
  have hordinary' : ordinaryMean M i ≤ ENNReal.ofReal (3/50 : ℝ) := by
    exact hordinary.trans (ENNReal.ofReal_le_ofReal (by nlinarith [htheta]))
  have hstrong' : strong20 M i ≤ ENNReal.ofReal (2379/2500 : ℝ) := by
    exact hstrong.trans (ENNReal.ofReal_le_ofReal (by nlinarith [htheta]))
  have hroot' : root20 M i ≤ ENNReal.ofReal (2013/10000 : ℝ) := by
    exact hroot.trans (ENNReal.ofReal_le_ofReal (by nlinarith [htheta]))
  have htri := Cold.cold_triangular_129 M h hM i hordinary' hstrong' hroot' 128 (by norm_num)
  have htrace_upper : coldNativeMean M i 128 ≤ coldMeanAt 128 := by
    simpa only [Cold.coldNativeMean, Cold.coldNativeTrace] using htri
  have hD128 : coldMeanAt 128 = (coldD128Target : ℝ) := by
    exact_mod_cast Numerics.Cold.coldD128_replay
  let Q : TriadicCube 2 := originCube 2 (i + 128)
  have hQscale : Q.scale = i + (128:ℤ) := by
    rfl
  obtain ⟨p, q, hp, hq, hmean⟩ := Cold.coldNativeResponse_mean_blocks M i Q
  have hdiag : ∀ a : BlockCoord 2,
      Integrable (fun ω => coldNativeResponse M i Q ω a a)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro a
    exact (Cold.coldNativeResponse_memLp hroot' 128 a a).integrable (by norm_num)
  have hmeanTrace := Cold.cold_graph_mean_trace (coldNativeResponse M i Q) hdiag hmean
  have hsourceMean : coldNativeMean M i 128 = 2 * (p + q) := by
    calc
      coldNativeMean M i 128 =
          ∫ ω, Cold.coldNativeCellTrace M i Q ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
        calc
          coldNativeMean M i 128 =
              ∫ ω, cutoffTraceDefect M i (i + (128:ℤ)) ω
                ∂(Cutoff.cutoffSampleLaw M).toMeasure := rfl
          _ = ∫ ω, cutoffTraceDefect M i Q.scale ω
              ∂(Cutoff.cutoffSampleLaw M).toMeasure := by rw [hQscale]
          _ = ∫ ω, Cold.coldNativeCellTrace M i Q ω
              ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
                (Cold.coldNativeCellTrace_integral M i Q).symm
      _ = ∫ ω, (coldNativeResponse M i Q ω).trace - 4
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
        congr 1
        funext ω
        exact (Cold.coldNativeResponse_trace M i Q ω).symm
      _ = 2 * (p + q) := hmeanTrace
  have hresponseMean := Cold.coldNativeResponse_mean M i Q
  let A := Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M i) (cubeSet Q)
  have hfull : toFullBlockMat (Variational.frameMatrix (Annealed.sigmaBar M i : ℝ) A) =
      1 + coldGraphBlockMean p q := by
    exact hresponseMean.symm.trans hmean
  have hsigma : 0 < (Annealed.sigmaBar M i : ℝ) :=
    (Annealed.sigmaBar_characterization M i).1
  have hlowerBlock : A.lowerRight =
      (((1 + q) / (Annealed.sigmaBar M i : ℝ)) : ℝ) • (1 : Mat 2) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      have hentry := congrArg (fun B : FullBlockMat 2 => B (Sum.inr x) (Sum.inr x)) hfull
      simp [A, coldGraphBlockMean, toFullBlockMat, Variational.frameMatrix,
        Ch02.blockDiag, Matrix.smul_apply, smul_eq_mul] at hentry ⊢
      field_simp [hsigma.ne'] at hentry ⊢
      nlinarith [hentry]
    · have hentry := congrArg (fun B : FullBlockMat 2 => B (Sum.inr x) (Sum.inr y)) hfull
      simp [A, coldGraphBlockMean, toFullBlockMat, Variational.frameMatrix,
        Ch02.blockDiag, Matrix.smul_apply, smul_eq_mul, hxy] at hentry ⊢
      rcases hentry with hσzero | hzero
      · exact (hsigma.ne' hσzero).elim
      · simpa [A] using hzero
  have hscaledResponse : (Annealed.sigmaBar M i : ℝ) *
      physicalInverseResponse M i Q e = 1 + q := by
    have hquad : physicalInverseResponse M i Q e = (1 + q) /
        (Annealed.sigmaBar M i : ℝ) := by
      unfold physicalInverseResponse
      rw [hlowerBlock]
      have hId : matVecMul (1 : Mat 2) e = e := Matrix.one_mulVec e
      rw [smul_matVecMul, hId, vecDot_smul_right, he]
      ring
    rw [hquad]
    field_simp [hsigma.ne']
  have hmean_upper : coldNativeMean M i 128 ≤ (coldD128Target : ℝ) := by
    rw [hD128] at htrace_upper
    exact htrace_upper
  refine ⟨?_, ?_, ?_⟩
  · rw [hscaledResponse, hsourceMean]
    nlinarith [hp]
  · exact sigmaBar_mul_physicalInverseResponse_ge_one M i Q e he
  · rw [hscaledResponse]
    have hqcap : 2 * q ≤ (coldD128Target : ℝ) := by
      rw [hsourceMean] at hmean_upper
      nlinarith [hmean_upper, hp]
    linarith

end ASDExplicitGamma.Scalar
end
