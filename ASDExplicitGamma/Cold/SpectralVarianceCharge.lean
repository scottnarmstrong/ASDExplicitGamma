module

public import ASDExplicitGamma.Cold.MatrixFrobeniusMoment
public import ASDExplicitGamma.Gaussian.RioTwoSum

/-! # Spectral variance charge without representation-dependent elaboration -/

@[expose] public section
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- A raw trace spectral charge bounds the actual centered Frobenius norm. -/
theorem matrix_center_l2_le_of_spectral {Ω n : Type*} [MeasurableSpace Ω]
    [Fintype n] [DecidableEq n] {μprob : Measure Ω} [IsProbabilityMeasure μprob]
    (A : Ω → Matrix n n ℝ) (T : Ω → ℝ) {D L : ℝ}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 μprob) (hT : MemLp T 2 μprob)
    (hspectral : ∀ ω, matrixFrobeniusSq (A ω-1) ≤ 2*T ω+T ω^2)
    (hmean : (∫ ω, T ω ∂μprob) ≤ D) (hcap : lpNorm T 2 μprob ≤ L) :
    matrixFrobeniusL2 μprob (fun ω => A ω-matrixMean μprob A) ≤ Real.sqrt (2*D+L^2) := by
  have hTi := hT.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hDiff : ∀ i j, MemLp (fun ω => (A ω-1) i j) 2 μprob := fun i j => (hA i j).sub (memLp_const _)
  have hInt := integral_mono (integrable_matrixFrobeniusSq hDiff)
    ((hTi.const_mul 2).add hT.integrable_sq) hspectral
  have hnorm : (lpNorm T 2 μprob)^2 = ∫ ω, T ω^2 ∂μprob := ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hT
  have hL := lpNorm_nonneg.trans hcap
  have hs := (sq_le_sq₀ (lpNorm_nonneg (f := T) (p := 2) (μ := μprob)) hL).mpr hcap
  rw [hnorm] at hs
  have hc := integral_matrixFrobeniusSq_center_le μprob A 1 hA
  apply Real.sqrt_le_sqrt
  change (∫ ω, matrixFrobeniusSq (A ω-matrixMean μprob A) ∂μprob) ≤ _
  change (∫ ω, matrixFrobeniusSq (A ω-1) ∂μprob) ≤ ∫ ω, 2*T ω+T ω^2 ∂μprob at hInt
  rw [integral_add (f := fun ω => 2*T ω) (hTi.const_mul 2) hT.integrable_sq,integral_const_mul] at hInt
  linarith only [hc,hInt,hs,hmean]

end ASDExplicitGamma.Cold
