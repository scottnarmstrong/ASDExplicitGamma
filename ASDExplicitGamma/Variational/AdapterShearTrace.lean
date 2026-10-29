module

public import ASDExplicitGamma.Variational.AdapterConstantSkew
public import ASDExplicitGamma.Variational.AdapterDuality

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response

noncomputable section

/-- The signed linear trace coefficient of a constant stream shift. -/
def shearTraceLinear (A : BlockMat 2) : ℝ := A.upperRight 1 0 - A.upperRight 0 1

private theorem constantSkewCongruence_trace_upperLeft (g : ℝ) (A : BlockMat 2)
    (hA : IsSymmetricBlockMat A) :
    Matrix.trace (constantSkewCongruence g A).upperLeft =
      Matrix.trace A.upperLeft + 2 * g * shearTraceLinear A +
        g ^ 2 * Matrix.trace A.lowerRight := by
  have h01 := hA (Sum.inl 0) (Sum.inr 1)
  have h10 := hA (Sum.inl 1) (Sum.inr 0)
  change A.upperRight 0 1 = A.lowerLeft 1 0 at h01
  change A.upperRight 1 0 = A.lowerLeft 0 1 at h10
  simp [Matrix.trace, Matrix.diag, constantSkewCongruence, constantSkewMatrix, ofFullBlockMat,
    toFullBlockMat, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, responsePlanarJ, shearTraceLinear]
  rw [← h01, ← h10]
  ring

/-- Exact frame-unit shear trace formula for the actual coarse matrix. -/
theorem traceDefect_constantSkew {Q : TriadicCube 2} (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (κ : Vec 2 → ℝ) {Λ : ℝ}
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q)
      (fun x => responsePlanarCoefficient ν (κ x))) (g : ℝ) :
    traceDefect (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x + σ * g)) σ =
      traceDefect (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x)) σ +
        2 * g * shearTraceLinear (coarseBlockMatrix (cubeSet Q)
          (fun x => responsePlanarCoefficient ν (κ x))) +
        g ^ 2 * Matrix.trace (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
          (fun x => responsePlanarCoefficient ν (κ x)))).lowerRight := by
  unfold traceDefect
  rw [coarseBlockMatrix_constantSkew ν hν κ hEll,
    constantSkewCongruence_lowerRight,
    constantSkewCongruence_trace_upperLeft _ _ (coarseBlockMatrix_symmetric _ _)]
  simp only [frameMatrix, Matrix.trace_smul]
  field_simp [hσ.ne']
  ring

/-- Physical units: the quadratic trace coefficient is tr D / σ². -/
theorem traceDefect_constantSkew_physical {Q : TriadicCube 2} (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (κ : Vec 2 → ℝ) {Λ : ℝ}
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q)
      (fun x => responsePlanarCoefficient ν (κ x))) (g : ℝ) :
    traceDefect (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x + g)) σ =
      traceDefect (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x)) σ +
        2 * (g / σ) * shearTraceLinear (coarseBlockMatrix (cubeSet Q)
          (fun x => responsePlanarCoefficient ν (κ x))) +
        g ^ 2 * (Matrix.trace (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
          (fun x => responsePlanarCoefficient ν (κ x)))).lowerRight / σ ^ 2) := by
  have h := traceDefect_constantSkew ν σ hν hσ κ hEll (g / σ)
  rw [mul_div_cancel₀ g hσ.ne'] at h
  convert h using 1; ring

private theorem shifted_response_isElliptic (Q : TriadicCube 2)
    (ν : ℝ) (hν : 0 < ν) (k : ResponseCoefficient (cubeSet Q)) (η : ℝ) :
    IsEllipticFieldOn ν ((ν ^ 2 + ‖k + BoundedContinuousFunction.const _ η‖ ^ 2) / ν)
      (cubeSet Q) (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x + η)) := by
  let k' := k + BoundedContinuousFunction.const (closure (cubeSet Q)) η
  have hEll := responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k'
  have he (x : Vec 2) (hx : x ∈ cubeSet Q) :
      responseCoefficientExtension k' x = responseCoefficientExtension k x + η := by
    rw [responseCoefficientExtension_eq k' hx, responseCoefficientExtension_eq k hx]
    rfl
  refine ⟨?_, ?_⟩
  · have hm := hEll.1
    convert hm using 1
    funext x
    by_cases hx : x ∈ cubeSet Q
    · simp only [hx, ite_true, responsePlanarCoefficientField, he x hx]
    · simp only [hx, ite_false]
  · intro x hx
    simpa only [responsePlanarCoefficientField, he x hx] using hEll.2 x hx

/-- The sharp discriminant inequality in the source's stationary gauge.
Every hypothesis is a source structural assumption. -/
theorem shearTraceLinear_sq_le (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (cubeSet Q)) :
    (shearTraceLinear (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k))) ^ 2 ≤
      Matrix.trace (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
        (responsePlanarCoefficientField ν k))).lowerRight *
        traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ := by
  let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)
  let T := traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ
  let z := shearTraceLinear A
  let d := Matrix.trace (frameMatrix σ A).lowerRight
  have hpoly (g : ℝ) : 0 ≤ d * (g * g) + (2 * z) * g + T := by
    have hn := traceDefect_nonneg_of_ellipticFieldOn_triCube hν
      (shifted_response_isElliptic Q ν hν k (σ * g)) hσ
    rw [traceDefect_constantSkew ν σ hν hσ (responseCoefficientExtension k)
      (responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k)] at hn
    change 0 ≤ T + 2 * g * z + g ^ 2 * d at hn
    nlinarith only [hn]
  have hd := discrim_le_zero hpoly
  dsimp only [discrim] at hd
  change z ^ 2 ≤ d * T
  nlinarith only [hd]

/-- Exact reciprocal-block invariance, hence invariance of every history
formed solely from these blocks and their inverses. -/
theorem coarse_lowerRight_constantSkew {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k : ResponseCoefficient (cubeSet Q)) (g : ℝ) :
    (coarseBlockMatrix (cubeSet Q)
      (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x + g))).lowerRight =
      (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)).lowerRight := by
  rw [response_coarseBlockMatrix_constantSkew Q ν hν k, constantSkewCongruence_lowerRight]

/-- An arbitrary observable of the complete reciprocal-block family is gauge
invariant. This includes inverse matrices, norms, maxima, and history sums. -/
theorem reciprocal_history_constantSkew {ι α : Type*} (Q : ι → TriadicCube 2)
    (ν : ℝ) (hν : 0 < ν) (k : ∀ i, ResponseCoefficient (cubeSet (Q i)))
    (g : ι → ℝ) (Φ : (ι → Mat 2) → α) :
    Φ (fun i => (coarseBlockMatrix (cubeSet (Q i))
      (fun x => responsePlanarCoefficient ν (responseCoefficientExtension (k i) x + g i))).lowerRight) =
    Φ (fun i => (coarseBlockMatrix (cubeSet (Q i))
      (responsePlanarCoefficientField ν (k i))).lowerRight) := by
  congr 1
  funext i
  exact coarse_lowerRight_constantSkew ν hν (k i) (g i)

/-- Source trace identity, deriving ellipticity from bounded continuous k. -/
theorem response_traceDefect_constantSkew (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (cubeSet Q)) (g : ℝ) :
    traceDefect (cubeSet Q)
      (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x + σ * g)) σ =
      traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ +
        2 * g * shearTraceLinear (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)) +
        g ^ 2 * Matrix.trace (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField ν k))).lowerRight :=
  traceDefect_constantSkew ν σ hν hσ (responseCoefficientExtension k)
    (responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k) g

/-- Source identity with a physical scalar shift and coefficient tr D / σ². -/
theorem response_traceDefect_constantSkew_physical (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (cubeSet Q)) (g : ℝ) :
    traceDefect (cubeSet Q)
      (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x + g)) σ =
      traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ +
        2 * (g / σ) * shearTraceLinear (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)) +
        g ^ 2 * (Matrix.trace (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField ν k))).lowerRight / σ ^ 2) :=
  traceDefect_constantSkew_physical ν σ hν hσ (responseCoefficientExtension k)
    (responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k) g

end

end ASDExplicitGamma.Variational
