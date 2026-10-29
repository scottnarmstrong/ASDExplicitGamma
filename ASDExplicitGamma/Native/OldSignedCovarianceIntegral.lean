module

public import ASDExplicitGamma.Gaussian.HilbertKernel

/-! Dominated passage of the actual complete white-mode contraction through
a spatial integral. Absolute quadratic domination keeps correlations intact. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
noncomputable section

/-- A complete real white basis contracts inside any spatial integral with
an actual integrable quadratic majorant. No independence of the multiplier
from the spatial fields is used. -/
theorem old_signed_weighted_white_covariance {X H I : Type*}
    [MeasurableSpace X] (mu : Measure X) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Countable I]
    (e : HilbertBasis I ℝ H) (A B : X → H) (r : X → ℝ)
    (hA : AEStronglyMeasurable A mu) (hB : AEStronglyMeasurable B mu)
    (hr : AEStronglyMeasurable r mu)
    (hi : Integrable (fun x => |r x| *(‖A x‖^2+‖B x‖^2)) mu) :
    HasSum (fun n => ∫ x,r x*inner ℝ (e n) (A x)*inner ℝ (e n) (B x) ∂mu)
      (∫ x,r x*inner ℝ (A x) (B x) ∂mu) := by
  have hs (u : H) : HasSum (fun n => inner ℝ (e n) u^2) (‖u‖^2) := by
    simpa only [real_inner_comm u,pow_two,real_inner_self_eq_norm_sq] using
      e.hasSum_inner_mul_inner u u
  let bound : I → X → ℝ := fun n x =>
    (|r x| /2)*(inner ℝ (e n) (A x)^2+inner ℝ (e n) (B x)^2)
  have hb (x : X) : HasSum (fun n => bound n x)
      ((|r x| /2)*(‖A x‖^2+‖B x‖^2)) :=
    ((hs (A x)).add (hs (B x))).mul_left (|r x| /2)
  apply hasSum_integral_of_dominated_convergence bound
  · intro n
    exact (hr.mul (hA.const_inner (𝕜 := ℝ) (c := e n))).mul (hB.const_inner (𝕜 := ℝ) (c := e n))
  · intro n
    filter_upwards with x
    dsimp only [bound]
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    have hc : |inner ℝ (e n) (A x)| *|inner ℝ (e n) (B x)| ≤
        (inner ℝ (e n) (A x)^2+inner ℝ (e n) (B x)^2)/2 := by
      nlinarith only [sq_nonneg (|inner ℝ (e n) (A x)|-|inner ℝ (e n) (B x)|),
        sq_abs (inner ℝ (e n) (A x)),sq_abs (inner ℝ (e n) (B x))]
    nlinarith only [mul_le_mul_of_nonneg_left hc (abs_nonneg (r x))]
  · exact Filter.Eventually.of_forall fun x => (hb x).summable
  · have he : (fun x => ∑' n,bound n x)=fun x =>
        (1/2:ℝ)*(|r x| *(‖A x‖^2+‖B x‖^2)) := by
      funext x
      rw [(hb x).tsum_eq]
      ring
    rw [he]
    exact hi.const_mul _
  · filter_upwards with x
    have hh := (e.hasSum_inner_mul_inner (A x) (B x)).mul_left (r x)
    simpa only [real_inner_comm (A x),mul_assoc] using hh

end
end ASDExplicitGamma.Native
