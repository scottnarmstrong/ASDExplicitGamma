module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt

/-! Scalar sharp response envelope from the two reflected energy inequalities. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- The energy cross inequality gives the exact product lower bound. -/
theorem clipped_energy_product_lower (A B S : ℝ)
    (h : ∀ t : ℝ, 0 ≤ A*(t*t)-2*S*t+B) : S^2 ≤ A*B := by
  have hd := discrim_le_zero (a := A) (b := -2*S) (c := B) (fun x => by
    simpa only [sub_eq_add_neg,neg_mul] using h x)
  unfold discrim at hd
  nlinarith only [hd]

/-- The sharp response cap, including a zero loading, with no inversion
or lower bound on the molecular ellipticity in its constant. -/
theorem clipped_response_scalar_bound (A B S t : ℝ) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (hA : 0 ≤ A) (hprod : S^2 ≤ A*B) (hsum : A+B ≤ 2*(1+t)*S) :
    A ≤ (1+t+Real.sqrt (t*(t+2)))*S := by
  have hroot : (Real.sqrt (t*(t+2)))^2=t*(t+2) := Real.sq_sqrt (by positivity)
  have hr0 := Real.sqrt_nonneg (t*(t+2))
  have hq : (A-(1+t)*S)^2 ≤ (Real.sqrt (t*(t+2))*S)^2 := by
    have hmul := mul_le_mul_of_nonneg_left hsum hA
    have he : (Real.sqrt (t*(t+2))*S)^2=(t*(t+2))*S^2 := by rw [mul_pow,hroot]
    rw [he]
    nlinarith only [hmul,hprod]
  have hh : A-(1+t)*S ≤ Real.sqrt (t*(t+2))*S :=
    (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) (mul_nonneg hr0 hS)).mp (by simpa only [sq_abs] using hq))
  linarith only [hh]

end ASDExplicitGamma.Inverse
