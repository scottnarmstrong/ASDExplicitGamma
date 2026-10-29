module

public import ASDExplicitGamma.Numerics.Model.FourierMoments
public import ASDExplicitGamma.Model.Q3Cov

/-! The exact covariance integrals in the finite-mode q3 projection certificate. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
open MeasureTheory

def q3ModeCoefficient : ℕ → ℚ
  | 0 => 1
  | 2 => -39/5
  | 4 => 143/5
  | 6 => -429/5
  | 7 => 429/5
  | 9 => -143/5
  | 11 => 39/5
  | 13 => -1
  | _ => 0

noncomputable def q3CosineCoefficient (ell w : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos (w*u)
noncomputable def q3SineCoefficient (w : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, ASDExplicitGamma.q3Cov u*Real.sin (w*u)

noncomputable def q3CosineMomentSum (ell w : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 14, (q3ModeCoefficient k : ℝ)*(cosineMoment w k-ell*cosineMoment w (k+1))
noncomputable def q3SineMomentSum (w : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 14, (q3ModeCoefficient k : ℝ)*sineMoment w k

theorem q3_cosine_coefficient_formula (ell w : ℝ) :
    q3CosineCoefficient ell w = q3CosineMomentSum ell w := by
  have hcont (k : ℕ) : Continuous (fun u : ℝ => u^k*Real.cos (w*u)) :=
    (continuous_id.pow k).mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  calc
    _ = ∫ u in (0 : ℝ)..1, ∑ k ∈ Finset.range 14, (q3ModeCoefficient k : ℝ)*
        (u^k*Real.cos (w*u)-ell*(u^(k+1)*Real.cos (w*u))) := by
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by simpa using hu
      rw [ASDExplicitGamma.Model.q3Cov_eq_polynomial_on_unit_interval u hu'.1 hu'.2]
      norm_num [Finset.sum_range_succ,q3ModeCoefficient]
      ring
    _ = ∑ k ∈ Finset.range 14, ∫ u in (0 : ℝ)..1, (q3ModeCoefficient k : ℝ)*
        (u^k*Real.cos (w*u)-ell*(u^(k+1)*Real.cos (w*u))) := by
      apply intervalIntegral.integral_finsetSum
      intro k _
      exact (((hcont k).sub ((hcont (k+1)).const_mul ell)).const_mul (q3ModeCoefficient k : ℝ)).intervalIntegrable 0 1
    _ = q3CosineMomentSum ell w := by
      apply Finset.sum_congr rfl
      intro k _
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub ((hcont k).intervalIntegrable 0 1)
          (((hcont (k+1)).const_mul ell).intervalIntegrable 0 1),
        intervalIntegral.integral_const_mul]
      rfl

theorem q3_sine_coefficient_formula (w : ℝ) :
    q3SineCoefficient w = q3SineMomentSum w := by
  have hcont (k : ℕ) : Continuous (fun u : ℝ => u^k*Real.sin (w*u)) :=
    (continuous_id.pow k).mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  calc
    _ = ∫ u in (0 : ℝ)..1, ∑ k ∈ Finset.range 14, (q3ModeCoefficient k : ℝ)*(u^k*Real.sin (w*u)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by simpa using hu
      rw [ASDExplicitGamma.Model.q3Cov_eq_polynomial_on_unit_interval u hu'.1 hu'.2]
      norm_num [Finset.sum_range_succ,q3ModeCoefficient]
      ring
    _ = ∑ k ∈ Finset.range 14, ∫ u in (0 : ℝ)..1, (q3ModeCoefficient k : ℝ)*(u^k*Real.sin (w*u)) := by
      apply intervalIntegral.integral_finsetSum
      intro k _
      exact ((hcont k).const_mul (q3ModeCoefficient k : ℝ)).intervalIntegrable 0 1
    _ = q3SineMomentSum w := by
      apply Finset.sum_congr rfl
      intro k _
      rw [intervalIntegral.integral_const_mul]
      rfl

/-- The source length/cube ratio at depth j. -/
def q3ModeLength (j : ℕ) : ℚ := 1/3^j
/-- Index n represents the positive Fourier mode m=n+1. -/
noncomputable def q3ModeFrequency (j n : ℕ) : ℝ :=
  Real.pi*(((n+1 : ℕ) : ℝ)/(3 : ℝ)^j)
noncomputable def q3ModeCosine (j n : ℕ) : ℝ :=
  let ell : ℝ := q3ModeLength j
  let w := q3ModeFrequency j n
  2*ell*(q3CosineCoefficient ell w-q3SineCoefficient w/(Real.pi*((n+1 : ℕ) : ℝ)))
noncomputable def q3ModeSine (j n : ℕ) : ℝ :=
  let ell : ℝ := q3ModeLength j
  let w := q3ModeFrequency j n
  2*ell*(q3CosineCoefficient ell w+q3SineCoefficient w/(Real.pi*((n+1 : ℕ) : ℝ)))
noncomputable def q3ModeDifference (j n : ℕ) : ℝ := q3ModeSine j n-q3ModeCosine j n

/-- Finite projection in the exact source normalization, with no floating endpoints. -/
noncomputable def q3Projection (j N : ℕ) : ℝ :=
  2*∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
    (((m+1 : ℕ) : ℝ)^2/(((m+1 : ℕ) : ℝ)^2+((n+1 : ℕ) : ℝ)^2))*
      q3ModeCosine j m*q3ModeSine j n

end ASDExplicitGamma.Numerics.Model
