module

public import ASDExplicitGamma.Native.ParentBoundaryBetaClock
public import ASDExplicitGamma.Gaussian.Q3ModelCovariance

/-! Exact own-native shell geometry for the actual canonical model. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic
noncomputable section

/-- The actual shell/parent ratio is the exact triadic power. -/
theorem parent_boundary_model_length_ratio (n : ℤ) (s : ℕ) :
    cubeScaleFactor (originCube 2 n)/(q3ModelLength (n+(s:ℤ))).1 = (1/3:ℝ)^s := by
  simp only [cubeScaleFactor_originCube,q3ModelLength,
    zpow_add₀ (by norm_num : (3:ℝ)≠0),zpow_natCast]
  rw [div_mul_eq_div_div,div_self (zpow_ne_zero n (by norm_num : (3:ℝ)≠0)),
    one_div,one_div_pow]
  rw [one_div]

/-- Every genuinely fresh shell satisfies the own-native scale
hypothesis of the centered covariance clock. -/
theorem parent_boundary_model_scale (n : ℤ) (s : ℕ) (hs : 1≤s) :
    3*cubeScaleFactor (originCube 2 n)≤(q3ModelLength (n+(s:ℤ))).1 := by
  have hr := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1/3:ℝ)≤1) hs
  have he := parent_boundary_model_length_ratio n s
  have hh : cubeScaleFactor (originCube 2 n)/(q3ModelLength (n+(s:ℤ))).1≤1/3 := by
    rw [he]
    simpa only [pow_one] using hr
  have hL := (q3ModelLength (n+(s:ℤ))).2
  have hc := (div_le_iff₀ hL).mp hh
  linarith only [hc]

/-- The actual complete Dirichlet coefficient of a shell has the
summable geometric clock, with its physical variance retained. -/
theorem parent_boundary_model_dirichlet_clock (n : ℤ) (s : ℕ) (b : ℝ) :
    parentBoundaryDirichletEnergy (originCube 2 n) b (q3ModelLength (n+(s:ℤ))) ≤
      (26/15:ℝ)*(1/9:ℝ)^s*b^2 := by
  have hh := parent_boundary_dirichlet_energy_rational_clock (originCube 2 n) b
    (q3ModelLength (n+(s:ℤ)))
  rw [parent_boundary_model_length_ratio] at hh
  have he : ((1/3:ℝ)^s)^2=(1/9:ℝ)^s := by
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  rwa [he] at hh

/-- The sharp centered covariance estimate applies directly at every
actual own-native shell, for either sign and every comparison depth. -/
theorem parent_boundary_model_beta_clock (n : ℤ) (s depth : ℕ) (hs : 1≤s)
    (b : ℝ) (plus : Bool) :
    Real.sqrt (descendantsAverage (originCube 2 n) depth (fun U =>
      parentBoundaryCenteredBeta (originCube 2 n) U b (q3ModelLength (n+(s:ℤ))) plus^2)) ≤
      b^2*Real.sqrt (parentBoundaryCovarianceClock (cubeScaleFactor (originCube 2 n)) depth
        (q3ModelLength (n+(s:ℤ))).1) :=
  parent_boundary_centered_beta_clock n depth b _ plus (parent_boundary_model_scale n s hs)

end
end ASDExplicitGamma.Native
