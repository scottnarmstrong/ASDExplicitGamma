module

public import ASDExplicitGamma.Numerics.Scalar.Factors
public import ASDExplicitGamma.Numerics.Scalar.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Readable forms of the coercivity, factor and chaining-row certificates, with the expression interpreter unfolded. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Scalar
open Mirror

/-- The coercivity bound. The negative powers of three have their positive-root meanings. -/
theorem f7_coercivity_readable :
    let s := Real.sqrt 3
    let c0 := Real.sqrt (8*s/(9-s))/Real.pi
    let c0' := Real.sqrt (s/(Real.pi^2*(1-s/9)))
    let c1 := Real.sqrt ((s-1)/(Real.pi^2*(1-s/9)))
    let C1 := c1+2/Real.pi+1/2
    c0' < (467/1000 : ℝ) ∧
    (2/Real.pi)*Real.sqrt (78/5) < (503/200 : ℝ) ∧
    c0*c1*Real.sqrt (23244/25) < (2031/500 : ℝ) ∧
    1/s+C1 < (1009/500 : ℝ) ∧
    1/Real.pi < (319/1000 : ℝ) ∧
    1+1/Real.sqrt s < (44/25 : ℝ) ∧
    1/2+1/Real.sqrt s < (63/50 : ℝ) := by
  have h := f7_coercivity
  norm_num [cZeroPrimeExpr, cZeroExpr, cOneExpr, largeCOneExpr,
    fSevenDerivativeExpr, fSevenProductExpr, fSevenFrameExpr, piSquareExpr,
    alphaExpr, fourthThreeExpr, sqrtThreeExpr, piExpr, sc, evalReal,
    scalarRealEnv, ite_true, Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul,
    ← pow_two] at h ⊢
  exact h

/-- The factor bounds, retaining every radical of the joint-disk pure factor. -/
theorem f7_factors_readable :
    let alpha := 1/Real.sqrt (Real.sqrt 3)
    Real.sqrt (alpha^2+1/2+Real.sqrt (1/4+alpha^2)) < (141/100 : ℝ) ∧
    Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt
      (1+Real.sqrt 15)))))) < (513/500 : ℝ) ∧
    (3/2 : ℝ)+(467/1000 : ℝ)^2*(936/5)/729 < 1557/1000 := by
  have h := f7_factors
  norm_num [pureFactorExpr, mixedFactorExpr, flatFactorExpr, alphaExpr,
    fourthThreeExpr, sqrtThreeExpr, sc, evalReal, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_add, Rat.cast_mul, Rat.cast_pow, ← pow_two] at h ⊢
  exact h

/-- The chaining-row bound in the source's μ/τ notation. -/
theorem f8_row_readable :
    let mu1 := (312/5 : ℝ)
    let mu2 := (141648/25 : ℝ)
    let mu3 := (90462528/125 : ℝ)
    let A1 := Real.sqrt (12*mu1)+2*Real.sqrt (2*mu1)
    let A2 := (3/2)*Real.sqrt (12*mu2)+6*Real.sqrt (2*mu2)
    let A3 := (1/2)*Real.sqrt (12*mu3)+4*Real.sqrt (2*mu3)
    A1+A2/81+A3/6561 < 64 := by
  have h := f8_row
  norm_num [fEightRowExpr, sc, evalReal, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_mul] at h ⊢
  exact h

/-- The geometry bound: the fourth-root representation of the source coefficient. -/
theorem f8_geometry_readable :
    let CP := Real.sqrt (Real.sqrt 3)/(Real.pi^2*(1-Real.sqrt (Real.sqrt 3)/9))
    CP < (8/45 : ℝ) ∧ Real.sqrt 3*CP*(156/5) < (728/75 : ℝ) ∧
      (728/75 : ℝ) < 10 ∧ (7 : ℕ)^5 < 3^9 := by
  have h := f8_geometry
  norm_num [poincareExpr, residualGeometryExpr, fourthThreeExpr, sqrtThreeExpr,
    piSquareExpr, piExpr, scalarRealEnv, ite_true, sc, evalReal,
    Rat.cast_div, Rat.cast_ofNat, ← pow_two] at h ⊢
  exact h

/-- The positive fourth root is the source power of three. -/
theorem fourth_root_three_eq : Real.sqrt (Real.sqrt 3) = (3 : ℝ)^(1/4 : ℝ) := by
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- The source's alpha equals the reciprocal fourth root used by the grid formula. -/
theorem alpha_source_eq : 1/Real.sqrt (Real.sqrt 3) = (3 : ℝ)^(-(1/4 : ℝ)) := by
  rw [fourth_root_three_eq, Real.rpow_neg (by norm_num), one_div]

/-- Six successive positive square roots are precisely the 64th root. -/
theorem sixty_fourth_root_eq (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt x))))) =
      x^(1/64 : ℝ) := by
  simp only [Real.sqrt_eq_rpow]
  repeat rw [← Real.rpow_mul hx]
  norm_num

/-- The factor bounds in exact fractional-power notation. -/
theorem f7_factors_source :
    let alpha := (3 : ℝ)^(-(1/4 : ℝ))
    Real.sqrt (alpha^2+1/2+Real.sqrt (1/4+alpha^2)) < (141/100 : ℝ) ∧
    (1+Real.sqrt 15)^(1/64 : ℝ) < (513/500 : ℝ) ∧
    (3/2 : ℝ)+(467/1000 : ℝ)^2*(936/5)/729 < 1557/1000 := by
  have h := f7_factors_readable
  dsimp only at h ⊢
  rw [alpha_source_eq, sixty_fourth_root_eq _ (by positivity)] at h
  exact h

/-- The geometric negative power in the chaining-row denominator. -/
theorem three_negative_seven_quarters :
    (3 : ℝ)^(-(7/4 : ℝ)) = Real.sqrt (Real.sqrt 3)/9 := by
  rw [show (-(7/4 : ℝ)) = (1/4 : ℝ)-(2 : ℕ) by norm_num,
    Real.rpow_sub_natCast (by norm_num), ← fourth_root_three_eq]
  norm_num

/-- The negative three-halves power in the coercivity denominator. -/
theorem three_negative_three_halves :
    (3 : ℝ)^(-(3/2 : ℝ)) = Real.sqrt 3/9 := by
  rw [show (-(3/2 : ℝ)) = (1/2 : ℝ)-(2 : ℕ) by norm_num,
    Real.rpow_sub_natCast (by norm_num), ← Real.sqrt_eq_rpow]
  norm_num

/-- The coercivity bound in exact power notation. -/
theorem f7_coercivity_source :
    let s := Real.sqrt 3
    let c0 := Real.sqrt (8*s/(9-s))/Real.pi
    let c0' := Real.sqrt (s/(Real.pi^2*(1-(3 : ℝ)^(-(3/2 : ℝ)))))
    let c1 := Real.sqrt ((s-1)/(Real.pi^2*(1-s/9)))
    let C1 := c1+2/Real.pi+1/2
    c0' < (467/1000 : ℝ) ∧
    (2/Real.pi)*Real.sqrt (78/5) < (503/200 : ℝ) ∧
    c0*c1*Real.sqrt (23244/25) < (2031/500 : ℝ) ∧
    1/s+C1 < (1009/500 : ℝ) ∧
    1/Real.pi < (319/1000 : ℝ) ∧
    1+(3 : ℝ)^(-(1/4 : ℝ)) < (44/25 : ℝ) ∧
    1/2+(3 : ℝ)^(-(1/4 : ℝ)) < (63/50 : ℝ) := by
  simpa only [three_negative_three_halves, ← alpha_source_eq] using f7_coercivity_readable

/-- The geometry bound in fractional-power notation. -/
theorem f8_geometry_source :
    let CP := (3 : ℝ)^(1/4 : ℝ)/(Real.pi^2*(1-(3 : ℝ)^(-(7/4 : ℝ))))
    CP < (8/45 : ℝ) ∧ Real.sqrt 3*CP*(156/5) < (728/75 : ℝ) ∧
      (728/75 : ℝ) < 10 ∧ (7 : ℕ)^5 < 3^9 := by
  simpa only [three_negative_seven_quarters, ← fourth_root_three_eq] using
    f8_geometry_readable

end ASDExplicitGamma.Numerics.Scalar
