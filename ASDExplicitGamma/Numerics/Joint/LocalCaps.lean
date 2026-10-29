module

public import ASDExplicitGamma.Numerics.Scalar.Factors
public import ASDExplicitGamma.Numerics.Scalar.Readable

/-! NU-MA-LOCAL-CAPS: half-gain constants.
Panel denominators/radicands are already checked in MainReturn's successful formula replays.
-/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Joint
open Mirror Scalar

local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.divPos
local prefix:max "√ₑ " => Expr.sqrt

def localC0Expr : Expr :=
  √ₑ (sc 8 *ₑ sqrtThreeExpr /ₑ (piSquareExpr *ₑ (sc 9 -ₑ sqrtThreeExpr)))
def localRExpr : Expr := sc 2 /ₑ piExpr +ₑ sc (1/2)
def localR0Expr : Expr := localC0Expr +ₑ sc (1/2)
def halfGainExpr : Expr := sc (1/2) +ₑ alphaExpr
def halfGainStarExpr : Expr :=
  (sc 1 +ₑ √ₑ (sc 1 +ₑ sc 4 *ₑ (halfGainExpr *ₑ halfGainExpr))) /ₑ sc 2

theorem local_caps_kernel_check :
    scalarUpperCheck cOneExpr (304/1000) = true ∧
    scalarUpperCheck localC0Expr (440/1000) = true ∧
    scalarUpperCheck (localC0Expr *ₑ cOneExpr) (13376/100000) = true ∧
    scalarUpperCheck (cOneExpr +ₑ localRExpr) (1440/1000) = true ∧
    scalarUpperCheck (cOneExpr *ₑ localR0Expr) (285/1000) = true ∧
    scalarUpperCheck (sc 1 /ₑ sqrtThreeExpr +ₑ cOneExpr +ₑ localRExpr) (2018/1000) = true ∧
    scalarUpperCheck (sc 1 /ₑ piExpr) (319/1000) = true ∧
    scalarUpperCheck halfGainExpr (1260/1000) = true ∧
    scalarUpperCheck halfGainStarExpr (1856/1000) = true ∧
    scalarUpperCheck (sc 2 /ₑ piExpr) (637/1000) = true := by
  decide +kernel

/-- All ten source coefficients, with the corrected half-gain D_f. -/
theorem local_caps :
    let s := Real.sqrt 3
    let c1 := Real.sqrt ((s-1)/(Real.pi^2*(1-s/9)))
    let c0 := Real.sqrt (8*s/(Real.pi^2*(9-s)))
    let R := 2/Real.pi+1/2
    let R0 := c0+1/2
    let Df := 1/2+(3 : ℝ)^(-(1/4 : ℝ))
    c1 < 304/1000 ∧ c0 < 440/1000 ∧ c0*c1 < 13376/100000 ∧
    c1+R < 1440/1000 ∧ c1*R0 < 285/1000 ∧
    1/s+c1+R < 2018/1000 ∧ 1/Real.pi < 319/1000 ∧
    Df < 1260/1000 ∧ (1+Real.sqrt (1+4*Df^2))/2 < 1856/1000 ∧
    2/Real.pi < 637/1000 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := local_caps_kernel_check
  have H0 := scalar_upper_sound _ _ h0
  have H1 := scalar_upper_sound _ _ h1
  have H2 := scalar_upper_sound _ _ h2
  have H3 := scalar_upper_sound _ _ h3
  have H4 := scalar_upper_sound _ _ h4
  have H5 := scalar_upper_sound _ _ h5
  have H6 := scalar_upper_sound _ _ h6
  have H7 := scalar_upper_sound _ _ h7
  have H8 := scalar_upper_sound _ _ h8
  have H9 := scalar_upper_sound _ _ h9
  rw [← alpha_source_eq]
  norm_num [cOneExpr, localC0Expr, localRExpr, localR0Expr, halfGainExpr,
    halfGainStarExpr, alphaExpr, fourthThreeExpr, sqrtThreeExpr, piSquareExpr,
    piExpr, sc, evalReal, scalarRealEnv, ← pow_two] at H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 ⊢
  exact ⟨H0,H1,H2,H3,H4,H5,H6,H7,H8,H9⟩

/-- Keep the q3 covariance moments separate from the main trial loads. -/
theorem local_covariance_identities :
    (31.2 : ℚ) = 2*(78/5) ∧
    (1859.52 : ℚ) = 2*((3432/5)+(78/5)^2) ∧
    (128 : ℕ) ≥ 5*20 ∧ (∏ i ∈ Finset.range 64, (2*i+1 : ℕ)) < 48^64 := by
  decide +kernel

/-- Source row/column majorants for arbitrary nonnegative covariance scales. -/
theorem local_row_column_majorants (A2 A4 : ℝ) :
    let s := Real.sqrt 3
    let c1 := Real.sqrt ((s-1)/(Real.pi^2*(1-s/9)))
    let c0 := Real.sqrt (8*s/(Real.pi^2*(9-s)))
    let R := 2/Real.pi+1/2
    let R0 := c0+1/2
    (2/Real.pi)*Real.sqrt ((156/5)*A2)+c0*c1*Real.sqrt ((46488/25)*A4) ≤
      (637/1000)*Real.sqrt ((156/5)*A2)+(440/1000)*(304/1000)*Real.sqrt ((46488/25)*A4) ∧
    (1/s+c1+R)*Real.sqrt ((156/5)*A2)+c1*R0*Real.sqrt ((46488/25)*A4) ≤
      (2018/1000)*Real.sqrt ((156/5)*A2)+(285/1000)*Real.sqrt ((46488/25)*A4) := by
  obtain ⟨_,_,hp,_,_,hr,_,_,_,hd⟩ := local_caps
  dsimp only
  constructor
  · have hp' := mul_le_mul_of_nonneg_right hp.le (Real.sqrt_nonneg ((46488/25)*A4))
    have hd' := mul_le_mul_of_nonneg_right hd.le (Real.sqrt_nonneg ((156/5)*A2))
    linarith only [hp',hd']
  · have h := local_caps
    have hc := mul_le_mul_of_nonneg_right h.2.2.2.2.1.le (Real.sqrt_nonneg ((46488/25)*A4))
    have hr' := mul_le_mul_of_nonneg_right hr.le (Real.sqrt_nonneg ((156/5)*A2))
    exact add_le_add hr' hc

/-- The exact endpoint mixed-polynomial comparisons for the distinct OLD local bank. -/
theorem mixed_polynomial_gates :
    ∀ k ∈ Finset.range 4,
      ((1+(1/10^24 : ℚ)/(14103/10000))^k)*((3683/2500)+(3/10^46))-3683/2500 <
        12*(1/10^24 : ℚ) := by
  decide +kernel

end ASDExplicitGamma.Numerics.Joint
