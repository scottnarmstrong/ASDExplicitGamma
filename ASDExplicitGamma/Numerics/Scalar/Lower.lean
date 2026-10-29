module

public import ASDExplicitGamma.Numerics.Scalar.Factors
import Mathlib.Tactic.IntervalCases

/-! Generated data (exact rationals), checked by kernel reduction.
No source producer is imported or executed. Every arithmetic tree has its real interpretation
and is evaluated by the sound grid mirror. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Scalar
open Mirror
local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.divPos
local prefix:max "√ₑ " => Expr.sqrt

def lowerA4Expr : Expr := sc (8392611373095084661337932723209/100000000000000000000000000000000)

def lowerA5Expr : Expr := sc (4441091003104432097305984305313/50000000000000000000000000000000)

def lowerXiExpr : Expr := sc (9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057/65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

def lowerS1Expr : Expr := ((√ₑ (sc (156/5))) *ₑ sc (1/729))

def lowerS2Expr : Expr := ((√ₑ (sc (46488/25))) *ₑ sc (1/531441))

def lowerAExpr : Expr := (((lowerS1Expr *ₑ sc (36/25)) +ₑ sc (1/1)) +ₑ (lowerS2Expr *ₑ sc (57/200)))

def lowerKappaExpr : Expr := sc (612499/177147000)

def lowerOscillationExpr : Expr := (lowerS1Expr *ₑ sc (11/25))

def lowerFlatTailExpr : Expr := sc (143/687760767034750685005384250249063588831229009549424064697322725)

def lowerZExpr : Expr := ((√ₑ ((lowerFlatTailExpr /ₑ sc (2/1)))) +ₑ ((lowerS1Expr *ₑ sc (38/125)) *ₑ ((√ₑ ((lowerFlatTailExpr /ₑ sc (2/1)))) +ₑ sc (2/1))))

def lowerKrExpr : Expr := ((lowerS1Expr *ₑ sc (1009/500)) +ₑ (lowerS2Expr *ₑ sc (57/200)))

def lowerEbarExpr : Expr := ((√ₑ ((lowerFlatTailExpr /ₑ sc (2/1)))) +ₑ ((lowerS1Expr *ₑ sc (319/1000)) *ₑ lowerOscillationExpr))

def lowerMExpr : Expr := (((sc (5423/2500) *ₑ sc (2/1)) +ₑ sc (1/1)) +ₑ (√ₑ ((sc (5423/2500) *ₑ sc (2/1)))))

def lowerSmExpr : Expr := (√ₑ ((sc (14103/10000) *ₑ lowerMExpr)))

def lowerTExpr : Expr := (√ₑ (lowerXiExpr))

def lowerHalfExpr : Expr := (√ₑ ((lowerXiExpr /ₑ sc (2/1))))

def quarticDeltaExpr : Expr := ((√ₑ (sc (78/5))) *ₑ sc (467/729000))

def quarticPPExpr : Expr := (((lowerA5Expr /ₑ sc (2/1)) +ₑ sc (1/1)) *ₑ sc (1/2))

def quarticRRExpr : Expr := (lowerMExpr *ₑ (quarticDeltaExpr *ₑ quarticDeltaExpr))

def quarticRDExpr : Expr := (sc (14103/10000) *ₑ (quarticDeltaExpr *ₑ quarticDeltaExpr))

def quarticEbarExpr : Expr := (((√ₑ (quarticPPExpr)) +ₑ (√ₑ (quarticRRExpr))) *ₑ ((√ₑ (quarticPPExpr)) +ₑ (√ₑ (quarticRRExpr))))

def quarticErawExpr : Expr := (lowerMExpr *ₑ (((√ₑ ((sc (1/2) /ₑ (sc (1/1) -ₑ sc (19/25))))) +ₑ quarticDeltaExpr) *ₑ ((√ₑ ((sc (1/2) /ₑ (sc (1/1) -ₑ sc (19/25))))) +ₑ quarticDeltaExpr)))

def quarticGrawExpr : Expr := ((quarticErawExpr +ₑ (sc (14103/10000) *ₑ ((quarticDeltaExpr *ₑ quarticDeltaExpr) +ₑ sc (1/2)))) *ₑ sc (2/1))

def quarticGapExpr : Expr := (((((((lowerA5Expr *ₑ sc (1/2)) /ₑ sc (2/1)) +ₑ ((√ₑ ((quarticPPExpr *ₑ quarticRRExpr))) *ₑ sc (2/1))) +ₑ quarticRRExpr) +ₑ ((√ₑ ((quarticPPExpr *ₑ quarticRDExpr))) *ₑ sc (2/1))) +ₑ quarticRDExpr) +ₑ ((quarticDeltaExpr *ₑ sc (2/1)) *ₑ ((√ₑ (((sc (14103/10000) *ₑ quarticEbarExpr) +ₑ (sc (1/200000000000000000000000) *ₑ quarticErawExpr)))) +ₑ (√ₑ (sc (1/2))))))

def quarticLExpr : Expr := ((((√ₑ (((lowerXiExpr *ₑ sc (1/2)) /ₑ sc (2/1)))) +ₑ (√ₑ ((sc (14103/10000) *ₑ quarticRRExpr)))) +ₑ (√ₑ (((sc (14103/10000) *ₑ quarticGapExpr) +ₑ (sc (1/200000000000000000000000) *ₑ quarticGrawExpr))))) +ₑ (((sc (19/25) *ₑ sc (14103/10000)) +ₑ sc (1/1)) *ₑ quarticDeltaExpr))

def quarticLambdaExpr : Expr := ((quarticLExpr +ₑ (((sc (44/25) *ₑ sc (14103/10000)) *ₑ lowerAExpr) *ₑ (√ₑ ((lowerXiExpr /ₑ sc (2/1)))))) *ₑ (quarticLExpr +ₑ (((sc (44/25) *ₑ sc (14103/10000)) *ₑ lowerAExpr) *ₑ (√ₑ ((lowerXiExpr /ₑ sc (2/1)))))))

def quarticRoughOldExpr : Expr := (((((sc (44/25) *ₑ sc (44/25)) *ₑ sc (2/1)) *ₑ (lowerAExpr *ₑ lowerAExpr)) *ₑ (sc (14103/10000) *ₑ (sc (14103/10000) *ₑ (sc (14103/10000) *ₑ sc (14103/10000))))) +ₑ sc (1/1))

def quarticFlatExpr : Expr := ((sc (14103/10000) +ₑ (sc (1/200000000000000000000000) *ₑ sc (513/500))) *ₑ sc (1557/1000))

def quarticDefectExpr : Expr := (((lowerAExpr *ₑ lowerAExpr) *ₑ sc (3/1)) *ₑ ((sc (14103/10000) *ₑ quarticLambdaExpr) +ₑ ((sc (1/200000000000000000000000) *ₑ sc (513/500)) *ₑ quarticRoughOldExpr)))

def quarticSharpExpr : Expr := ((quarticFlatExpr +ₑ ((√ₑ ((quarticFlatExpr *ₑ quarticDefectExpr))) *ₑ sc (141/50))) +ₑ (sc (44/25) *ₑ quarticDefectExpr))

def quarticChargeExpr : Expr := ((quarticSharpExpr *ₑ sc (187/250000)) /ₑ sc (249813/250000))

def lowerHistoryExpr : Expr := (sc (5423/2500) /ₑ (sc (1/1) -ₑ sc (19/25)))

def lowerColumnMixExpr : Expr := ((sc (19/25) *ₑ (√ₑ (sc (2/1)))) *ₑ sc (205069/19683000))

def lowerX4SquareExpr : Expr := ((sc (14103/10000) *ₑ lowerA4Expr) +ₑ (sc (1/200000000000000000000000) *ₑ lowerHistoryExpr))

def lowerX5SquareExpr : Expr := ((sc (14103/10000) *ₑ lowerA5Expr) +ₑ (sc (1/200000000000000000000000) *ₑ lowerHistoryExpr))

def lowerX4Expr : Expr := (√ₑ (lowerX4SquareExpr))

def lowerL4SquareExpr : Expr := (((sc (14103/10000) *ₑ sc (14103/10000)) *ₑ lowerA4Expr) +ₑ ((((sc (14103/10000) *ₑ sc (2/1)) *ₑ sc (1/200000000000000000000000)) +ₑ (sc (1/200000000000000000000000) *ₑ sc (1/200000000000000000000000))) *ₑ lowerHistoryExpr))

def lowerL4Expr : Expr := (√ₑ (lowerL4SquareExpr))

def lowerDmixExpr : Expr := ((lowerAExpr *ₑ lowerX4Expr) +ₑ (lowerColumnMixExpr *ₑ lowerTExpr))

def lowerSourceSquareExpr : Expr := (((lowerAExpr *ₑ lowerL4Expr) +ₑ (lowerColumnMixExpr *ₑ (√ₑ ((sc (14103/10000) *ₑ lowerXiExpr))))) *ₑ ((lowerAExpr *ₑ lowerL4Expr) +ₑ (lowerColumnMixExpr *ₑ (√ₑ ((sc (14103/10000) *ₑ lowerXiExpr))))))

def lowerParentWeightedExpr : Expr := ((sc (14103/10000) *ₑ lowerXiExpr) +ₑ (((sc (1/200000000000000000000000) *ₑ sc (44/25)) *ₑ sc (14103/10000)) *ₑ sc (5423/2500)))

def lowerUnewExpr : Expr := ((((√ₑ ((((lowerA5Expr /ₑ sc (2/1)) +ₑ sc (1/1)) *ₑ lowerMExpr))) *ₑ sc (2/1)) *ₑ lowerOscillationExpr) +ₑ ((lowerMExpr *ₑ lowerOscillationExpr) *ₑ lowerOscillationExpr))

def lowerTerm1Expr : Expr := ((sc (431/500) *ₑ sc (431/500)) *ₑ lowerUnewExpr)

def lowerTerm2Expr : Expr := lowerSourceSquareExpr

def lowerTerm3Expr : Expr := ((sc (431/500) *ₑ lowerX5SquareExpr) /ₑ sc (2/1))

def lowerTerm4Expr : Expr := (((sc (431/500) *ₑ sc (2/1)) *ₑ ((lowerKrExpr *ₑ lowerX4Expr) +ₑ (lowerColumnMixExpr *ₑ lowerTExpr))) *ₑ lowerHalfExpr)

def lowerTerm5Expr : Expr := (((sc (431/500) *ₑ (√ₑ ((lowerXiExpr *ₑ sc (2/1))))) *ₑ lowerX4Expr) *ₑ lowerEbarExpr)

def lowerTerm6Expr : Expr := ((((sc (431/500) *ₑ sc (2/1)) *ₑ lowerKappaExpr) *ₑ ((√ₑ (sc (2/1))) +ₑ lowerTExpr)) *ₑ lowerHalfExpr)

def lowerTerm7Expr : Expr := ((((sc (431/500) *ₑ sc (2/1)) *ₑ lowerDmixExpr) *ₑ lowerSmExpr) *ₑ lowerOscillationExpr)

def lowerTerm8Expr : Expr := (((sc (431/500) *ₑ sc (2/1)) *ₑ lowerZExpr) *ₑ lowerTExpr)

def lowerTerm9Expr : Expr := (((lowerKappaExpr *ₑ sc (2/1)) *ₑ sc (63/50)) *ₑ ((((√ₑ (sc (2/1))) *ₑ sc (14103/10000)) *ₑ lowerDmixExpr) +ₑ (√ₑ ((lowerSourceSquareExpr *ₑ lowerParentWeightedExpr)))))

def lowerTerm10Expr : Expr := (((((lowerKappaExpr *ₑ sc (2/1)) *ₑ sc (431/500)) *ₑ ((√ₑ (sc (2/1))) +ₑ lowerTExpr)) *ₑ (lowerSmExpr +ₑ sc (1/1))) *ₑ lowerOscillationExpr)

def lowerErrorExpr : Expr := ((((((((((sc (0/1) +ₑ lowerTerm1Expr) +ₑ lowerTerm2Expr) +ₑ lowerTerm3Expr) +ₑ lowerTerm4Expr) +ₑ lowerTerm5Expr) +ₑ lowerTerm6Expr) +ₑ lowerTerm7Expr) +ₑ lowerTerm8Expr) +ₑ lowerTerm9Expr) +ₑ lowerTerm10Expr)

def lowerPrefactorExpr : Expr := ((((sc (431/500) *ₑ sc (2/1)) -ₑ (sc (431/500) *ₑ sc (431/500))) *ₑ (sc (1/2) -ₑ (lowerFlatTailExpr /ₑ sc (4/1)))) -ₑ (((sc (431/500) *ₑ sc (431/500)) *ₑ lowerA5Expr) /ₑ sc (4/1)))

def lowerBaseExpr : Expr := (lowerPrefactorExpr -ₑ (lowerErrorExpr /ₑ sc (2/1)))

def lowerGainExpr : Expr := (lowerBaseExpr -ₑ (quarticChargeExpr /ₑ sc (31/50)))


theorem quartic_charge_kernel_check :
    scalarUpperCheck quarticChargeExpr (16040885867990175/10^18) = true := by
  decide +kernel

/-- Exact outward charge of the original quartic assembly. -/
theorem quartic_charge_lt : evalReal scalarRealEnv quarticChargeExpr <
    (16040885867990175/10^18 : ℝ) := by
  simpa using scalar_upper_sound _ _ quartic_charge_kernel_check

theorem lower_gain_kernel_check :
    scalarUpperCheck (.neg lowerGainExpr) (-(3143488/10^7)) = true := by
  decide +kernel

/-- NU-SC-K-MARGIN: the full ten-term trial minus the original quartic charge. -/
theorem lower_gain_margin :
    (3143488/10^7 : ℝ) ≤ evalReal scalarRealEnv lowerGainExpr ∧
    (12493/40000 : ℝ) < 3143488/10^7 ∧
    (12493/40000 : ℝ) = (31/50)*((1+3*(1/200)/2)/2) := by
  have h := scalar_upper_sound _ _ lower_gain_kernel_check
  change -evalReal scalarRealEnv lowerGainExpr < _ at h
  norm_num at h
  refine ⟨?_, by norm_num, by norm_num⟩
  linarith only [h]

end ASDExplicitGamma.Numerics.Scalar
