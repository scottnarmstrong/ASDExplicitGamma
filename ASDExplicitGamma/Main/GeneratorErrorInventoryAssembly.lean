module

public import ASDExplicitGamma.Main.ErrorCorrected

/-! The seven-row scalar assembly of the main error.
The linear row carries `(AG - 2 b_e) G`, the bottom covariance (FOURLOAD) row carries
`2 b_e G`, and the covariance row carries `√(v + v q/4)`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

/-- Add the seven producer rows into the corrected source error. -/
theorem main_generator_error_inventory_bound_of_rows
    (v a f H xi q linearRow squareRow covarianceRow oscillationRow parentGapRow
      bottomRow remainderRow : ℝ)
    (hLinear : linearRow ≤ mainLinearError v H xi q +
      (mainFourLoadAG v H xi q - 2 * mainBe v q) * mainG xi)
    (hSquare : squareRow ≤ mainLoadZ v a f H xi (mainKd v) ^ 2)
    (hCovariance : covarianceRow ≤
      v / 2 * mainR1 a f H ^ 2 +
        2 * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) *
          mainT0 xi * Real.sqrt (v + v * q / 4) +
        Real.sqrt 2 * mainT0 xi * mainR1 a f H * mainEcov v q)
    (hOscillation : oscillationRow ≤
      2 * mainLoadD v a f H xi (mainKd v) * mainLoadQ H (mainOp v) (mainOm v))
    (hParentGap : parentGapRow ≤ 2 * mainBe v q * mainV xi f)
    (hBottom : bottomRow ≤ 2 * mainBe v q * mainG xi)
    (hRemainder : remainderRow ≤
      2 * mainKd v * (63 / 50) *
        (Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) +
          mainLoadZ v a f H xi (mainKd v) * mainRec xi)) :
    linearRow + squareRow + covarianceRow + oscillationRow + parentGapRow +
      bottomRow + remainderRow ≤ mainSourceError' v a f H xi q := by
  have h := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    hLinear hSquare) hCovariance) hOscillation) hParentGap) hBottom) hRemainder
  refine h.trans (le_of_eq ?_)
  unfold mainSourceError' mainError'
  ring

end ASDExplicitGamma.Main
