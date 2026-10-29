module

public import ASDExplicitGamma.Scalar.UpperCellEnergyHistoryEnvelope

/-! Joining the two source branches without an independence assumption. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

/-- The prescribed local and full-history comparisons imply the literal
all-event polynomial payment, for any load (including a random fresh load).
The branch estimates are explicit analytic inputs, not a physical export. -/
theorem upper_cell_all_event_comparison_algebra
    (M F theta p2 Enew Eold : ℝ)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hthetaM : theta ≤ M)
    (hp2 : 0 ≤ p2) (hEold : 0 ≤ Eold) (hEcap : Eold ≤ M*p2)
    (hsmall : theta*F ≤ 2/5 → Enew ≤ (1+(5/4:ℝ)*(theta*F))*Eold)
    (hlarge : Enew ≤ M*(1+3*M*F)*(1+2*F+4*F^2)*p2) :
    Enew ≤ Eold+6*M^2*F*(1+2*F+4*F^2)*p2 := by
  have hpoly : 1 ≤ 1+2*F+4*F^2 := by nlinarith only [hF,sq_nonneg F]
  have hpoly0 : 0 ≤ 1+2*F+4*F^2 := le_trans zero_le_one hpoly
  have hMF := mul_nonneg hM hF
  have hthetaF := mul_le_mul_of_nonneg_right hthetaM hF
  by_cases hcase : theta*F ≤ 2/5
  · have hprod := mul_le_mul hthetaF hEcap hEold hMF
    have hgain : (5/4:ℝ)*(theta*F)*Eold ≤ (5/4:ℝ)*M^2*F*p2 := by
      nlinarith only [hprod]
    have hpolyGain := mul_le_mul_of_nonneg_left hpoly
      (show 0 ≤ 6*M^2*F*p2 by positivity)
    have hbase : (5/4:ℝ)*M^2*F*p2 ≤ 6*M^2*F*p2 := by
      have hh : 0 ≤ M^2*F*p2 := by positivity
      linarith only [hh]
    have hh := hsmall hcase
    nlinarith only [hh,hgain,hbase,hpolyGain]
  · have hMFsmall : (2/5:ℝ) ≤ M*F := (le_of_not_ge hcase).trans hthetaF
    have hscaled := mul_le_mul_of_nonneg_left hMFsmall hM
    have hbase : M*(1+3*M*F) ≤ 6*M^2*F := by
      have hn : 0 ≤ M^2*F := by positivity
      nlinarith only [hscaled,hn]
    have hpay := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase hpoly0) hp2
    exact hlarge.trans (hpay.trans (le_add_of_nonneg_left hEold))

end ASDExplicitGamma.Scalar
