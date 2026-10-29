module

public import ASDExplicitGamma.Scalar.SignalClock
public import ASDExplicitGamma.Scalar.Molecular
public import ASDExplicitGamma.Statements.NativeInductionState

/-! The analytic signal interval uses only the strictly earlier scalar corridors. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Algsuperdiff.Section3

/-- Rational endpoint conversion for the nonmolecular target, including a crossing from below. -/
theorem signal_interval_of_corridors (nu B BN sigma a : ℝ)
    (hs : 0 < sigma) (hBN : nu^2 < BN)
    (hclock : BN=a*B) (hal : (2108/1000:ℝ)<a) (hau : a<(2113/1000:ℝ))
    (hl : (31/50:ℝ)*B+(19/50:ℝ)*nu^2 ≤ sigma^2)
    (hu : sigma^2 ≤ nu^2+(13/8:ℝ)*B) :
    (37/250:ℝ) < (BN-B)/(2*sigma^2) ∧ (BN-B)/(2*sigma^2) < (9/10:ℝ) := by
  have ha : 0 < a := by linarith only [hal]
  have hB : 0 < B := by
    rw [hclock] at hBN
    exact (pos_of_mul_pos_right (lt_of_le_of_lt (sq_nonneg nu) hBN) ha.le)
  have hlow := mul_lt_mul_of_pos_right hal hB
  have hhi := mul_lt_mul_of_pos_right hau hB
  rw [← hclock] at hlow hhi
  have hden : 0 < 2*sigma^2 := mul_pos (by norm_num) (sq_pos_of_pos hs)
  constructor
  · rw [lt_div_iff₀ hden]
    nlinarith only [hlow,hhi,hBN,hu,hB]
  · rw [div_lt_iff₀ hden]
    nlinarith only [hhi,hl,hB,sq_nonneg nu]

/-- SC-UPPER-SIGNAL-INTERVAL in the true running frame, with the source floor length. -/
theorem sigmaBar_signal_interval (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hgamma0 : 0 < M.gamma) (hgamma : M.gamma ≤ 17/50000) (hstate : nativeInductionState M h n)
    (hBN : M.nu^2 < shellVarianceSum h M.gamma (n+⌊(17/50:ℝ)/M.gamma⌋)) :
    let N := n+⌊(17/50:ℝ)/M.gamma⌋
    let z := (shellVarianceSum h M.gamma N-shellVarianceSum h M.gamma n)/
      (2*(Annealed.sigmaBar M n : ℝ)^2)
    (37/250:ℝ)<z ∧ z<(9/10:ℝ) := by
  obtain ⟨_,_,_,_,_,_,hl,hu⟩ := hstate
  obtain ⟨hal,hau⟩ := signal_clock_ratio M.gamma hgamma0 hgamma
  exact signal_interval_of_corridors M.nu _ _ _ _ (Annealed.sigmaBar M n).property
    hBN (shellVarianceSum_add h M.gamma n _) hal hau hl hu

end ASDExplicitGamma.Scalar
