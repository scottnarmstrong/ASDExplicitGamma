module

public import ASDExplicitGamma.Native.HeatVHEATDriftAverage
public import ASDExplicitGamma.Native.HeatVHEATDriftShells

/-! Complete drift expectation: exact leading moments plus the correlated
first-line VHEAT bill, with actual finite shell sums retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The full common-bank polynomial before taking the child average. -/
def heatVHEATDriftFull (k : ℕ) (e K C b R A T : ℝ) : ℝ :=
  (k:ℝ)*e*(2*K*(b+R)+C*(b+R)^2)*(A^(k-1)*(T+4))

end
end ASDExplicitGamma.Native
