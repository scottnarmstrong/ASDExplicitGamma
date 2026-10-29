module

public import ASDExplicitGamma.Numerics.Model.BflatJ0
public import ASDExplicitGamma.Numerics.Model.BflatJ1
public import ASDExplicitGamma.Numerics.Model.BflatJ2
public import ASDExplicitGamma.Numerics.Model.BflatJ3
public import ASDExplicitGamma.Numerics.Model.BflatJ4
public import ASDExplicitGamma.Numerics.Model.BflatJ5

/-! NU-MO-BFLAT-CAPS: six strict caps for the actual q3 covariance-integral projections.
The 2944 one-dimensional modes use certified signed recurrence intervals. Pair symmetry
reduces the correction to 42089 positive rational block charges. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Model

/-- The shell lengths are exactly `3⁻ʲ`, with the six source mode cutoffs. -/
theorem bflat_caps :
    2-2*q3Projection 0 32 < (1119/1000 : ℝ) ∧
    2-2*q3Projection 1 32 < (47/100 : ℝ) ∧
    2-2*q3Projection 2 64 < (17/100 : ℝ) ∧
    2-2*q3Projection 3 256 < (29/500 : ℝ) ∧
    2-2*q3Projection 4 512 < (1/50 : ℝ) ∧
    2-2*q3Projection 5 2048 < (7/1000 : ℝ) :=
  ⟨by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using bflat_cap_j0, by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using bflat_cap_j1,
    by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using bflat_cap_j2, by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using bflat_cap_j3,
    by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using bflat_cap_j4, by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using bflat_cap_j5⟩

end ASDExplicitGamma.Numerics.Model
