module

public import ASDExplicitGamma.Native.OldSignedQ1PaymentDegree

/-! Pure square-root algebra collecting all four q1 error blocks. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Mirror
noncomputable section

/-- Abstract endpoint values, with history parameters kept opaque. -/
def oldSignedQ1AbstractEndpoint (v a2 ka kd op om beta X Y A D c a : ℝ) : ℕ → ℝ
  | 0 => v
  | 1 => Real.sqrt v
  | 2 => op^2
  | 3 => om^2
  | 4 => ka
  | 5 => kd
  | 6 => ((3683/2500:ℝ)+1)^2*op^2+(3683/2500:ℝ)*A*om^2
  | 7 => beta
  | 8 => X
  | 9 => Y
  | 10 => A
  | 11 => D
  | 12 => c
  | 13 => a
  | 14 => a2
  | 15 => kd
  | _ => 0

/-- The collected panel formula after the physical x/y/ybar substitutions. -/
def oldSignedQ1CollectedBill (v a2 ka kd op om beta X Y A D c a : ℝ) : ℝ :=
  let B := (3683/2500:ℝ)
  let s := Real.sqrt 2
  let x := Real.sqrt (2*v)
  let y := Real.sqrt v
  let w := Real.sqrt X
  let q := Real.sqrt ((B+1)^2*op^2+B*A*om^2)
  let flat := s*w*x*op+2*s*Real.sqrt Y*y*om+B*op^2+A*om^2+2*kd*(w*y+s*c*om)
  let AV := 2*ka*w*Real.sqrt v+2*ka*q+2*kd*D*ka*B*s
  let AG := 2*kd*(w*(x+y)/s+D*B*op+c*om)
  let err := flat+ka^2*B*X+AV*w+AG*s*w+2*kd*D*ka*B*X+2*beta*w+2*beta*s*w
  let aff := v/2*a+2*v*(B-1)+(4+2*s)*(156/5)*a2/9
  aff+err

/-- No derivative or covariance summand is discarded in collecting the bill. -/
theorem old_signed_q1_payment_algebra (v a2 ka kd op om beta X Y A D c a : ℝ)
    (hv : 0 ≤ v) (hop : 0 ≤ op) (hom : 0 ≤ om) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    evalReal (oldSignedQ1AbstractEndpoint v a2 ka kd op om beta X Y A D c a)
      oldSignedQ1PaymentExpr=oldSignedQ1CollectedBill v a2 ka kd op om beta X Y A D c a := by
  simp only [oldSignedQ1PaymentExpr,oldSignedQ1AffineExpr,oldSignedQ1FlatExpr,
    oldSignedQ1SourceExpr,oldSignedQ1DerivativeExpr,oldSignedQ1BoundaryExpr,
    evalReal,oldSignedQ1AbstractEndpoint,oldSignedQ1CollectedBill,Rat.cast_ofNat,Rat.cast_div,
    Real.sqrt_sq hop,Real.sqrt_sq hom,Real.sqrt_mul hX,Real.sqrt_mul hY,
    Real.sqrt_div (mul_nonneg hX hv),Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num)]
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  ring_nf
  simp only [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sq_sqrt hX]
  ring

end
end ASDExplicitGamma.Native
