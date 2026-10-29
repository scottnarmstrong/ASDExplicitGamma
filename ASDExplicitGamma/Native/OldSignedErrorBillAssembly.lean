module

public import ASDExplicitGamma.Native.OldSignedErrorBill

/-! Exact scalar collection of the nine signed-trial estimates into AN
(5.1). This is algebra only; all factors stay on their physical cell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Response Scalar
noncomputable section

/-- The literal error bill is the sum of the flat, source, mixed,
derivative and covariance bills used in the actual trial assembly. -/
theorem old_signed_error_bill_split (B M theta V G d x y Oplus Ominus betaPlus betaMinus kappa : ℝ) :
    oldSignedErrorBill B M theta V G d x y Oplus Ominus betaPlus betaMinus kappa=
      (2*Real.sqrt (6*theta)*(x*Oplus+y*Ominus)+M*(Oplus^2+Ominus^2))+B*d^2+
      2*(d*(Real.sqrt (6*theta)*x+(M+1)*Oplus))+
      2*(d*(Real.sqrt (6*theta)*y+(M+1)*Ominus))+
      2*(kappa*G*(Real.sqrt theta*x+(1+inverseHistoryDiscount)*B*Oplus))+
      2*(kappa*(Real.sqrt 2+G)*((1+inverseHistoryDiscount)*B*d))+
      2*(kappa*(Real.sqrt 2+G)*(Real.sqrt theta*y+(Real.sqrt (B*M)+1)*Ominus))+
      2*(betaPlus*V)+2*(betaMinus*G) := by
  unfold oldSignedErrorBill
  ring

end
end ASDExplicitGamma.Native
