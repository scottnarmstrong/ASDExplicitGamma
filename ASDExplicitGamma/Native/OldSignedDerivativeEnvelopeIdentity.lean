module

public import ASDExplicitGamma.Native.OldSignedCellDerivativeBounds

/-! Exact expanded form of the OLD derivative spatial envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native

/-- The quadratic weak-root product is paid as W before expectation. -/
theorem old_signed_derivative_envelope_identity (W kd ka D B op J N E : ℝ) (hW : 0≤W) :
    2*kd*(Real.sqrt (2*W)*(Real.sqrt J+(D*B)*op)+
      (D*B)*(Real.sqrt 2+Real.sqrt (2*W))*(ka*Real.sqrt W)+
      (Real.sqrt 2+Real.sqrt (2*W))*(Real.sqrt N+Real.sqrt E))=
    (2*kd*Real.sqrt 2)*(Real.sqrt W*Real.sqrt J+Real.sqrt W*Real.sqrt N+Real.sqrt W*Real.sqrt E+
      (D*(op+ka))*(B*Real.sqrt W)+(D*ka)*(B*W)+Real.sqrt N+Real.sqrt E) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  ring_nf
  rw [Real.sq_sqrt hW]
  ring

end ASDExplicitGamma.Native
