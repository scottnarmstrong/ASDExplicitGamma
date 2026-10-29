module

public import ASDExplicitGamma.Native.GenericSourceChildRationalData
public import ASDExplicitGamma.Native.GenericSourceChildUniform
public import ASDExplicitGamma.Native.GenericSourceChildBandMeanCap

/-! Exact real meanings of the auxiliary rational refined-mean endpoints. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Native
noncomputable section

/-- The rational endpoint variance is exactly the generic finite variance
at gamma zero, rather than a separately supplied numerical bound. -/
theorem native_source_child_rational_variance_cast (height : ℕ) :
    (nativeSourceChildRationalVariance height:ℝ)=nativeSourceGenericVarianceCap (17/50000) height := by
  simp only [nativeSourceChildRationalVariance,nativeGamma,nativeE,
    Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_ofNat,Rat.cast_natCast,
    nativeSourceGenericVarianceCap,nativeSourceE]
  ring

/-- The rational mean rate is the literal actual child drift coefficient. -/
theorem native_source_child_rational_C_cast :
    (nativeSourceChildRationalC:ℝ)=nativeSourceChildMeanC := by
  norm_num [nativeSourceChildRationalC,nativeSourceChildMeanC,nativeB]

/-- The finite rational frame is the exact endpoint E factor. -/
theorem native_source_child_rational_frame_cast (height : ℕ) :
    (nativeE (2*nativeGamma*height):ℝ)=nativeSourceE (17/50000) height := by
  simp only [nativeE,nativeGamma,Rat.cast_div,Rat.cast_sub,Rat.cast_mul,
    Rat.cast_ofNat,Rat.cast_natCast,nativeSourceE]
  ring

/-- The rational positive numerator retains the exact forcing terms of the
child scalar ODE, including both rare products and the inverse-trace reserve. -/
theorem native_source_child_rational_return_cast (high : Bool) (height : ℕ) :
    (nativeSourceChildRationalReturn high height:ℝ)=
      nativeSourceE (17/50000) height*
        (((nativeQstar:ℝ)+nativeSourceChildMeanL height (3/10^46:ℝ)
          (nativeSourceChildAuxNorm high:ℝ) (nativeSourceGenericVarianceCap (17/50000) height))/
          (1-nativeSourceGenericVarianceCap (17/50000) height*nativeSourceChildMeanC)) := by
  simp only [nativeSourceChildRationalReturn,nativeSourceChildRationalRare,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,
    Rat.cast_natCast,native_source_child_rational_variance_cast,native_source_child_rational_C_cast,
    native_source_child_rational_frame_cast]
  norm_num only [nativeB,nativeEps,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow]
  unfold nativeSourceChildMeanL nativeSourceChildMeanR nativeSourceChildMeanC
  ring

end
end ASDExplicitGamma.Native
