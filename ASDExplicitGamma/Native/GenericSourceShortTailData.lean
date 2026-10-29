module

public import ASDExplicitGamma.Native.GenericSourceShortTail
public import ASDExplicitGamma.Numerics.Native.State
public import Mathlib.Tactic.FinCases

/-! Rational payments for the entire post-gap-64 tail and the complete
rare-trace companion sum. All physical tail estimates remain separate. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Native

/-- Exact rational OLD history weight at the endpoint. -/
def nativeSourceRationalHistoryWeight : ℚ := (759836/1000000)^2*nativeE (2*nativeGamma)

/-- The unrounded rational raw endpoint, including the averaged initial
allowance, every p20 term and the complete quadratic frame correction. -/
def nativeSourceRationalRawEndpoint (height : ℕ) : ℚ :=
  let e := (9/2)*nativeGamma*nativeE (2*nativeGamma*height)
  let f := 4*((1009309/500000)+nativeGamma*(32474*(height+1)+11483216))*
    nativeE ((2*height+4)*nativeGamma)
  let H := e*((78*height+76*(521/1000))*nativeB+2*(521/1000)*nativeB*f+
    ((1975/1000)+38*(1565/1000))*nativeB^2*f)
  nativeE (2*nativeGamma*height)*
    ((1+(1/1000:ℚ))*(nativeAvg*nativeA+H)+8*(1+1000)*((11/10)*nativeGamma*height)^2)

/-- The rational weight is the exact endpoint of the real source weight. -/
theorem native_source_rational_history_weight_cast :
    (nativeSourceRationalHistoryWeight:ℝ)=nativeSourceHistoryWeight (17/50000) := by
  norm_num [nativeSourceRationalHistoryWeight,nativeSourceHistoryWeight,nativeSourceAlphaPlus,nativeE,nativeGamma,
    nativeSourceE]

/-- The rational raw endpoint is exactly the real finite raw profile. -/
theorem native_source_rational_raw_endpoint_cast (height : ℕ) :
    (nativeSourceRationalRawEndpoint height:ℝ)=nativeSourceGenericRawFrame (17/50000) 1 height := by
  simp only [nativeSourceRationalRawEndpoint,nativeSourceGenericRawFrame,nativeSourceWeakFrame,
    nativeSourceGenericRawFrameInput,nativeSourceGenericRawIncrement,nativeSourceRawMomentIncrement,
    nativeSourceGenericVarianceCap,nativeSourceGenericFullResponseCap,nativeSourceAverageFactor,
    nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128,nativeSourceFrameEta,nativeSourceE,
    nativeGamma,nativeE,nativeAvg,nativeRoot,nativeA,nativeB,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast,
    Nat.cast_add,Nat.cast_one,mul_one]
  ring

/-- A positive 10^-5 allowance pays the complete mean tail after gap 64
in each of the six source rows, using its entire quadratic-geometric sum. -/
theorem native_source_short_tail_endpoint_numeric (r : Fin 6) :
    25*nativeSourceRationalHistoryWeight^(56-r.val)*nativeSourceRationalRawEndpoint 65 ≤
      (1/100000:ℚ) := by
  fin_cases r <;> decide +kernel

/-- A positive whole-series allowance for the rare L20 trace companion. -/
theorem native_source_whole_trace_endpoint_numeric (r : Fin 6) :
    25*nativeSourceRationalRawEndpoint (9+r.val) ≤ (10^12:ℚ) := by
  fin_cases r <;> decide +kernel

end ASDExplicitGamma.Native
