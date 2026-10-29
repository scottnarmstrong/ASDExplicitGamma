module
public import ASDExplicitGamma.Numerics.Native.Heat009Complete
public import ASDExplicitGamma.Numerics.Native.Heat049Complete
public import ASDExplicitGamma.Numerics.Native.History
public import ASDExplicitGamma.Numerics.Native.HistoryConstants

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeRootReturn : ℚ := (1006272492144223490856435893287948857761694389356791537669601999618398132840355802850711273781335549/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeBufferMeanReturn : ℚ := (158639007176644525640753418649430464015596405264832169149275076799437972196132795625488273197051481/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeRootReturn_formula : nativeShiftedFrame 9 nativeHeat009Result.1 = nativeRootReturn := by
  decide +kernel

theorem nativeRootReturn_valid : nativeRootValid (nativeHeat009Result.1*(nativeHeat009Result.1+8)) 2 = true := by
  decide +kernel

theorem nativeRootReturn_domain : 0 ≤ (11/10)*(2*nativeGamma*(9 : ℕ)) ∧ (11/10)*(2*nativeGamma*(9 : ℕ)) < 1 := by
  decide +kernel

theorem nativeRootReturn_bound : nativeFrameReal (((11/10)*(2*nativeGamma*(9 : ℕ)) : ℚ) : ℝ) (nativeHeat009Result.1 : ℝ) ≤ (nativeRootReturn : ℝ) := by
  have h := nativeShiftedFrame_sound 9 nativeHeat009Result.1 nativeRootReturn_domain nativeRootReturn_valid
  simpa only [nativeRootReturn_formula] using h

theorem nativeBufferMeanReturn_formula : nativeUp (nativeE (98*nativeGamma)*nativeHeat049Result.2) = nativeBufferMeanReturn := by
  decide +kernel

theorem nativeBufferMeanReturn_bound : (nativeE (98*nativeGamma) : ℝ)*(nativeHeat049Result.2 : ℝ) ≤ (nativeBufferMeanReturn : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).2 (nativeUp_ge (nativeE (98*nativeGamma)*nativeHeat049Result.2))
  simpa only [nativeBufferMeanReturn_formula,Rat.cast_mul] using h

theorem nativeRootReturn_caps : nativeRootReturn < (2012545/10^7 : ℚ) ∧ (2012545/10^7 : ℚ) < 2013/10000 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Native
