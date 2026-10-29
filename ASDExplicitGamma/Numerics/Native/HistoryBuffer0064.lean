module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
public import ASDExplicitGamma.Numerics.Native.Heat113Passes
public import ASDExplicitGamma.Numerics.Native.Heat114Passes
public import ASDExplicitGamma.Numerics.Native.Heat115Passes
public import ASDExplicitGamma.Numerics.Native.Heat116Passes
public import ASDExplicitGamma.Numerics.Native.Heat117Passes
public import ASDExplicitGamma.Numerics.Native.Heat118Passes
public import ASDExplicitGamma.Numerics.Native.Heat119Passes
public import ASDExplicitGamma.Numerics.Native.Heat120Passes
public import ASDExplicitGamma.Numerics.Native.Heat121Passes
public import ASDExplicitGamma.Numerics.Native.Heat122Passes
public import ASDExplicitGamma.Numerics.Native.Heat123Passes
public import ASDExplicitGamma.Numerics.Native.Heat124Passes
public import ASDExplicitGamma.Numerics.Native.Heat125Passes
public import ASDExplicitGamma.Numerics.Native.Heat126Passes
public import ASDExplicitGamma.Numerics.Native.Heat127Passes
public import ASDExplicitGamma.Numerics.Native.Heat128Passes
public import ASDExplicitGamma.Numerics.Native.Heat129Passes
public import ASDExplicitGamma.Numerics.Native.Heat130Passes
public import ASDExplicitGamma.Numerics.Native.Heat131Passes
public import ASDExplicitGamma.Numerics.Native.Heat132Passes
public import ASDExplicitGamma.Numerics.Native.Heat133Passes
public import ASDExplicitGamma.Numerics.Native.Heat134Passes
public import ASDExplicitGamma.Numerics.Native.Heat135Passes
public import ASDExplicitGamma.Numerics.Native.Heat136Passes
public import ASDExplicitGamma.Numerics.Native.Heat137Passes
public import ASDExplicitGamma.Numerics.Native.Heat138Passes
public import ASDExplicitGamma.Numerics.Native.Heat139Passes
public import ASDExplicitGamma.Numerics.Native.Heat140Passes
public import ASDExplicitGamma.Numerics.Native.Heat141Passes
public import ASDExplicitGamma.Numerics.Native.Heat142Passes
public import ASDExplicitGamma.Numerics.Native.Heat143Passes
public import ASDExplicitGamma.Numerics.Native.Heat144Passes
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0064Inputs : List ℚ := [
  nativeHeat113Result.1,
  nativeHeat114Result.1,
  nativeHeat115Result.1,
  nativeHeat116Result.1,
  nativeHeat117Result.1,
  nativeHeat118Result.1,
  nativeHeat119Result.1,
  nativeHeat120Result.1,
  nativeHeat121Result.1,
  nativeHeat122Result.1,
  nativeHeat123Result.1,
  nativeHeat124Result.1,
  nativeHeat125Result.1,
  nativeHeat126Result.1,
  nativeHeat127Result.1,
  nativeHeat128Result.1,
  nativeHeat129Result.1,
  nativeHeat130Result.1,
  nativeHeat131Result.1,
  nativeHeat132Result.1,
  nativeHeat133Result.1,
  nativeHeat134Result.1,
  nativeHeat135Result.1,
  nativeHeat136Result.1,
  nativeHeat137Result.1,
  nativeHeat138Result.1,
  nativeHeat139Result.1,
  nativeHeat140Result.1,
  nativeHeat141Result.1,
  nativeHeat142Result.1,
  nativeHeat143Result.1,
  nativeHeat144Result.1
]

def nativeHistoryBuffer0064Start : ℚ × ℚ := ((131403232927139413270943018109166438266671843519464140309185193811127222747299756757232797091897/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(7320158266941163935353072257755758136301983275035737054823946522768778197067237372531847155465579199/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0064End : ℚ × ℚ := ((53890729228893908948650697579230642336746572461746780685585969132785895404612208062887595381/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58565206214182480118952768380515175935160497675284625367287198846912330255667298458109730955431717833/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0064Inputs_length : nativeHistoryBuffer0064Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0064Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(113+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(113+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0064Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0064Inputs.getD i.val 0)*(nativeHistoryBuffer0064Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0064_checked : nativeHistorySteps 49 64 32 nativeHistoryBuffer0064Inputs nativeHistoryBuffer0064Start = nativeHistoryBuffer0064End := by
  decide +kernel

theorem nativeHistoryBuffer0064Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0064Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0064Weight : nativeHistoryRatio^64 ≤ nativeHistoryBuffer0064Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0064Real_bound : nativeHistoryReal 49 64 nativeHistoryBuffer0064Inputs ≤ (nativeHistoryBuffer0064End.2 : ℝ)-(nativeHistoryBuffer0064Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0064Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0064Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0064Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0064Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0064Inputs.length) := nativeHistoryBuffer0064Domains ⟨i,by simpa only [nativeHistoryBuffer0064Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0064Inputs.length) := nativeHistoryBuffer0064Roots ⟨i,by simpa only [nativeHistoryBuffer0064Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0064Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 64 nativeHistoryBuffer0064Inputs nativeHistoryBuffer0064Start ht hd hr hw
  simpa only [nativeHistoryBuffer0064Inputs_length,nativeHistoryBuffer0064_checked] using hs

end ASDExplicitGamma.Numerics.Native
