module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
public import ASDExplicitGamma.Numerics.Native.Heat105Passes
public import ASDExplicitGamma.Numerics.Native.Heat106Passes
public import ASDExplicitGamma.Numerics.Native.Heat107Passes
public import ASDExplicitGamma.Numerics.Native.Heat108Passes
public import ASDExplicitGamma.Numerics.Native.Heat109Passes
public import ASDExplicitGamma.Numerics.Native.Heat110Passes
public import ASDExplicitGamma.Numerics.Native.Heat111Passes
public import ASDExplicitGamma.Numerics.Native.Heat112Passes
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
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0096Inputs : List ℚ := [
  nativeHeat105Result.1,
  nativeHeat106Result.1,
  nativeHeat107Result.1,
  nativeHeat108Result.1,
  nativeHeat109Result.1,
  nativeHeat110Result.1,
  nativeHeat111Result.1,
  nativeHeat112Result.1,
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
  nativeHeat136Result.1
]

def nativeHistoryStrong0096Start : ℚ × ℚ := ((53890729228893908948650697579230642336746572461746780685585969132785895404612208062887595381/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757521258969907276295890060294315921035934065314709990287111262669674550484330835229185817148366651/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0096End : ℚ × ℚ := ((6906723849481622278543480070058587293644127317416607730586931675871205564908114350710764033/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515061031581428243935938898831555620420203083534709906912052040943995394256445542776685285065296033/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0096Inputs_length : nativeHistoryStrong0096Inputs.length = 32 := rfl

theorem nativeHistoryStrong0096Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(105+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(105+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0096Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0096Inputs.getD i.val 0)*(nativeHistoryStrong0096Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0096_checked : nativeHistorySteps 9 96 32 nativeHistoryStrong0096Inputs nativeHistoryStrong0096Start = nativeHistoryStrong0096End := by
  decide +kernel

theorem nativeHistoryStrong0096Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0096Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0096Weight : nativeHistoryRatio^96 ≤ nativeHistoryStrong0096Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0096Real_bound : nativeHistoryReal 9 96 nativeHistoryStrong0096Inputs ≤ (nativeHistoryStrong0096End.2 : ℝ)-(nativeHistoryStrong0096Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0096Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0096Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0096Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0096Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0096Inputs.length) := nativeHistoryStrong0096Domains ⟨i,by simpa only [nativeHistoryStrong0096Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0096Inputs.length) := nativeHistoryStrong0096Roots ⟨i,by simpa only [nativeHistoryStrong0096Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0096Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 96 nativeHistoryStrong0096Inputs nativeHistoryStrong0096Start ht hd hr hw
  simpa only [nativeHistoryStrong0096Inputs_length,nativeHistoryStrong0096_checked] using hs

end ASDExplicitGamma.Numerics.Native
