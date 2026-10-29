module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
public import ASDExplicitGamma.Numerics.Native.Heat145Passes
public import ASDExplicitGamma.Numerics.Native.Heat146Passes
public import ASDExplicitGamma.Numerics.Native.Heat147Passes
public import ASDExplicitGamma.Numerics.Native.Heat148Passes
public import ASDExplicitGamma.Numerics.Native.Heat149Passes
public import ASDExplicitGamma.Numerics.Native.Heat150Passes
public import ASDExplicitGamma.Numerics.Native.Heat151Passes
public import ASDExplicitGamma.Numerics.Native.Heat152Passes
public import ASDExplicitGamma.Numerics.Native.Heat153Passes
public import ASDExplicitGamma.Numerics.Native.Heat154Passes
public import ASDExplicitGamma.Numerics.Native.Heat155Passes
public import ASDExplicitGamma.Numerics.Native.Heat156Passes
public import ASDExplicitGamma.Numerics.Native.Heat157Passes
public import ASDExplicitGamma.Numerics.Native.Heat158Passes
public import ASDExplicitGamma.Numerics.Native.Heat159Passes
public import ASDExplicitGamma.Numerics.Native.Heat160Passes
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0096Inputs : List ℚ := [
  nativeHeat145Result.1,
  nativeHeat146Result.1,
  nativeHeat147Result.1,
  nativeHeat148Result.1,
  nativeHeat149Result.1,
  nativeHeat150Result.1,
  nativeHeat151Result.1,
  nativeHeat152Result.1,
  nativeHeat153Result.1,
  nativeHeat154Result.1,
  nativeHeat155Result.1,
  nativeHeat156Result.1,
  nativeHeat157Result.1,
  nativeHeat158Result.1,
  nativeHeat159Result.1,
  nativeHeat160Result.1,
  nativeAvg*nativeA+(nativeRaw 161).2.2,
  nativeAvg*nativeA+(nativeRaw 162).2.2,
  nativeAvg*nativeA+(nativeRaw 163).2.2,
  nativeAvg*nativeA+(nativeRaw 164).2.2,
  nativeAvg*nativeA+(nativeRaw 165).2.2,
  nativeAvg*nativeA+(nativeRaw 166).2.2,
  nativeAvg*nativeA+(nativeRaw 167).2.2,
  nativeAvg*nativeA+(nativeRaw 168).2.2,
  nativeAvg*nativeA+(nativeRaw 169).2.2,
  nativeAvg*nativeA+(nativeRaw 170).2.2,
  nativeAvg*nativeA+(nativeRaw 171).2.2,
  nativeAvg*nativeA+(nativeRaw 172).2.2,
  nativeAvg*nativeA+(nativeRaw 173).2.2,
  nativeAvg*nativeA+(nativeRaw 174).2.2,
  nativeAvg*nativeA+(nativeRaw 175).2.2,
  nativeAvg*nativeA+(nativeRaw 176).2.2
]

def nativeHistoryBuffer0096Start : ℚ × ℚ := ((53890729228893908948650697579230642336746572461746780685585969132785895404612208062887595381/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58565206214182480118952768380515175935160497675284625367287198846912330255667298458109730955431717833/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0096End : ℚ × ℚ := ((6906723849481622278543480070058587293644127317416607730586931675871205564908114350710764033/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566239681696774951318853339535728119205550171644744132084318624527712801593245630331887677535285919/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0096Inputs_length : nativeHistoryBuffer0096Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0096Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(145+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(145+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0096Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0096Inputs.getD i.val 0)*(nativeHistoryBuffer0096Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0096_checked : nativeHistorySteps 49 96 32 nativeHistoryBuffer0096Inputs nativeHistoryBuffer0096Start = nativeHistoryBuffer0096End := by
  decide +kernel

theorem nativeHistoryBuffer0096Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0096Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0096Weight : nativeHistoryRatio^96 ≤ nativeHistoryBuffer0096Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0096Real_bound : nativeHistoryReal 49 96 nativeHistoryBuffer0096Inputs ≤ (nativeHistoryBuffer0096End.2 : ℝ)-(nativeHistoryBuffer0096Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0096Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0096Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0096Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0096Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0096Inputs.length) := nativeHistoryBuffer0096Domains ⟨i,by simpa only [nativeHistoryBuffer0096Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0096Inputs.length) := nativeHistoryBuffer0096Roots ⟨i,by simpa only [nativeHistoryBuffer0096Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0096Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 96 nativeHistoryBuffer0096Inputs nativeHistoryBuffer0096Start ht hd hr hw
  simpa only [nativeHistoryBuffer0096Inputs_length,nativeHistoryBuffer0096_checked] using hs

end ASDExplicitGamma.Numerics.Native
