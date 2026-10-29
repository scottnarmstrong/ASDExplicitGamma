module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
public import ASDExplicitGamma.Numerics.Native.Heat049Passes
public import ASDExplicitGamma.Numerics.Native.Heat050Passes
public import ASDExplicitGamma.Numerics.Native.Heat051Passes
public import ASDExplicitGamma.Numerics.Native.Heat052Passes
public import ASDExplicitGamma.Numerics.Native.Heat053Passes
public import ASDExplicitGamma.Numerics.Native.Heat054Passes
public import ASDExplicitGamma.Numerics.Native.Heat055Passes
public import ASDExplicitGamma.Numerics.Native.Heat056Passes
public import ASDExplicitGamma.Numerics.Native.Heat057Passes
public import ASDExplicitGamma.Numerics.Native.Heat058Passes
public import ASDExplicitGamma.Numerics.Native.Heat059Passes
public import ASDExplicitGamma.Numerics.Native.Heat060Passes
public import ASDExplicitGamma.Numerics.Native.Heat061Passes
public import ASDExplicitGamma.Numerics.Native.Heat062Passes
public import ASDExplicitGamma.Numerics.Native.Heat063Passes
public import ASDExplicitGamma.Numerics.Native.Heat064Passes
public import ASDExplicitGamma.Numerics.Native.Heat065Passes
public import ASDExplicitGamma.Numerics.Native.Heat066Passes
public import ASDExplicitGamma.Numerics.Native.Heat067Passes
public import ASDExplicitGamma.Numerics.Native.Heat068Passes
public import ASDExplicitGamma.Numerics.Native.Heat069Passes
public import ASDExplicitGamma.Numerics.Native.Heat070Passes
public import ASDExplicitGamma.Numerics.Native.Heat071Passes
public import ASDExplicitGamma.Numerics.Native.Heat072Passes
public import ASDExplicitGamma.Numerics.Native.Heat073Passes
public import ASDExplicitGamma.Numerics.Native.Heat074Passes
public import ASDExplicitGamma.Numerics.Native.Heat075Passes
public import ASDExplicitGamma.Numerics.Native.Heat076Passes
public import ASDExplicitGamma.Numerics.Native.Heat077Passes
public import ASDExplicitGamma.Numerics.Native.Heat078Passes
public import ASDExplicitGamma.Numerics.Native.Heat079Passes
public import ASDExplicitGamma.Numerics.Native.Heat080Passes
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0000Inputs : List ℚ := [
  nativeHeat049Result.1,
  nativeHeat050Result.1,
  nativeHeat051Result.1,
  nativeHeat052Result.1,
  nativeHeat053Result.1,
  nativeHeat054Result.1,
  nativeHeat055Result.1,
  nativeHeat056Result.1,
  nativeHeat057Result.1,
  nativeHeat058Result.1,
  nativeHeat059Result.1,
  nativeHeat060Result.1,
  nativeHeat061Result.1,
  nativeHeat062Result.1,
  nativeHeat063Result.1,
  nativeHeat064Result.1,
  nativeHeat065Result.1,
  nativeHeat066Result.1,
  nativeHeat067Result.1,
  nativeHeat068Result.1,
  nativeHeat069Result.1,
  nativeHeat070Result.1,
  nativeHeat071Result.1,
  nativeHeat072Result.1,
  nativeHeat073Result.1,
  nativeHeat074Result.1,
  nativeHeat075Result.1,
  nativeHeat076Result.1,
  nativeHeat077Result.1,
  nativeHeat078Result.1,
  nativeHeat079Result.1,
  nativeHeat080Result.1
]

def nativeHistoryBuffer0000Start : ℚ × ℚ := ((1/1 : ℚ),(0/1 : ℚ))
def nativeHistoryBuffer0000End : ℚ × ℚ := ((51264653110528196233010474094698914761560440183286109130721933663896264646506431396097970427500063/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(11607972432150672026522436717775641623668026233449521444730673195884526282693605836931284699422517573/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0000Inputs_length : nativeHistoryBuffer0000Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0000Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(49+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(49+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0000Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0000Inputs.getD i.val 0)*(nativeHistoryBuffer0000Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0000_checked : nativeHistorySteps 49 0 32 nativeHistoryBuffer0000Inputs nativeHistoryBuffer0000Start = nativeHistoryBuffer0000End := by
  decide +kernel

theorem nativeHistoryBuffer0000Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0000Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0000Weight : nativeHistoryRatio^0 ≤ nativeHistoryBuffer0000Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0000Real_bound : nativeHistoryReal 49 0 nativeHistoryBuffer0000Inputs ≤ (nativeHistoryBuffer0000End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0000Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0000Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0000Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0000Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0000Inputs.length) := nativeHistoryBuffer0000Domains ⟨i,by simpa only [nativeHistoryBuffer0000Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0000Inputs.length) := nativeHistoryBuffer0000Roots ⟨i,by simpa only [nativeHistoryBuffer0000Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0000Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 0 nativeHistoryBuffer0000Inputs nativeHistoryBuffer0000Start ht hd hr hw
  simpa only [nativeHistoryBuffer0000Inputs_length,nativeHistoryBuffer0000_checked] using hs

end ASDExplicitGamma.Numerics.Native
