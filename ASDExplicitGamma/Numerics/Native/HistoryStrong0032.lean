module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
public import ASDExplicitGamma.Numerics.Native.Heat041Passes
public import ASDExplicitGamma.Numerics.Native.Heat042Passes
public import ASDExplicitGamma.Numerics.Native.Heat043Passes
public import ASDExplicitGamma.Numerics.Native.Heat044Passes
public import ASDExplicitGamma.Numerics.Native.Heat045Passes
public import ASDExplicitGamma.Numerics.Native.Heat046Passes
public import ASDExplicitGamma.Numerics.Native.Heat047Passes
public import ASDExplicitGamma.Numerics.Native.Heat048Passes
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
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0032Inputs : List ℚ := [
  nativeHeat041Result.1,
  nativeHeat042Result.1,
  nativeHeat043Result.1,
  nativeHeat044Result.1,
  nativeHeat045Result.1,
  nativeHeat046Result.1,
  nativeHeat047Result.1,
  nativeHeat048Result.1,
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
  nativeHeat072Result.1
]

def nativeHistoryStrong0032Start : ℚ × ℚ := ((51264653110528196233010474094698914761560440183286109130721933663896264646506431396097970427500063/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(57923240424503355732014867292731572825875010476763785858934521519506527730238077282441343183511167/62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0032End : ℚ × ℚ := ((131403232927139413270943018109166438266671843519464140309185193811127222747299756757232797091897/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9512667185420404753235360374110163013897140776143070431121952336756679728155604459019362127403067737/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0032Inputs_length : nativeHistoryStrong0032Inputs.length = 32 := rfl

theorem nativeHistoryStrong0032Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(41+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(41+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0032Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0032Inputs.getD i.val 0)*(nativeHistoryStrong0032Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0032_checked : nativeHistorySteps 9 32 32 nativeHistoryStrong0032Inputs nativeHistoryStrong0032Start = nativeHistoryStrong0032End := by
  decide +kernel

theorem nativeHistoryStrong0032Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0032Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0032Weight : nativeHistoryRatio^32 ≤ nativeHistoryStrong0032Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0032Real_bound : nativeHistoryReal 9 32 nativeHistoryStrong0032Inputs ≤ (nativeHistoryStrong0032End.2 : ℝ)-(nativeHistoryStrong0032Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0032Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0032Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0032Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0032Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0032Inputs.length) := nativeHistoryStrong0032Domains ⟨i,by simpa only [nativeHistoryStrong0032Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0032Inputs.length) := nativeHistoryStrong0032Roots ⟨i,by simpa only [nativeHistoryStrong0032Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0032Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 32 nativeHistoryStrong0032Inputs nativeHistoryStrong0032Start ht hd hr hw
  simpa only [nativeHistoryStrong0032Inputs_length,nativeHistoryStrong0032_checked] using hs

end ASDExplicitGamma.Numerics.Native
