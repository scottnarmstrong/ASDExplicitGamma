module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
public import ASDExplicitGamma.Numerics.Native.Heat009Passes
public import ASDExplicitGamma.Numerics.Native.Heat010Passes
public import ASDExplicitGamma.Numerics.Native.Heat011Passes
public import ASDExplicitGamma.Numerics.Native.Heat012Passes
public import ASDExplicitGamma.Numerics.Native.Heat013Passes
public import ASDExplicitGamma.Numerics.Native.Heat014Passes
public import ASDExplicitGamma.Numerics.Native.Heat015Passes
public import ASDExplicitGamma.Numerics.Native.Heat016Passes
public import ASDExplicitGamma.Numerics.Native.Heat017Passes
public import ASDExplicitGamma.Numerics.Native.Heat018Passes
public import ASDExplicitGamma.Numerics.Native.Heat019Passes
public import ASDExplicitGamma.Numerics.Native.Heat020Passes
public import ASDExplicitGamma.Numerics.Native.Heat021Passes
public import ASDExplicitGamma.Numerics.Native.Heat022Passes
public import ASDExplicitGamma.Numerics.Native.Heat023Passes
public import ASDExplicitGamma.Numerics.Native.Heat024Passes
public import ASDExplicitGamma.Numerics.Native.Heat025Passes
public import ASDExplicitGamma.Numerics.Native.Heat026Passes
public import ASDExplicitGamma.Numerics.Native.Heat027Passes
public import ASDExplicitGamma.Numerics.Native.Heat028Passes
public import ASDExplicitGamma.Numerics.Native.Heat029Passes
public import ASDExplicitGamma.Numerics.Native.Heat030Passes
public import ASDExplicitGamma.Numerics.Native.Heat031Passes
public import ASDExplicitGamma.Numerics.Native.Heat032Passes
public import ASDExplicitGamma.Numerics.Native.Heat033Passes
public import ASDExplicitGamma.Numerics.Native.Heat034Passes
public import ASDExplicitGamma.Numerics.Native.Heat035Passes
public import ASDExplicitGamma.Numerics.Native.Heat036Passes
public import ASDExplicitGamma.Numerics.Native.Heat037Passes
public import ASDExplicitGamma.Numerics.Native.Heat038Passes
public import ASDExplicitGamma.Numerics.Native.Heat039Passes
public import ASDExplicitGamma.Numerics.Native.Heat040Passes
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0000Inputs : List ℚ := [
  nativeHeat009Result.1,
  nativeHeat010Result.1,
  nativeHeat011Result.1,
  nativeHeat012Result.1,
  nativeHeat013Result.1,
  nativeHeat014Result.1,
  nativeHeat015Result.1,
  nativeHeat016Result.1,
  nativeHeat017Result.1,
  nativeHeat018Result.1,
  nativeHeat019Result.1,
  nativeHeat020Result.1,
  nativeHeat021Result.1,
  nativeHeat022Result.1,
  nativeHeat023Result.1,
  nativeHeat024Result.1,
  nativeHeat025Result.1,
  nativeHeat026Result.1,
  nativeHeat027Result.1,
  nativeHeat028Result.1,
  nativeHeat029Result.1,
  nativeHeat030Result.1,
  nativeHeat031Result.1,
  nativeHeat032Result.1,
  nativeHeat033Result.1,
  nativeHeat034Result.1,
  nativeHeat035Result.1,
  nativeHeat036Result.1,
  nativeHeat037Result.1,
  nativeHeat038Result.1,
  nativeHeat039Result.1,
  nativeHeat040Result.1
]

def nativeHistoryStrong0000Start : ℚ × ℚ := ((1/1 : ℚ),(0/1 : ℚ))
def nativeHistoryStrong0000End : ℚ × ℚ := ((51264653110528196233010474094698914761560440183286109130721933663896264646506431396097970427500063/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(57923240424503355732014867292731572825875010476763785858934521519506527730238077282441343183511167/62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0000Inputs_length : nativeHistoryStrong0000Inputs.length = 32 := rfl

theorem nativeHistoryStrong0000Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(9+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(9+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0000Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0000Inputs.getD i.val 0)*(nativeHistoryStrong0000Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0000_checked : nativeHistorySteps 9 0 32 nativeHistoryStrong0000Inputs nativeHistoryStrong0000Start = nativeHistoryStrong0000End := by
  decide +kernel

theorem nativeHistoryStrong0000Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0000Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0000Weight : nativeHistoryRatio^0 ≤ nativeHistoryStrong0000Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0000Real_bound : nativeHistoryReal 9 0 nativeHistoryStrong0000Inputs ≤ (nativeHistoryStrong0000End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0000Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0000Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0000Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0000Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0000Inputs.length) := nativeHistoryStrong0000Domains ⟨i,by simpa only [nativeHistoryStrong0000Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0000Inputs.length) := nativeHistoryStrong0000Roots ⟨i,by simpa only [nativeHistoryStrong0000Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0000Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 0 nativeHistoryStrong0000Inputs nativeHistoryStrong0000Start ht hd hr hw
  simpa only [nativeHistoryStrong0000Inputs_length,nativeHistoryStrong0000_checked] using hs

end ASDExplicitGamma.Numerics.Native
