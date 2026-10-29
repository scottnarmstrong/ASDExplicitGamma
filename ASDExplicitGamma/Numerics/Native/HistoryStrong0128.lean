module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
public import ASDExplicitGamma.Numerics.Native.Heat137Passes
public import ASDExplicitGamma.Numerics.Native.Heat138Passes
public import ASDExplicitGamma.Numerics.Native.Heat139Passes
public import ASDExplicitGamma.Numerics.Native.Heat140Passes
public import ASDExplicitGamma.Numerics.Native.Heat141Passes
public import ASDExplicitGamma.Numerics.Native.Heat142Passes
public import ASDExplicitGamma.Numerics.Native.Heat143Passes
public import ASDExplicitGamma.Numerics.Native.Heat144Passes
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

def nativeHistoryStrong0128Inputs : List ℚ := [
  nativeHeat137Result.1,
  nativeHeat138Result.1,
  nativeHeat139Result.1,
  nativeHeat140Result.1,
  nativeHeat141Result.1,
  nativeHeat142Result.1,
  nativeHeat143Result.1,
  nativeHeat144Result.1,
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
  nativeAvg*nativeA+(nativeRaw 168).2.2
]

def nativeHistoryStrong0128Start : ℚ × ℚ := ((6906723849481622278543480070058587293644127317416607730586931675871205564908114350710764033/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515061031581428243935938898831555620420203083534709906912052040943995394256445542776685285065296033/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0128End : ℚ × ℚ := ((1416283209095549299797276381654664966001910515183972732739379003373390715312677559085997/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531121400334977404125557484728141237665600545353473043247240440338419702326395938384565629818439/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0128Inputs_length : nativeHistoryStrong0128Inputs.length = 32 := rfl

theorem nativeHistoryStrong0128Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(137+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(137+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0128Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0128Inputs.getD i.val 0)*(nativeHistoryStrong0128Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0128_checked : nativeHistorySteps 9 128 32 nativeHistoryStrong0128Inputs nativeHistoryStrong0128Start = nativeHistoryStrong0128End := by
  decide +kernel

theorem nativeHistoryStrong0128Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0128Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0128Weight : nativeHistoryRatio^128 ≤ nativeHistoryStrong0128Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0128Real_bound : nativeHistoryReal 9 128 nativeHistoryStrong0128Inputs ≤ (nativeHistoryStrong0128End.2 : ℝ)-(nativeHistoryStrong0128Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0128Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0128Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0128Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0128Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0128Inputs.length) := nativeHistoryStrong0128Domains ⟨i,by simpa only [nativeHistoryStrong0128Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0128Inputs.length) := nativeHistoryStrong0128Roots ⟨i,by simpa only [nativeHistoryStrong0128Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0128Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 128 nativeHistoryStrong0128Inputs nativeHistoryStrong0128Start ht hd hr hw
  simpa only [nativeHistoryStrong0128Inputs_length,nativeHistoryStrong0128_checked] using hs

end ASDExplicitGamma.Numerics.Native
