module

public import ASDExplicitGamma.Native.HeatOldRawSound
public import ASDExplicitGamma.Native.HeatOldStepChecks0
public import ASDExplicitGamma.Native.HeatOldStepChecks1
public import ASDExplicitGamma.Native.HeatOldStepChecks2
public import ASDExplicitGamma.Native.HeatOldStepChecks3

/-! All configured OLD four-pass profiles, with their radicals discharged. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- Every intermediate OLD step is certified for every configured gap. -/
theorem heat_configured_old_steps_valid (index : Fin 153) (n : ℕ) (hn : n < 4) :
    HeatOldStepValid (nativeRaw (nativeConfiguredSystem index).gap).1
      (heatOldIncrement (nativeConfiguredSystem index).gap
        (nativeRaw (nativeConfiguredSystem index).gap).1
        (nativeRaw (nativeConfiguredSystem index).gap).2.1
        (nativeRaw (nativeConfiguredSystem index).gap).2.2 n) := by
  fin_cases index
  · change HeatOldStepValid (nativeRaw 1).1
      (heatOldIncrement 1 (nativeRaw 1).1 (nativeRaw 1).2.1 (nativeRaw 1).2.2 n)
    rw [nativeGap001Raw_formula]
    exact heat_old_steps_001_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 10).1
      (heatOldIncrement 10 (nativeRaw 10).1 (nativeRaw 10).2.1 (nativeRaw 10).2.2 n)
    rw [nativeGap010Raw_formula]
    exact heat_old_steps_010_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 11).1
      (heatOldIncrement 11 (nativeRaw 11).1 (nativeRaw 11).2.1 (nativeRaw 11).2.2 n)
    rw [nativeGap011Raw_formula]
    exact heat_old_steps_011_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 12).1
      (heatOldIncrement 12 (nativeRaw 12).1 (nativeRaw 12).2.1 (nativeRaw 12).2.2 n)
    rw [nativeGap012Raw_formula]
    exact heat_old_steps_012_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 13).1
      (heatOldIncrement 13 (nativeRaw 13).1 (nativeRaw 13).2.1 (nativeRaw 13).2.2 n)
    rw [nativeGap013Raw_formula]
    exact heat_old_steps_013_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 14).1
      (heatOldIncrement 14 (nativeRaw 14).1 (nativeRaw 14).2.1 (nativeRaw 14).2.2 n)
    rw [nativeGap014Raw_formula]
    exact heat_old_steps_014_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 15).1
      (heatOldIncrement 15 (nativeRaw 15).1 (nativeRaw 15).2.1 (nativeRaw 15).2.2 n)
    rw [nativeGap015Raw_formula]
    exact heat_old_steps_015_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 16).1
      (heatOldIncrement 16 (nativeRaw 16).1 (nativeRaw 16).2.1 (nativeRaw 16).2.2 n)
    rw [nativeGap016Raw_formula]
    exact heat_old_steps_016_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 17).1
      (heatOldIncrement 17 (nativeRaw 17).1 (nativeRaw 17).2.1 (nativeRaw 17).2.2 n)
    rw [nativeGap017Raw_formula]
    exact heat_old_steps_017_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 18).1
      (heatOldIncrement 18 (nativeRaw 18).1 (nativeRaw 18).2.1 (nativeRaw 18).2.2 n)
    rw [nativeGap018Raw_formula]
    exact heat_old_steps_018_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 19).1
      (heatOldIncrement 19 (nativeRaw 19).1 (nativeRaw 19).2.1 (nativeRaw 19).2.2 n)
    rw [nativeGap019Raw_formula]
    exact heat_old_steps_019_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 20).1
      (heatOldIncrement 20 (nativeRaw 20).1 (nativeRaw 20).2.1 (nativeRaw 20).2.2 n)
    rw [nativeGap020Raw_formula]
    exact heat_old_steps_020_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 21).1
      (heatOldIncrement 21 (nativeRaw 21).1 (nativeRaw 21).2.1 (nativeRaw 21).2.2 n)
    rw [nativeGap021Raw_formula]
    exact heat_old_steps_021_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 22).1
      (heatOldIncrement 22 (nativeRaw 22).1 (nativeRaw 22).2.1 (nativeRaw 22).2.2 n)
    rw [nativeGap022Raw_formula]
    exact heat_old_steps_022_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 23).1
      (heatOldIncrement 23 (nativeRaw 23).1 (nativeRaw 23).2.1 (nativeRaw 23).2.2 n)
    rw [nativeGap023Raw_formula]
    exact heat_old_steps_023_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 24).1
      (heatOldIncrement 24 (nativeRaw 24).1 (nativeRaw 24).2.1 (nativeRaw 24).2.2 n)
    rw [nativeGap024Raw_formula]
    exact heat_old_steps_024_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 25).1
      (heatOldIncrement 25 (nativeRaw 25).1 (nativeRaw 25).2.1 (nativeRaw 25).2.2 n)
    rw [nativeGap025Raw_formula]
    exact heat_old_steps_025_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 26).1
      (heatOldIncrement 26 (nativeRaw 26).1 (nativeRaw 26).2.1 (nativeRaw 26).2.2 n)
    rw [nativeGap026Raw_formula]
    exact heat_old_steps_026_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 27).1
      (heatOldIncrement 27 (nativeRaw 27).1 (nativeRaw 27).2.1 (nativeRaw 27).2.2 n)
    rw [nativeGap027Raw_formula]
    exact heat_old_steps_027_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 28).1
      (heatOldIncrement 28 (nativeRaw 28).1 (nativeRaw 28).2.1 (nativeRaw 28).2.2 n)
    rw [nativeGap028Raw_formula]
    exact heat_old_steps_028_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 29).1
      (heatOldIncrement 29 (nativeRaw 29).1 (nativeRaw 29).2.1 (nativeRaw 29).2.2 n)
    rw [nativeGap029Raw_formula]
    exact heat_old_steps_029_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 30).1
      (heatOldIncrement 30 (nativeRaw 30).1 (nativeRaw 30).2.1 (nativeRaw 30).2.2 n)
    rw [nativeGap030Raw_formula]
    exact heat_old_steps_030_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 31).1
      (heatOldIncrement 31 (nativeRaw 31).1 (nativeRaw 31).2.1 (nativeRaw 31).2.2 n)
    rw [nativeGap031Raw_formula]
    exact heat_old_steps_031_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 32).1
      (heatOldIncrement 32 (nativeRaw 32).1 (nativeRaw 32).2.1 (nativeRaw 32).2.2 n)
    rw [nativeGap032Raw_formula]
    exact heat_old_steps_032_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 33).1
      (heatOldIncrement 33 (nativeRaw 33).1 (nativeRaw 33).2.1 (nativeRaw 33).2.2 n)
    rw [nativeGap033Raw_formula]
    exact heat_old_steps_033_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 34).1
      (heatOldIncrement 34 (nativeRaw 34).1 (nativeRaw 34).2.1 (nativeRaw 34).2.2 n)
    rw [nativeGap034Raw_formula]
    exact heat_old_steps_034_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 35).1
      (heatOldIncrement 35 (nativeRaw 35).1 (nativeRaw 35).2.1 (nativeRaw 35).2.2 n)
    rw [nativeGap035Raw_formula]
    exact heat_old_steps_035_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 36).1
      (heatOldIncrement 36 (nativeRaw 36).1 (nativeRaw 36).2.1 (nativeRaw 36).2.2 n)
    rw [nativeGap036Raw_formula]
    exact heat_old_steps_036_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 37).1
      (heatOldIncrement 37 (nativeRaw 37).1 (nativeRaw 37).2.1 (nativeRaw 37).2.2 n)
    rw [nativeGap037Raw_formula]
    exact heat_old_steps_037_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 38).1
      (heatOldIncrement 38 (nativeRaw 38).1 (nativeRaw 38).2.1 (nativeRaw 38).2.2 n)
    rw [nativeGap038Raw_formula]
    exact heat_old_steps_038_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 39).1
      (heatOldIncrement 39 (nativeRaw 39).1 (nativeRaw 39).2.1 (nativeRaw 39).2.2 n)
    rw [nativeGap039Raw_formula]
    exact heat_old_steps_039_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 40).1
      (heatOldIncrement 40 (nativeRaw 40).1 (nativeRaw 40).2.1 (nativeRaw 40).2.2 n)
    rw [nativeGap040Raw_formula]
    exact heat_old_steps_040_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 41).1
      (heatOldIncrement 41 (nativeRaw 41).1 (nativeRaw 41).2.1 (nativeRaw 41).2.2 n)
    rw [nativeGap041Raw_formula]
    exact heat_old_steps_041_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 42).1
      (heatOldIncrement 42 (nativeRaw 42).1 (nativeRaw 42).2.1 (nativeRaw 42).2.2 n)
    rw [nativeGap042Raw_formula]
    exact heat_old_steps_042_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 43).1
      (heatOldIncrement 43 (nativeRaw 43).1 (nativeRaw 43).2.1 (nativeRaw 43).2.2 n)
    rw [nativeGap043Raw_formula]
    exact heat_old_steps_043_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 44).1
      (heatOldIncrement 44 (nativeRaw 44).1 (nativeRaw 44).2.1 (nativeRaw 44).2.2 n)
    rw [nativeGap044Raw_formula]
    exact heat_old_steps_044_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 45).1
      (heatOldIncrement 45 (nativeRaw 45).1 (nativeRaw 45).2.1 (nativeRaw 45).2.2 n)
    rw [nativeGap045Raw_formula]
    exact heat_old_steps_045_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 46).1
      (heatOldIncrement 46 (nativeRaw 46).1 (nativeRaw 46).2.1 (nativeRaw 46).2.2 n)
    rw [nativeGap046Raw_formula]
    exact heat_old_steps_046_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 47).1
      (heatOldIncrement 47 (nativeRaw 47).1 (nativeRaw 47).2.1 (nativeRaw 47).2.2 n)
    rw [nativeGap047Raw_formula]
    exact heat_old_steps_047_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 48).1
      (heatOldIncrement 48 (nativeRaw 48).1 (nativeRaw 48).2.1 (nativeRaw 48).2.2 n)
    rw [nativeGap048Raw_formula]
    exact heat_old_steps_048_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 49).1
      (heatOldIncrement 49 (nativeRaw 49).1 (nativeRaw 49).2.1 (nativeRaw 49).2.2 n)
    rw [nativeGap049Raw_formula]
    exact heat_old_steps_049_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 50).1
      (heatOldIncrement 50 (nativeRaw 50).1 (nativeRaw 50).2.1 (nativeRaw 50).2.2 n)
    rw [nativeGap050Raw_formula]
    exact heat_old_steps_050_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 51).1
      (heatOldIncrement 51 (nativeRaw 51).1 (nativeRaw 51).2.1 (nativeRaw 51).2.2 n)
    rw [nativeGap051Raw_formula]
    exact heat_old_steps_051_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 52).1
      (heatOldIncrement 52 (nativeRaw 52).1 (nativeRaw 52).2.1 (nativeRaw 52).2.2 n)
    rw [nativeGap052Raw_formula]
    exact heat_old_steps_052_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 53).1
      (heatOldIncrement 53 (nativeRaw 53).1 (nativeRaw 53).2.1 (nativeRaw 53).2.2 n)
    rw [nativeGap053Raw_formula]
    exact heat_old_steps_053_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 54).1
      (heatOldIncrement 54 (nativeRaw 54).1 (nativeRaw 54).2.1 (nativeRaw 54).2.2 n)
    rw [nativeGap054Raw_formula]
    exact heat_old_steps_054_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 55).1
      (heatOldIncrement 55 (nativeRaw 55).1 (nativeRaw 55).2.1 (nativeRaw 55).2.2 n)
    rw [nativeGap055Raw_formula]
    exact heat_old_steps_055_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 56).1
      (heatOldIncrement 56 (nativeRaw 56).1 (nativeRaw 56).2.1 (nativeRaw 56).2.2 n)
    rw [nativeGap056Raw_formula]
    exact heat_old_steps_056_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 57).1
      (heatOldIncrement 57 (nativeRaw 57).1 (nativeRaw 57).2.1 (nativeRaw 57).2.2 n)
    rw [nativeGap057Raw_formula]
    exact heat_old_steps_057_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 58).1
      (heatOldIncrement 58 (nativeRaw 58).1 (nativeRaw 58).2.1 (nativeRaw 58).2.2 n)
    rw [nativeGap058Raw_formula]
    exact heat_old_steps_058_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 59).1
      (heatOldIncrement 59 (nativeRaw 59).1 (nativeRaw 59).2.1 (nativeRaw 59).2.2 n)
    rw [nativeGap059Raw_formula]
    exact heat_old_steps_059_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 60).1
      (heatOldIncrement 60 (nativeRaw 60).1 (nativeRaw 60).2.1 (nativeRaw 60).2.2 n)
    rw [nativeGap060Raw_formula]
    exact heat_old_steps_060_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 61).1
      (heatOldIncrement 61 (nativeRaw 61).1 (nativeRaw 61).2.1 (nativeRaw 61).2.2 n)
    rw [nativeGap061Raw_formula]
    exact heat_old_steps_061_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 62).1
      (heatOldIncrement 62 (nativeRaw 62).1 (nativeRaw 62).2.1 (nativeRaw 62).2.2 n)
    rw [nativeGap062Raw_formula]
    exact heat_old_steps_062_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 63).1
      (heatOldIncrement 63 (nativeRaw 63).1 (nativeRaw 63).2.1 (nativeRaw 63).2.2 n)
    rw [nativeGap063Raw_formula]
    exact heat_old_steps_063_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 64).1
      (heatOldIncrement 64 (nativeRaw 64).1 (nativeRaw 64).2.1 (nativeRaw 64).2.2 n)
    rw [nativeGap064Raw_formula]
    exact heat_old_steps_064_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 65).1
      (heatOldIncrement 65 (nativeRaw 65).1 (nativeRaw 65).2.1 (nativeRaw 65).2.2 n)
    rw [nativeGap065Raw_formula]
    exact heat_old_steps_065_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 66).1
      (heatOldIncrement 66 (nativeRaw 66).1 (nativeRaw 66).2.1 (nativeRaw 66).2.2 n)
    rw [nativeGap066Raw_formula]
    exact heat_old_steps_066_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 67).1
      (heatOldIncrement 67 (nativeRaw 67).1 (nativeRaw 67).2.1 (nativeRaw 67).2.2 n)
    rw [nativeGap067Raw_formula]
    exact heat_old_steps_067_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 68).1
      (heatOldIncrement 68 (nativeRaw 68).1 (nativeRaw 68).2.1 (nativeRaw 68).2.2 n)
    rw [nativeGap068Raw_formula]
    exact heat_old_steps_068_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 69).1
      (heatOldIncrement 69 (nativeRaw 69).1 (nativeRaw 69).2.1 (nativeRaw 69).2.2 n)
    rw [nativeGap069Raw_formula]
    exact heat_old_steps_069_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 70).1
      (heatOldIncrement 70 (nativeRaw 70).1 (nativeRaw 70).2.1 (nativeRaw 70).2.2 n)
    rw [nativeGap070Raw_formula]
    exact heat_old_steps_070_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 71).1
      (heatOldIncrement 71 (nativeRaw 71).1 (nativeRaw 71).2.1 (nativeRaw 71).2.2 n)
    rw [nativeGap071Raw_formula]
    exact heat_old_steps_071_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 72).1
      (heatOldIncrement 72 (nativeRaw 72).1 (nativeRaw 72).2.1 (nativeRaw 72).2.2 n)
    rw [nativeGap072Raw_formula]
    exact heat_old_steps_072_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 73).1
      (heatOldIncrement 73 (nativeRaw 73).1 (nativeRaw 73).2.1 (nativeRaw 73).2.2 n)
    rw [nativeGap073Raw_formula]
    exact heat_old_steps_073_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 74).1
      (heatOldIncrement 74 (nativeRaw 74).1 (nativeRaw 74).2.1 (nativeRaw 74).2.2 n)
    rw [nativeGap074Raw_formula]
    exact heat_old_steps_074_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 75).1
      (heatOldIncrement 75 (nativeRaw 75).1 (nativeRaw 75).2.1 (nativeRaw 75).2.2 n)
    rw [nativeGap075Raw_formula]
    exact heat_old_steps_075_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 76).1
      (heatOldIncrement 76 (nativeRaw 76).1 (nativeRaw 76).2.1 (nativeRaw 76).2.2 n)
    rw [nativeGap076Raw_formula]
    exact heat_old_steps_076_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 77).1
      (heatOldIncrement 77 (nativeRaw 77).1 (nativeRaw 77).2.1 (nativeRaw 77).2.2 n)
    rw [nativeGap077Raw_formula]
    exact heat_old_steps_077_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 78).1
      (heatOldIncrement 78 (nativeRaw 78).1 (nativeRaw 78).2.1 (nativeRaw 78).2.2 n)
    rw [nativeGap078Raw_formula]
    exact heat_old_steps_078_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 79).1
      (heatOldIncrement 79 (nativeRaw 79).1 (nativeRaw 79).2.1 (nativeRaw 79).2.2 n)
    rw [nativeGap079Raw_formula]
    exact heat_old_steps_079_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 80).1
      (heatOldIncrement 80 (nativeRaw 80).1 (nativeRaw 80).2.1 (nativeRaw 80).2.2 n)
    rw [nativeGap080Raw_formula]
    exact heat_old_steps_080_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 81).1
      (heatOldIncrement 81 (nativeRaw 81).1 (nativeRaw 81).2.1 (nativeRaw 81).2.2 n)
    rw [nativeGap081Raw_formula]
    exact heat_old_steps_081_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 82).1
      (heatOldIncrement 82 (nativeRaw 82).1 (nativeRaw 82).2.1 (nativeRaw 82).2.2 n)
    rw [nativeGap082Raw_formula]
    exact heat_old_steps_082_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 83).1
      (heatOldIncrement 83 (nativeRaw 83).1 (nativeRaw 83).2.1 (nativeRaw 83).2.2 n)
    rw [nativeGap083Raw_formula]
    exact heat_old_steps_083_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 84).1
      (heatOldIncrement 84 (nativeRaw 84).1 (nativeRaw 84).2.1 (nativeRaw 84).2.2 n)
    rw [nativeGap084Raw_formula]
    exact heat_old_steps_084_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 85).1
      (heatOldIncrement 85 (nativeRaw 85).1 (nativeRaw 85).2.1 (nativeRaw 85).2.2 n)
    rw [nativeGap085Raw_formula]
    exact heat_old_steps_085_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 86).1
      (heatOldIncrement 86 (nativeRaw 86).1 (nativeRaw 86).2.1 (nativeRaw 86).2.2 n)
    rw [nativeGap086Raw_formula]
    exact heat_old_steps_086_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 87).1
      (heatOldIncrement 87 (nativeRaw 87).1 (nativeRaw 87).2.1 (nativeRaw 87).2.2 n)
    rw [nativeGap087Raw_formula]
    exact heat_old_steps_087_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 88).1
      (heatOldIncrement 88 (nativeRaw 88).1 (nativeRaw 88).2.1 (nativeRaw 88).2.2 n)
    rw [nativeGap088Raw_formula]
    exact heat_old_steps_088_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 89).1
      (heatOldIncrement 89 (nativeRaw 89).1 (nativeRaw 89).2.1 (nativeRaw 89).2.2 n)
    rw [nativeGap089Raw_formula]
    exact heat_old_steps_089_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 90).1
      (heatOldIncrement 90 (nativeRaw 90).1 (nativeRaw 90).2.1 (nativeRaw 90).2.2 n)
    rw [nativeGap090Raw_formula]
    exact heat_old_steps_090_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 91).1
      (heatOldIncrement 91 (nativeRaw 91).1 (nativeRaw 91).2.1 (nativeRaw 91).2.2 n)
    rw [nativeGap091Raw_formula]
    exact heat_old_steps_091_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 92).1
      (heatOldIncrement 92 (nativeRaw 92).1 (nativeRaw 92).2.1 (nativeRaw 92).2.2 n)
    rw [nativeGap092Raw_formula]
    exact heat_old_steps_092_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 93).1
      (heatOldIncrement 93 (nativeRaw 93).1 (nativeRaw 93).2.1 (nativeRaw 93).2.2 n)
    rw [nativeGap093Raw_formula]
    exact heat_old_steps_093_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 94).1
      (heatOldIncrement 94 (nativeRaw 94).1 (nativeRaw 94).2.1 (nativeRaw 94).2.2 n)
    rw [nativeGap094Raw_formula]
    exact heat_old_steps_094_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 95).1
      (heatOldIncrement 95 (nativeRaw 95).1 (nativeRaw 95).2.1 (nativeRaw 95).2.2 n)
    rw [nativeGap095Raw_formula]
    exact heat_old_steps_095_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 96).1
      (heatOldIncrement 96 (nativeRaw 96).1 (nativeRaw 96).2.1 (nativeRaw 96).2.2 n)
    rw [nativeGap096Raw_formula]
    exact heat_old_steps_096_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 97).1
      (heatOldIncrement 97 (nativeRaw 97).1 (nativeRaw 97).2.1 (nativeRaw 97).2.2 n)
    rw [nativeGap097Raw_formula]
    exact heat_old_steps_097_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 98).1
      (heatOldIncrement 98 (nativeRaw 98).1 (nativeRaw 98).2.1 (nativeRaw 98).2.2 n)
    rw [nativeGap098Raw_formula]
    exact heat_old_steps_098_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 99).1
      (heatOldIncrement 99 (nativeRaw 99).1 (nativeRaw 99).2.1 (nativeRaw 99).2.2 n)
    rw [nativeGap099Raw_formula]
    exact heat_old_steps_099_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 100).1
      (heatOldIncrement 100 (nativeRaw 100).1 (nativeRaw 100).2.1 (nativeRaw 100).2.2 n)
    rw [nativeGap100Raw_formula]
    exact heat_old_steps_100_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 101).1
      (heatOldIncrement 101 (nativeRaw 101).1 (nativeRaw 101).2.1 (nativeRaw 101).2.2 n)
    rw [nativeGap101Raw_formula]
    exact heat_old_steps_101_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 102).1
      (heatOldIncrement 102 (nativeRaw 102).1 (nativeRaw 102).2.1 (nativeRaw 102).2.2 n)
    rw [nativeGap102Raw_formula]
    exact heat_old_steps_102_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 103).1
      (heatOldIncrement 103 (nativeRaw 103).1 (nativeRaw 103).2.1 (nativeRaw 103).2.2 n)
    rw [nativeGap103Raw_formula]
    exact heat_old_steps_103_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 104).1
      (heatOldIncrement 104 (nativeRaw 104).1 (nativeRaw 104).2.1 (nativeRaw 104).2.2 n)
    rw [nativeGap104Raw_formula]
    exact heat_old_steps_104_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 105).1
      (heatOldIncrement 105 (nativeRaw 105).1 (nativeRaw 105).2.1 (nativeRaw 105).2.2 n)
    rw [nativeGap105Raw_formula]
    exact heat_old_steps_105_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 106).1
      (heatOldIncrement 106 (nativeRaw 106).1 (nativeRaw 106).2.1 (nativeRaw 106).2.2 n)
    rw [nativeGap106Raw_formula]
    exact heat_old_steps_106_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 107).1
      (heatOldIncrement 107 (nativeRaw 107).1 (nativeRaw 107).2.1 (nativeRaw 107).2.2 n)
    rw [nativeGap107Raw_formula]
    exact heat_old_steps_107_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 108).1
      (heatOldIncrement 108 (nativeRaw 108).1 (nativeRaw 108).2.1 (nativeRaw 108).2.2 n)
    rw [nativeGap108Raw_formula]
    exact heat_old_steps_108_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 109).1
      (heatOldIncrement 109 (nativeRaw 109).1 (nativeRaw 109).2.1 (nativeRaw 109).2.2 n)
    rw [nativeGap109Raw_formula]
    exact heat_old_steps_109_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 110).1
      (heatOldIncrement 110 (nativeRaw 110).1 (nativeRaw 110).2.1 (nativeRaw 110).2.2 n)
    rw [nativeGap110Raw_formula]
    exact heat_old_steps_110_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 111).1
      (heatOldIncrement 111 (nativeRaw 111).1 (nativeRaw 111).2.1 (nativeRaw 111).2.2 n)
    rw [nativeGap111Raw_formula]
    exact heat_old_steps_111_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 112).1
      (heatOldIncrement 112 (nativeRaw 112).1 (nativeRaw 112).2.1 (nativeRaw 112).2.2 n)
    rw [nativeGap112Raw_formula]
    exact heat_old_steps_112_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 113).1
      (heatOldIncrement 113 (nativeRaw 113).1 (nativeRaw 113).2.1 (nativeRaw 113).2.2 n)
    rw [nativeGap113Raw_formula]
    exact heat_old_steps_113_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 114).1
      (heatOldIncrement 114 (nativeRaw 114).1 (nativeRaw 114).2.1 (nativeRaw 114).2.2 n)
    rw [nativeGap114Raw_formula]
    exact heat_old_steps_114_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 115).1
      (heatOldIncrement 115 (nativeRaw 115).1 (nativeRaw 115).2.1 (nativeRaw 115).2.2 n)
    rw [nativeGap115Raw_formula]
    exact heat_old_steps_115_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 116).1
      (heatOldIncrement 116 (nativeRaw 116).1 (nativeRaw 116).2.1 (nativeRaw 116).2.2 n)
    rw [nativeGap116Raw_formula]
    exact heat_old_steps_116_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 117).1
      (heatOldIncrement 117 (nativeRaw 117).1 (nativeRaw 117).2.1 (nativeRaw 117).2.2 n)
    rw [nativeGap117Raw_formula]
    exact heat_old_steps_117_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 118).1
      (heatOldIncrement 118 (nativeRaw 118).1 (nativeRaw 118).2.1 (nativeRaw 118).2.2 n)
    rw [nativeGap118Raw_formula]
    exact heat_old_steps_118_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 119).1
      (heatOldIncrement 119 (nativeRaw 119).1 (nativeRaw 119).2.1 (nativeRaw 119).2.2 n)
    rw [nativeGap119Raw_formula]
    exact heat_old_steps_119_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 120).1
      (heatOldIncrement 120 (nativeRaw 120).1 (nativeRaw 120).2.1 (nativeRaw 120).2.2 n)
    rw [nativeGap120Raw_formula]
    exact heat_old_steps_120_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 121).1
      (heatOldIncrement 121 (nativeRaw 121).1 (nativeRaw 121).2.1 (nativeRaw 121).2.2 n)
    rw [nativeGap121Raw_formula]
    exact heat_old_steps_121_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 122).1
      (heatOldIncrement 122 (nativeRaw 122).1 (nativeRaw 122).2.1 (nativeRaw 122).2.2 n)
    rw [nativeGap122Raw_formula]
    exact heat_old_steps_122_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 123).1
      (heatOldIncrement 123 (nativeRaw 123).1 (nativeRaw 123).2.1 (nativeRaw 123).2.2 n)
    rw [nativeGap123Raw_formula]
    exact heat_old_steps_123_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 124).1
      (heatOldIncrement 124 (nativeRaw 124).1 (nativeRaw 124).2.1 (nativeRaw 124).2.2 n)
    rw [nativeGap124Raw_formula]
    exact heat_old_steps_124_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 125).1
      (heatOldIncrement 125 (nativeRaw 125).1 (nativeRaw 125).2.1 (nativeRaw 125).2.2 n)
    rw [nativeGap125Raw_formula]
    exact heat_old_steps_125_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 126).1
      (heatOldIncrement 126 (nativeRaw 126).1 (nativeRaw 126).2.1 (nativeRaw 126).2.2 n)
    rw [nativeGap126Raw_formula]
    exact heat_old_steps_126_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 127).1
      (heatOldIncrement 127 (nativeRaw 127).1 (nativeRaw 127).2.1 (nativeRaw 127).2.2 n)
    rw [nativeGap127Raw_formula]
    exact heat_old_steps_127_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 128).1
      (heatOldIncrement 128 (nativeRaw 128).1 (nativeRaw 128).2.1 (nativeRaw 128).2.2 n)
    rw [nativeGap128Raw_formula]
    exact heat_old_steps_128_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 129).1
      (heatOldIncrement 129 (nativeRaw 129).1 (nativeRaw 129).2.1 (nativeRaw 129).2.2 n)
    rw [nativeGap129Raw_formula]
    exact heat_old_steps_129_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 130).1
      (heatOldIncrement 130 (nativeRaw 130).1 (nativeRaw 130).2.1 (nativeRaw 130).2.2 n)
    rw [nativeGap130Raw_formula]
    exact heat_old_steps_130_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 131).1
      (heatOldIncrement 131 (nativeRaw 131).1 (nativeRaw 131).2.1 (nativeRaw 131).2.2 n)
    rw [nativeGap131Raw_formula]
    exact heat_old_steps_131_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 132).1
      (heatOldIncrement 132 (nativeRaw 132).1 (nativeRaw 132).2.1 (nativeRaw 132).2.2 n)
    rw [nativeGap132Raw_formula]
    exact heat_old_steps_132_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 133).1
      (heatOldIncrement 133 (nativeRaw 133).1 (nativeRaw 133).2.1 (nativeRaw 133).2.2 n)
    rw [nativeGap133Raw_formula]
    exact heat_old_steps_133_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 134).1
      (heatOldIncrement 134 (nativeRaw 134).1 (nativeRaw 134).2.1 (nativeRaw 134).2.2 n)
    rw [nativeGap134Raw_formula]
    exact heat_old_steps_134_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 135).1
      (heatOldIncrement 135 (nativeRaw 135).1 (nativeRaw 135).2.1 (nativeRaw 135).2.2 n)
    rw [nativeGap135Raw_formula]
    exact heat_old_steps_135_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 136).1
      (heatOldIncrement 136 (nativeRaw 136).1 (nativeRaw 136).2.1 (nativeRaw 136).2.2 n)
    rw [nativeGap136Raw_formula]
    exact heat_old_steps_136_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 137).1
      (heatOldIncrement 137 (nativeRaw 137).1 (nativeRaw 137).2.1 (nativeRaw 137).2.2 n)
    rw [nativeGap137Raw_formula]
    exact heat_old_steps_137_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 138).1
      (heatOldIncrement 138 (nativeRaw 138).1 (nativeRaw 138).2.1 (nativeRaw 138).2.2 n)
    rw [nativeGap138Raw_formula]
    exact heat_old_steps_138_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 139).1
      (heatOldIncrement 139 (nativeRaw 139).1 (nativeRaw 139).2.1 (nativeRaw 139).2.2 n)
    rw [nativeGap139Raw_formula]
    exact heat_old_steps_139_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 140).1
      (heatOldIncrement 140 (nativeRaw 140).1 (nativeRaw 140).2.1 (nativeRaw 140).2.2 n)
    rw [nativeGap140Raw_formula]
    exact heat_old_steps_140_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 141).1
      (heatOldIncrement 141 (nativeRaw 141).1 (nativeRaw 141).2.1 (nativeRaw 141).2.2 n)
    rw [nativeGap141Raw_formula]
    exact heat_old_steps_141_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 142).1
      (heatOldIncrement 142 (nativeRaw 142).1 (nativeRaw 142).2.1 (nativeRaw 142).2.2 n)
    rw [nativeGap142Raw_formula]
    exact heat_old_steps_142_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 143).1
      (heatOldIncrement 143 (nativeRaw 143).1 (nativeRaw 143).2.1 (nativeRaw 143).2.2 n)
    rw [nativeGap143Raw_formula]
    exact heat_old_steps_143_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 144).1
      (heatOldIncrement 144 (nativeRaw 144).1 (nativeRaw 144).2.1 (nativeRaw 144).2.2 n)
    rw [nativeGap144Raw_formula]
    exact heat_old_steps_144_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 145).1
      (heatOldIncrement 145 (nativeRaw 145).1 (nativeRaw 145).2.1 (nativeRaw 145).2.2 n)
    rw [nativeGap145Raw_formula]
    exact heat_old_steps_145_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 146).1
      (heatOldIncrement 146 (nativeRaw 146).1 (nativeRaw 146).2.1 (nativeRaw 146).2.2 n)
    rw [nativeGap146Raw_formula]
    exact heat_old_steps_146_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 147).1
      (heatOldIncrement 147 (nativeRaw 147).1 (nativeRaw 147).2.1 (nativeRaw 147).2.2 n)
    rw [nativeGap147Raw_formula]
    exact heat_old_steps_147_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 148).1
      (heatOldIncrement 148 (nativeRaw 148).1 (nativeRaw 148).2.1 (nativeRaw 148).2.2 n)
    rw [nativeGap148Raw_formula]
    exact heat_old_steps_148_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 149).1
      (heatOldIncrement 149 (nativeRaw 149).1 (nativeRaw 149).2.1 (nativeRaw 149).2.2 n)
    rw [nativeGap149Raw_formula]
    exact heat_old_steps_149_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 150).1
      (heatOldIncrement 150 (nativeRaw 150).1 (nativeRaw 150).2.1 (nativeRaw 150).2.2 n)
    rw [nativeGap150Raw_formula]
    exact heat_old_steps_150_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 151).1
      (heatOldIncrement 151 (nativeRaw 151).1 (nativeRaw 151).2.1 (nativeRaw 151).2.2 n)
    rw [nativeGap151Raw_formula]
    exact heat_old_steps_151_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 152).1
      (heatOldIncrement 152 (nativeRaw 152).1 (nativeRaw 152).2.1 (nativeRaw 152).2.2 n)
    rw [nativeGap152Raw_formula]
    exact heat_old_steps_152_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 153).1
      (heatOldIncrement 153 (nativeRaw 153).1 (nativeRaw 153).2.1 (nativeRaw 153).2.2 n)
    rw [nativeGap153Raw_formula]
    exact heat_old_steps_153_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 154).1
      (heatOldIncrement 154 (nativeRaw 154).1 (nativeRaw 154).2.1 (nativeRaw 154).2.2 n)
    rw [nativeGap154Raw_formula]
    exact heat_old_steps_154_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 155).1
      (heatOldIncrement 155 (nativeRaw 155).1 (nativeRaw 155).2.1 (nativeRaw 155).2.2 n)
    rw [nativeGap155Raw_formula]
    exact heat_old_steps_155_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 156).1
      (heatOldIncrement 156 (nativeRaw 156).1 (nativeRaw 156).2.1 (nativeRaw 156).2.2 n)
    rw [nativeGap156Raw_formula]
    exact heat_old_steps_156_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 157).1
      (heatOldIncrement 157 (nativeRaw 157).1 (nativeRaw 157).2.1 (nativeRaw 157).2.2 n)
    rw [nativeGap157Raw_formula]
    exact heat_old_steps_157_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 158).1
      (heatOldIncrement 158 (nativeRaw 158).1 (nativeRaw 158).2.1 (nativeRaw 158).2.2 n)
    rw [nativeGap158Raw_formula]
    exact heat_old_steps_158_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 159).1
      (heatOldIncrement 159 (nativeRaw 159).1 (nativeRaw 159).2.1 (nativeRaw 159).2.2 n)
    rw [nativeGap159Raw_formula]
    exact heat_old_steps_159_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 160).1
      (heatOldIncrement 160 (nativeRaw 160).1 (nativeRaw 160).2.1 (nativeRaw 160).2.2 n)
    rw [nativeGap160Raw_formula]
    exact heat_old_steps_160_valid.2.2.2 ⟨n,hn⟩
  · change HeatOldStepValid (nativeRaw 161).1
      (heatOldIncrement 161 (nativeRaw 161).1 (nativeRaw 161).2.1 (nativeRaw 161).2.2 n)
    rw [nativeGap161Raw_formula]
    exact heat_old_steps_161_valid.2.2.2 ⟨n,hn⟩

/-- The literal OLD x slot bounds the full real four-pass profile for every
selected individual solve; no cooperative moment output is used. -/
theorem heat_configured_old_real_profile (index : Fin 153) :
    nativeSourceGenericIndividualCap (nativeConfiguredSystem index).gap nativeA
      (nativeOld (nativeConfiguredSystem index).gap).e
      (nativeOld (nativeConfiguredSystem index).gap).f 4 ≤
        ((nativeOld (nativeConfiguredSystem index).gap).x:ℝ) := by
  let height := (nativeConfiguredSystem index).gap
  have hv := heat_configured_individual_old_valid index
  exact heat_old_four_profile_sound height (nativeRaw height).1 (nativeRaw height).2.1
    (nativeRaw height).2.2 hv.2.2.1 hv.1 (heat_old_raw_increment_le height)
    (heat_configured_old_steps_valid index)

end
end ASDExplicitGamma.Native
