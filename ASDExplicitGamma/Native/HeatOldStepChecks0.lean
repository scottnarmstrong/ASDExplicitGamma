module

public import ASDExplicitGamma.Native.HeatOldStepCertificates

/-! Exact radical checks along the OLD producer path. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

-- Elaborate these kernel checks one at a time: with asynchronous elaboration the checks are held together
-- until the end of the file and peak at ~9 GiB; sequentially they peak at ~2 GiB for the same CPU time.
set_option Elab.async false

theorem heat_old_steps_001_valid :
    0 ≤ nativeGap001Raw.1 ∧ 0 ≤ nativeGap001Raw.2.1 ∧ 0 ≤ nativeGap001Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap001Raw.1
      (heatOldIncrement 1 nativeGap001Raw.1 nativeGap001Raw.2.1 nativeGap001Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_010_valid :
    0 ≤ nativeGap010Raw.1 ∧ 0 ≤ nativeGap010Raw.2.1 ∧ 0 ≤ nativeGap010Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap010Raw.1
      (heatOldIncrement 10 nativeGap010Raw.1 nativeGap010Raw.2.1 nativeGap010Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_011_valid :
    0 ≤ nativeGap011Raw.1 ∧ 0 ≤ nativeGap011Raw.2.1 ∧ 0 ≤ nativeGap011Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap011Raw.1
      (heatOldIncrement 11 nativeGap011Raw.1 nativeGap011Raw.2.1 nativeGap011Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_012_valid :
    0 ≤ nativeGap012Raw.1 ∧ 0 ≤ nativeGap012Raw.2.1 ∧ 0 ≤ nativeGap012Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap012Raw.1
      (heatOldIncrement 12 nativeGap012Raw.1 nativeGap012Raw.2.1 nativeGap012Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_013_valid :
    0 ≤ nativeGap013Raw.1 ∧ 0 ≤ nativeGap013Raw.2.1 ∧ 0 ≤ nativeGap013Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap013Raw.1
      (heatOldIncrement 13 nativeGap013Raw.1 nativeGap013Raw.2.1 nativeGap013Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_014_valid :
    0 ≤ nativeGap014Raw.1 ∧ 0 ≤ nativeGap014Raw.2.1 ∧ 0 ≤ nativeGap014Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap014Raw.1
      (heatOldIncrement 14 nativeGap014Raw.1 nativeGap014Raw.2.1 nativeGap014Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_015_valid :
    0 ≤ nativeGap015Raw.1 ∧ 0 ≤ nativeGap015Raw.2.1 ∧ 0 ≤ nativeGap015Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap015Raw.1
      (heatOldIncrement 15 nativeGap015Raw.1 nativeGap015Raw.2.1 nativeGap015Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_016_valid :
    0 ≤ nativeGap016Raw.1 ∧ 0 ≤ nativeGap016Raw.2.1 ∧ 0 ≤ nativeGap016Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap016Raw.1
      (heatOldIncrement 16 nativeGap016Raw.1 nativeGap016Raw.2.1 nativeGap016Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_017_valid :
    0 ≤ nativeGap017Raw.1 ∧ 0 ≤ nativeGap017Raw.2.1 ∧ 0 ≤ nativeGap017Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap017Raw.1
      (heatOldIncrement 17 nativeGap017Raw.1 nativeGap017Raw.2.1 nativeGap017Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_018_valid :
    0 ≤ nativeGap018Raw.1 ∧ 0 ≤ nativeGap018Raw.2.1 ∧ 0 ≤ nativeGap018Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap018Raw.1
      (heatOldIncrement 18 nativeGap018Raw.1 nativeGap018Raw.2.1 nativeGap018Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_019_valid :
    0 ≤ nativeGap019Raw.1 ∧ 0 ≤ nativeGap019Raw.2.1 ∧ 0 ≤ nativeGap019Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap019Raw.1
      (heatOldIncrement 19 nativeGap019Raw.1 nativeGap019Raw.2.1 nativeGap019Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_020_valid :
    0 ≤ nativeGap020Raw.1 ∧ 0 ≤ nativeGap020Raw.2.1 ∧ 0 ≤ nativeGap020Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap020Raw.1
      (heatOldIncrement 20 nativeGap020Raw.1 nativeGap020Raw.2.1 nativeGap020Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_021_valid :
    0 ≤ nativeGap021Raw.1 ∧ 0 ≤ nativeGap021Raw.2.1 ∧ 0 ≤ nativeGap021Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap021Raw.1
      (heatOldIncrement 21 nativeGap021Raw.1 nativeGap021Raw.2.1 nativeGap021Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_022_valid :
    0 ≤ nativeGap022Raw.1 ∧ 0 ≤ nativeGap022Raw.2.1 ∧ 0 ≤ nativeGap022Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap022Raw.1
      (heatOldIncrement 22 nativeGap022Raw.1 nativeGap022Raw.2.1 nativeGap022Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_023_valid :
    0 ≤ nativeGap023Raw.1 ∧ 0 ≤ nativeGap023Raw.2.1 ∧ 0 ≤ nativeGap023Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap023Raw.1
      (heatOldIncrement 23 nativeGap023Raw.1 nativeGap023Raw.2.1 nativeGap023Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_024_valid :
    0 ≤ nativeGap024Raw.1 ∧ 0 ≤ nativeGap024Raw.2.1 ∧ 0 ≤ nativeGap024Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap024Raw.1
      (heatOldIncrement 24 nativeGap024Raw.1 nativeGap024Raw.2.1 nativeGap024Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_025_valid :
    0 ≤ nativeGap025Raw.1 ∧ 0 ≤ nativeGap025Raw.2.1 ∧ 0 ≤ nativeGap025Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap025Raw.1
      (heatOldIncrement 25 nativeGap025Raw.1 nativeGap025Raw.2.1 nativeGap025Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_026_valid :
    0 ≤ nativeGap026Raw.1 ∧ 0 ≤ nativeGap026Raw.2.1 ∧ 0 ≤ nativeGap026Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap026Raw.1
      (heatOldIncrement 26 nativeGap026Raw.1 nativeGap026Raw.2.1 nativeGap026Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_027_valid :
    0 ≤ nativeGap027Raw.1 ∧ 0 ≤ nativeGap027Raw.2.1 ∧ 0 ≤ nativeGap027Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap027Raw.1
      (heatOldIncrement 27 nativeGap027Raw.1 nativeGap027Raw.2.1 nativeGap027Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_028_valid :
    0 ≤ nativeGap028Raw.1 ∧ 0 ≤ nativeGap028Raw.2.1 ∧ 0 ≤ nativeGap028Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap028Raw.1
      (heatOldIncrement 28 nativeGap028Raw.1 nativeGap028Raw.2.1 nativeGap028Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_029_valid :
    0 ≤ nativeGap029Raw.1 ∧ 0 ≤ nativeGap029Raw.2.1 ∧ 0 ≤ nativeGap029Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap029Raw.1
      (heatOldIncrement 29 nativeGap029Raw.1 nativeGap029Raw.2.1 nativeGap029Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_030_valid :
    0 ≤ nativeGap030Raw.1 ∧ 0 ≤ nativeGap030Raw.2.1 ∧ 0 ≤ nativeGap030Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap030Raw.1
      (heatOldIncrement 30 nativeGap030Raw.1 nativeGap030Raw.2.1 nativeGap030Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_031_valid :
    0 ≤ nativeGap031Raw.1 ∧ 0 ≤ nativeGap031Raw.2.1 ∧ 0 ≤ nativeGap031Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap031Raw.1
      (heatOldIncrement 31 nativeGap031Raw.1 nativeGap031Raw.2.1 nativeGap031Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_032_valid :
    0 ≤ nativeGap032Raw.1 ∧ 0 ≤ nativeGap032Raw.2.1 ∧ 0 ≤ nativeGap032Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap032Raw.1
      (heatOldIncrement 32 nativeGap032Raw.1 nativeGap032Raw.2.1 nativeGap032Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_033_valid :
    0 ≤ nativeGap033Raw.1 ∧ 0 ≤ nativeGap033Raw.2.1 ∧ 0 ≤ nativeGap033Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap033Raw.1
      (heatOldIncrement 33 nativeGap033Raw.1 nativeGap033Raw.2.1 nativeGap033Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_034_valid :
    0 ≤ nativeGap034Raw.1 ∧ 0 ≤ nativeGap034Raw.2.1 ∧ 0 ≤ nativeGap034Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap034Raw.1
      (heatOldIncrement 34 nativeGap034Raw.1 nativeGap034Raw.2.1 nativeGap034Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_035_valid :
    0 ≤ nativeGap035Raw.1 ∧ 0 ≤ nativeGap035Raw.2.1 ∧ 0 ≤ nativeGap035Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap035Raw.1
      (heatOldIncrement 35 nativeGap035Raw.1 nativeGap035Raw.2.1 nativeGap035Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_036_valid :
    0 ≤ nativeGap036Raw.1 ∧ 0 ≤ nativeGap036Raw.2.1 ∧ 0 ≤ nativeGap036Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap036Raw.1
      (heatOldIncrement 36 nativeGap036Raw.1 nativeGap036Raw.2.1 nativeGap036Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_037_valid :
    0 ≤ nativeGap037Raw.1 ∧ 0 ≤ nativeGap037Raw.2.1 ∧ 0 ≤ nativeGap037Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap037Raw.1
      (heatOldIncrement 37 nativeGap037Raw.1 nativeGap037Raw.2.1 nativeGap037Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_038_valid :
    0 ≤ nativeGap038Raw.1 ∧ 0 ≤ nativeGap038Raw.2.1 ∧ 0 ≤ nativeGap038Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap038Raw.1
      (heatOldIncrement 38 nativeGap038Raw.1 nativeGap038Raw.2.1 nativeGap038Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_039_valid :
    0 ≤ nativeGap039Raw.1 ∧ 0 ≤ nativeGap039Raw.2.1 ∧ 0 ≤ nativeGap039Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap039Raw.1
      (heatOldIncrement 39 nativeGap039Raw.1 nativeGap039Raw.2.1 nativeGap039Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_040_valid :
    0 ≤ nativeGap040Raw.1 ∧ 0 ≤ nativeGap040Raw.2.1 ∧ 0 ≤ nativeGap040Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap040Raw.1
      (heatOldIncrement 40 nativeGap040Raw.1 nativeGap040Raw.2.1 nativeGap040Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_041_valid :
    0 ≤ nativeGap041Raw.1 ∧ 0 ≤ nativeGap041Raw.2.1 ∧ 0 ≤ nativeGap041Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap041Raw.1
      (heatOldIncrement 41 nativeGap041Raw.1 nativeGap041Raw.2.1 nativeGap041Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_042_valid :
    0 ≤ nativeGap042Raw.1 ∧ 0 ≤ nativeGap042Raw.2.1 ∧ 0 ≤ nativeGap042Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap042Raw.1
      (heatOldIncrement 42 nativeGap042Raw.1 nativeGap042Raw.2.1 nativeGap042Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_043_valid :
    0 ≤ nativeGap043Raw.1 ∧ 0 ≤ nativeGap043Raw.2.1 ∧ 0 ≤ nativeGap043Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap043Raw.1
      (heatOldIncrement 43 nativeGap043Raw.1 nativeGap043Raw.2.1 nativeGap043Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_044_valid :
    0 ≤ nativeGap044Raw.1 ∧ 0 ≤ nativeGap044Raw.2.1 ∧ 0 ≤ nativeGap044Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap044Raw.1
      (heatOldIncrement 44 nativeGap044Raw.1 nativeGap044Raw.2.1 nativeGap044Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_045_valid :
    0 ≤ nativeGap045Raw.1 ∧ 0 ≤ nativeGap045Raw.2.1 ∧ 0 ≤ nativeGap045Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap045Raw.1
      (heatOldIncrement 45 nativeGap045Raw.1 nativeGap045Raw.2.1 nativeGap045Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_046_valid :
    0 ≤ nativeGap046Raw.1 ∧ 0 ≤ nativeGap046Raw.2.1 ∧ 0 ≤ nativeGap046Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap046Raw.1
      (heatOldIncrement 46 nativeGap046Raw.1 nativeGap046Raw.2.1 nativeGap046Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_047_valid :
    0 ≤ nativeGap047Raw.1 ∧ 0 ≤ nativeGap047Raw.2.1 ∧ 0 ≤ nativeGap047Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap047Raw.1
      (heatOldIncrement 47 nativeGap047Raw.1 nativeGap047Raw.2.1 nativeGap047Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_048_valid :
    0 ≤ nativeGap048Raw.1 ∧ 0 ≤ nativeGap048Raw.2.1 ∧ 0 ≤ nativeGap048Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap048Raw.1
      (heatOldIncrement 48 nativeGap048Raw.1 nativeGap048Raw.2.1 nativeGap048Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

end ASDExplicitGamma.Native
