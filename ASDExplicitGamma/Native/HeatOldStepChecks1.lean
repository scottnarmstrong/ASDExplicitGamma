module

public import ASDExplicitGamma.Native.HeatOldStepCertificates

/-! Exact radical checks along the OLD producer path. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

-- Elaborate these kernel checks one at a time: with asynchronous elaboration the checks are held together
-- until the end of the file and peak at ~9 GiB; sequentially they peak at ~2 GiB for the same CPU time.
set_option Elab.async false

theorem heat_old_steps_049_valid :
    0 ≤ nativeGap049Raw.1 ∧ 0 ≤ nativeGap049Raw.2.1 ∧ 0 ≤ nativeGap049Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap049Raw.1
      (heatOldIncrement 49 nativeGap049Raw.1 nativeGap049Raw.2.1 nativeGap049Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_050_valid :
    0 ≤ nativeGap050Raw.1 ∧ 0 ≤ nativeGap050Raw.2.1 ∧ 0 ≤ nativeGap050Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap050Raw.1
      (heatOldIncrement 50 nativeGap050Raw.1 nativeGap050Raw.2.1 nativeGap050Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_051_valid :
    0 ≤ nativeGap051Raw.1 ∧ 0 ≤ nativeGap051Raw.2.1 ∧ 0 ≤ nativeGap051Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap051Raw.1
      (heatOldIncrement 51 nativeGap051Raw.1 nativeGap051Raw.2.1 nativeGap051Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_052_valid :
    0 ≤ nativeGap052Raw.1 ∧ 0 ≤ nativeGap052Raw.2.1 ∧ 0 ≤ nativeGap052Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap052Raw.1
      (heatOldIncrement 52 nativeGap052Raw.1 nativeGap052Raw.2.1 nativeGap052Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_053_valid :
    0 ≤ nativeGap053Raw.1 ∧ 0 ≤ nativeGap053Raw.2.1 ∧ 0 ≤ nativeGap053Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap053Raw.1
      (heatOldIncrement 53 nativeGap053Raw.1 nativeGap053Raw.2.1 nativeGap053Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_054_valid :
    0 ≤ nativeGap054Raw.1 ∧ 0 ≤ nativeGap054Raw.2.1 ∧ 0 ≤ nativeGap054Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap054Raw.1
      (heatOldIncrement 54 nativeGap054Raw.1 nativeGap054Raw.2.1 nativeGap054Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_055_valid :
    0 ≤ nativeGap055Raw.1 ∧ 0 ≤ nativeGap055Raw.2.1 ∧ 0 ≤ nativeGap055Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap055Raw.1
      (heatOldIncrement 55 nativeGap055Raw.1 nativeGap055Raw.2.1 nativeGap055Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_056_valid :
    0 ≤ nativeGap056Raw.1 ∧ 0 ≤ nativeGap056Raw.2.1 ∧ 0 ≤ nativeGap056Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap056Raw.1
      (heatOldIncrement 56 nativeGap056Raw.1 nativeGap056Raw.2.1 nativeGap056Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_057_valid :
    0 ≤ nativeGap057Raw.1 ∧ 0 ≤ nativeGap057Raw.2.1 ∧ 0 ≤ nativeGap057Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap057Raw.1
      (heatOldIncrement 57 nativeGap057Raw.1 nativeGap057Raw.2.1 nativeGap057Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_058_valid :
    0 ≤ nativeGap058Raw.1 ∧ 0 ≤ nativeGap058Raw.2.1 ∧ 0 ≤ nativeGap058Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap058Raw.1
      (heatOldIncrement 58 nativeGap058Raw.1 nativeGap058Raw.2.1 nativeGap058Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_059_valid :
    0 ≤ nativeGap059Raw.1 ∧ 0 ≤ nativeGap059Raw.2.1 ∧ 0 ≤ nativeGap059Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap059Raw.1
      (heatOldIncrement 59 nativeGap059Raw.1 nativeGap059Raw.2.1 nativeGap059Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_060_valid :
    0 ≤ nativeGap060Raw.1 ∧ 0 ≤ nativeGap060Raw.2.1 ∧ 0 ≤ nativeGap060Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap060Raw.1
      (heatOldIncrement 60 nativeGap060Raw.1 nativeGap060Raw.2.1 nativeGap060Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_061_valid :
    0 ≤ nativeGap061Raw.1 ∧ 0 ≤ nativeGap061Raw.2.1 ∧ 0 ≤ nativeGap061Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap061Raw.1
      (heatOldIncrement 61 nativeGap061Raw.1 nativeGap061Raw.2.1 nativeGap061Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_062_valid :
    0 ≤ nativeGap062Raw.1 ∧ 0 ≤ nativeGap062Raw.2.1 ∧ 0 ≤ nativeGap062Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap062Raw.1
      (heatOldIncrement 62 nativeGap062Raw.1 nativeGap062Raw.2.1 nativeGap062Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_063_valid :
    0 ≤ nativeGap063Raw.1 ∧ 0 ≤ nativeGap063Raw.2.1 ∧ 0 ≤ nativeGap063Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap063Raw.1
      (heatOldIncrement 63 nativeGap063Raw.1 nativeGap063Raw.2.1 nativeGap063Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_064_valid :
    0 ≤ nativeGap064Raw.1 ∧ 0 ≤ nativeGap064Raw.2.1 ∧ 0 ≤ nativeGap064Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap064Raw.1
      (heatOldIncrement 64 nativeGap064Raw.1 nativeGap064Raw.2.1 nativeGap064Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_065_valid :
    0 ≤ nativeGap065Raw.1 ∧ 0 ≤ nativeGap065Raw.2.1 ∧ 0 ≤ nativeGap065Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap065Raw.1
      (heatOldIncrement 65 nativeGap065Raw.1 nativeGap065Raw.2.1 nativeGap065Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_066_valid :
    0 ≤ nativeGap066Raw.1 ∧ 0 ≤ nativeGap066Raw.2.1 ∧ 0 ≤ nativeGap066Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap066Raw.1
      (heatOldIncrement 66 nativeGap066Raw.1 nativeGap066Raw.2.1 nativeGap066Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_067_valid :
    0 ≤ nativeGap067Raw.1 ∧ 0 ≤ nativeGap067Raw.2.1 ∧ 0 ≤ nativeGap067Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap067Raw.1
      (heatOldIncrement 67 nativeGap067Raw.1 nativeGap067Raw.2.1 nativeGap067Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_068_valid :
    0 ≤ nativeGap068Raw.1 ∧ 0 ≤ nativeGap068Raw.2.1 ∧ 0 ≤ nativeGap068Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap068Raw.1
      (heatOldIncrement 68 nativeGap068Raw.1 nativeGap068Raw.2.1 nativeGap068Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_069_valid :
    0 ≤ nativeGap069Raw.1 ∧ 0 ≤ nativeGap069Raw.2.1 ∧ 0 ≤ nativeGap069Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap069Raw.1
      (heatOldIncrement 69 nativeGap069Raw.1 nativeGap069Raw.2.1 nativeGap069Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_070_valid :
    0 ≤ nativeGap070Raw.1 ∧ 0 ≤ nativeGap070Raw.2.1 ∧ 0 ≤ nativeGap070Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap070Raw.1
      (heatOldIncrement 70 nativeGap070Raw.1 nativeGap070Raw.2.1 nativeGap070Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_071_valid :
    0 ≤ nativeGap071Raw.1 ∧ 0 ≤ nativeGap071Raw.2.1 ∧ 0 ≤ nativeGap071Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap071Raw.1
      (heatOldIncrement 71 nativeGap071Raw.1 nativeGap071Raw.2.1 nativeGap071Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_072_valid :
    0 ≤ nativeGap072Raw.1 ∧ 0 ≤ nativeGap072Raw.2.1 ∧ 0 ≤ nativeGap072Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap072Raw.1
      (heatOldIncrement 72 nativeGap072Raw.1 nativeGap072Raw.2.1 nativeGap072Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_073_valid :
    0 ≤ nativeGap073Raw.1 ∧ 0 ≤ nativeGap073Raw.2.1 ∧ 0 ≤ nativeGap073Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap073Raw.1
      (heatOldIncrement 73 nativeGap073Raw.1 nativeGap073Raw.2.1 nativeGap073Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_074_valid :
    0 ≤ nativeGap074Raw.1 ∧ 0 ≤ nativeGap074Raw.2.1 ∧ 0 ≤ nativeGap074Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap074Raw.1
      (heatOldIncrement 74 nativeGap074Raw.1 nativeGap074Raw.2.1 nativeGap074Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_075_valid :
    0 ≤ nativeGap075Raw.1 ∧ 0 ≤ nativeGap075Raw.2.1 ∧ 0 ≤ nativeGap075Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap075Raw.1
      (heatOldIncrement 75 nativeGap075Raw.1 nativeGap075Raw.2.1 nativeGap075Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_076_valid :
    0 ≤ nativeGap076Raw.1 ∧ 0 ≤ nativeGap076Raw.2.1 ∧ 0 ≤ nativeGap076Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap076Raw.1
      (heatOldIncrement 76 nativeGap076Raw.1 nativeGap076Raw.2.1 nativeGap076Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_077_valid :
    0 ≤ nativeGap077Raw.1 ∧ 0 ≤ nativeGap077Raw.2.1 ∧ 0 ≤ nativeGap077Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap077Raw.1
      (heatOldIncrement 77 nativeGap077Raw.1 nativeGap077Raw.2.1 nativeGap077Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_078_valid :
    0 ≤ nativeGap078Raw.1 ∧ 0 ≤ nativeGap078Raw.2.1 ∧ 0 ≤ nativeGap078Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap078Raw.1
      (heatOldIncrement 78 nativeGap078Raw.1 nativeGap078Raw.2.1 nativeGap078Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_079_valid :
    0 ≤ nativeGap079Raw.1 ∧ 0 ≤ nativeGap079Raw.2.1 ∧ 0 ≤ nativeGap079Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap079Raw.1
      (heatOldIncrement 79 nativeGap079Raw.1 nativeGap079Raw.2.1 nativeGap079Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_080_valid :
    0 ≤ nativeGap080Raw.1 ∧ 0 ≤ nativeGap080Raw.2.1 ∧ 0 ≤ nativeGap080Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap080Raw.1
      (heatOldIncrement 80 nativeGap080Raw.1 nativeGap080Raw.2.1 nativeGap080Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_081_valid :
    0 ≤ nativeGap081Raw.1 ∧ 0 ≤ nativeGap081Raw.2.1 ∧ 0 ≤ nativeGap081Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap081Raw.1
      (heatOldIncrement 81 nativeGap081Raw.1 nativeGap081Raw.2.1 nativeGap081Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_082_valid :
    0 ≤ nativeGap082Raw.1 ∧ 0 ≤ nativeGap082Raw.2.1 ∧ 0 ≤ nativeGap082Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap082Raw.1
      (heatOldIncrement 82 nativeGap082Raw.1 nativeGap082Raw.2.1 nativeGap082Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_083_valid :
    0 ≤ nativeGap083Raw.1 ∧ 0 ≤ nativeGap083Raw.2.1 ∧ 0 ≤ nativeGap083Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap083Raw.1
      (heatOldIncrement 83 nativeGap083Raw.1 nativeGap083Raw.2.1 nativeGap083Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_084_valid :
    0 ≤ nativeGap084Raw.1 ∧ 0 ≤ nativeGap084Raw.2.1 ∧ 0 ≤ nativeGap084Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap084Raw.1
      (heatOldIncrement 84 nativeGap084Raw.1 nativeGap084Raw.2.1 nativeGap084Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_085_valid :
    0 ≤ nativeGap085Raw.1 ∧ 0 ≤ nativeGap085Raw.2.1 ∧ 0 ≤ nativeGap085Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap085Raw.1
      (heatOldIncrement 85 nativeGap085Raw.1 nativeGap085Raw.2.1 nativeGap085Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_086_valid :
    0 ≤ nativeGap086Raw.1 ∧ 0 ≤ nativeGap086Raw.2.1 ∧ 0 ≤ nativeGap086Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap086Raw.1
      (heatOldIncrement 86 nativeGap086Raw.1 nativeGap086Raw.2.1 nativeGap086Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_087_valid :
    0 ≤ nativeGap087Raw.1 ∧ 0 ≤ nativeGap087Raw.2.1 ∧ 0 ≤ nativeGap087Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap087Raw.1
      (heatOldIncrement 87 nativeGap087Raw.1 nativeGap087Raw.2.1 nativeGap087Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_088_valid :
    0 ≤ nativeGap088Raw.1 ∧ 0 ≤ nativeGap088Raw.2.1 ∧ 0 ≤ nativeGap088Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap088Raw.1
      (heatOldIncrement 88 nativeGap088Raw.1 nativeGap088Raw.2.1 nativeGap088Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

end ASDExplicitGamma.Native
