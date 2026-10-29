module

public import ASDExplicitGamma.Numerics.Native.Systems
public import ASDExplicitGamma.Native.HeatSourceRows010
public import ASDExplicitGamma.Native.HeatSourceRows001To024
public import ASDExplicitGamma.Native.HeatSourceRows025To039
public import ASDExplicitGamma.Native.HeatSourceRows040To054
public import ASDExplicitGamma.Native.HeatSourceRows055To069
public import ASDExplicitGamma.Native.HeatSourceRows070To084
public import ASDExplicitGamma.Native.HeatSourceRows085To099
public import ASDExplicitGamma.Native.HeatSourceRows100To114
public import ASDExplicitGamma.Native.HeatSourceRows115To129
public import ASDExplicitGamma.Native.HeatSourceRows130To144
public import ASDExplicitGamma.Native.HeatSourceRows145To159
public import ASDExplicitGamma.Native.HeatSourceRows160To161

/-! Source identities for all153 configured individual-response systems. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

/-- Exact unscaling of every configured source row, not a comparison against
the distinct refined-child heat forcing. -/
theorem native_configured_individual_row_unscale (j : Fin 153) (i : Fin 21) (hi : i.val ≠ 0) :
    let c := nativeIndividualRow (nativeConfiguredSystem j).gap i.val (nativeOld (nativeConfiguredSystem j).gap)
    (nativeConfiguredSystem j).system.diag.getD i.val 0 = c.2.1 ∧
    (nativeConfiguredSystem j).system.subdiag.getD i.val 0 * (nativeConfiguredSystem j).system.z = c.1 ∧
    (nativeConfiguredSystem j).system.force.getD i.val 0 * (nativeConfiguredSystem j).system.z^i.val = c.2.2 := by
  have hk : i.val-1 < 20 := by omega
  have he : i.val-1+1 = i.val := by omega
  fin_cases j
  · have hs := native_gap001_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap010_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap011_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap012_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap013_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap014_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap015_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap016_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap017_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap018_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap019_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap020_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap021_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap022_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap023_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap024_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap025_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap026_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap027_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap028_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap029_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap030_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap031_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap032_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap033_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap034_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap035_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap036_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap037_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap038_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap039_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap040_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap041_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap042_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap043_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap044_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap045_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap046_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap047_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap048_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap049_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap050_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap051_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap052_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap053_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap054_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap055_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap056_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap057_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap058_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap059_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap060_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap061_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap062_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap063_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap064_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap065_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap066_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap067_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap068_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap069_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap070_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap071_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap072_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap073_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap074_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap075_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap076_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap077_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap078_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap079_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap080_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap081_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap082_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap083_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap084_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap085_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap086_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap087_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap088_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap089_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap090_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap091_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap092_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap093_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap094_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap095_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap096_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap097_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap098_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap099_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap100_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap101_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap102_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap103_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap104_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap105_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap106_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap107_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap108_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap109_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap110_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap111_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap112_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap113_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap114_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap115_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap116_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap117_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap118_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap119_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap120_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap121_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap122_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap123_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap124_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap125_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap126_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap127_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap128_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap129_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap130_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap131_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap132_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap133_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap134_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap135_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap136_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap137_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap138_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap139_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap140_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap141_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap142_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap143_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap144_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap145_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap146_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap147_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap148_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap149_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap150_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap151_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap152_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap153_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap154_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap155_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap156_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap157_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap158_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap159_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap160_source_row (i.val-1) hk
    rw [he] at hs
    exact hs
  · have hs := native_gap161_source_row (i.val-1) hk
    rw [he] at hs
    exact hs

end ASDExplicitGamma.Native
