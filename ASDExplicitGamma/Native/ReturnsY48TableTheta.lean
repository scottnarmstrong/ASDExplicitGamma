module

public import ASDExplicitGamma.Native.ReturnsHeatTable

/-! The 48-pass caps of the refined heat step are below the direct individual caps, for every
shell count `9 ≤ g ≤ 160`: the heat result's first component is the 48-pass cap itself. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

def nativeReturnsY48Table : List ℚ := [
  nativeHeat009Y48,
  nativeHeat010Y48,
  nativeHeat011Y48,
  nativeHeat012Y48,
  nativeHeat013Y48,
  nativeHeat014Y48,
  nativeHeat015Y48,
  nativeHeat016Y48,
  nativeHeat017Y48,
  nativeHeat018Y48,
  nativeHeat019Y48,
  nativeHeat020Y48,
  nativeHeat021Y48,
  nativeHeat022Y48,
  nativeHeat023Y48,
  nativeHeat024Y48,
  nativeHeat025Y48,
  nativeHeat026Y48,
  nativeHeat027Y48,
  nativeHeat028Y48,
  nativeHeat029Y48,
  nativeHeat030Y48,
  nativeHeat031Y48,
  nativeHeat032Y48,
  nativeHeat033Y48,
  nativeHeat034Y48,
  nativeHeat035Y48,
  nativeHeat036Y48,
  nativeHeat037Y48,
  nativeHeat038Y48,
  nativeHeat039Y48,
  nativeHeat040Y48,
  nativeHeat041Y48,
  nativeHeat042Y48,
  nativeHeat043Y48,
  nativeHeat044Y48,
  nativeHeat045Y48,
  nativeHeat046Y48,
  nativeHeat047Y48,
  nativeHeat048Y48,
  nativeHeat049Y48,
  nativeHeat050Y48,
  nativeHeat051Y48,
  nativeHeat052Y48,
  nativeHeat053Y48,
  nativeHeat054Y48,
  nativeHeat055Y48,
  nativeHeat056Y48,
  nativeHeat057Y48,
  nativeHeat058Y48,
  nativeHeat059Y48,
  nativeHeat060Y48,
  nativeHeat061Y48,
  nativeHeat062Y48,
  nativeHeat063Y48,
  nativeHeat064Y48,
  nativeHeat065Y48,
  nativeHeat066Y48,
  nativeHeat067Y48,
  nativeHeat068Y48,
  nativeHeat069Y48,
  nativeHeat070Y48,
  nativeHeat071Y48,
  nativeHeat072Y48,
  nativeHeat073Y48,
  nativeHeat074Y48,
  nativeHeat075Y48,
  nativeHeat076Y48,
  nativeHeat077Y48,
  nativeHeat078Y48,
  nativeHeat079Y48,
  nativeHeat080Y48,
  nativeHeat081Y48,
  nativeHeat082Y48,
  nativeHeat083Y48,
  nativeHeat084Y48,
  nativeHeat085Y48,
  nativeHeat086Y48,
  nativeHeat087Y48,
  nativeHeat088Y48,
  nativeHeat089Y48,
  nativeHeat090Y48,
  nativeHeat091Y48,
  nativeHeat092Y48,
  nativeHeat093Y48,
  nativeHeat094Y48,
  nativeHeat095Y48,
  nativeHeat096Y48,
  nativeHeat097Y48,
  nativeHeat098Y48,
  nativeHeat099Y48,
  nativeHeat100Y48,
  nativeHeat101Y48,
  nativeHeat102Y48,
  nativeHeat103Y48,
  nativeHeat104Y48,
  nativeHeat105Y48,
  nativeHeat106Y48,
  nativeHeat107Y48,
  nativeHeat108Y48,
  nativeHeat109Y48,
  nativeHeat110Y48,
  nativeHeat111Y48,
  nativeHeat112Y48,
  nativeHeat113Y48,
  nativeHeat114Y48,
  nativeHeat115Y48,
  nativeHeat116Y48,
  nativeHeat117Y48,
  nativeHeat118Y48,
  nativeHeat119Y48,
  nativeHeat120Y48,
  nativeHeat121Y48,
  nativeHeat122Y48,
  nativeHeat123Y48,
  nativeHeat124Y48,
  nativeHeat125Y48,
  nativeHeat126Y48,
  nativeHeat127Y48,
  nativeHeat128Y48,
  nativeHeat129Y48,
  nativeHeat130Y48,
  nativeHeat131Y48,
  nativeHeat132Y48,
  nativeHeat133Y48,
  nativeHeat134Y48,
  nativeHeat135Y48,
  nativeHeat136Y48,
  nativeHeat137Y48,
  nativeHeat138Y48,
  nativeHeat139Y48,
  nativeHeat140Y48,
  nativeHeat141Y48,
  nativeHeat142Y48,
  nativeHeat143Y48,
  nativeHeat144Y48,
  nativeHeat145Y48,
  nativeHeat146Y48,
  nativeHeat147Y48,
  nativeHeat148Y48,
  nativeHeat149Y48,
  nativeHeat150Y48,
  nativeHeat151Y48,
  nativeHeat152Y48,
  nativeHeat153Y48,
  nativeHeat154Y48,
  nativeHeat155Y48,
  nativeHeat156Y48,
  nativeHeat157Y48,
  nativeHeat158Y48,
  nativeHeat159Y48,
  nativeHeat160Y48
]

theorem nativeHeatY48Gen_eq_table (g : ℕ) (h9 : 9 ≤ g) (h160 : g ≤ 160) :
    nativeHeatY48Gen g = nativeReturnsY48Table.getD (g - 9) 0 := by
  interval_cases g
  · exact nativeHeatStepY48_009_Gen
  · exact nativeHeatStepY48_010_Gen
  · exact nativeHeatStepY48_011_Gen
  · exact nativeHeatStepY48_012_Gen
  · exact nativeHeatStepY48_013_Gen
  · exact nativeHeatStepY48_014_Gen
  · exact nativeHeatStepY48_015_Gen
  · exact nativeHeatStepY48_016_Gen
  · exact nativeHeatStepY48_017_Gen
  · exact nativeHeatStepY48_018_Gen
  · exact nativeHeatStepY48_019_Gen
  · exact nativeHeatStepY48_020_Gen
  · exact nativeHeatStepY48_021_Gen
  · exact nativeHeatStepY48_022_Gen
  · exact nativeHeatStepY48_023_Gen
  · exact nativeHeatStepY48_024_Gen
  · exact nativeHeatStepY48_025_Gen
  · exact nativeHeatStepY48_026_Gen
  · exact nativeHeatStepY48_027_Gen
  · exact nativeHeatStepY48_028_Gen
  · exact nativeHeatStepY48_029_Gen
  · exact nativeHeatStepY48_030_Gen
  · exact nativeHeatStepY48_031_Gen
  · exact nativeHeatStepY48_032_Gen
  · exact nativeHeatStepY48_033_Gen
  · exact nativeHeatStepY48_034_Gen
  · exact nativeHeatStepY48_035_Gen
  · exact nativeHeatStepY48_036_Gen
  · exact nativeHeatStepY48_037_Gen
  · exact nativeHeatStepY48_038_Gen
  · exact nativeHeatStepY48_039_Gen
  · exact nativeHeatStepY48_040_Gen
  · exact nativeHeatStepY48_041_Gen
  · exact nativeHeatStepY48_042_Gen
  · exact nativeHeatStepY48_043_Gen
  · exact nativeHeatStepY48_044_Gen
  · exact nativeHeatStepY48_045_Gen
  · exact nativeHeatStepY48_046_Gen
  · exact nativeHeatStepY48_047_Gen
  · exact nativeHeatStepY48_048_Gen
  · exact nativeHeatStepY48_049_Gen
  · exact nativeHeatStepY48_050_Gen
  · exact nativeHeatStepY48_051_Gen
  · exact nativeHeatStepY48_052_Gen
  · exact nativeHeatStepY48_053_Gen
  · exact nativeHeatStepY48_054_Gen
  · exact nativeHeatStepY48_055_Gen
  · exact nativeHeatStepY48_056_Gen
  · exact nativeHeatStepY48_057_Gen
  · exact nativeHeatStepY48_058_Gen
  · exact nativeHeatStepY48_059_Gen
  · exact nativeHeatStepY48_060_Gen
  · exact nativeHeatStepY48_061_Gen
  · exact nativeHeatStepY48_062_Gen
  · exact nativeHeatStepY48_063_Gen
  · exact nativeHeatStepY48_064_Gen
  · exact nativeHeatStepY48_065_Gen
  · exact nativeHeatStepY48_066_Gen
  · exact nativeHeatStepY48_067_Gen
  · exact nativeHeatStepY48_068_Gen
  · exact nativeHeatStepY48_069_Gen
  · exact nativeHeatStepY48_070_Gen
  · exact nativeHeatStepY48_071_Gen
  · exact nativeHeatStepY48_072_Gen
  · exact nativeHeatStepY48_073_Gen
  · exact nativeHeatStepY48_074_Gen
  · exact nativeHeatStepY48_075_Gen
  · exact nativeHeatStepY48_076_Gen
  · exact nativeHeatStepY48_077_Gen
  · exact nativeHeatStepY48_078_Gen
  · exact nativeHeatStepY48_079_Gen
  · exact nativeHeatStepY48_080_Gen
  · exact nativeHeatStepY48_081_Gen
  · exact nativeHeatStepY48_082_Gen
  · exact nativeHeatStepY48_083_Gen
  · exact nativeHeatStepY48_084_Gen
  · exact nativeHeatStepY48_085_Gen
  · exact nativeHeatStepY48_086_Gen
  · exact nativeHeatStepY48_087_Gen
  · exact nativeHeatStepY48_088_Gen
  · exact nativeHeatStepY48_089_Gen
  · exact nativeHeatStepY48_090_Gen
  · exact nativeHeatStepY48_091_Gen
  · exact nativeHeatStepY48_092_Gen
  · exact nativeHeatStepY48_093_Gen
  · exact nativeHeatStepY48_094_Gen
  · exact nativeHeatStepY48_095_Gen
  · exact nativeHeatStepY48_096_Gen
  · exact nativeHeatStepY48_097_Gen
  · exact nativeHeatStepY48_098_Gen
  · exact nativeHeatStepY48_099_Gen
  · exact nativeHeatStepY48_100_Gen
  · exact nativeHeatStepY48_101_Gen
  · exact nativeHeatStepY48_102_Gen
  · exact nativeHeatStepY48_103_Gen
  · exact nativeHeatStepY48_104_Gen
  · exact nativeHeatStepY48_105_Gen
  · exact nativeHeatStepY48_106_Gen
  · exact nativeHeatStepY48_107_Gen
  · exact nativeHeatStepY48_108_Gen
  · exact nativeHeatStepY48_109_Gen
  · exact nativeHeatStepY48_110_Gen
  · exact nativeHeatStepY48_111_Gen
  · exact nativeHeatStepY48_112_Gen
  · exact nativeHeatStepY48_113_Gen
  · exact nativeHeatStepY48_114_Gen
  · exact nativeHeatStepY48_115_Gen
  · exact nativeHeatStepY48_116_Gen
  · exact nativeHeatStepY48_117_Gen
  · exact nativeHeatStepY48_118_Gen
  · exact nativeHeatStepY48_119_Gen
  · exact nativeHeatStepY48_120_Gen
  · exact nativeHeatStepY48_121_Gen
  · exact nativeHeatStepY48_122_Gen
  · exact nativeHeatStepY48_123_Gen
  · exact nativeHeatStepY48_124_Gen
  · exact nativeHeatStepY48_125_Gen
  · exact nativeHeatStepY48_126_Gen
  · exact nativeHeatStepY48_127_Gen
  · exact nativeHeatStepY48_128_Gen
  · exact nativeHeatStepY48_129_Gen
  · exact nativeHeatStepY48_130_Gen
  · exact nativeHeatStepY48_131_Gen
  · exact nativeHeatStepY48_132_Gen
  · exact nativeHeatStepY48_133_Gen
  · exact nativeHeatStepY48_134_Gen
  · exact nativeHeatStepY48_135_Gen
  · exact nativeHeatStepY48_136_Gen
  · exact nativeHeatStepY48_137_Gen
  · exact nativeHeatStepY48_138_Gen
  · exact nativeHeatStepY48_139_Gen
  · exact nativeHeatStepY48_140_Gen
  · exact nativeHeatStepY48_141_Gen
  · exact nativeHeatStepY48_142_Gen
  · exact nativeHeatStepY48_143_Gen
  · exact nativeHeatStepY48_144_Gen
  · exact nativeHeatStepY48_145_Gen
  · exact nativeHeatStepY48_146_Gen
  · exact nativeHeatStepY48_147_Gen
  · exact nativeHeatStepY48_148_Gen
  · exact nativeHeatStepY48_149_Gen
  · exact nativeHeatStepY48_150_Gen
  · exact nativeHeatStepY48_151_Gen
  · exact nativeHeatStepY48_152_Gen
  · exact nativeHeatStepY48_153_Gen
  · exact nativeHeatStepY48_154_Gen
  · exact nativeHeatStepY48_155_Gen
  · exact nativeHeatStepY48_156_Gen
  · exact nativeHeatStepY48_157_Gen
  · exact nativeHeatStepY48_158_Gen
  · exact nativeHeatStepY48_159_Gen
  · exact nativeHeatStepY48_160_Gen

theorem nativeReturnsY48Table_eq_result :
    ∀ i : Fin 152, nativeReturnsY48Table.getD i.val 0 = (nativeReturnsHeatTable.getD i.val (0, 0)).1 := by
  decide +kernel

theorem nativeHeatResultGen_fst_eq_Y48 (g : ℕ) (h9 : 9 ≤ g) (h160 : g ≤ 160) :
    (nativeHeatResultGen g).1 = nativeHeatY48Gen g := by
  rw [nativeHeatResultGen_eq_table g h9 h160, nativeHeatY48Gen_eq_table g h9 h160]
  exact (nativeReturnsY48Table_eq_result ⟨g - 9, by omega⟩).symm

end ASDExplicitGamma.Native
