module

public import ASDExplicitGamma.Native.HeatStepDataGenDispatch
public import ASDExplicitGamma.Numerics.Native.Returns

/-! NA-RETURNS: the table of heat returns `(min Y₄₈ y₀, mean)` for `9 ≤ g ≤ 160`, and the
identification of the generic heat result with the certified numerics. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

def nativeReturnsHeatTable : List (ℚ × ℚ) := [
  nativeHeat009Result,
  nativeHeat010Result,
  nativeHeat011Result,
  nativeHeat012Result,
  nativeHeat013Result,
  nativeHeat014Result,
  nativeHeat015Result,
  nativeHeat016Result,
  nativeHeat017Result,
  nativeHeat018Result,
  nativeHeat019Result,
  nativeHeat020Result,
  nativeHeat021Result,
  nativeHeat022Result,
  nativeHeat023Result,
  nativeHeat024Result,
  nativeHeat025Result,
  nativeHeat026Result,
  nativeHeat027Result,
  nativeHeat028Result,
  nativeHeat029Result,
  nativeHeat030Result,
  nativeHeat031Result,
  nativeHeat032Result,
  nativeHeat033Result,
  nativeHeat034Result,
  nativeHeat035Result,
  nativeHeat036Result,
  nativeHeat037Result,
  nativeHeat038Result,
  nativeHeat039Result,
  nativeHeat040Result,
  nativeHeat041Result,
  nativeHeat042Result,
  nativeHeat043Result,
  nativeHeat044Result,
  nativeHeat045Result,
  nativeHeat046Result,
  nativeHeat047Result,
  nativeHeat048Result,
  nativeHeat049Result,
  nativeHeat050Result,
  nativeHeat051Result,
  nativeHeat052Result,
  nativeHeat053Result,
  nativeHeat054Result,
  nativeHeat055Result,
  nativeHeat056Result,
  nativeHeat057Result,
  nativeHeat058Result,
  nativeHeat059Result,
  nativeHeat060Result,
  nativeHeat061Result,
  nativeHeat062Result,
  nativeHeat063Result,
  nativeHeat064Result,
  nativeHeat065Result,
  nativeHeat066Result,
  nativeHeat067Result,
  nativeHeat068Result,
  nativeHeat069Result,
  nativeHeat070Result,
  nativeHeat071Result,
  nativeHeat072Result,
  nativeHeat073Result,
  nativeHeat074Result,
  nativeHeat075Result,
  nativeHeat076Result,
  nativeHeat077Result,
  nativeHeat078Result,
  nativeHeat079Result,
  nativeHeat080Result,
  nativeHeat081Result,
  nativeHeat082Result,
  nativeHeat083Result,
  nativeHeat084Result,
  nativeHeat085Result,
  nativeHeat086Result,
  nativeHeat087Result,
  nativeHeat088Result,
  nativeHeat089Result,
  nativeHeat090Result,
  nativeHeat091Result,
  nativeHeat092Result,
  nativeHeat093Result,
  nativeHeat094Result,
  nativeHeat095Result,
  nativeHeat096Result,
  nativeHeat097Result,
  nativeHeat098Result,
  nativeHeat099Result,
  nativeHeat100Result,
  nativeHeat101Result,
  nativeHeat102Result,
  nativeHeat103Result,
  nativeHeat104Result,
  nativeHeat105Result,
  nativeHeat106Result,
  nativeHeat107Result,
  nativeHeat108Result,
  nativeHeat109Result,
  nativeHeat110Result,
  nativeHeat111Result,
  nativeHeat112Result,
  nativeHeat113Result,
  nativeHeat114Result,
  nativeHeat115Result,
  nativeHeat116Result,
  nativeHeat117Result,
  nativeHeat118Result,
  nativeHeat119Result,
  nativeHeat120Result,
  nativeHeat121Result,
  nativeHeat122Result,
  nativeHeat123Result,
  nativeHeat124Result,
  nativeHeat125Result,
  nativeHeat126Result,
  nativeHeat127Result,
  nativeHeat128Result,
  nativeHeat129Result,
  nativeHeat130Result,
  nativeHeat131Result,
  nativeHeat132Result,
  nativeHeat133Result,
  nativeHeat134Result,
  nativeHeat135Result,
  nativeHeat136Result,
  nativeHeat137Result,
  nativeHeat138Result,
  nativeHeat139Result,
  nativeHeat140Result,
  nativeHeat141Result,
  nativeHeat142Result,
  nativeHeat143Result,
  nativeHeat144Result,
  nativeHeat145Result,
  nativeHeat146Result,
  nativeHeat147Result,
  nativeHeat148Result,
  nativeHeat149Result,
  nativeHeat150Result,
  nativeHeat151Result,
  nativeHeat152Result,
  nativeHeat153Result,
  nativeHeat154Result,
  nativeHeat155Result,
  nativeHeat156Result,
  nativeHeat157Result,
  nativeHeat158Result,
  nativeHeat159Result,
  nativeHeat160Result
]

/-- The generic heat result is the certified numeric result, for every shell count `9 ≤ g ≤ 160`. -/
theorem nativeHeatResultGen_eq_table (g : ℕ) (h9 : 9 ≤ g) (h160 : g ≤ 160) :
    nativeHeatResultGen g = nativeReturnsHeatTable.getD (g - 9) (0, 0) := by
  interval_cases g
  · exact nativeHeatResultGen_009
  · exact nativeHeatResultGen_010
  · exact nativeHeatResultGen_011
  · exact nativeHeatResultGen_012
  · exact nativeHeatResultGen_013
  · exact nativeHeatResultGen_014
  · exact nativeHeatResultGen_015
  · exact nativeHeatResultGen_016
  · exact nativeHeatResultGen_017
  · exact nativeHeatResultGen_018
  · exact nativeHeatResultGen_019
  · exact nativeHeatResultGen_020
  · exact nativeHeatResultGen_021
  · exact nativeHeatResultGen_022
  · exact nativeHeatResultGen_023
  · exact nativeHeatResultGen_024
  · exact nativeHeatResultGen_025
  · exact nativeHeatResultGen_026
  · exact nativeHeatResultGen_027
  · exact nativeHeatResultGen_028
  · exact nativeHeatResultGen_029
  · exact nativeHeatResultGen_030
  · exact nativeHeatResultGen_031
  · exact nativeHeatResultGen_032
  · exact nativeHeatResultGen_033
  · exact nativeHeatResultGen_034
  · exact nativeHeatResultGen_035
  · exact nativeHeatResultGen_036
  · exact nativeHeatResultGen_037
  · exact nativeHeatResultGen_038
  · exact nativeHeatResultGen_039
  · exact nativeHeatResultGen_040
  · exact nativeHeatResultGen_041
  · exact nativeHeatResultGen_042
  · exact nativeHeatResultGen_043
  · exact nativeHeatResultGen_044
  · exact nativeHeatResultGen_045
  · exact nativeHeatResultGen_046
  · exact nativeHeatResultGen_047
  · exact nativeHeatResultGen_048
  · exact nativeHeatResultGen_049
  · exact nativeHeatResultGen_050
  · exact nativeHeatResultGen_051
  · exact nativeHeatResultGen_052
  · exact nativeHeatResultGen_053
  · exact nativeHeatResultGen_054
  · exact nativeHeatResultGen_055
  · exact nativeHeatResultGen_056
  · exact nativeHeatResultGen_057
  · exact nativeHeatResultGen_058
  · exact nativeHeatResultGen_059
  · exact nativeHeatResultGen_060
  · exact nativeHeatResultGen_061
  · exact nativeHeatResultGen_062
  · exact nativeHeatResultGen_063
  · exact nativeHeatResultGen_064
  · exact nativeHeatResultGen_065
  · exact nativeHeatResultGen_066
  · exact nativeHeatResultGen_067
  · exact nativeHeatResultGen_068
  · exact nativeHeatResultGen_069
  · exact nativeHeatResultGen_070
  · exact nativeHeatResultGen_071
  · exact nativeHeatResultGen_072
  · exact nativeHeatResultGen_073
  · exact nativeHeatResultGen_074
  · exact nativeHeatResultGen_075
  · exact nativeHeatResultGen_076
  · exact nativeHeatResultGen_077
  · exact nativeHeatResultGen_078
  · exact nativeHeatResultGen_079
  · exact nativeHeatResultGen_080
  · exact nativeHeatResultGen_081
  · exact nativeHeatResultGen_082
  · exact nativeHeatResultGen_083
  · exact nativeHeatResultGen_084
  · exact nativeHeatResultGen_085
  · exact nativeHeatResultGen_086
  · exact nativeHeatResultGen_087
  · exact nativeHeatResultGen_088
  · exact nativeHeatResultGen_089
  · exact nativeHeatResultGen_090
  · exact nativeHeatResultGen_091
  · exact nativeHeatResultGen_092
  · exact nativeHeatResultGen_093
  · exact nativeHeatResultGen_094
  · exact nativeHeatResultGen_095
  · exact nativeHeatResultGen_096
  · exact nativeHeatResultGen_097
  · exact nativeHeatResultGen_098
  · exact nativeHeatResultGen_099
  · exact nativeHeatResultGen_100
  · exact nativeHeatResultGen_101
  · exact nativeHeatResultGen_102
  · exact nativeHeatResultGen_103
  · exact nativeHeatResultGen_104
  · exact nativeHeatResultGen_105
  · exact nativeHeatResultGen_106
  · exact nativeHeatResultGen_107
  · exact nativeHeatResultGen_108
  · exact nativeHeatResultGen_109
  · exact nativeHeatResultGen_110
  · exact nativeHeatResultGen_111
  · exact nativeHeatResultGen_112
  · exact nativeHeatResultGen_113
  · exact nativeHeatResultGen_114
  · exact nativeHeatResultGen_115
  · exact nativeHeatResultGen_116
  · exact nativeHeatResultGen_117
  · exact nativeHeatResultGen_118
  · exact nativeHeatResultGen_119
  · exact nativeHeatResultGen_120
  · exact nativeHeatResultGen_121
  · exact nativeHeatResultGen_122
  · exact nativeHeatResultGen_123
  · exact nativeHeatResultGen_124
  · exact nativeHeatResultGen_125
  · exact nativeHeatResultGen_126
  · exact nativeHeatResultGen_127
  · exact nativeHeatResultGen_128
  · exact nativeHeatResultGen_129
  · exact nativeHeatResultGen_130
  · exact nativeHeatResultGen_131
  · exact nativeHeatResultGen_132
  · exact nativeHeatResultGen_133
  · exact nativeHeatResultGen_134
  · exact nativeHeatResultGen_135
  · exact nativeHeatResultGen_136
  · exact nativeHeatResultGen_137
  · exact nativeHeatResultGen_138
  · exact nativeHeatResultGen_139
  · exact nativeHeatResultGen_140
  · exact nativeHeatResultGen_141
  · exact nativeHeatResultGen_142
  · exact nativeHeatResultGen_143
  · exact nativeHeatResultGen_144
  · exact nativeHeatResultGen_145
  · exact nativeHeatResultGen_146
  · exact nativeHeatResultGen_147
  · exact nativeHeatResultGen_148
  · exact nativeHeatResultGen_149
  · exact nativeHeatResultGen_150
  · exact nativeHeatResultGen_151
  · exact nativeHeatResultGen_152
  · exact nativeHeatResultGen_153
  · exact nativeHeatResultGen_154
  · exact nativeHeatResultGen_155
  · exact nativeHeatResultGen_156
  · exact nativeHeatResultGen_157
  · exact nativeHeatResultGen_158
  · exact nativeHeatResultGen_159
  · exact nativeHeatResultGen_160

theorem nativeReturnsHeatTable_nonneg : ∀ i : Fin 152, 0 ≤ (nativeReturnsHeatTable.getD i.val (0, 0)).1 := by
  decide +kernel

theorem nativeHeatResultGen_fst_nonneg (g : ℕ) (h9 : 9 ≤ g) (h160 : g ≤ 160) :
    0 ≤ (nativeHeatResultGen g).1 := by
  rw [nativeHeatResultGen_eq_table g h9 h160]
  exact nativeReturnsHeatTable_nonneg ⟨g - 9, by omega⟩

end ASDExplicitGamma.Native
