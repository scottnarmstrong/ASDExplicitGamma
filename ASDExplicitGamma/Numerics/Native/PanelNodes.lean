module
public import ASDExplicitGamma.Numerics.Native.PanelFormula

/-! Named real DAG nodes, exposing the OLD panel formula without a deep stack reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics.Mirror

theorem nativePlanReal_append (stack : List ℝ) (xs ys : List Expr) :
    nativePlanReal stack (xs++ys) = nativePlanReal (nativePlanReal stack xs) ys := by
  induction xs generalizing stack with
  | nil => rfl
  | cons e es ih => exact ih _

noncomputable def nativePanelNode000 (_inputs : List ℝ) : ℝ := ((2/1 : ℚ) : ℝ)

noncomputable def nativePanelNode001 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode000 inputs)

noncomputable def nativePanelNode002 (_inputs : List ℝ) : ℝ := ((3/1 : ℚ) : ℝ)

noncomputable def nativePanelNode003 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode002 inputs)

noncomputable def nativePanelNode004 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode003 inputs)

noncomputable def nativePanelNode005 (_inputs : List ℝ) : ℝ := ((105/1 : ℚ) : ℝ)

noncomputable def nativePanelNode006 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode005 inputs)

noncomputable def nativePanelNode007 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode006 inputs)

noncomputable def nativePanelNode008 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode007 inputs)

noncomputable def nativePanelNode009 (_inputs : List ℝ) : ℝ := ((1/1 : ℚ) : ℝ)

noncomputable def nativePanelNode010 (inputs : List ℝ) : ℝ := (nativePanelNode009 inputs) / (nativePanelNode004 inputs)

noncomputable def nativePanelNode011 (inputs : List ℝ) : ℝ := (nativePanelNode010 inputs) + (nativePanelNode009 inputs)

noncomputable def nativePanelNode012 (inputs : List ℝ) : ℝ := (inputs.getD 7 0) * (inputs.getD 0 0)

noncomputable def nativePanelNode013 (inputs : List ℝ) : ℝ := (inputs.getD 4 0) + (nativePanelNode012 inputs)

noncomputable def nativePanelNode014 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode013 inputs)

noncomputable def nativePanelNode015 (inputs : List ℝ) : ℝ := (inputs.getD 17 0) * (nativePanelNode000 inputs)

noncomputable def nativePanelNode016 (inputs : List ℝ) : ℝ := (nativePanelNode015 inputs) * (inputs.getD 0 0)

noncomputable def nativePanelNode017 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode016 inputs)

noncomputable def nativePanelNode018 (_inputs : List ℝ) : ℝ := ((3683/2500 : ℚ) : ℝ)

noncomputable def nativePanelNode019 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode018 inputs)

noncomputable def nativePanelNode020 (inputs : List ℝ) : ℝ := (nativePanelNode004 inputs) * (nativePanelNode019 inputs)

noncomputable def nativePanelNode021 (_inputs : List ℝ) : ℝ := ((3/10000000000000000000000000000000000000000000000 : ℚ) : ℝ)

noncomputable def nativePanelNode022 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode021 inputs)

noncomputable def nativePanelNode023 (inputs : List ℝ) : ℝ := (nativePanelNode008 inputs) * (nativePanelNode022 inputs)

noncomputable def nativePanelNode024 (inputs : List ℝ) : ℝ := (nativePanelNode020 inputs) + (nativePanelNode023 inputs)

noncomputable def nativePanelNode025 (inputs : List ℝ) : ℝ := (nativePanelNode017 inputs) * (nativePanelNode024 inputs)

noncomputable def nativePanelNode026 (inputs : List ℝ) : ℝ := (nativePanelNode014 inputs) + (nativePanelNode025 inputs)

noncomputable def nativePanelNode027 (inputs : List ℝ) : ℝ := (nativePanelNode009 inputs) * (nativePanelNode026 inputs)

noncomputable def nativePanelNode028 (inputs : List ℝ) : ℝ := (nativePanelNode027 inputs) * (nativePanelNode026 inputs)

noncomputable def nativePanelNode029 (inputs : List ℝ) : ℝ := (inputs.getD 6 0) * (inputs.getD 0 0)

noncomputable def nativePanelNode030 (inputs : List ℝ) : ℝ := (inputs.getD 3 0) + (nativePanelNode029 inputs)

noncomputable def nativePanelNode031 (inputs : List ℝ) : ℝ := (inputs.getD 5 0) * (inputs.getD 0 0)

noncomputable def nativePanelNode032 (inputs : List ℝ) : ℝ := (inputs.getD 2 0) + (nativePanelNode031 inputs)

noncomputable def nativePanelNode033 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode032 inputs)

noncomputable def nativePanelNode034 (inputs : List ℝ) : ℝ := (nativePanelNode028 inputs) * (nativePanelNode000 inputs)

noncomputable def nativePanelNode035 (inputs : List ℝ) : ℝ := (nativePanelNode034 inputs) + (nativePanelNode009 inputs)

noncomputable def nativePanelNode036 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode034 inputs)

noncomputable def nativePanelNode037 (inputs : List ℝ) : ℝ := (nativePanelNode035 inputs) + (nativePanelNode036 inputs)

noncomputable def nativePanelNode038 (inputs : List ℝ) : ℝ := (nativePanelNode011 inputs) * (nativePanelNode037 inputs)

noncomputable def nativePanelNode039 (inputs : List ℝ) : ℝ := (nativePanelNode038 inputs) * (nativePanelNode028 inputs)

noncomputable def nativePanelNode040 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode039 inputs)

noncomputable def nativePanelNode041 (inputs : List ℝ) : ℝ := (nativePanelNode037 inputs) * (nativePanelNode018 inputs)

noncomputable def nativePanelNode042 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode041 inputs)

noncomputable def nativePanelNode043 (inputs : List ℝ) : ℝ := (nativePanelNode042 inputs) + (nativePanelNode009 inputs)

noncomputable def nativePanelNode044 (inputs : List ℝ) : ℝ := (nativePanelNode009 inputs) * (inputs.getD 13 0)

noncomputable def nativePanelNode045 (inputs : List ℝ) : ℝ := (nativePanelNode044 inputs) * (inputs.getD 13 0)

noncomputable def nativePanelNode046 (_inputs : List ℝ) : ℝ := ((38229489/6250000 : ℚ) : ℝ)

noncomputable def nativePanelNode047 (inputs : List ℝ) : ℝ := (nativePanelNode045 inputs) * (nativePanelNode046 inputs)

noncomputable def nativePanelNode048 (inputs : List ℝ) : ℝ := (nativePanelNode009 inputs) * (nativePanelNode042 inputs)

noncomputable def nativePanelNode049 (inputs : List ℝ) : ℝ := (nativePanelNode048 inputs) * (nativePanelNode042 inputs)

noncomputable def nativePanelNode050 (inputs : List ℝ) : ℝ := (nativePanelNode009 inputs) * (inputs.getD 12 0)

noncomputable def nativePanelNode051 (inputs : List ℝ) : ℝ := (nativePanelNode050 inputs) * (inputs.getD 12 0)

noncomputable def nativePanelNode052 (inputs : List ℝ) : ℝ := (nativePanelNode049 inputs) * (nativePanelNode051 inputs)

noncomputable def nativePanelNode053 (inputs : List ℝ) : ℝ := (nativePanelNode047 inputs) + (nativePanelNode052 inputs)

noncomputable def nativePanelNode054 (inputs : List ℝ) : ℝ := Real.sqrt (nativePanelNode053 inputs)

noncomputable def nativePanelNode055 (inputs : List ℝ) : ℝ := (nativePanelNode001 inputs) * (nativePanelNode033 inputs)

noncomputable def nativePanelNode056 (inputs : List ℝ) : ℝ := (nativePanelNode055 inputs) * (inputs.getD 9 0)

noncomputable def nativePanelNode057 (inputs : List ℝ) : ℝ := (nativePanelNode056 inputs) * (inputs.getD 13 0)

noncomputable def nativePanelNode058 (inputs : List ℝ) : ℝ := (nativePanelNode001 inputs) * (nativePanelNode000 inputs)

noncomputable def nativePanelNode059 (inputs : List ℝ) : ℝ := (nativePanelNode058 inputs) * (nativePanelNode040 inputs)

noncomputable def nativePanelNode060 (inputs : List ℝ) : ℝ := (nativePanelNode059 inputs) * (inputs.getD 8 0)

noncomputable def nativePanelNode061 (inputs : List ℝ) : ℝ := (nativePanelNode060 inputs) * (inputs.getD 12 0)

noncomputable def nativePanelNode062 (inputs : List ℝ) : ℝ := (nativePanelNode057 inputs) + (nativePanelNode061 inputs)

noncomputable def nativePanelNode063 (inputs : List ℝ) : ℝ := (nativePanelNode045 inputs) * (nativePanelNode018 inputs)

noncomputable def nativePanelNode064 (inputs : List ℝ) : ℝ := (nativePanelNode062 inputs) + (nativePanelNode063 inputs)

noncomputable def nativePanelNode065 (inputs : List ℝ) : ℝ := (nativePanelNode037 inputs) * (nativePanelNode051 inputs)

noncomputable def nativePanelNode066 (inputs : List ℝ) : ℝ := (nativePanelNode064 inputs) + (nativePanelNode065 inputs)

noncomputable def nativePanelNode067 (inputs : List ℝ) : ℝ := (inputs.getD 14 0) * (nativePanelNode000 inputs)

noncomputable def nativePanelNode068 (inputs : List ℝ) : ℝ := (nativePanelNode033 inputs) * (inputs.getD 8 0)

noncomputable def nativePanelNode069 (inputs : List ℝ) : ℝ := (nativePanelNode001 inputs) * (nativePanelNode043 inputs)

noncomputable def nativePanelNode070 (inputs : List ℝ) : ℝ := (nativePanelNode069 inputs) * (inputs.getD 12 0)

noncomputable def nativePanelNode071 (inputs : List ℝ) : ℝ := (nativePanelNode068 inputs) + (nativePanelNode070 inputs)

noncomputable def nativePanelNode072 (inputs : List ℝ) : ℝ := (nativePanelNode067 inputs) * (nativePanelNode071 inputs)

noncomputable def nativePanelNode073 (inputs : List ℝ) : ℝ := (nativePanelNode066 inputs) + (nativePanelNode072 inputs)

noncomputable def nativePanelNode074 (inputs : List ℝ) : ℝ := (nativePanelNode009 inputs) * (inputs.getD 15 0)

noncomputable def nativePanelNode075 (inputs : List ℝ) : ℝ := (nativePanelNode074 inputs) * (inputs.getD 15 0)

noncomputable def nativePanelNode076 (inputs : List ℝ) : ℝ := (nativePanelNode075 inputs) * (nativePanelNode018 inputs)

noncomputable def nativePanelNode077 (inputs : List ℝ) : ℝ := (inputs.getD 15 0) * (nativePanelNode000 inputs)

noncomputable def nativePanelNode078 (inputs : List ℝ) : ℝ := (nativePanelNode077 inputs) * (nativePanelNode033 inputs)

noncomputable def nativePanelNode079 (inputs : List ℝ) : ℝ := Real.sqrt (inputs.getD 17 0)

noncomputable def nativePanelNode080 (inputs : List ℝ) : ℝ := (nativePanelNode078 inputs) * (nativePanelNode079 inputs)

noncomputable def nativePanelNode081 (inputs : List ℝ) : ℝ := (nativePanelNode077 inputs) * (nativePanelNode054 inputs)

noncomputable def nativePanelNode082 (inputs : List ℝ) : ℝ := (nativePanelNode080 inputs) + (nativePanelNode081 inputs)

noncomputable def nativePanelNode083 (inputs : List ℝ) : ℝ := (nativePanelNode067 inputs) * (nativePanelNode011 inputs)

noncomputable def nativePanelNode084 (inputs : List ℝ) : ℝ := (nativePanelNode083 inputs) * (inputs.getD 15 0)

noncomputable def nativePanelNode085 (inputs : List ℝ) : ℝ := (nativePanelNode084 inputs) * (nativePanelNode018 inputs)

noncomputable def nativePanelNode086 (inputs : List ℝ) : ℝ := (nativePanelNode085 inputs) * (nativePanelNode001 inputs)

noncomputable def nativePanelNode087 (inputs : List ℝ) : ℝ := (nativePanelNode082 inputs) + (nativePanelNode086 inputs)

noncomputable def nativePanelNode088 (inputs : List ℝ) : ℝ := (inputs.getD 9 0) + (inputs.getD 8 0)

noncomputable def nativePanelNode089 (inputs : List ℝ) : ℝ := (nativePanelNode033 inputs) * (nativePanelNode088 inputs)

noncomputable def nativePanelNode090 (inputs : List ℝ) : ℝ := (nativePanelNode089 inputs) / (nativePanelNode001 inputs)

noncomputable def nativePanelNode091 (inputs : List ℝ) : ℝ := (nativePanelNode011 inputs) * (nativePanelNode018 inputs)

noncomputable def nativePanelNode092 (inputs : List ℝ) : ℝ := (nativePanelNode091 inputs) * (inputs.getD 13 0)

noncomputable def nativePanelNode093 (inputs : List ℝ) : ℝ := (nativePanelNode090 inputs) + (nativePanelNode092 inputs)

noncomputable def nativePanelNode094 (inputs : List ℝ) : ℝ := (nativePanelNode043 inputs) * (inputs.getD 12 0)

noncomputable def nativePanelNode095 (inputs : List ℝ) : ℝ := (nativePanelNode093 inputs) + (nativePanelNode094 inputs)

noncomputable def nativePanelNode096 (inputs : List ℝ) : ℝ := (nativePanelNode067 inputs) * (nativePanelNode095 inputs)

noncomputable def nativePanelNode097 (inputs : List ℝ) : ℝ := (nativePanelNode076 inputs) * (nativePanelNode032 inputs)

noncomputable def nativePanelNode098 (inputs : List ℝ) : ℝ := (nativePanelNode073 inputs) + (nativePanelNode097 inputs)

noncomputable def nativePanelNode099 (inputs : List ℝ) : ℝ := (nativePanelNode087 inputs) * (nativePanelNode033 inputs)

noncomputable def nativePanelNode100 (inputs : List ℝ) : ℝ := (nativePanelNode098 inputs) + (nativePanelNode099 inputs)

noncomputable def nativePanelNode101 (inputs : List ℝ) : ℝ := (nativePanelNode096 inputs) * (nativePanelNode001 inputs)

noncomputable def nativePanelNode102 (inputs : List ℝ) : ℝ := (nativePanelNode101 inputs) * (nativePanelNode033 inputs)

noncomputable def nativePanelNode103 (inputs : List ℝ) : ℝ := (nativePanelNode100 inputs) + (nativePanelNode102 inputs)

noncomputable def nativePanelNode104 (inputs : List ℝ) : ℝ := (nativePanelNode085 inputs) * (nativePanelNode032 inputs)

noncomputable def nativePanelNode105 (inputs : List ℝ) : ℝ := (nativePanelNode103 inputs) + (nativePanelNode104 inputs)

noncomputable def nativePanelNode106 (inputs : List ℝ) : ℝ := (inputs.getD 11 0) * (nativePanelNode000 inputs)

noncomputable def nativePanelNode107 (inputs : List ℝ) : ℝ := (nativePanelNode106 inputs) * (nativePanelNode033 inputs)

noncomputable def nativePanelNode108 (inputs : List ℝ) : ℝ := (nativePanelNode105 inputs) + (nativePanelNode107 inputs)

noncomputable def nativePanelNode109 (inputs : List ℝ) : ℝ := (inputs.getD 10 0) * (nativePanelNode000 inputs)

noncomputable def nativePanelNode110 (inputs : List ℝ) : ℝ := (nativePanelNode109 inputs) * (nativePanelNode001 inputs)

noncomputable def nativePanelNode111 (inputs : List ℝ) : ℝ := (nativePanelNode110 inputs) * (nativePanelNode033 inputs)

noncomputable def nativePanelNode112 (inputs : List ℝ) : ℝ := (nativePanelNode108 inputs) + (nativePanelNode111 inputs)

noncomputable def nativePanelNode113 (inputs : List ℝ) : ℝ := (inputs.getD 1 0) / (nativePanelNode000 inputs)

noncomputable def nativePanelNode114 (inputs : List ℝ) : ℝ := (nativePanelNode113 inputs) * (nativePanelNode030 inputs)

noncomputable def nativePanelNode115 (_inputs : List ℝ) : ℝ := ((1183/2500 : ℚ) : ℝ)

noncomputable def nativePanelNode116 (inputs : List ℝ) : ℝ := (nativePanelNode015 inputs) * (nativePanelNode115 inputs)

noncomputable def nativePanelNode117 (inputs : List ℝ) : ℝ := (nativePanelNode114 inputs) + (nativePanelNode116 inputs)

noncomputable def nativePanelNode118 (_inputs : List ℝ) : ℝ := ((4/1 : ℚ) : ℝ)

noncomputable def nativePanelNode119 (inputs : List ℝ) : ℝ := (nativePanelNode058 inputs) + (nativePanelNode118 inputs)

noncomputable def nativePanelNode120 (_inputs : List ℝ) : ℝ := ((156/5 : ℚ) : ℝ)

noncomputable def nativePanelNode121 (inputs : List ℝ) : ℝ := (nativePanelNode119 inputs) * (nativePanelNode120 inputs)

noncomputable def nativePanelNode122 (inputs : List ℝ) : ℝ := (nativePanelNode121 inputs) * (inputs.getD 16 0)

noncomputable def nativePanelNode123 (_inputs : List ℝ) : ℝ := ((9/1 : ℚ) : ℝ)

noncomputable def nativePanelNode124 (inputs : List ℝ) : ℝ := (nativePanelNode122 inputs) / (nativePanelNode123 inputs)

noncomputable def nativePanelNode125 (inputs : List ℝ) : ℝ := (nativePanelNode117 inputs) + (nativePanelNode124 inputs)

noncomputable def nativePanelNode126 (inputs : List ℝ) : ℝ := (nativePanelNode125 inputs) + (nativePanelNode112 inputs)

def nativePanelOpsChunk000 : List Expr := [
  .const (2/1 : ℚ),
  .sqrt (.var 0),
  .const (3/1 : ℚ),
  .sqrt (.var 0),
  .sqrt (.var 0),
  .const (105/1 : ℚ),
  .sqrt (.var 0),
  .sqrt (.var 0),
  .sqrt (.var 0),
  .const (1/1 : ℚ),
  .divPos (.var 0) (.var 5),
  .add (.var 0) (.var 1),
  .mul (.var 19) (.var 12),
  .add (.var 17) (.var 0),
  .sqrt (.var 0),
  .mul (.var 32) (.var 14)
]

noncomputable def nativePanelStack000 (inputs : List ℝ) : List ℝ := [] ++ inputs

theorem nativePanelChunk000_real (inputs : List ℝ) :
    nativePlanReal (nativePanelStack000 inputs) nativePanelOpsChunk000 = [nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs := by
  rfl

def nativePanelOpsChunk016 : List Expr := [
  .mul (.var 0) (.var 16),
  .sqrt (.var 0),
  .const (3683/2500 : ℚ),
  .sqrt (.var 0),
  .mul (.var 15) (.var 0),
  .const (3/10000000000000000000000000000000000000000000000 : ℚ),
  .sqrt (.var 0),
  .mul (.var 14) (.var 0),
  .add (.var 3) (.var 0),
  .mul (.var 7) (.var 0),
  .add (.var 11) (.var 0),
  .mul (.var 17) (.var 0),
  .mul (.var 0) (.var 1),
  .mul (.var 35) (.var 29),
  .add (.var 33) (.var 0),
  .mul (.var 36) (.var 31)
]

noncomputable def nativePanelStack016 (inputs : List ℝ) : List ℝ := [nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs

theorem nativePanelChunk016_real (inputs : List ℝ) :
    nativePlanReal (nativePanelStack016 inputs) nativePanelOpsChunk016 = [nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs := by
  rfl

def nativePanelOpsChunk032 : List Expr := [
  .add (.var 34) (.var 0),
  .sqrt (.var 0),
  .mul (.var 5) (.var 33),
  .add (.var 0) (.var 25),
  .sqrt (.var 1),
  .add (.var 1) (.var 0),
  .mul (.var 26) (.var 0),
  .mul (.var 0) (.var 10),
  .sqrt (.var 0),
  .mul (.var 3) (.var 22),
  .sqrt (.var 0),
  .add (.var 0) (.var 33),
  .mul (.var 34) (.var 57),
  .mul (.var 0) (.var 58),
  .const (38229489/6250000 : ℚ),
  .mul (.var 1) (.var 0)
]

noncomputable def nativePanelStack032 (inputs : List ℝ) : List ℝ := [nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs

theorem nativePanelChunk032_real (inputs : List ℝ) :
    nativePlanReal (nativePanelStack032 inputs) nativePanelOpsChunk032 = [nativePanelNode047 inputs, nativePanelNode046 inputs, nativePanelNode045 inputs, nativePanelNode044 inputs, nativePanelNode043 inputs, nativePanelNode042 inputs, nativePanelNode041 inputs, nativePanelNode040 inputs, nativePanelNode039 inputs, nativePanelNode038 inputs, nativePanelNode037 inputs, nativePanelNode036 inputs, nativePanelNode035 inputs, nativePanelNode034 inputs, nativePanelNode033 inputs, nativePanelNode032 inputs, nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs := by
  rfl

def nativePanelOpsChunk048 : List Expr := [
  .mul (.var 38) (.var 5),
  .mul (.var 0) (.var 6),
  .mul (.var 40) (.var 62),
  .mul (.var 0) (.var 63),
  .mul (.var 2) (.var 0),
  .add (.var 5) (.var 0),
  .sqrt (.var 0),
  .mul (.var 53) (.var 21),
  .mul (.var 0) (.var 65),
  .mul (.var 0) (.var 70),
  .mul (.var 56) (.var 57),
  .mul (.var 0) (.var 18),
  .mul (.var 0) (.var 68),
  .mul (.var 0) (.var 73),
  .add (.var 4) (.var 0),
  .mul (.var 17) (.var 44)
]

noncomputable def nativePanelStack048 (inputs : List ℝ) : List ℝ := [nativePanelNode047 inputs, nativePanelNode046 inputs, nativePanelNode045 inputs, nativePanelNode044 inputs, nativePanelNode043 inputs, nativePanelNode042 inputs, nativePanelNode041 inputs, nativePanelNode040 inputs, nativePanelNode039 inputs, nativePanelNode038 inputs, nativePanelNode037 inputs, nativePanelNode036 inputs, nativePanelNode035 inputs, nativePanelNode034 inputs, nativePanelNode033 inputs, nativePanelNode032 inputs, nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs

theorem nativePanelChunk048_real (inputs : List ℝ) :
    nativePlanReal (nativePanelStack048 inputs) nativePanelOpsChunk048 = [nativePanelNode063 inputs, nativePanelNode062 inputs, nativePanelNode061 inputs, nativePanelNode060 inputs, nativePanelNode059 inputs, nativePanelNode058 inputs, nativePanelNode057 inputs, nativePanelNode056 inputs, nativePanelNode055 inputs, nativePanelNode054 inputs, nativePanelNode053 inputs, nativePanelNode052 inputs, nativePanelNode051 inputs, nativePanelNode050 inputs, nativePanelNode049 inputs, nativePanelNode048 inputs, nativePanelNode047 inputs, nativePanelNode046 inputs, nativePanelNode045 inputs, nativePanelNode044 inputs, nativePanelNode043 inputs, nativePanelNode042 inputs, nativePanelNode041 inputs, nativePanelNode040 inputs, nativePanelNode039 inputs, nativePanelNode038 inputs, nativePanelNode037 inputs, nativePanelNode036 inputs, nativePanelNode035 inputs, nativePanelNode034 inputs, nativePanelNode033 inputs, nativePanelNode032 inputs, nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs := by
  rfl

def nativePanelOpsChunk064 : List Expr := [
  .add (.var 1) (.var 0),
  .mul (.var 27) (.var 13),
  .add (.var 1) (.var 0),
  .mul (.var 81) (.var 66),
  .mul (.var 34) (.var 76),
  .mul (.var 67) (.var 25),
  .mul (.var 0) (.var 82),
  .add (.var 2) (.var 0),
  .mul (.var 4) (.var 0),
  .add (.var 6) (.var 0),
  .mul (.var 64) (.var 89),
  .mul (.var 0) (.var 90),
  .mul (.var 0) (.var 57),
  .mul (.var 92) (.var 76),
  .mul (.var 0) (.var 44),
  .sqrt (.var 96)
]

noncomputable def nativePanelStack064 (inputs : List ℝ) : List ℝ := [nativePanelNode063 inputs, nativePanelNode062 inputs, nativePanelNode061 inputs, nativePanelNode060 inputs, nativePanelNode059 inputs, nativePanelNode058 inputs, nativePanelNode057 inputs, nativePanelNode056 inputs, nativePanelNode055 inputs, nativePanelNode054 inputs, nativePanelNode053 inputs, nativePanelNode052 inputs, nativePanelNode051 inputs, nativePanelNode050 inputs, nativePanelNode049 inputs, nativePanelNode048 inputs, nativePanelNode047 inputs, nativePanelNode046 inputs, nativePanelNode045 inputs, nativePanelNode044 inputs, nativePanelNode043 inputs, nativePanelNode042 inputs, nativePanelNode041 inputs, nativePanelNode040 inputs, nativePanelNode039 inputs, nativePanelNode038 inputs, nativePanelNode037 inputs, nativePanelNode036 inputs, nativePanelNode035 inputs, nativePanelNode034 inputs, nativePanelNode033 inputs, nativePanelNode032 inputs, nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs

theorem nativePanelChunk064_real (inputs : List ℝ) :
    nativePlanReal (nativePanelStack064 inputs) nativePanelOpsChunk064 = [nativePanelNode079 inputs, nativePanelNode078 inputs, nativePanelNode077 inputs, nativePanelNode076 inputs, nativePanelNode075 inputs, nativePanelNode074 inputs, nativePanelNode073 inputs, nativePanelNode072 inputs, nativePanelNode071 inputs, nativePanelNode070 inputs, nativePanelNode069 inputs, nativePanelNode068 inputs, nativePanelNode067 inputs, nativePanelNode066 inputs, nativePanelNode065 inputs, nativePanelNode064 inputs, nativePanelNode063 inputs, nativePanelNode062 inputs, nativePanelNode061 inputs, nativePanelNode060 inputs, nativePanelNode059 inputs, nativePanelNode058 inputs, nativePanelNode057 inputs, nativePanelNode056 inputs, nativePanelNode055 inputs, nativePanelNode054 inputs, nativePanelNode053 inputs, nativePanelNode052 inputs, nativePanelNode051 inputs, nativePanelNode050 inputs, nativePanelNode049 inputs, nativePanelNode048 inputs, nativePanelNode047 inputs, nativePanelNode046 inputs, nativePanelNode045 inputs, nativePanelNode044 inputs, nativePanelNode043 inputs, nativePanelNode042 inputs, nativePanelNode041 inputs, nativePanelNode040 inputs, nativePanelNode039 inputs, nativePanelNode038 inputs, nativePanelNode037 inputs, nativePanelNode036 inputs, nativePanelNode035 inputs, nativePanelNode034 inputs, nativePanelNode033 inputs, nativePanelNode032 inputs, nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs := by
  rfl

def nativePanelOpsChunk080 : List Expr := [
  .mul (.var 1) (.var 0),
  .mul (.var 3) (.var 26),
  .add (.var 1) (.var 0),
  .mul (.var 15) (.var 71),
  .mul (.var 0) (.var 99),
  .mul (.var 0) (.var 66),
  .mul (.var 0) (.var 84),
  .add (.var 4) (.var 0),
  .add (.var 97) (.var 96),
  .mul (.var 55) (.var 0),
  .divPos (.var 0) (.var 88),
  .mul (.var 79) (.var 72),
  .mul (.var 0) (.var 105),
  .add (.var 2) (.var 0),
  .mul (.var 50) (.var 106),
  .add (.var 1) (.var 0)
]

noncomputable def nativePanelStack080 (inputs : List ℝ) : List ℝ := [nativePanelNode079 inputs, nativePanelNode078 inputs, nativePanelNode077 inputs, nativePanelNode076 inputs, nativePanelNode075 inputs, nativePanelNode074 inputs, nativePanelNode073 inputs, nativePanelNode072 inputs, nativePanelNode071 inputs, nativePanelNode070 inputs, nativePanelNode069 inputs, nativePanelNode068 inputs, nativePanelNode067 inputs, nativePanelNode066 inputs, nativePanelNode065 inputs, nativePanelNode064 inputs, nativePanelNode063 inputs, nativePanelNode062 inputs, nativePanelNode061 inputs, nativePanelNode060 inputs, nativePanelNode059 inputs, nativePanelNode058 inputs, nativePanelNode057 inputs, nativePanelNode056 inputs, nativePanelNode055 inputs, nativePanelNode054 inputs, nativePanelNode053 inputs, nativePanelNode052 inputs, nativePanelNode051 inputs, nativePanelNode050 inputs, nativePanelNode049 inputs, nativePanelNode048 inputs, nativePanelNode047 inputs, nativePanelNode046 inputs, nativePanelNode045 inputs, nativePanelNode044 inputs, nativePanelNode043 inputs, nativePanelNode042 inputs, nativePanelNode041 inputs, nativePanelNode040 inputs, nativePanelNode039 inputs, nativePanelNode038 inputs, nativePanelNode037 inputs, nativePanelNode036 inputs, nativePanelNode035 inputs, nativePanelNode034 inputs, nativePanelNode033 inputs, nativePanelNode032 inputs, nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs

theorem nativePanelChunk080_real (inputs : List ℝ) :
    nativePlanReal (nativePanelStack080 inputs) nativePanelOpsChunk080 = [nativePanelNode095 inputs, nativePanelNode094 inputs, nativePanelNode093 inputs, nativePanelNode092 inputs, nativePanelNode091 inputs, nativePanelNode090 inputs, nativePanelNode089 inputs, nativePanelNode088 inputs, nativePanelNode087 inputs, nativePanelNode086 inputs, nativePanelNode085 inputs, nativePanelNode084 inputs, nativePanelNode083 inputs, nativePanelNode082 inputs, nativePanelNode081 inputs, nativePanelNode080 inputs, nativePanelNode079 inputs, nativePanelNode078 inputs, nativePanelNode077 inputs, nativePanelNode076 inputs, nativePanelNode075 inputs, nativePanelNode074 inputs, nativePanelNode073 inputs, nativePanelNode072 inputs, nativePanelNode071 inputs, nativePanelNode070 inputs, nativePanelNode069 inputs, nativePanelNode068 inputs, nativePanelNode067 inputs, nativePanelNode066 inputs, nativePanelNode065 inputs, nativePanelNode064 inputs, nativePanelNode063 inputs, nativePanelNode062 inputs, nativePanelNode061 inputs, nativePanelNode060 inputs, nativePanelNode059 inputs, nativePanelNode058 inputs, nativePanelNode057 inputs, nativePanelNode056 inputs, nativePanelNode055 inputs, nativePanelNode054 inputs, nativePanelNode053 inputs, nativePanelNode052 inputs, nativePanelNode051 inputs, nativePanelNode050 inputs, nativePanelNode049 inputs, nativePanelNode048 inputs, nativePanelNode047 inputs, nativePanelNode046 inputs, nativePanelNode045 inputs, nativePanelNode044 inputs, nativePanelNode043 inputs, nativePanelNode042 inputs, nativePanelNode041 inputs, nativePanelNode040 inputs, nativePanelNode039 inputs, nativePanelNode038 inputs, nativePanelNode037 inputs, nativePanelNode036 inputs, nativePanelNode035 inputs, nativePanelNode034 inputs, nativePanelNode033 inputs, nativePanelNode032 inputs, nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs := by
  rfl

def nativePanelOpsChunk096 : List Expr := [
  .mul (.var 28) (.var 0),
  .mul (.var 20) (.var 64),
  .add (.var 24) (.var 0),
  .mul (.var 11) (.var 65),
  .add (.var 1) (.var 0),
  .mul (.var 4) (.var 99),
  .mul (.var 0) (.var 68),
  .add (.var 2) (.var 0),
  .mul (.var 18) (.var 71),
  .add (.var 1) (.var 0),
  .mul (.var 117) (.var 105),
  .mul (.var 0) (.var 73),
  .add (.var 2) (.var 0),
  .mul (.var 119) (.var 108),
  .mul (.var 0) (.var 108),
  .mul (.var 0) (.var 77)
]

noncomputable def nativePanelStack096 (inputs : List ℝ) : List ℝ := [nativePanelNode095 inputs, nativePanelNode094 inputs, nativePanelNode093 inputs, nativePanelNode092 inputs, nativePanelNode091 inputs, nativePanelNode090 inputs, nativePanelNode089 inputs, nativePanelNode088 inputs, nativePanelNode087 inputs, nativePanelNode086 inputs, nativePanelNode085 inputs, nativePanelNode084 inputs, nativePanelNode083 inputs, nativePanelNode082 inputs, nativePanelNode081 inputs, nativePanelNode080 inputs, nativePanelNode079 inputs, nativePanelNode078 inputs, nativePanelNode077 inputs, nativePanelNode076 inputs, nativePanelNode075 inputs, nativePanelNode074 inputs, nativePanelNode073 inputs, nativePanelNode072 inputs, nativePanelNode071 inputs, nativePanelNode070 inputs, nativePanelNode069 inputs, nativePanelNode068 inputs, nativePanelNode067 inputs, nativePanelNode066 inputs, nativePanelNode065 inputs, nativePanelNode064 inputs, nativePanelNode063 inputs, nativePanelNode062 inputs, nativePanelNode061 inputs, nativePanelNode060 inputs, nativePanelNode059 inputs, nativePanelNode058 inputs, nativePanelNode057 inputs, nativePanelNode056 inputs, nativePanelNode055 inputs, nativePanelNode054 inputs, nativePanelNode053 inputs, nativePanelNode052 inputs, nativePanelNode051 inputs, nativePanelNode050 inputs, nativePanelNode049 inputs, nativePanelNode048 inputs, nativePanelNode047 inputs, nativePanelNode046 inputs, nativePanelNode045 inputs, nativePanelNode044 inputs, nativePanelNode043 inputs, nativePanelNode042 inputs, nativePanelNode041 inputs, nativePanelNode040 inputs, nativePanelNode039 inputs, nativePanelNode038 inputs, nativePanelNode037 inputs, nativePanelNode036 inputs, nativePanelNode035 inputs, nativePanelNode034 inputs, nativePanelNode033 inputs, nativePanelNode032 inputs, nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs

theorem nativePanelChunk096_real (inputs : List ℝ) :
    nativePlanReal (nativePanelStack096 inputs) nativePanelOpsChunk096 = [nativePanelNode111 inputs, nativePanelNode110 inputs, nativePanelNode109 inputs, nativePanelNode108 inputs, nativePanelNode107 inputs, nativePanelNode106 inputs, nativePanelNode105 inputs, nativePanelNode104 inputs, nativePanelNode103 inputs, nativePanelNode102 inputs, nativePanelNode101 inputs, nativePanelNode100 inputs, nativePanelNode099 inputs, nativePanelNode098 inputs, nativePanelNode097 inputs, nativePanelNode096 inputs, nativePanelNode095 inputs, nativePanelNode094 inputs, nativePanelNode093 inputs, nativePanelNode092 inputs, nativePanelNode091 inputs, nativePanelNode090 inputs, nativePanelNode089 inputs, nativePanelNode088 inputs, nativePanelNode087 inputs, nativePanelNode086 inputs, nativePanelNode085 inputs, nativePanelNode084 inputs, nativePanelNode083 inputs, nativePanelNode082 inputs, nativePanelNode081 inputs, nativePanelNode080 inputs, nativePanelNode079 inputs, nativePanelNode078 inputs, nativePanelNode077 inputs, nativePanelNode076 inputs, nativePanelNode075 inputs, nativePanelNode074 inputs, nativePanelNode073 inputs, nativePanelNode072 inputs, nativePanelNode071 inputs, nativePanelNode070 inputs, nativePanelNode069 inputs, nativePanelNode068 inputs, nativePanelNode067 inputs, nativePanelNode066 inputs, nativePanelNode065 inputs, nativePanelNode064 inputs, nativePanelNode063 inputs, nativePanelNode062 inputs, nativePanelNode061 inputs, nativePanelNode060 inputs, nativePanelNode059 inputs, nativePanelNode058 inputs, nativePanelNode057 inputs, nativePanelNode056 inputs, nativePanelNode055 inputs, nativePanelNode054 inputs, nativePanelNode053 inputs, nativePanelNode052 inputs, nativePanelNode051 inputs, nativePanelNode050 inputs, nativePanelNode049 inputs, nativePanelNode048 inputs, nativePanelNode047 inputs, nativePanelNode046 inputs, nativePanelNode045 inputs, nativePanelNode044 inputs, nativePanelNode043 inputs, nativePanelNode042 inputs, nativePanelNode041 inputs, nativePanelNode040 inputs, nativePanelNode039 inputs, nativePanelNode038 inputs, nativePanelNode037 inputs, nativePanelNode036 inputs, nativePanelNode035 inputs, nativePanelNode034 inputs, nativePanelNode033 inputs, nativePanelNode032 inputs, nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs := by
  rfl

def nativePanelOpsChunk112 : List Expr := [
  .add (.var 3) (.var 0),
  .divPos (.var 114) (.var 112),
  .mul (.var 0) (.var 83),
  .const (1183/2500 : ℚ),
  .mul (.var 100) (.var 0),
  .add (.var 2) (.var 0),
  .const (4/1 : ℚ),
  .add (.var 60) (.var 0),
  .const (156/5 : ℚ),
  .mul (.var 1) (.var 0),
  .mul (.var 0) (.var 138),
  .const (9/1 : ℚ),
  .divPos (.var 1) (.var 0),
  .add (.var 7) (.var 0),
  .add (.var 0) (.var 13)
]

noncomputable def nativePanelStack112 (inputs : List ℝ) : List ℝ := [nativePanelNode111 inputs, nativePanelNode110 inputs, nativePanelNode109 inputs, nativePanelNode108 inputs, nativePanelNode107 inputs, nativePanelNode106 inputs, nativePanelNode105 inputs, nativePanelNode104 inputs, nativePanelNode103 inputs, nativePanelNode102 inputs, nativePanelNode101 inputs, nativePanelNode100 inputs, nativePanelNode099 inputs, nativePanelNode098 inputs, nativePanelNode097 inputs, nativePanelNode096 inputs, nativePanelNode095 inputs, nativePanelNode094 inputs, nativePanelNode093 inputs, nativePanelNode092 inputs, nativePanelNode091 inputs, nativePanelNode090 inputs, nativePanelNode089 inputs, nativePanelNode088 inputs, nativePanelNode087 inputs, nativePanelNode086 inputs, nativePanelNode085 inputs, nativePanelNode084 inputs, nativePanelNode083 inputs, nativePanelNode082 inputs, nativePanelNode081 inputs, nativePanelNode080 inputs, nativePanelNode079 inputs, nativePanelNode078 inputs, nativePanelNode077 inputs, nativePanelNode076 inputs, nativePanelNode075 inputs, nativePanelNode074 inputs, nativePanelNode073 inputs, nativePanelNode072 inputs, nativePanelNode071 inputs, nativePanelNode070 inputs, nativePanelNode069 inputs, nativePanelNode068 inputs, nativePanelNode067 inputs, nativePanelNode066 inputs, nativePanelNode065 inputs, nativePanelNode064 inputs, nativePanelNode063 inputs, nativePanelNode062 inputs, nativePanelNode061 inputs, nativePanelNode060 inputs, nativePanelNode059 inputs, nativePanelNode058 inputs, nativePanelNode057 inputs, nativePanelNode056 inputs, nativePanelNode055 inputs, nativePanelNode054 inputs, nativePanelNode053 inputs, nativePanelNode052 inputs, nativePanelNode051 inputs, nativePanelNode050 inputs, nativePanelNode049 inputs, nativePanelNode048 inputs, nativePanelNode047 inputs, nativePanelNode046 inputs, nativePanelNode045 inputs, nativePanelNode044 inputs, nativePanelNode043 inputs, nativePanelNode042 inputs, nativePanelNode041 inputs, nativePanelNode040 inputs, nativePanelNode039 inputs, nativePanelNode038 inputs, nativePanelNode037 inputs, nativePanelNode036 inputs, nativePanelNode035 inputs, nativePanelNode034 inputs, nativePanelNode033 inputs, nativePanelNode032 inputs, nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs

theorem nativePanelChunk112_real (inputs : List ℝ) :
    nativePlanReal (nativePanelStack112 inputs) nativePanelOpsChunk112 = [nativePanelNode126 inputs, nativePanelNode125 inputs, nativePanelNode124 inputs, nativePanelNode123 inputs, nativePanelNode122 inputs, nativePanelNode121 inputs, nativePanelNode120 inputs, nativePanelNode119 inputs, nativePanelNode118 inputs, nativePanelNode117 inputs, nativePanelNode116 inputs, nativePanelNode115 inputs, nativePanelNode114 inputs, nativePanelNode113 inputs, nativePanelNode112 inputs, nativePanelNode111 inputs, nativePanelNode110 inputs, nativePanelNode109 inputs, nativePanelNode108 inputs, nativePanelNode107 inputs, nativePanelNode106 inputs, nativePanelNode105 inputs, nativePanelNode104 inputs, nativePanelNode103 inputs, nativePanelNode102 inputs, nativePanelNode101 inputs, nativePanelNode100 inputs, nativePanelNode099 inputs, nativePanelNode098 inputs, nativePanelNode097 inputs, nativePanelNode096 inputs, nativePanelNode095 inputs, nativePanelNode094 inputs, nativePanelNode093 inputs, nativePanelNode092 inputs, nativePanelNode091 inputs, nativePanelNode090 inputs, nativePanelNode089 inputs, nativePanelNode088 inputs, nativePanelNode087 inputs, nativePanelNode086 inputs, nativePanelNode085 inputs, nativePanelNode084 inputs, nativePanelNode083 inputs, nativePanelNode082 inputs, nativePanelNode081 inputs, nativePanelNode080 inputs, nativePanelNode079 inputs, nativePanelNode078 inputs, nativePanelNode077 inputs, nativePanelNode076 inputs, nativePanelNode075 inputs, nativePanelNode074 inputs, nativePanelNode073 inputs, nativePanelNode072 inputs, nativePanelNode071 inputs, nativePanelNode070 inputs, nativePanelNode069 inputs, nativePanelNode068 inputs, nativePanelNode067 inputs, nativePanelNode066 inputs, nativePanelNode065 inputs, nativePanelNode064 inputs, nativePanelNode063 inputs, nativePanelNode062 inputs, nativePanelNode061 inputs, nativePanelNode060 inputs, nativePanelNode059 inputs, nativePanelNode058 inputs, nativePanelNode057 inputs, nativePanelNode056 inputs, nativePanelNode055 inputs, nativePanelNode054 inputs, nativePanelNode053 inputs, nativePanelNode052 inputs, nativePanelNode051 inputs, nativePanelNode050 inputs, nativePanelNode049 inputs, nativePanelNode048 inputs, nativePanelNode047 inputs, nativePanelNode046 inputs, nativePanelNode045 inputs, nativePanelNode044 inputs, nativePanelNode043 inputs, nativePanelNode042 inputs, nativePanelNode041 inputs, nativePanelNode040 inputs, nativePanelNode039 inputs, nativePanelNode038 inputs, nativePanelNode037 inputs, nativePanelNode036 inputs, nativePanelNode035 inputs, nativePanelNode034 inputs, nativePanelNode033 inputs, nativePanelNode032 inputs, nativePanelNode031 inputs, nativePanelNode030 inputs, nativePanelNode029 inputs, nativePanelNode028 inputs, nativePanelNode027 inputs, nativePanelNode026 inputs, nativePanelNode025 inputs, nativePanelNode024 inputs, nativePanelNode023 inputs, nativePanelNode022 inputs, nativePanelNode021 inputs, nativePanelNode020 inputs, nativePanelNode019 inputs, nativePanelNode018 inputs, nativePanelNode017 inputs, nativePanelNode016 inputs, nativePanelNode015 inputs, nativePanelNode014 inputs, nativePanelNode013 inputs, nativePanelNode012 inputs, nativePanelNode011 inputs, nativePanelNode010 inputs, nativePanelNode009 inputs, nativePanelNode008 inputs, nativePanelNode007 inputs, nativePanelNode006 inputs, nativePanelNode005 inputs, nativePanelNode004 inputs, nativePanelNode003 inputs, nativePanelNode002 inputs, nativePanelNode001 inputs, nativePanelNode000 inputs] ++ inputs := by
  rfl

theorem nativePanelOps_chunks : nativePanelOps = nativePanelOpsChunk000 ++ nativePanelOpsChunk016 ++ nativePanelOpsChunk032 ++ nativePanelOpsChunk048 ++ nativePanelOpsChunk064 ++ nativePanelOpsChunk080 ++ nativePanelOpsChunk096 ++ nativePanelOpsChunk112 := by
  decide +kernel

theorem nativePanelValue_node (fields : List ℝ) (s : ℝ) :
    nativePanelValue fields s = nativePanelNode126 (s::fields.reverse) := by
  unfold nativePanelValue
  rw [nativePanelOps_chunks]
  simp only [nativePlanReal_append]
  have h0 := nativePanelChunk000_real (s::fields.reverse)
  simp only [nativePanelStack000,List.nil_append] at h0
  rw [h0]
  have h16 := nativePanelChunk016_real (s::fields.reverse)
  simp only [nativePanelStack016] at h16
  rw [h16]
  have h32 := nativePanelChunk032_real (s::fields.reverse)
  simp only [nativePanelStack032] at h32
  rw [h32]
  have h48 := nativePanelChunk048_real (s::fields.reverse)
  simp only [nativePanelStack048] at h48
  rw [h48]
  have h64 := nativePanelChunk064_real (s::fields.reverse)
  simp only [nativePanelStack064] at h64
  rw [h64]
  have h80 := nativePanelChunk080_real (s::fields.reverse)
  simp only [nativePanelStack080] at h80
  rw [h80]
  have h96 := nativePanelChunk096_real (s::fields.reverse)
  simp only [nativePanelStack096] at h96
  rw [h96]
  have h112 := nativePanelChunk112_real (s::fields.reverse)
  simp only [nativePanelStack112] at h112
  rw [h112]
  rfl

end ASDExplicitGamma.Numerics.Native
