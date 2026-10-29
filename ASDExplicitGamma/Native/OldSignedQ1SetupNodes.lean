module

public import ASDExplicitGamma.Native.OldSignedQ1VarianceClock

/-! Named nodes for the exact physical coefficients of the frozen q1 setup.
The source program is split only to avoid reducing its unrelated later outputs. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

def oldSignedQ1SetupNode000 (_inputs : List ℝ) : ℝ := ((2/1 : ℚ) : ℝ)

def oldSignedQ1SetupNode001 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode000 inputs)

def oldSignedQ1SetupNode002 (_inputs : List ℝ) : ℝ := ((3/1 : ℚ) : ℝ)

def oldSignedQ1SetupNode003 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode002 inputs)

def oldSignedQ1SetupNode004 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode003 inputs)

def oldSignedQ1SetupNode005 (_inputs : List ℝ) : ℝ := ((105/1 : ℚ) : ℝ)

def oldSignedQ1SetupNode006 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode005 inputs)

def oldSignedQ1SetupNode007 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode006 inputs)

def oldSignedQ1SetupNode008 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode007 inputs)

def oldSignedQ1SetupNode009 (_inputs : List ℝ) : ℝ := ((1/1 : ℚ) : ℝ)

def oldSignedQ1SetupNode010 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode009 inputs) / (oldSignedQ1SetupNode004 inputs)

def oldSignedQ1SetupNode011 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode010 inputs) + (oldSignedQ1SetupNode009 inputs)

def oldSignedQ1SetupNode012 (_inputs : List ℝ) : ℝ := ((3/20 : ℚ) : ℝ)

def oldSignedQ1SetupNode013 (inputs : List ℝ) : ℝ := (inputs.getD 2 0) * (oldSignedQ1SetupNode012 inputs)

def oldSignedQ1SetupNode014 (inputs : List ℝ) : ℝ := Real.exp (oldSignedQ1SetupNode013 inputs)

def oldSignedQ1SetupNode015 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode009 inputs) / (oldSignedQ1SetupNode014 inputs)

def oldSignedQ1SetupNode016 (_inputs : List ℝ) : ℝ := ((3/4 : ℚ) : ℝ)

def oldSignedQ1SetupNode017 (inputs : List ℝ) : ℝ := (inputs.getD 2 0) * (oldSignedQ1SetupNode016 inputs)

def oldSignedQ1SetupNode018 (inputs : List ℝ) : ℝ := Real.exp (oldSignedQ1SetupNode017 inputs)

def oldSignedQ1SetupNode019 (_inputs : List ℝ) : ℝ := ((17/25000 : ℚ) : ℝ)

def oldSignedQ1SetupNode020 (inputs : List ℝ) : ℝ := (inputs.getD 2 0) * (oldSignedQ1SetupNode019 inputs)

def oldSignedQ1SetupNode021 (inputs : List ℝ) : ℝ := Real.exp (oldSignedQ1SetupNode020 inputs)

def oldSignedQ1SetupNode022 (_inputs : List ℝ) : ℝ := ((153/100000 : ℚ) : ℝ)

def oldSignedQ1SetupNode023 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode021 inputs) * (oldSignedQ1SetupNode022 inputs)

def oldSignedQ1SetupNode024 (_inputs : List ℝ) : ℝ := ((0/1 : ℚ) : ℝ)

def oldSignedQ1SetupNode025 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode024 inputs) + (oldSignedQ1SetupNode023 inputs)

def oldSignedQ1SetupNode026 (_inputs : List ℝ) : ℝ := ((1/531441 : ℚ) : ℝ)

def oldSignedQ1SetupNode027 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode023 inputs) * (oldSignedQ1SetupNode026 inputs)

def oldSignedQ1SetupNode028 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode024 inputs) + (oldSignedQ1SetupNode027 inputs)

def oldSignedQ1SetupNode029 (_inputs : List ℝ) : ℝ := ((1/282429536481 : ℚ) : ℝ)

def oldSignedQ1SetupNode030 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode023 inputs) * (oldSignedQ1SetupNode029 inputs)

def oldSignedQ1SetupNode031 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode024 inputs) + (oldSignedQ1SetupNode030 inputs)

def oldSignedQ1SetupNode032 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode025 inputs)

def oldSignedQ1SetupNode033 (_inputs : List ℝ) : ℝ := ((156/5 : ℚ) : ℝ)

def oldSignedQ1SetupNode034 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode028 inputs) * (oldSignedQ1SetupNode033 inputs)

def oldSignedQ1SetupNode035 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode034 inputs)

def oldSignedQ1SetupNode036 (_inputs : List ℝ) : ℝ := ((36/25 : ℚ) : ℝ)

def oldSignedQ1SetupNode037 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode035 inputs) * (oldSignedQ1SetupNode036 inputs)

def oldSignedQ1SetupNode038 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode032 inputs) + (oldSignedQ1SetupNode037 inputs)

def oldSignedQ1SetupNode039 (_inputs : List ℝ) : ℝ := ((46488/25 : ℚ) : ℝ)

def oldSignedQ1SetupNode040 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode031 inputs) * (oldSignedQ1SetupNode039 inputs)

def oldSignedQ1SetupNode041 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode040 inputs)

def oldSignedQ1SetupNode042 (_inputs : List ℝ) : ℝ := ((57/200 : ℚ) : ℝ)

def oldSignedQ1SetupNode043 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode041 inputs) * (oldSignedQ1SetupNode042 inputs)

def oldSignedQ1SetupNode044 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode038 inputs) + (oldSignedQ1SetupNode043 inputs)

def oldSignedQ1SetupNode045 (_inputs : List ℝ) : ℝ := ((78/5 : ℚ) : ℝ)

def oldSignedQ1SetupNode046 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode028 inputs) * (oldSignedQ1SetupNode045 inputs)

def oldSignedQ1SetupNode047 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode046 inputs)

def oldSignedQ1SetupNode048 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode047 inputs) * (oldSignedQ1SetupNode036 inputs)

def oldSignedQ1SetupNode049 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode032 inputs) + (oldSignedQ1SetupNode048 inputs)

def oldSignedQ1SetupNode050 (_inputs : List ℝ) : ℝ := ((23244/25 : ℚ) : ℝ)

def oldSignedQ1SetupNode051 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode031 inputs) * (oldSignedQ1SetupNode050 inputs)

def oldSignedQ1SetupNode052 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode051 inputs)

def oldSignedQ1SetupNode053 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode052 inputs) * (oldSignedQ1SetupNode042 inputs)

def oldSignedQ1SetupNode054 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode049 inputs) + (oldSignedQ1SetupNode053 inputs)

def oldSignedQ1SetupNode055 (_inputs : List ℝ) : ℝ := ((637/1000 : ℚ) : ℝ)

def oldSignedQ1SetupNode056 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode035 inputs) * (oldSignedQ1SetupNode055 inputs)

def oldSignedQ1SetupNode057 (_inputs : List ℝ) : ℝ := ((418/3125 : ℚ) : ℝ)

def oldSignedQ1SetupNode058 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode041 inputs) * (oldSignedQ1SetupNode057 inputs)

def oldSignedQ1SetupNode059 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode056 inputs) + (oldSignedQ1SetupNode058 inputs)

def oldSignedQ1SetupNode060 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode001 inputs) + (oldSignedQ1SetupNode009 inputs)

def oldSignedQ1SetupNode061 (_inputs : List ℝ) : ℝ := ((11/25 : ℚ) : ℝ)

def oldSignedQ1SetupNode062 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode060 inputs) * (oldSignedQ1SetupNode061 inputs)

def oldSignedQ1SetupNode063 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode062 inputs) * (oldSignedQ1SetupNode035 inputs)

def oldSignedQ1SetupNode064 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode035 inputs) * (oldSignedQ1SetupNode061 inputs)

def oldSignedQ1SetupNode065 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode025 inputs) * (oldSignedQ1SetupNode000 inputs)

def oldSignedQ1SetupNode066 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode025 inputs) * (oldSignedQ1SetupNode065 inputs)

def oldSignedQ1SetupNode067 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode066 inputs) / (oldSignedQ1SetupNode000 inputs)

def oldSignedQ1SetupNode068 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode067 inputs)

def oldSignedQ1SetupNode069 (_inputs : List ℝ) : ℝ := ((38/125 : ℚ) : ℝ)

def oldSignedQ1SetupNode070 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode035 inputs) * (oldSignedQ1SetupNode069 inputs)

def oldSignedQ1SetupNode071 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode065 inputs) / (oldSignedQ1SetupNode000 inputs)

def oldSignedQ1SetupNode072 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode071 inputs)

def oldSignedQ1SetupNode073 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode032 inputs) * (oldSignedQ1SetupNode000 inputs)

def oldSignedQ1SetupNode074 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode072 inputs) + (oldSignedQ1SetupNode073 inputs)

def oldSignedQ1SetupNode075 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode070 inputs) * (oldSignedQ1SetupNode074 inputs)

def oldSignedQ1SetupNode076 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode068 inputs) + (oldSignedQ1SetupNode075 inputs)

def oldSignedQ1SetupNode077 (inputs : List ℝ) : ℝ := (oldSignedQ1SetupNode025 inputs) + (oldSignedQ1SetupNode071 inputs)

def oldSignedQ1SetupNode078 (inputs : List ℝ) : ℝ := Real.sqrt (oldSignedQ1SetupNode077 inputs)

def oldSignedQ1SetupNode079 (_inputs : List ℝ) : ℝ := ((39/5 : ℚ) : ℝ)

def oldSignedQ1SetupStack000 (inputs : List ℝ) : List ℝ := [] ++ inputs

def oldSignedQ1SetupStack016 (inputs : List ℝ) : List ℝ := [oldSignedQ1SetupNode015 inputs, oldSignedQ1SetupNode014 inputs, oldSignedQ1SetupNode013 inputs, oldSignedQ1SetupNode012 inputs, oldSignedQ1SetupNode011 inputs, oldSignedQ1SetupNode010 inputs, oldSignedQ1SetupNode009 inputs, oldSignedQ1SetupNode008 inputs, oldSignedQ1SetupNode007 inputs, oldSignedQ1SetupNode006 inputs, oldSignedQ1SetupNode005 inputs, oldSignedQ1SetupNode004 inputs, oldSignedQ1SetupNode003 inputs, oldSignedQ1SetupNode002 inputs, oldSignedQ1SetupNode001 inputs, oldSignedQ1SetupNode000 inputs] ++ inputs

def oldSignedQ1SetupStack032 (inputs : List ℝ) : List ℝ := [oldSignedQ1SetupNode031 inputs, oldSignedQ1SetupNode030 inputs, oldSignedQ1SetupNode029 inputs, oldSignedQ1SetupNode028 inputs, oldSignedQ1SetupNode027 inputs, oldSignedQ1SetupNode026 inputs, oldSignedQ1SetupNode025 inputs, oldSignedQ1SetupNode024 inputs, oldSignedQ1SetupNode023 inputs, oldSignedQ1SetupNode022 inputs, oldSignedQ1SetupNode021 inputs, oldSignedQ1SetupNode020 inputs, oldSignedQ1SetupNode019 inputs, oldSignedQ1SetupNode018 inputs, oldSignedQ1SetupNode017 inputs, oldSignedQ1SetupNode016 inputs, oldSignedQ1SetupNode015 inputs, oldSignedQ1SetupNode014 inputs, oldSignedQ1SetupNode013 inputs, oldSignedQ1SetupNode012 inputs, oldSignedQ1SetupNode011 inputs, oldSignedQ1SetupNode010 inputs, oldSignedQ1SetupNode009 inputs, oldSignedQ1SetupNode008 inputs, oldSignedQ1SetupNode007 inputs, oldSignedQ1SetupNode006 inputs, oldSignedQ1SetupNode005 inputs, oldSignedQ1SetupNode004 inputs, oldSignedQ1SetupNode003 inputs, oldSignedQ1SetupNode002 inputs, oldSignedQ1SetupNode001 inputs, oldSignedQ1SetupNode000 inputs] ++ inputs

def oldSignedQ1SetupStack048 (inputs : List ℝ) : List ℝ := [oldSignedQ1SetupNode047 inputs, oldSignedQ1SetupNode046 inputs, oldSignedQ1SetupNode045 inputs, oldSignedQ1SetupNode044 inputs, oldSignedQ1SetupNode043 inputs, oldSignedQ1SetupNode042 inputs, oldSignedQ1SetupNode041 inputs, oldSignedQ1SetupNode040 inputs, oldSignedQ1SetupNode039 inputs, oldSignedQ1SetupNode038 inputs, oldSignedQ1SetupNode037 inputs, oldSignedQ1SetupNode036 inputs, oldSignedQ1SetupNode035 inputs, oldSignedQ1SetupNode034 inputs, oldSignedQ1SetupNode033 inputs, oldSignedQ1SetupNode032 inputs, oldSignedQ1SetupNode031 inputs, oldSignedQ1SetupNode030 inputs, oldSignedQ1SetupNode029 inputs, oldSignedQ1SetupNode028 inputs, oldSignedQ1SetupNode027 inputs, oldSignedQ1SetupNode026 inputs, oldSignedQ1SetupNode025 inputs, oldSignedQ1SetupNode024 inputs, oldSignedQ1SetupNode023 inputs, oldSignedQ1SetupNode022 inputs, oldSignedQ1SetupNode021 inputs, oldSignedQ1SetupNode020 inputs, oldSignedQ1SetupNode019 inputs, oldSignedQ1SetupNode018 inputs, oldSignedQ1SetupNode017 inputs, oldSignedQ1SetupNode016 inputs, oldSignedQ1SetupNode015 inputs, oldSignedQ1SetupNode014 inputs, oldSignedQ1SetupNode013 inputs, oldSignedQ1SetupNode012 inputs, oldSignedQ1SetupNode011 inputs, oldSignedQ1SetupNode010 inputs, oldSignedQ1SetupNode009 inputs, oldSignedQ1SetupNode008 inputs, oldSignedQ1SetupNode007 inputs, oldSignedQ1SetupNode006 inputs, oldSignedQ1SetupNode005 inputs, oldSignedQ1SetupNode004 inputs, oldSignedQ1SetupNode003 inputs, oldSignedQ1SetupNode002 inputs, oldSignedQ1SetupNode001 inputs, oldSignedQ1SetupNode000 inputs] ++ inputs

def oldSignedQ1SetupStack064 (inputs : List ℝ) : List ℝ := [oldSignedQ1SetupNode063 inputs, oldSignedQ1SetupNode062 inputs, oldSignedQ1SetupNode061 inputs, oldSignedQ1SetupNode060 inputs, oldSignedQ1SetupNode059 inputs, oldSignedQ1SetupNode058 inputs, oldSignedQ1SetupNode057 inputs, oldSignedQ1SetupNode056 inputs, oldSignedQ1SetupNode055 inputs, oldSignedQ1SetupNode054 inputs, oldSignedQ1SetupNode053 inputs, oldSignedQ1SetupNode052 inputs, oldSignedQ1SetupNode051 inputs, oldSignedQ1SetupNode050 inputs, oldSignedQ1SetupNode049 inputs, oldSignedQ1SetupNode048 inputs, oldSignedQ1SetupNode047 inputs, oldSignedQ1SetupNode046 inputs, oldSignedQ1SetupNode045 inputs, oldSignedQ1SetupNode044 inputs, oldSignedQ1SetupNode043 inputs, oldSignedQ1SetupNode042 inputs, oldSignedQ1SetupNode041 inputs, oldSignedQ1SetupNode040 inputs, oldSignedQ1SetupNode039 inputs, oldSignedQ1SetupNode038 inputs, oldSignedQ1SetupNode037 inputs, oldSignedQ1SetupNode036 inputs, oldSignedQ1SetupNode035 inputs, oldSignedQ1SetupNode034 inputs, oldSignedQ1SetupNode033 inputs, oldSignedQ1SetupNode032 inputs, oldSignedQ1SetupNode031 inputs, oldSignedQ1SetupNode030 inputs, oldSignedQ1SetupNode029 inputs, oldSignedQ1SetupNode028 inputs, oldSignedQ1SetupNode027 inputs, oldSignedQ1SetupNode026 inputs, oldSignedQ1SetupNode025 inputs, oldSignedQ1SetupNode024 inputs, oldSignedQ1SetupNode023 inputs, oldSignedQ1SetupNode022 inputs, oldSignedQ1SetupNode021 inputs, oldSignedQ1SetupNode020 inputs, oldSignedQ1SetupNode019 inputs, oldSignedQ1SetupNode018 inputs, oldSignedQ1SetupNode017 inputs, oldSignedQ1SetupNode016 inputs, oldSignedQ1SetupNode015 inputs, oldSignedQ1SetupNode014 inputs, oldSignedQ1SetupNode013 inputs, oldSignedQ1SetupNode012 inputs, oldSignedQ1SetupNode011 inputs, oldSignedQ1SetupNode010 inputs, oldSignedQ1SetupNode009 inputs, oldSignedQ1SetupNode008 inputs, oldSignedQ1SetupNode007 inputs, oldSignedQ1SetupNode006 inputs, oldSignedQ1SetupNode005 inputs, oldSignedQ1SetupNode004 inputs, oldSignedQ1SetupNode003 inputs, oldSignedQ1SetupNode002 inputs, oldSignedQ1SetupNode001 inputs, oldSignedQ1SetupNode000 inputs] ++ inputs

def oldSignedQ1SetupStack080 (inputs : List ℝ) : List ℝ := [oldSignedQ1SetupNode079 inputs, oldSignedQ1SetupNode078 inputs, oldSignedQ1SetupNode077 inputs, oldSignedQ1SetupNode076 inputs, oldSignedQ1SetupNode075 inputs, oldSignedQ1SetupNode074 inputs, oldSignedQ1SetupNode073 inputs, oldSignedQ1SetupNode072 inputs, oldSignedQ1SetupNode071 inputs, oldSignedQ1SetupNode070 inputs, oldSignedQ1SetupNode069 inputs, oldSignedQ1SetupNode068 inputs, oldSignedQ1SetupNode067 inputs, oldSignedQ1SetupNode066 inputs, oldSignedQ1SetupNode065 inputs, oldSignedQ1SetupNode064 inputs, oldSignedQ1SetupNode063 inputs, oldSignedQ1SetupNode062 inputs, oldSignedQ1SetupNode061 inputs, oldSignedQ1SetupNode060 inputs, oldSignedQ1SetupNode059 inputs, oldSignedQ1SetupNode058 inputs, oldSignedQ1SetupNode057 inputs, oldSignedQ1SetupNode056 inputs, oldSignedQ1SetupNode055 inputs, oldSignedQ1SetupNode054 inputs, oldSignedQ1SetupNode053 inputs, oldSignedQ1SetupNode052 inputs, oldSignedQ1SetupNode051 inputs, oldSignedQ1SetupNode050 inputs, oldSignedQ1SetupNode049 inputs, oldSignedQ1SetupNode048 inputs, oldSignedQ1SetupNode047 inputs, oldSignedQ1SetupNode046 inputs, oldSignedQ1SetupNode045 inputs, oldSignedQ1SetupNode044 inputs, oldSignedQ1SetupNode043 inputs, oldSignedQ1SetupNode042 inputs, oldSignedQ1SetupNode041 inputs, oldSignedQ1SetupNode040 inputs, oldSignedQ1SetupNode039 inputs, oldSignedQ1SetupNode038 inputs, oldSignedQ1SetupNode037 inputs, oldSignedQ1SetupNode036 inputs, oldSignedQ1SetupNode035 inputs, oldSignedQ1SetupNode034 inputs, oldSignedQ1SetupNode033 inputs, oldSignedQ1SetupNode032 inputs, oldSignedQ1SetupNode031 inputs, oldSignedQ1SetupNode030 inputs, oldSignedQ1SetupNode029 inputs, oldSignedQ1SetupNode028 inputs, oldSignedQ1SetupNode027 inputs, oldSignedQ1SetupNode026 inputs, oldSignedQ1SetupNode025 inputs, oldSignedQ1SetupNode024 inputs, oldSignedQ1SetupNode023 inputs, oldSignedQ1SetupNode022 inputs, oldSignedQ1SetupNode021 inputs, oldSignedQ1SetupNode020 inputs, oldSignedQ1SetupNode019 inputs, oldSignedQ1SetupNode018 inputs, oldSignedQ1SetupNode017 inputs, oldSignedQ1SetupNode016 inputs, oldSignedQ1SetupNode015 inputs, oldSignedQ1SetupNode014 inputs, oldSignedQ1SetupNode013 inputs, oldSignedQ1SetupNode012 inputs, oldSignedQ1SetupNode011 inputs, oldSignedQ1SetupNode010 inputs, oldSignedQ1SetupNode009 inputs, oldSignedQ1SetupNode008 inputs, oldSignedQ1SetupNode007 inputs, oldSignedQ1SetupNode006 inputs, oldSignedQ1SetupNode005 inputs, oldSignedQ1SetupNode004 inputs, oldSignedQ1SetupNode003 inputs, oldSignedQ1SetupNode002 inputs, oldSignedQ1SetupNode001 inputs, oldSignedQ1SetupNode000 inputs] ++ inputs

private def setupChunk000 : List Expr := [
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
  .const (3/20 : ℚ),
  .mul (.var 15) (.var 0),
  .exp (.var 0),
  .divPos (.var 5) (.var 0)
]

private theorem setup_chunk_000 (inputs : List ℝ) :
    nativePlanReal (oldSignedQ1SetupStack000 inputs) setupChunk000=oldSignedQ1SetupStack016 inputs := by
  rfl

private def setupChunk016 : List Expr := [
  .const (3/4 : ℚ),
  .mul (.var 19) (.var 0),
  .exp (.var 0),
  .const (17/25000 : ℚ),
  .mul (.var 22) (.var 0),
  .exp (.var 0),
  .const (153/100000 : ℚ),
  .mul (.var 1) (.var 0),
  .const (0/1 : ℚ),
  .add (.var 0) (.var 1),
  .const (1/531441 : ℚ),
  .mul (.var 3) (.var 0),
  .add (.var 3) (.var 0),
  .const (1/282429536481 : ℚ),
  .mul (.var 6) (.var 0),
  .add (.var 6) (.var 0)
]

private theorem setup_chunk_016 (inputs : List ℝ) :
    nativePlanReal (oldSignedQ1SetupStack016 inputs) setupChunk016=oldSignedQ1SetupStack032 inputs := by
  rfl

private def setupChunk032 : List Expr := [
  .sqrt (.var 6),
  .const (156/5 : ℚ),
  .mul (.var 5) (.var 0),
  .sqrt (.var 0),
  .const (36/25 : ℚ),
  .mul (.var 1) (.var 0),
  .add (.var 5) (.var 0),
  .const (46488/25 : ℚ),
  .mul (.var 8) (.var 0),
  .sqrt (.var 0),
  .const (57/200 : ℚ),
  .mul (.var 1) (.var 0),
  .add (.var 5) (.var 0),
  .const (78/5 : ℚ),
  .mul (.var 17) (.var 0),
  .sqrt (.var 0)
]

private theorem setup_chunk_032 (inputs : List ℝ) :
    nativePlanReal (oldSignedQ1SetupStack032 inputs) setupChunk032=oldSignedQ1SetupStack048 inputs := by
  rfl

private def setupChunk048 : List Expr := [
  .mul (.var 0) (.var 11),
  .add (.var 16) (.var 0),
  .const (23244/25 : ℚ),
  .mul (.var 19) (.var 0),
  .sqrt (.var 0),
  .mul (.var 0) (.var 10),
  .add (.var 4) (.var 0),
  .const (637/1000 : ℚ),
  .mul (.var 20) (.var 0),
  .const (418/3125 : ℚ),
  .mul (.var 16) (.var 0),
  .add (.var 2) (.var 0),
  .add (.var 58) (.var 50),
  .const (11/25 : ℚ),
  .mul (.var 1) (.var 0),
  .mul (.var 0) (.var 27)
]

private theorem setup_chunk_048 (inputs : List ℝ) :
    nativePlanReal (oldSignedQ1SetupStack048 inputs) setupChunk048=oldSignedQ1SetupStack064 inputs := by
  rfl

private def setupChunk064 : List Expr := [
  .mul (.var 28) (.var 2),
  .mul (.var 39) (.var 64),
  .mul (.var 40) (.var 0),
  .divPos (.var 0) (.var 66),
  .sqrt (.var 0),
  .const (38/125 : ℚ),
  .mul (.var 34) (.var 0),
  .divPos (.var 5) (.var 70),
  .sqrt (.var 0),
  .mul (.var 40) (.var 72),
  .add (.var 1) (.var 0),
  .mul (.var 4) (.var 0),
  .add (.var 7) (.var 0),
  .add (.var 51) (.var 5),
  .sqrt (.var 0),
  .const (39/5 : ℚ)
]

private theorem setup_chunk_064 (inputs : List ℝ) :
    nativePlanReal (oldSignedQ1SetupStack064 inputs) setupChunk064=oldSignedQ1SetupStack080 inputs := by
  rfl

private def setupPrefix : List Expr := setupChunk000 ++ setupChunk016 ++ setupChunk032 ++ setupChunk048 ++ setupChunk064

private theorem setup_prefix_real (inputs : List ℝ) :
    nativePlanReal inputs setupPrefix=oldSignedQ1SetupStack080 inputs := by
  unfold setupPrefix
  simp only [nativePlanReal_append]
  change nativePlanReal (nativePlanReal (nativePlanReal (nativePlanReal (nativePlanReal (oldSignedQ1SetupStack000 inputs) setupChunk000) setupChunk016) setupChunk032) setupChunk048) setupChunk064=_
  rw [setup_chunk_000,setup_chunk_016,setup_chunk_032,setup_chunk_048,setup_chunk_064]

/-- Later setup instructions preserve every physical coefficient already computed. -/
theorem old_signed_q1_setup_prefix_value (i : ℕ) :
    nativeSetupQ1001Real.getD (334+i) 0=(oldSignedQ1SetupStack080
      (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0)).getD i 0 := by
  have hsplit : nativeSetupQ1001Ops=setupPrefix++nativeSetupQ1001Ops.drop 80 := by decide +kernel
  have hlen : (nativeSetupQ1001Ops.drop 80).length=334 := by decide +kernel
  rw [nativeSetupQ1001Real,hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) setupPrefix)
    (nativeSetupQ1001Ops.drop 80) i
  simp only [hlen] at hh
  rw [hh,setup_prefix_real]

/-- Exact physical setup field 0, as a named source-program node. -/
theorem old_signed_q1_setup_field_00 :
    nativeSetupQ1001FieldsR.getD 0 0=oldSignedQ1SetupNode025
      (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) := by
  simpa only [nativeSetupQ1001FieldsR,oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ]
    using old_signed_q1_setup_prefix_value 54

/-- Exact physical setup field 1, as a named source-program node. -/
theorem old_signed_q1_setup_field_01 :
    nativeSetupQ1001FieldsR.getD 1 0=oldSignedQ1SetupNode028
      (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) := by
  simpa only [nativeSetupQ1001FieldsR,oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ]
    using old_signed_q1_setup_prefix_value 51

/-- Exact physical setup field 2, as a named source-program node. -/
theorem old_signed_q1_setup_field_02 :
    nativeSetupQ1001FieldsR.getD 2 0=oldSignedQ1SetupNode044
      (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) := by
  simpa only [nativeSetupQ1001FieldsR,oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ]
    using old_signed_q1_setup_prefix_value 35

/-- Exact physical setup field 3, as a named source-program node. -/
theorem old_signed_q1_setup_field_03 :
    nativeSetupQ1001FieldsR.getD 3 0=oldSignedQ1SetupNode059
      (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) := by
  simpa only [nativeSetupQ1001FieldsR,oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ]
    using old_signed_q1_setup_prefix_value 20

/-- Exact physical setup field 4, as a named source-program node. -/
theorem old_signed_q1_setup_field_04 :
    nativeSetupQ1001FieldsR.getD 4 0=oldSignedQ1SetupNode063
      (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) := by
  simpa only [nativeSetupQ1001FieldsR,oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ]
    using old_signed_q1_setup_prefix_value 16

/-- Exact physical setup field 5, as a named source-program node. -/
theorem old_signed_q1_setup_field_05 :
    nativeSetupQ1001FieldsR.getD 5 0=oldSignedQ1SetupNode064
      (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) := by
  simpa only [nativeSetupQ1001FieldsR,oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ]
    using old_signed_q1_setup_prefix_value 15

/-- Exact physical setup field 6, as a named source-program node. -/
theorem old_signed_q1_setup_field_06 :
    nativeSetupQ1001FieldsR.getD 6 0=oldSignedQ1SetupNode076
      (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) := by
  simpa only [nativeSetupQ1001FieldsR,oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ]
    using old_signed_q1_setup_prefix_value 3

/-- Exact physical setup field 7, as a named source-program node. -/
theorem old_signed_q1_setup_field_07 :
    nativeSetupQ1001FieldsR.getD 7 0=oldSignedQ1SetupNode076
      (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) := by
  simpa only [nativeSetupQ1001FieldsR,oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ]
    using old_signed_q1_setup_prefix_value 3

/-- Exact physical setup field 8, as a named source-program node. -/
theorem old_signed_q1_setup_field_08 :
    nativeSetupQ1001FieldsR.getD 8 0=oldSignedQ1SetupNode078
      (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) := by
  simpa only [nativeSetupQ1001FieldsR,oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ]
    using old_signed_q1_setup_prefix_value 1

/-- Exact physical setup field 9, as a named source-program node. -/
theorem old_signed_q1_setup_field_09 :
    nativeSetupQ1001FieldsR.getD 9 0=oldSignedQ1SetupNode032
      (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) := by
  simpa only [nativeSetupQ1001FieldsR,oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ]
    using old_signed_q1_setup_prefix_value 47

end
end ASDExplicitGamma.Native
