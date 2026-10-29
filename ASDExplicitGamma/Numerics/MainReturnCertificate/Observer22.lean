module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer22Panel0Data : MainPanelData :=
  {
    observer := 22, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((13462474572016 : ℚ) / 57444969294043988584725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer22Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49396032800234780844892369151, ellLower := 352028235732372428114101009851,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172650768236319515140013166, offsetUpper := 6186676426870427073821644036,
    supportELower := 38568480237834029058201285388, supportEUpper := 40094229807936939713457950842,
    supportLambdaLower := 352028235732372428114101009851,
    supportLambdaUpper := 361984932938689584084604536500,
    supportJLower := 42088762595157753339342295486, supportJUpper := 43714079137323835554303996207,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer22Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer22Panel0Data observer22Panel0Endpoints
theorem observer22_panel0_kernel_check : observer22Panel0Check = true := by
  decide +kernel
theorem observer22_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer22Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer22Panel0Data) s observer22Panel0Data.anchor ≤
        (observer22Panel0Endpoints.energyUpper : ℝ) ∧
      (observer22Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer22Panel0Data) s observer22Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer22Panel0Data) s observer22Panel0Data.anchor ≤
        (observer22Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer22Panel0Data) s observer22Panel0Data.anchor ≤
        (observer22Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer22Panel0Data) s observer22Panel0Data.anchor ≤
        (observer22Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer22Panel0Data observer22Panel0Endpoints
    observer22_panel0_kernel_check s hs
def observer22Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer22Panel0Endpoints
theorem observer22_panel0_recurrence_field_kernel_check :
    observer22Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer22_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer22Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer22Panel0Endpoints
    observer22_panel0_recurrence_field_kernel_check

def observer22Panel1Data : MainPanelData :=
  {
    observer := 22, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((13462474572016 : ℚ) / 57444969294043988584725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer22Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51117946607046234027083140152, ellLower := 351861518462991824827688990034,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376330559910739005854636167, offsetUpper := 6390852035697282905700625975,
    supportELower := 40094180724028801684955893278, supportEUpper := 41500794935132561823711211463,
    supportLambdaLower := 351861518462991824827688990034,
    supportLambdaUpper := 361427533578054482758190269827,
    supportJLower := 43612795908658719933232783178, supportJUpper := 45115070270913106651293114162,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer22Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer22Panel1Data observer22Panel1Endpoints
theorem observer22_panel1_kernel_check : observer22Panel1Check = true := by
  decide +kernel
theorem observer22_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer22Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer22Panel1Data) s observer22Panel1Data.anchor ≤
        (observer22Panel1Endpoints.energyUpper : ℝ) ∧
      (observer22Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer22Panel1Data) s observer22Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer22Panel1Data) s observer22Panel1Data.anchor ≤
        (observer22Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer22Panel1Data) s observer22Panel1Data.anchor ≤
        (observer22Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer22Panel1Data) s observer22Panel1Data.anchor ≤
        (observer22Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer22Panel1Data observer22Panel1Endpoints
    observer22_panel1_kernel_check s hs
def observer22Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer22Panel1Endpoints
theorem observer22_panel1_recurrence_field_kernel_check :
    observer22Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer22_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer22Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer22Panel1Endpoints
    observer22_panel1_recurrence_field_kernel_check

def observer22Panel2Data : MainPanelData :=
  {
    observer := 22, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((13462474572016 : ℚ) / 57444969294043988584725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer22Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52820531071465863925991049618, ellLower := 351681244118350130636979333394,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6592084297937423421089524878, offsetUpper := 6607097131982949222386568262,
    supportELower := 41500741010890156921768120135, supportEUpper := 42887800285245982411300718131,
    supportLambdaLower := 351681244118350130636979333394,
    supportLambdaUpper := 360900895038226053049802411796,
    supportJLower := 45017553452073658228137913468, supportJUpper := 46496809235628242941798742249,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer22Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer22Panel2Data observer22Panel2Endpoints
theorem observer22_panel2_kernel_check : observer22Panel2Check = true := by
  decide +kernel
theorem observer22_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer22Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer22Panel2Data) s observer22Panel2Data.anchor ≤
        (observer22Panel2Endpoints.energyUpper : ℝ) ∧
      (observer22Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer22Panel2Data) s observer22Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer22Panel2Data) s observer22Panel2Data.anchor ≤
        (observer22Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer22Panel2Data) s observer22Panel2Data.anchor ≤
        (observer22Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer22Panel2Data) s observer22Panel2Data.anchor ≤
        (observer22Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer22Panel2Data observer22Panel2Endpoints
    observer22_panel2_kernel_check s hs
def observer22Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer22Panel2Endpoints
theorem observer22_panel2_recurrence_field_kernel_check :
    observer22Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer22_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer22Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer22Panel2Endpoints
    observer22_panel2_recurrence_field_kernel_check

def observer22Panel3Data : MainPanelData :=
  {
    observer := 22, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((13462474572016 : ℚ) / 57444969294043988584725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer22Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54513026116497438265484518774, ellLower := 351504920124484311624607870086,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806723024760605153882993321, offsetUpper := 6822224677735001085255326794,
    supportELower := 42887741556240649934173073241, supportEUpper := 44264500017180316517079332375,
    supportLambdaLower := 351504920124484311624607870086,
    supportLambdaUpper := 360403589362484378877542859637,
    supportJLower := 46402790757485493050419151941, supportJUpper := 47868535910805160305854760972,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer22Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer22Panel3Data observer22Panel3Endpoints
theorem observer22_panel3_kernel_check : observer22Panel3Check = true := by
  decide +kernel
theorem observer22_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer22Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer22Panel3Data) s observer22Panel3Data.anchor ≤
        (observer22Panel3Endpoints.energyUpper : ℝ) ∧
      (observer22Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer22Panel3Data) s observer22Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer22Panel3Data) s observer22Panel3Data.anchor ≤
        (observer22Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer22Panel3Data) s observer22Panel3Data.anchor ≤
        (observer22Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer22Panel3Data) s observer22Panel3Data.anchor ≤
        (observer22Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer22Panel3Data observer22Panel3Endpoints
    observer22_panel3_kernel_check s hs
def observer22Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer22Panel3Endpoints
theorem observer22_panel3_recurrence_field_kernel_check :
    observer22Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer22_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer22Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer22Panel3Endpoints
    observer22_panel3_recurrence_field_kernel_check

def observer22Panel4Data : MainPanelData :=
  {
    observer := 22, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((13462474572016 : ℚ) / 57444969294043988584725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer22Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56198960565639175669163125516, ellLower := 351333824530363841781864495775,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020653122057987474487823936, offsetUpper := 7036641980126085512541376289,
    supportELower := 44264436502649148919563416146, supportEUpper := 45634444160140839347335671973,
    supportLambdaLower := 351333824530363841781864495775,
    supportLambdaUpper := 359933491615809518672443990563,
    supportJLower := 47777774747952787337382061103, supportJUpper := 49233779076298934534060111879,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer22Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer22Panel4Data observer22Panel4Endpoints
theorem observer22_panel4_kernel_check : observer22Panel4Check = true := by
  decide +kernel
theorem observer22_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer22Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer22Panel4Data) s observer22Panel4Data.anchor ≤
        (observer22Panel4Endpoints.energyUpper : ℝ) ∧
      (observer22Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer22Panel4Data) s observer22Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer22Panel4Data) s observer22Panel4Data.anchor ≤
        (observer22Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer22Panel4Data) s observer22Panel4Data.anchor ≤
        (observer22Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer22Panel4Data) s observer22Panel4Data.anchor ≤
        (observer22Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer22Panel4Data observer22Panel4Endpoints
    observer22_panel4_kernel_check s hs
def observer22Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer22Panel4Endpoints
theorem observer22_panel4_recurrence_field_kernel_check :
    observer22Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer22_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer22Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer22Panel4Endpoints
    observer22_panel4_recurrence_field_kernel_check

def observer22Panel5Data : MainPanelData :=
  {
    observer := 22, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((13462474572016 : ℚ) / 57444969294043988584725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer22Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57880365087597386497340209094, ellLower := 351168214119844359659124692405,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217637502305688389279816066, offsetUpper := 7234112509947363683707379031,
    supportELower := 45634375873230718146907369807, supportEUpper := 46999444233719810227219386094,
    supportLambdaLower := 351168214119844359659124692405,
    supportLambdaUpper := 359488476914080461448206801383,
    supportJLower := 49146058014429161743498616731, supportJUpper := 50594329002860614841701454108,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer22Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer22Panel5Data observer22Panel5Endpoints
theorem observer22_panel5_kernel_check : observer22Panel5Check = true := by
  decide +kernel
theorem observer22_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer22Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer22Panel5Data) s observer22Panel5Data.anchor ≤
        (observer22Panel5Endpoints.energyUpper : ℝ) ∧
      (observer22Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer22Panel5Data) s observer22Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer22Panel5Data) s observer22Panel5Data.anchor ≤
        (observer22Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer22Panel5Data) s observer22Panel5Data.anchor ≤
        (observer22Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer22Panel5Data) s observer22Panel5Data.anchor ≤
        (observer22Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer22Panel5Data observer22Panel5Endpoints
    observer22_panel5_kernel_check s hs
def observer22Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer22Panel5Endpoints
theorem observer22_panel5_recurrence_field_kernel_check :
    observer22Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer22_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer22Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer22Panel5Endpoints
    observer22_panel5_recurrence_field_kernel_check

def observer22Panel6Data : MainPanelData :=
  {
    observer := 22, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((13462474572016 : ℚ) / 57444969294043988584725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer22Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59557814094990118955027409574, ellLower := 351008050160546843212030334716,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7430202951478135598119142359, offsetUpper := 7447163161846929493731823310,
    supportELower := 46999371184509872682186576410, supportEUpper := 48360575262918949115501127859,
    supportLambdaLower := 351008050160546843212030334716,
    supportLambdaUpper := 359066564127122267580189575547,
    supportJLower := 50509451686115341114306879757, supportJUpper := 51951240904190171791303023615,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer22Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer22Panel6Data observer22Panel6Endpoints
theorem observer22_panel6_kernel_check : observer22Panel6Check = true := by
  decide +kernel
theorem observer22_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer22Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer22Panel6Data) s observer22Panel6Data.anchor ≤
        (observer22Panel6Endpoints.energyUpper : ℝ) ∧
      (observer22Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer22Panel6Data) s observer22Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer22Panel6Data) s observer22Panel6Data.anchor ≤
        (observer22Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer22Panel6Data) s observer22Panel6Data.anchor ≤
        (observer22Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer22Panel6Data) s observer22Panel6Data.anchor ≤
        (observer22Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer22Panel6Data observer22Panel6Endpoints
    observer22_panel6_kernel_check s hs
def observer22Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer22Panel6Endpoints
theorem observer22_panel6_recurrence_field_kernel_check :
    observer22Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer22_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer22Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer22Panel6Endpoints
    observer22_panel6_recurrence_field_kernel_check

def observer22Panel7Data : MainPanelData :=
  {
    observer := 22, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((13462474572016 : ℚ) / 57444969294043988584725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer22Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61232232283550955648554127219, ellLower := 350853182275523914628107987155,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642468825719001126590600322, offsetUpper := 7659913555004001051804875066,
    supportELower := 48360497459666759803768417601, supportEUpper := 49718539486946239467364115298,
    supportLambdaLower := 350853182275523914628107987155,
    supportLambdaUpper := 358665945509001771456495685047,
    supportJLower := 51869029282421998950049497472, supportJUpper := 53305198942036257181929072149,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer22Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer22Panel7Data observer22Panel7Endpoints
theorem observer22_panel7_kernel_check : observer22Panel7Check = true := by
  decide +kernel
theorem observer22_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer22Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer22Panel7Data) s observer22Panel7Data.anchor ≤
        (observer22Panel7Endpoints.energyUpper : ℝ) ∧
      (observer22Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer22Panel7Data) s observer22Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer22Panel7Data) s observer22Panel7Data.anchor ≤
        (observer22Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer22Panel7Data) s observer22Panel7Data.anchor ≤
        (observer22Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer22Panel7Data) s observer22Panel7Data.anchor ≤
        (observer22Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer22Panel7Data observer22Panel7Endpoints
    observer22_panel7_kernel_check s hs
def observer22Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer22Panel7Endpoints
theorem observer22_panel7_recurrence_field_kernel_check :
    observer22Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer22_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer22Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer22Panel7Endpoints
    observer22_panel7_recurrence_field_kernel_check

def observer22InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 22, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer22Panel0Endpoints, observer22Panel1Endpoints, observer22Panel2Endpoints, observer22Panel3Endpoints, observer22Panel4Endpoints, observer22Panel5Endpoints, observer22Panel6Endpoints, observer22Panel7Endpoints]
  }
def observer22FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer22InsertionEndpoints.frameLower
    observer22InsertionEndpoints.frameUpper
theorem observer22_frame_recurrence_field_kernel_check :
    observer22FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer22_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer22InsertionEndpoints.frameLower
      observer22InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer22InsertionEndpoints.frameLower
    observer22InsertionEndpoints.frameUpper
    observer22_frame_recurrence_field_kernel_check
def observer22RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer22Panel0Endpoints ∧
  panelRecurrenceFields observer22Panel1Endpoints ∧
  panelRecurrenceFields observer22Panel2Endpoints ∧
  panelRecurrenceFields observer22Panel3Endpoints ∧
  panelRecurrenceFields observer22Panel4Endpoints ∧
  panelRecurrenceFields observer22Panel5Endpoints ∧
  panelRecurrenceFields observer22Panel6Endpoints ∧
  panelRecurrenceFields observer22Panel7Endpoints ∧ insertionFrameRecurrenceFields observer22InsertionEndpoints.frameLower
      observer22InsertionEndpoints.frameUpper
theorem observer22_all_recurrence_fields :
    observer22RecurrenceFieldBounds := by
  exact ⟨observer22_panel0_recurrence_fields_sound,
    observer22_panel1_recurrence_fields_sound,
    observer22_panel2_recurrence_fields_sound,
    observer22_panel3_recurrence_fields_sound,
    observer22_panel4_recurrence_fields_sound,
    observer22_panel5_recurrence_fields_sound,
    observer22_panel6_recurrence_fields_sound,
    observer22_panel7_recurrence_fields_sound,
    observer22_frame_recurrence_fields_sound⟩
def observer22PanelFormulaBounds : Prop :=
  panelFormulaBounds observer22Panel0Data observer22Panel0Endpoints ∧
  panelFormulaBounds observer22Panel1Data observer22Panel1Endpoints ∧
  panelFormulaBounds observer22Panel2Data observer22Panel2Endpoints ∧
  panelFormulaBounds observer22Panel3Data observer22Panel3Endpoints ∧
  panelFormulaBounds observer22Panel4Data observer22Panel4Endpoints ∧
  panelFormulaBounds observer22Panel5Data observer22Panel5Endpoints ∧
  panelFormulaBounds observer22Panel6Data observer22Panel6Endpoints ∧
  panelFormulaBounds observer22Panel7Data observer22Panel7Endpoints
theorem observer22_all_panel_formula_bounds : observer22PanelFormulaBounds := by
  exact ⟨observer22_panel0_formula_sound,
    observer22_panel1_formula_sound,
    observer22_panel2_formula_sound,
    observer22_panel3_formula_sound,
    observer22_panel4_formula_sound,
    observer22_panel5_formula_sound,
    observer22_panel6_formula_sound,
    observer22_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
