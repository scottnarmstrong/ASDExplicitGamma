module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer35Panel0Data : MainPanelData :=
  {
    observer := 35, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((21463532847470874058 : ℚ) / 146017404457939093410075032521674525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer35Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393299882771758979672121690, ellLower := 352020925116850225100015823897,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172437439892082100811744684, offsetUpper := 6186462613795942380613379655,
    supportELower := 38565850736204524130625374283, supportEUpper := 40091571084600740914678904142,
    supportLambdaLower := 352020925116850225100015823897,
    supportLambdaUpper := 361977517511496237110263675443,
    supportJLower := 42086059987373026381625532521, supportJUpper := 43711346259715703285781540897,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer35Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer35Panel0Data observer35Panel0Endpoints
theorem observer35_panel0_kernel_check : observer35Panel0Check = true := by
  decide +kernel
theorem observer35_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer35Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer35Panel0Data) s observer35Panel0Data.anchor ≤
        (observer35Panel0Endpoints.energyUpper : ℝ) ∧
      (observer35Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer35Panel0Data) s observer35Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer35Panel0Data) s observer35Panel0Data.anchor ≤
        (observer35Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer35Panel0Data) s observer35Panel0Data.anchor ≤
        (observer35Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer35Panel0Data) s observer35Panel0Data.anchor ≤
        (observer35Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer35Panel0Data observer35Panel0Endpoints
    observer35_panel0_kernel_check s hs
def observer35Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer35Panel0Endpoints
theorem observer35_panel0_recurrence_field_kernel_check :
    observer35Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer35_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer35Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer35Panel0Endpoints
    observer35_panel0_recurrence_field_kernel_check

def observer35Panel1Data : MainPanelData :=
  {
    observer := 35, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((21463532847470874058 : ℚ) / 146017404457939093410075032521674525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer35Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115185404733088605127591555, ellLower := 351854276336349891358128670317,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376117369422585894215369337, offsetUpper := 6390638359688424343021683955,
    supportELower := 40091522003412179800202228636, supportEUpper := 41498107206175484694710371468,
    supportLambdaLower := 351854276336349891358128670317,
    supportLambdaUpper := 361420190227936613132498624771,
    supportJLower := 43610064766775678713783515339, supportJUpper := 45112309108454850826035357716,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer35Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer35Panel1Data observer35Panel1Endpoints
theorem observer35_panel1_kernel_check : observer35Panel1Check = true := by
  decide +kernel
theorem observer35_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer35Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer35Panel1Data) s observer35Panel1Data.anchor ≤
        (observer35Panel1Endpoints.energyUpper : ℝ) ∧
      (observer35Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer35Panel1Data) s observer35Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer35Panel1Data) s observer35Panel1Data.anchor ≤
        (observer35Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer35Panel1Data) s observer35Panel1Data.anchor ≤
        (observer35Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer35Panel1Data) s observer35Panel1Data.anchor ≤
        (observer35Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer35Panel1Data observer35Panel1Endpoints
    observer35_panel1_kernel_check s hs
def observer35Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer35Panel1Endpoints
theorem observer35_panel1_recurrence_field_kernel_check :
    observer35Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer35_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer35Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer35Panel1Endpoints
    observer35_panel1_recurrence_field_kernel_check

def observer35Panel2Data : MainPanelData :=
  {
    observer := 35, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((21463532847470874058 : ℚ) / 146017404457939093410075032521674525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer35Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817741763221262068947287139, ellLower := 351674067985940909990825617913,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591870696495006933391770380, offsetUpper := 6606883044083918718539245977,
    supportELower := 41498053284741650276505098668, supportEUpper := 42885083756867056019185305967,
    supportLambdaLower := 351674067985940909990825617913,
    supportLambdaUpper := 360893621037147466226746595328,
    supportJLower := 45014793964601059376413354847, supportJUpper := 46494019967238530681452771921,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer35Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer35Panel2Data observer35Panel2Endpoints
theorem observer35_panel2_kernel_check : observer35Panel2Check = true := by
  decide +kernel
theorem observer35_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer35Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer35Panel2Data) s observer35Panel2Data.anchor ≤
        (observer35Panel2Endpoints.energyUpper : ℝ) ∧
      (observer35Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer35Panel2Data) s observer35Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer35Panel2Data) s observer35Panel2Data.anchor ≤
        (observer35Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer35Panel2Data) s observer35Panel2Data.anchor ≤
        (observer35Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer35Panel2Data) s observer35Panel2Data.anchor ≤
        (observer35Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer35Panel2Data observer35Panel2Endpoints
    observer35_panel2_kernel_check s hs
def observer35Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer35Panel2Endpoints
theorem observer35_panel2_recurrence_field_kernel_check :
    observer35Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer35_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer35Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer35Panel2Endpoints
    observer35_panel2_recurrence_field_kernel_check

def observer35Panel3Data : MainPanelData :=
  {
    observer := 35, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((21463532847470874058 : ℚ) / 146017404457939093410075032521674525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer35Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510208876314305650232310234, ellLower := 351497807655180370459610277778,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806508977643577020617753946, offsetUpper := 6822010143146378137577284318,
    supportELower := 42885025030758256501715757511, supportEUpper := 44261754888788590052680026879,
    supportLambdaLower := 351497807655180370459610277778,
    supportLambdaUpper := 360396382168832723462031770393,
    supportJLower := 46400003107310060206311860288, supportJUpper := 47865718710476917287300344583,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer35Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer35Panel3Data observer35Panel3Endpoints
theorem observer35_panel3_kernel_check : observer35Panel3Check = true := by
  decide +kernel
theorem observer35_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer35Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer35Panel3Data) s observer35Panel3Data.anchor ≤
        (observer35Panel3Endpoints.energyUpper : ℝ) ∧
      (observer35Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer35Panel3Data) s observer35Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer35Panel3Data) s observer35Panel3Data.anchor ≤
        (observer35Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer35Panel3Data) s observer35Panel3Data.anchor ≤
        (observer35Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer35Panel3Data) s observer35Panel3Data.anchor ≤
        (observer35Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer35Panel3Data observer35Panel3Endpoints
    observer35_panel3_kernel_check s hs
def observer35Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer35Panel3Endpoints
theorem observer35_panel3_recurrence_field_kernel_check :
    observer35Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer35_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer35Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer35Panel3Endpoints
    observer35_panel3_recurrence_field_kernel_check

def observer35Panel4Data : MainPanelData :=
  {
    observer := 35, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((21463532847470874058 : ℚ) / 146017404457939093410075032521674525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer35Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196115562815875578491586413, ellLower := 351326773540597669124711637155,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020438604788809130329971621, offsetUpper := 7036426974314586330416728672,
    supportELower := 44261691377240932218427987947, supportEUpper := 45631670624776243846897570197,
    supportLambdaLower := 351326773540597669124711637155,
    supportLambdaUpper := 359926348855428019318879472997,
    supportJLower := 47774959112646908909675104318, supportJUpper := 49230934113330524040086364927,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer35Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer35Panel4Data observer35Panel4Endpoints
theorem observer35_panel4_kernel_check : observer35Panel4Check = true := by
  decide +kernel
theorem observer35_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer35Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer35Panel4Data) s observer35Panel4Data.anchor ≤
        (observer35Panel4Endpoints.energyUpper : ℝ) ∧
      (observer35Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer35Panel4Data) s observer35Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer35Panel4Data) s observer35Panel4Data.anchor ≤
        (observer35Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer35Panel4Data) s observer35Panel4Data.anchor ≤
        (observer35Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer35Panel4Data) s observer35Panel4Data.anchor ≤
        (observer35Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer35Panel4Data observer35Panel4Endpoints
    observer35_panel4_kernel_check s hs
def observer35Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer35Panel4Endpoints
theorem observer35_panel4_recurrence_field_kernel_check :
    observer35Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer35_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer35Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer35Panel4Endpoints
    observer35_panel4_recurrence_field_kernel_check

def observer35Panel5Data : MainPanelData :=
  {
    observer := 35, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((21463532847470874058 : ℚ) / 146017404457939093410075032521674525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer35Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877492486954345270943715783, ellLower := 351161222559722963161805228503,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217422985991651992555263342, offsetUpper := 7233897503977548386385557951,
    supportELower := 45631602340935665522734764739, supportEUpper := 46996642478433823100659875812,
    supportLambdaLower := 351161222559722963161805228503,
    supportLambdaUpper := 359481396363864011134287713599,
    supportJLower := 49143214566532895154352817024, supportJUpper := 50591456442072463212002752948,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer35Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer35Panel5Data observer35Panel5Endpoints
theorem observer35_panel5_kernel_check : observer35Panel5Check = true := by
  decide +kernel
theorem observer35_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer35Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer35Panel5Data) s observer35Panel5Data.anchor ≤
        (observer35Panel5Endpoints.energyUpper : ℝ) ∧
      (observer35Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer35Panel5Data) s observer35Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer35Panel5Data) s observer35Panel5Data.anchor ≤
        (observer35Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer35Panel5Data) s observer35Panel5Data.anchor ≤
        (observer35Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer35Panel5Data) s observer35Panel5Data.anchor ≤
        (observer35Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer35Panel5Data observer35Panel5Endpoints
    observer35_panel5_kernel_check s hs
def observer35Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer35Panel5Endpoints
theorem observer35_panel5_recurrence_field_kernel_check :
    observer35Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer35_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer35Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer35Panel5Endpoints
    observer35_panel5_recurrence_field_kernel_check

def observer35Panel6Data : MainPanelData :=
  {
    observer := 35, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((21463532847470874058 : ℚ) / 146017404457939093410075032521674525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer35Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554914057072830998806414975, ellLower := 351001116101707819688553212979,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429987931128681372218839460, offsetUpper := 7446947650691183147672041270,
    supportELower := 46996569432378556779820716959, supportEUpper := 48357745469120265980327243112,
    supportLambdaLower := 351001116101707819688553212979,
    supportLambdaUpper := 359059543700750745145257805475,
    supportJLower := 50506580593395634976706249088, supportJUpper := 51948340906127773431779821167,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer35Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer35Panel6Data observer35Panel6Endpoints
theorem observer35_panel6_kernel_check : observer35Panel6Check = true := by
  decide +kernel
theorem observer35_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer35Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer35Panel6Data) s observer35Panel6Data.anchor ≤
        (observer35Panel6Endpoints.energyUpper : ℝ) ∧
      (observer35Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer35Panel6Data) s observer35Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer35Panel6Data) s observer35Panel6Data.anchor ≤
        (observer35Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer35Panel6Data) s observer35Panel6Data.anchor ≤
        (observer35Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer35Panel6Data) s observer35Panel6Data.anchor ≤
        (observer35Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer35Panel6Data observer35Panel6Endpoints
    observer35_panel6_kernel_check s hs
def observer35Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer35Panel6Endpoints
theorem observer35_panel6_recurrence_field_kernel_check :
    observer35Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer35_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer35Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer35Panel6Endpoints
    observer35_panel6_recurrence_field_kernel_check

def observer35Panel7Data : MainPanelData :=
  {
    observer := 35, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((21463532847470874058 : ℚ) / 146017404457939093410075032521674525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer35Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229304964820297601025901057, ellLower := 350846303900462590685828616928,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642253287697774246160968846, offsetUpper := 7659697524994842434701569551,
    supportELower := 48357667669107007671952764106, supportEUpper := 49715681830715820545343281172,
    supportLambdaLower := 350846303900462590685828616928,
    supportLambdaUpper := 358658983244466818575535696509,
    supportJLower := 51866130708111633578811050275, supportJUpper := 53302271663160488731098638138,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer35Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer35Panel7Data observer35Panel7Endpoints
theorem observer35_panel7_kernel_check : observer35Panel7Check = true := by
  decide +kernel
theorem observer35_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer35Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer35Panel7Data) s observer35Panel7Data.anchor ≤
        (observer35Panel7Endpoints.energyUpper : ℝ) ∧
      (observer35Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer35Panel7Data) s observer35Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer35Panel7Data) s observer35Panel7Data.anchor ≤
        (observer35Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer35Panel7Data) s observer35Panel7Data.anchor ≤
        (observer35Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer35Panel7Data) s observer35Panel7Data.anchor ≤
        (observer35Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer35Panel7Data observer35Panel7Endpoints
    observer35_panel7_kernel_check s hs
def observer35Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer35Panel7Endpoints
theorem observer35_panel7_recurrence_field_kernel_check :
    observer35Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer35_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer35Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer35Panel7Endpoints
    observer35_panel7_recurrence_field_kernel_check

def observer35InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 35, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer35Panel0Endpoints, observer35Panel1Endpoints, observer35Panel2Endpoints, observer35Panel3Endpoints, observer35Panel4Endpoints, observer35Panel5Endpoints, observer35Panel6Endpoints, observer35Panel7Endpoints]
  }
def observer35FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer35InsertionEndpoints.frameLower
    observer35InsertionEndpoints.frameUpper
theorem observer35_frame_recurrence_field_kernel_check :
    observer35FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer35_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer35InsertionEndpoints.frameLower
      observer35InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer35InsertionEndpoints.frameLower
    observer35InsertionEndpoints.frameUpper
    observer35_frame_recurrence_field_kernel_check
def observer35RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer35Panel0Endpoints ∧
  panelRecurrenceFields observer35Panel1Endpoints ∧
  panelRecurrenceFields observer35Panel2Endpoints ∧
  panelRecurrenceFields observer35Panel3Endpoints ∧
  panelRecurrenceFields observer35Panel4Endpoints ∧
  panelRecurrenceFields observer35Panel5Endpoints ∧
  panelRecurrenceFields observer35Panel6Endpoints ∧
  panelRecurrenceFields observer35Panel7Endpoints ∧ insertionFrameRecurrenceFields observer35InsertionEndpoints.frameLower
      observer35InsertionEndpoints.frameUpper
theorem observer35_all_recurrence_fields :
    observer35RecurrenceFieldBounds := by
  exact ⟨observer35_panel0_recurrence_fields_sound,
    observer35_panel1_recurrence_fields_sound,
    observer35_panel2_recurrence_fields_sound,
    observer35_panel3_recurrence_fields_sound,
    observer35_panel4_recurrence_fields_sound,
    observer35_panel5_recurrence_fields_sound,
    observer35_panel6_recurrence_fields_sound,
    observer35_panel7_recurrence_fields_sound,
    observer35_frame_recurrence_fields_sound⟩
def observer35PanelFormulaBounds : Prop :=
  panelFormulaBounds observer35Panel0Data observer35Panel0Endpoints ∧
  panelFormulaBounds observer35Panel1Data observer35Panel1Endpoints ∧
  panelFormulaBounds observer35Panel2Data observer35Panel2Endpoints ∧
  panelFormulaBounds observer35Panel3Data observer35Panel3Endpoints ∧
  panelFormulaBounds observer35Panel4Data observer35Panel4Endpoints ∧
  panelFormulaBounds observer35Panel5Data observer35Panel5Endpoints ∧
  panelFormulaBounds observer35Panel6Data observer35Panel6Endpoints ∧
  panelFormulaBounds observer35Panel7Data observer35Panel7Endpoints
theorem observer35_all_panel_formula_bounds : observer35PanelFormulaBounds := by
  exact ⟨observer35_panel0_formula_sound,
    observer35_panel1_formula_sound,
    observer35_panel2_formula_sound,
    observer35_panel3_formula_sound,
    observer35_panel4_formula_sound,
    observer35_panel5_formula_sound,
    observer35_panel6_formula_sound,
    observer35_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
