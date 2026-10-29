module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer13Panel0Data : MainPanelData :=
  {
    observer := 13, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((683964322 : ℚ) / 148275506652525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer13Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49780008639460335917734585729, ellLower := 353059978549264737678830319808,
    rhoLower := 99955809766760977548828223153564, rhoUpper := 99955909722620722231348458263183,
    offsetLower := 6216548241676147167614989359, offsetUpper := 6230641607857442268657180689,
    supportELower := 38937074517206760839015810360, supportEUpper := 40466954171702171472992255386,
    supportLambdaLower := 353059978549264737678830319808,
    supportLambdaUpper := 363031638069915125782623854164,
    supportJLower := 42467674302699408215804113558, supportJUpper := 44097270552401322730818493928,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer13Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer13Panel0Data observer13Panel0Endpoints
theorem observer13_panel0_kernel_check : observer13Panel0Check = true := by
  decide +kernel
theorem observer13_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer13Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer13Panel0Data) s observer13Panel0Data.anchor ≤
        (observer13Panel0Endpoints.energyUpper : ℝ) ∧
      (observer13Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer13Panel0Data) s observer13Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer13Panel0Data) s observer13Panel0Data.anchor ≤
        (observer13Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer13Panel0Data) s observer13Panel0Data.anchor ≤
        (observer13Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer13Panel0Data) s observer13Panel0Data.anchor ≤
        (observer13Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer13Panel0Data observer13Panel0Endpoints
    observer13_panel0_kernel_check s hs
def observer13Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer13Panel0Endpoints
theorem observer13_panel0_recurrence_field_kernel_check :
    observer13Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer13_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer13Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer13Panel0Endpoints
    observer13_panel0_recurrence_field_kernel_check

def observer13Panel1Data : MainPanelData :=
  {
    observer := 13, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((683964322 : ℚ) / 148275506652525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer13Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51505920317137437004539786879, ellLower := 352883589158018785379724876038,
    rhoLower := 99955809766760977548828223153564, rhoUpper := 99955909722620722231348458263183,
    offsetLower := 6435295897085966028336767088, offsetUpper := 6449885180083014674616793732,
    supportELower := 40466904706476746632944559750, supportEUpper := 41877619035264067561622099835,
    supportLambdaLower := 352883589158018785379724876038,
    supportLambdaUpper := 362464052159217417079994219698,
    supportJLower := 43995740598056934486741808510, supportJUpper := 45502259556856241732422042032,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer13Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer13Panel1Data observer13Panel1Endpoints
theorem observer13_panel1_kernel_check : observer13Panel1Check = true := by
  decide +kernel
theorem observer13_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer13Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer13Panel1Data) s observer13Panel1Data.anchor ≤
        (observer13Panel1Endpoints.energyUpper : ℝ) ∧
      (observer13Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer13Panel1Data) s observer13Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer13Panel1Data) s observer13Panel1Data.anchor ≤
        (observer13Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer13Panel1Data) s observer13Panel1Data.anchor ≤
        (observer13Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer13Panel1Data) s observer13Panel1Data.anchor ≤
        (observer13Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer13Panel1Data observer13Panel1Endpoints
    observer13_panel1_kernel_check s hs
def observer13Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer13Panel1Endpoints
theorem observer13_panel1_recurrence_field_kernel_check :
    observer13Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer13_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer13Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer13Panel1Endpoints
    observer13_panel1_recurrence_field_kernel_check

def observer13Panel2Data : MainPanelData :=
  {
    observer := 13, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((683964322 : ℚ) / 148275506652525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer13Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 53212477591132069350318280616, ellLower := 352693997985806740616686477650,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6637011137513455508581278457, offsetUpper := 6652091927932468849663476987,
    supportELower := 41877564717133078239025918312, supportEUpper := 43268695171099849847358378606,
    supportLambdaLower := 352693997985806740616686477650,
    supportLambdaUpper := 361927616004653062243987578328,
    supportJLower := 45404504696991145645192783088, supportJUpper := 46887971331146380469798254390,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer13Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer13Panel2Data observer13Panel2Endpoints
theorem observer13_panel2_kernel_check : observer13Panel2Check = true := by
  decide +kernel
theorem observer13_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer13Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer13Panel2Data) s observer13Panel2Data.anchor ≤
        (observer13Panel2Endpoints.energyUpper : ℝ) ∧
      (observer13Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer13Panel2Data) s observer13Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer13Panel2Data) s observer13Panel2Data.anchor ≤
        (observer13Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer13Panel2Data) s observer13Panel2Data.anchor ≤
        (observer13Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer13Panel2Data) s observer13Panel2Data.anchor ≤
        (observer13Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer13Panel2Data observer13Panel2Endpoints
    observer13_panel2_kernel_check s hs
def observer13Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer13Panel2Endpoints
theorem observer13_panel2_recurrence_field_kernel_check :
    observer13Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer13_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer13Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer13Panel2Endpoints
    observer13_panel2_recurrence_field_kernel_check

def observer13Panel3Data : MainPanelData :=
  {
    observer := 13, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((683964322 : ℚ) / 148275506652525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer13Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54908921078440489937649993349, ellLower := 352508688985721127083917583462,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6852202974039698445433178914, offsetUpper := 6867772728981943049565187861,
    supportELower := 43268636035779185672422830946, supportEUpper := 44649437699996084438355083083,
    supportLambdaLower := 352508688985721127083917583462,
    supportLambdaUpper := 361420874860405964333743360629,
    supportJLower := 46793722925636396943262006780, supportJUpper := 48263646448600144081692516690,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer13Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer13Panel3Data observer13Panel3Endpoints
theorem observer13_panel3_kernel_check : observer13Panel3Check = true := by
  decide +kernel
theorem observer13_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer13Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer13Panel3Data) s observer13Panel3Data.anchor ≤
        (observer13Panel3Endpoints.energyUpper : ℝ) ∧
      (observer13Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer13Panel3Data) s observer13Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer13Panel3Data) s observer13Panel3Data.anchor ≤
        (observer13Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer13Panel3Data) s observer13Panel3Data.anchor ≤
        (observer13Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer13Panel3Data) s observer13Panel3Data.anchor ≤
        (observer13Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer13Panel3Data observer13Panel3Endpoints
    observer13_panel3_kernel_check s hs
def observer13Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer13Panel3Endpoints
theorem observer13_panel3_recurrence_field_kernel_check :
    observer13Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer13_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer13Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer13Panel3Endpoints
    observer13_panel3_recurrence_field_kernel_check

def observer13Panel4Data : MainPanelData :=
  {
    observer := 13, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((683964322 : ℚ) / 148275506652525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer13Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56598780263770023711366388630, ellLower := 352328919038903704934546747435,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 7066687975971521317575203808, offsetUpper := 7082745089348931563263715028,
    supportELower := 44649373766860969075080479672, supportEUpper := 46023397552838228725504321623,
    supportLambdaLower := 352328919038903704934546747435,
    supportLambdaUpper := 360941679744348595443133451207,
    supportJLower := 48172662957250006124425947146, supportJUpper := 49632814350281714679935656136,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer13Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer13Panel4Data observer13Panel4Endpoints
theorem observer13_panel4_kernel_check : observer13Panel4Check = true := by
  decide +kernel
theorem observer13_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer13Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer13Panel4Data) s observer13Panel4Data.anchor ≤
        (observer13Panel4Endpoints.energyUpper : ℝ) ∧
      (observer13Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer13Panel4Data) s observer13Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer13Panel4Data) s observer13Panel4Data.anchor ≤
        (observer13Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer13Panel4Data) s observer13Panel4Data.anchor ≤
        (observer13Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer13Panel4Data) s observer13Panel4Data.anchor ≤
        (observer13Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer13Panel4Data observer13Panel4Endpoints
    observer13_panel4_kernel_check s hs
def observer13Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer13Panel4Endpoints
theorem observer13_panel4_recurrence_field_kernel_check :
    observer13Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer13_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer13Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer13Panel4Endpoints
    observer13_panel4_recurrence_field_kernel_check

def observer13Panel5Data : MainPanelData :=
  {
    observer := 13, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((683964322 : ℚ) / 148275506652525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer13Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 58284086446326915525056933711, ellLower := 352154925765599067850536666276,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 7280703772199814284307385540, offsetUpper := 7297247177870909958334025577,
    supportELower := 46023328835167746570134116856, supportEUpper := 47392387096491039434804963587,
    supportLambdaLower := 352154925765599067850536666276,
    supportLambdaUpper := 360487884095103653828549628078,
    supportJLower := 49544878092823737248639483518, supportJUpper := 50997265937442075973090459868,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer13Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer13Panel5Data observer13Panel5Endpoints
theorem observer13_panel5_kernel_check : observer13Panel5Check = true := by
  decide +kernel
theorem observer13_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer13Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer13Panel5Data) s observer13Panel5Data.anchor ≤
        (observer13Panel5Endpoints.energyUpper : ℝ) ∧
      (observer13Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer13Panel5Data) s observer13Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer13Panel5Data) s observer13Panel5Data.anchor ≤
        (observer13Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer13Panel5Data) s observer13Panel5Data.anchor ≤
        (observer13Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer13Panel5Data) s observer13Panel5Data.anchor ≤
        (observer13Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer13Panel5Data observer13Panel5Endpoints
    observer13_panel5_kernel_check s hs
def observer13Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer13Panel5Endpoints
theorem observer13_panel5_recurrence_field_kernel_check :
    observer13Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer13_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer13Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer13Panel5Endpoints
    observer13_panel5_recurrence_field_kernel_check

def observer13Panel6Data : MainPanelData :=
  {
    observer := 13, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((683964322 : ℚ) / 148275506652525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer13Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59965414640461206424147227730, ellLower := 351986653021597020463957679869,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7477283399627898852343761222, offsetUpper := 7494312188963178106521732425,
    supportELower := 47392313604491037894557287738, supportEUpper := 48757482153862359136191201191,
    supportLambdaLower := 351986653021597020463957679869,
    supportLambdaUpper := 360057487165083222790392172283,
    supportJLower := 50912180134707008099196864536, supportJUpper := 52358057025513191364095122914,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer13Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer13Panel6Data observer13Panel6Endpoints
theorem observer13_panel6_kernel_check : observer13Panel6Check = true := by
  decide +kernel
theorem observer13_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer13Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer13Panel6Data) s observer13Panel6Data.anchor ≤
        (observer13Panel6Endpoints.energyUpper : ℝ) ∧
      (observer13Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer13Panel6Data) s observer13Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer13Panel6Data) s observer13Panel6Data.anchor ≤
        (observer13Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer13Panel6Data) s observer13Panel6Data.anchor ≤
        (observer13Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer13Panel6Data) s observer13Panel6Data.anchor ≤
        (observer13Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer13Panel6Data observer13Panel6Endpoints
    observer13_panel6_kernel_check s hs
def observer13Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer13Panel6Endpoints
theorem observer13_panel6_recurrence_field_kernel_check :
    observer13Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer13_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer13Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer13Panel6Endpoints
    observer13_panel6_recurrence_field_kernel_check

def observer13Panel7Data : MainPanelData :=
  {
    observer := 13, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((683964322 : ℚ) / 148275506652525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer13Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61643690116679060533176556138, ellLower := 351823934556763775273447640684,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7690108078528833995993126855, offsetUpper := 7707621555474393319118665561,
    supportELower := 48757403895912008812663167361, supportEUpper := 50119385717108661075186403976,
    supportLambdaLower := 351823934556763775273447640684,
    supportLambdaUpper := 359648663390763309503737823491,
    supportJLower := 52275643241479646565397643767, supportJUpper := 53715872351016294170223782211,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer13Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer13Panel7Data observer13Panel7Endpoints
theorem observer13_panel7_kernel_check : observer13Panel7Check = true := by
  decide +kernel
theorem observer13_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer13Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer13Panel7Data) s observer13Panel7Data.anchor ≤
        (observer13Panel7Endpoints.energyUpper : ℝ) ∧
      (observer13Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer13Panel7Data) s observer13Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer13Panel7Data) s observer13Panel7Data.anchor ≤
        (observer13Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer13Panel7Data) s observer13Panel7Data.anchor ≤
        (observer13Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer13Panel7Data) s observer13Panel7Data.anchor ≤
        (observer13Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer13Panel7Data observer13Panel7Endpoints
    observer13_panel7_kernel_check s hs
def observer13Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer13Panel7Endpoints
theorem observer13_panel7_recurrence_field_kernel_check :
    observer13Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer13_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer13Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer13Panel7Endpoints
    observer13_panel7_recurrence_field_kernel_check

def observer13InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 13, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer13Panel0Endpoints, observer13Panel1Endpoints, observer13Panel2Endpoints, observer13Panel3Endpoints, observer13Panel4Endpoints, observer13Panel5Endpoints, observer13Panel6Endpoints, observer13Panel7Endpoints]
  }
def observer13FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer13InsertionEndpoints.frameLower
    observer13InsertionEndpoints.frameUpper
theorem observer13_frame_recurrence_field_kernel_check :
    observer13FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer13_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer13InsertionEndpoints.frameLower
      observer13InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer13InsertionEndpoints.frameLower
    observer13InsertionEndpoints.frameUpper
    observer13_frame_recurrence_field_kernel_check
def observer13RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer13Panel0Endpoints ∧
  panelRecurrenceFields observer13Panel1Endpoints ∧
  panelRecurrenceFields observer13Panel2Endpoints ∧
  panelRecurrenceFields observer13Panel3Endpoints ∧
  panelRecurrenceFields observer13Panel4Endpoints ∧
  panelRecurrenceFields observer13Panel5Endpoints ∧
  panelRecurrenceFields observer13Panel6Endpoints ∧
  panelRecurrenceFields observer13Panel7Endpoints ∧ insertionFrameRecurrenceFields observer13InsertionEndpoints.frameLower
      observer13InsertionEndpoints.frameUpper
theorem observer13_all_recurrence_fields :
    observer13RecurrenceFieldBounds := by
  exact ⟨observer13_panel0_recurrence_fields_sound,
    observer13_panel1_recurrence_fields_sound,
    observer13_panel2_recurrence_fields_sound,
    observer13_panel3_recurrence_fields_sound,
    observer13_panel4_recurrence_fields_sound,
    observer13_panel5_recurrence_fields_sound,
    observer13_panel6_recurrence_fields_sound,
    observer13_panel7_recurrence_fields_sound,
    observer13_frame_recurrence_fields_sound⟩
def observer13PanelFormulaBounds : Prop :=
  panelFormulaBounds observer13Panel0Data observer13Panel0Endpoints ∧
  panelFormulaBounds observer13Panel1Data observer13Panel1Endpoints ∧
  panelFormulaBounds observer13Panel2Data observer13Panel2Endpoints ∧
  panelFormulaBounds observer13Panel3Data observer13Panel3Endpoints ∧
  panelFormulaBounds observer13Panel4Data observer13Panel4Endpoints ∧
  panelFormulaBounds observer13Panel5Data observer13Panel5Endpoints ∧
  panelFormulaBounds observer13Panel6Data observer13Panel6Endpoints ∧
  panelFormulaBounds observer13Panel7Data observer13Panel7Endpoints
theorem observer13_all_panel_formula_bounds : observer13PanelFormulaBounds := by
  exact ⟨observer13_panel0_formula_sound,
    observer13_panel1_formula_sound,
    observer13_panel2_formula_sound,
    observer13_panel3_formula_sound,
    observer13_panel4_formula_sound,
    observer13_panel5_formula_sound,
    observer13_panel6_formula_sound,
    observer13_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
