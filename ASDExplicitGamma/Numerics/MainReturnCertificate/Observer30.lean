module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer30Panel0Data : MainPanelData :=
  {
    observer := 30, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((88327295668604176 : ℚ) / 2472817566054278538333841936725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer30Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393331356672799743188822660, ellLower := 352021008930312778709632971039,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172439903420243426930524466, offsetUpper := 6186465082921796873511354746,
    supportELower := 38565881025373792197317991991, supportEUpper := 40091601708441946305507044921,
    supportLambdaLower := 352021008930312778709632971039,
    supportLambdaUpper := 361977602516874822350446919318,
    supportJLower := 42086091114676919984414321701, supportJUpper := 43711377733610694529011514115,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer30Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer30Panel0Data observer30Panel0Endpoints
theorem observer30_panel0_kernel_check : observer30Panel0Check = true := by
  decide +kernel
theorem observer30_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer30Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer30Panel0Data) s observer30Panel0Data.anchor ≤
        (observer30Panel0Endpoints.energyUpper : ℝ) ∧
      (observer30Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer30Panel0Data) s observer30Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer30Panel0Data) s observer30Panel0Data.anchor ≤
        (observer30Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer30Panel0Data) s observer30Panel0Data.anchor ≤
        (observer30Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer30Panel0Data) s observer30Panel0Data.anchor ≤
        (observer30Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer30Panel0Data observer30Panel0Endpoints
    observer30_panel0_kernel_check s hs
def observer30Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer30Panel0Endpoints
theorem observer30_panel0_recurrence_field_kernel_check :
    observer30Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer30_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer30Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer30Panel0Endpoints
    observer30_panel0_recurrence_field_kernel_check

def observer30Panel1Data : MainPanelData :=
  {
    observer := 30, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((88327295668604176 : ℚ) / 2472817566054278538333841936725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer30Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115217202565099771884723572, ellLower := 351854359364973892232756903176,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376119831288383253106567548, offsetUpper := 6390640827160882810550290560,
    supportELower := 40091552627222063960781046206, supportEUpper := 41498138162202841550050022951,
    supportLambdaLower := 351854359364973892232756903176,
    supportLambdaUpper := 361420274407797092245573902932,
    supportJLower := 43610096220871802883108615237, supportJUpper := 45112340906280812472505761981,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer30Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer30Panel1Data observer30Panel1Endpoints
theorem observer30_panel1_kernel_check : observer30Panel1Check = true := by
  decide +kernel
theorem observer30_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer30Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer30Panel1Data) s observer30Panel1Data.anchor ≤
        (observer30Panel1Endpoints.energyUpper : ℝ) ∧
      (observer30Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer30Panel1Data) s observer30Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer30Panel1Data) s observer30Panel1Data.anchor ≤
        (observer30Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer30Panel1Data) s observer30Panel1Data.anchor ≤
        (observer30Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer30Panel1Data) s observer30Panel1Data.anchor ≤
        (observer30Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer30Panel1Data observer30Panel1Endpoints
    observer30_panel1_kernel_check s hs
def observer30Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer30Panel1Endpoints
theorem observer30_panel1_recurrence_field_kernel_check :
    observer30Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer30_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer30Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer30Panel1Endpoints
    observer30_panel1_recurrence_field_kernel_check

def observer30Panel2Data : MainPanelData :=
  {
    observer := 30, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((88327295668604176 : ℚ) / 2472817566054278538333841936725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer30Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817773882922207143067880617, ellLower := 351674150258142607077218187903,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591873163033117826160468253, offsetUpper := 6606885516239331461859819704,
    supportELower := 41498084240736666288622444301, supportEUpper := 42885115042708009075249503276,
    supportLambdaLower := 351674150258142607077218187903,
    supportLambdaUpper := 360893704422541716003713437012,
    supportJLower := 45014825743318092359394626180, supportJUpper := 46494052086933426235286637647,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer30Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer30Panel2Data observer30Panel2Endpoints
theorem observer30_panel2_kernel_check : observer30Panel2Check = true := by
  decide +kernel
theorem observer30_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer30Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer30Panel2Data) s observer30Panel2Data.anchor ≤
        (observer30Panel2Endpoints.energyUpper : ℝ) ∧
      (observer30Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer30Panel2Data) s observer30Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer30Panel2Data) s observer30Panel2Data.anchor ≤
        (observer30Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer30Panel2Data) s observer30Panel2Data.anchor ≤
        (observer30Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer30Panel2Data) s observer30Panel2Data.anchor ≤
        (observer30Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer30Panel2Data observer30Panel2Endpoints
    observer30_panel2_kernel_check s hs
def observer30Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer30Panel2Endpoints
theorem observer30_panel2_recurrence_field_kernel_check :
    observer30Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer30_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer30Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer30Panel2Endpoints
    observer30_panel2_recurrence_field_kernel_check

def observer30Panel3Data : MainPanelData :=
  {
    observer := 30, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((88327295668604176 : ℚ) / 2472817566054278538333841936725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer30Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510241315878686933810823548, ellLower := 351497889197523863339352608663,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806511449253411583857120296, offsetUpper := 6822012620385064911216528678,
    supportELower := 42885056316565860977853589150, supportEUpper := 44261786502148222402834300532,
    supportLambdaLower := 351497889197523863339352608663,
    supportLambdaUpper := 360396464788702664775782961283,
    supportJLower := 46400035208541099611247115236, supportJUpper := 47865751150035249050592130145,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer30Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer30Panel3Data observer30Panel3Endpoints
theorem observer30_panel3_kernel_check : observer30Panel3Check = true := by
  decide +kernel
theorem observer30_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer30Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer30Panel3Data) s observer30Panel3Data.anchor ≤
        (observer30Panel3Endpoints.energyUpper : ℝ) ∧
      (observer30Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer30Panel3Data) s observer30Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer30Panel3Data) s observer30Panel3Data.anchor ≤
        (observer30Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer30Panel3Data) s observer30Panel3Data.anchor ≤
        (observer30Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer30Panel3Data) s observer30Panel3Data.anchor ≤
        (observer30Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer30Panel3Data observer30Panel3Endpoints
    observer30_panel3_kernel_check s hs
def observer30Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer30Panel3Endpoints
theorem observer30_panel3_recurrence_field_kernel_check :
    observer30Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer30_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer30Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer30Panel3Endpoints
    observer30_panel3_recurrence_field_kernel_check

def observer30Panel4Data : MainPanelData :=
  {
    observer := 30, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((88327295668604176 : ℚ) / 2472817566054278538333841936725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer30Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196148320292092752732032531, ellLower := 351326854377974883000921703680,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020441081752197765246626004, offsetUpper := 7036429456919019377046127558,
    supportELower := 44261722990566219607982927310, supportEUpper := 45631702563432497948445449857,
    supportLambdaLower := 351326854377974883000921703680,
    supportLambdaUpper := 359926430736819374559463343578,
    supportJLower := 47774991534345968437992144346, supportJUpper := 49230966870800691694040083293,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer30Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer30Panel4Data observer30Panel4Endpoints
theorem observer30_panel4_kernel_check : observer30Panel4Check = true := by
  decide +kernel
theorem observer30_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer30Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer30Panel4Data) s observer30Panel4Data.anchor ≤
        (observer30Panel4Endpoints.energyUpper : ℝ) ∧
      (observer30Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer30Panel4Data) s observer30Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer30Panel4Data) s observer30Panel4Data.anchor ≤
        (observer30Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer30Panel4Data) s observer30Panel4Data.anchor ≤
        (observer30Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer30Panel4Data) s observer30Panel4Data.anchor ≤
        (observer30Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer30Panel4Data observer30Panel4Endpoints
    observer30_panel4_kernel_check s hs
def observer30Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer30Panel4Endpoints
theorem observer30_panel4_recurrence_field_kernel_check :
    observer30Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer30_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer30Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer30Panel4Endpoints
    observer30_panel4_recurrence_field_kernel_check

def observer30Panel5Data : MainPanelData :=
  {
    observer := 30, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((88327295668604176 : ℚ) / 2472817566054278538333841936725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer30Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877525560442219673212876348, ellLower := 351161302715510298071053139740,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217425462868628482499318104, offsetUpper := 7233899986508253967341136632,
    supportELower := 45631634279556589157934782487, supportEUpper := 46996674740233175638360259543,
    supportLambdaLower := 351161302715510298071053139740,
    supportLambdaUpper := 359481477532111245562492621758,
    supportJLower := 49143247306711692138645313884, supportJUpper := 50591489515554288093985185761,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer30Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer30Panel5Data observer30Panel5Endpoints
theorem observer30_panel5_kernel_check : observer30Panel5Check = true := by
  decide +kernel
theorem observer30_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer30Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer30Panel5Data) s observer30Panel5Data.anchor ≤
        (observer30Panel5Endpoints.energyUpper : ℝ) ∧
      (observer30Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer30Panel5Data) s observer30Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer30Panel5Data) s observer30Panel5Data.anchor ≤
        (observer30Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer30Panel5Data) s observer30Panel5Data.anchor ≤
        (observer30Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer30Panel5Data) s observer30Panel5Data.anchor ≤
        (observer30Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer30Panel5Data observer30Panel5Endpoints
    observer30_panel5_kernel_check s hs
def observer30Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer30Panel5Endpoints
theorem observer30_panel5_recurrence_field_kernel_check :
    observer30Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer30_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer30Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer30Panel5Endpoints
    observer30_panel5_recurrence_field_kernel_check

def observer30Panel6Data : MainPanelData :=
  {
    observer := 30, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((88327295668604176 : ℚ) / 2472817566054278538333841936725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer30Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554947444721284970549997932, ellLower := 351001195597903214305255461551,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429990413749899224289315905, offsetUpper := 7446950138979241918593335205,
    supportELower := 46996601694141603774036217764, supportEUpper := 48357778051973798046032747144,
    supportLambdaLower := 351001195597903214305255461551,
    supportLambdaUpper := 359059624179637983720392922746,
    supportJLower := 50506613650120635917088772379, supportJUpper := 51948374293770177883236676372,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer30Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer30Panel6Data observer30Panel6Endpoints
theorem observer30_panel6_kernel_check : observer30Panel6Check = true := by
  decide +kernel
theorem observer30_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer30Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer30Panel6Data) s observer30Panel6Data.anchor ≤
        (observer30Panel6Endpoints.energyUpper : ℝ) ∧
      (observer30Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer30Panel6Data) s observer30Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer30Panel6Data) s observer30Panel6Data.anchor ≤
        (observer30Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer30Panel6Data) s observer30Panel6Data.anchor ≤
        (observer30Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer30Panel6Data) s observer30Panel6Data.anchor ≤
        (observer30Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer30Panel6Data observer30Panel6Endpoints
    observer30_panel6_kernel_check s hs
def observer30Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer30Panel6Endpoints
theorem observer30_panel6_recurrence_field_kernel_check :
    observer30Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer30_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer30Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer30Panel6Endpoints
    observer30_panel6_recurrence_field_kernel_check

def observer30Panel7Data : MainPanelData :=
  {
    observer := 30, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((88327295668604176 : ℚ) / 2472817566054278538333841936725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer30Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229338664825178334914037970, ellLower := 350846382757806035818086536378,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642255776220542285470664785, offsetUpper := 7659700019197922294441919505,
    supportELower := 48357700251923269130428795133, supportEUpper := 49715714732595633989594790932,
    supportLambdaLower := 350846382757806035818086536378,
    supportLambdaUpper := 358659063056368595510525636674,
    supportJLower := 51866164079501329488609660496, supportJUpper := 53302305363159319944700047299,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer30Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer30Panel7Data observer30Panel7Endpoints
theorem observer30_panel7_kernel_check : observer30Panel7Check = true := by
  decide +kernel
theorem observer30_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer30Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer30Panel7Data) s observer30Panel7Data.anchor ≤
        (observer30Panel7Endpoints.energyUpper : ℝ) ∧
      (observer30Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer30Panel7Data) s observer30Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer30Panel7Data) s observer30Panel7Data.anchor ≤
        (observer30Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer30Panel7Data) s observer30Panel7Data.anchor ≤
        (observer30Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer30Panel7Data) s observer30Panel7Data.anchor ≤
        (observer30Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer30Panel7Data observer30Panel7Endpoints
    observer30_panel7_kernel_check s hs
def observer30Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer30Panel7Endpoints
theorem observer30_panel7_recurrence_field_kernel_check :
    observer30Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer30_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer30Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer30Panel7Endpoints
    observer30_panel7_recurrence_field_kernel_check

def observer30InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 30, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer30Panel0Endpoints, observer30Panel1Endpoints, observer30Panel2Endpoints, observer30Panel3Endpoints, observer30Panel4Endpoints, observer30Panel5Endpoints, observer30Panel6Endpoints, observer30Panel7Endpoints]
  }
def observer30FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer30InsertionEndpoints.frameLower
    observer30InsertionEndpoints.frameUpper
theorem observer30_frame_recurrence_field_kernel_check :
    observer30FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer30_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer30InsertionEndpoints.frameLower
      observer30InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer30InsertionEndpoints.frameLower
    observer30InsertionEndpoints.frameUpper
    observer30_frame_recurrence_field_kernel_check
def observer30RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer30Panel0Endpoints ∧
  panelRecurrenceFields observer30Panel1Endpoints ∧
  panelRecurrenceFields observer30Panel2Endpoints ∧
  panelRecurrenceFields observer30Panel3Endpoints ∧
  panelRecurrenceFields observer30Panel4Endpoints ∧
  panelRecurrenceFields observer30Panel5Endpoints ∧
  panelRecurrenceFields observer30Panel6Endpoints ∧
  panelRecurrenceFields observer30Panel7Endpoints ∧ insertionFrameRecurrenceFields observer30InsertionEndpoints.frameLower
      observer30InsertionEndpoints.frameUpper
theorem observer30_all_recurrence_fields :
    observer30RecurrenceFieldBounds := by
  exact ⟨observer30_panel0_recurrence_fields_sound,
    observer30_panel1_recurrence_fields_sound,
    observer30_panel2_recurrence_fields_sound,
    observer30_panel3_recurrence_fields_sound,
    observer30_panel4_recurrence_fields_sound,
    observer30_panel5_recurrence_fields_sound,
    observer30_panel6_recurrence_fields_sound,
    observer30_panel7_recurrence_fields_sound,
    observer30_frame_recurrence_fields_sound⟩
def observer30PanelFormulaBounds : Prop :=
  panelFormulaBounds observer30Panel0Data observer30Panel0Endpoints ∧
  panelFormulaBounds observer30Panel1Data observer30Panel1Endpoints ∧
  panelFormulaBounds observer30Panel2Data observer30Panel2Endpoints ∧
  panelFormulaBounds observer30Panel3Data observer30Panel3Endpoints ∧
  panelFormulaBounds observer30Panel4Data observer30Panel4Endpoints ∧
  panelFormulaBounds observer30Panel5Data observer30Panel5Endpoints ∧
  panelFormulaBounds observer30Panel6Data observer30Panel6Endpoints ∧
  panelFormulaBounds observer30Panel7Data observer30Panel7Endpoints
theorem observer30_all_panel_formula_bounds : observer30PanelFormulaBounds := by
  exact ⟨observer30_panel0_formula_sound,
    observer30_panel1_formula_sound,
    observer30_panel2_formula_sound,
    observer30_panel3_formula_sound,
    observer30_panel4_formula_sound,
    observer30_panel5_formula_sound,
    observer30_panel6_formula_sound,
    observer30_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
