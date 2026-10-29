module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer40Panel0Data : MainPanelData :=
  {
    observer := 40, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((5215638481935422455384 : ℚ) / 8622181715836845526771520595372359026725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer40Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393297863888258827972767061, ellLower := 352020919741170769883011555404,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172437281860880469337036832, offsetUpper := 6186462455405658116596641042,
    supportELower := 38565848793307123837515088457, supportEUpper := 40091569120238408179284422370,
    supportLambdaLower := 352020919741170769883011555404,
    supportLambdaUpper := 361977512059381984994297676812,
    supportJLower := 42086057990718831536345204011, supportJUpper := 43711344240832228029227399139,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer40Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer40Panel0Data observer40Panel0Endpoints
theorem observer40_panel0_kernel_check : observer40Panel0Check = true := by
  decide +kernel
theorem observer40_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer40Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer40Panel0Data) s observer40Panel0Data.anchor ≤
        (observer40Panel0Endpoints.energyUpper : ℝ) ∧
      (observer40Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer40Panel0Data) s observer40Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer40Panel0Data) s observer40Panel0Data.anchor ≤
        (observer40Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer40Panel0Data) s observer40Panel0Data.anchor ≤
        (observer40Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer40Panel0Data) s observer40Panel0Data.anchor ≤
        (observer40Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer40Panel0Data observer40Panel0Endpoints
    observer40_panel0_kernel_check s hs
def observer40Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer40Panel0Endpoints
theorem observer40_panel0_recurrence_field_kernel_check :
    observer40Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer40_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer40Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer40Panel0Endpoints
    observer40_panel0_recurrence_field_kernel_check

def observer40Panel1Data : MainPanelData :=
  {
    observer := 40, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((5215638481935422455384 : ℚ) / 8622181715836845526771520595372359026725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer40Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115183365073566933377862964, ellLower := 351854271011008409694907838656,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376117211498115808882900011, offsetUpper := 6390638201404296560068369467,
    supportELower := 40091520039051855978903865217, supportEUpper := 41498105220507665551538929661,
    supportLambdaLower := 351854271011008409694907838656,
    supportLambdaUpper := 361420184828768849789191233494,
    supportJLower := 43610062749161940075852943603, supportJUpper := 45112307068795354049430841996,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer40Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer40Panel1Data observer40Panel1Endpoints
theorem observer40_panel1_kernel_check : observer40Panel1Check = true := by
  decide +kernel
theorem observer40_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer40Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer40Panel1Data) s observer40Panel1Data.anchor ≤
        (observer40Panel1Endpoints.energyUpper : ℝ) ∧
      (observer40Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer40Panel1Data) s observer40Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer40Panel1Data) s observer40Panel1Data.anchor ≤
        (observer40Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer40Panel1Data) s observer40Panel1Data.anchor ≤
        (observer40Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer40Panel1Data) s observer40Panel1Data.anchor ≤
        (observer40Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer40Panel1Data observer40Panel1Endpoints
    observer40_panel1_kernel_check s hs
def observer40Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer40Panel1Endpoints
theorem observer40_panel1_recurrence_field_kernel_check :
    observer40Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer40_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer40Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer40Panel1Endpoints
    observer40_panel1_recurrence_field_kernel_check

def observer40Panel2Data : MainPanelData :=
  {
    observer := 40, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((5215638481935422455384 : ℚ) / 8622181715836845526771520595372359026725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer40Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817739702917989554818876675, ellLower := 351674062709115070152738501589,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591870538270913492716948430, offsetUpper := 6606882885499485217047566799,
    supportELower := 41498051299075905438311111335, supportEUpper := 42885081750045934379845430164,
    supportLambdaLower := 351674062709115070152738501589,
    supportLambdaUpper := 360893615688934868262414416302,
    supportJLower := 45014791926167056139838496350, supportJUpper := 46494017906935283062469574328,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer40Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer40Panel2Data observer40Panel2Endpoints
theorem observer40_panel2_kernel_check : observer40Panel2Check = true := by
  decide +kernel
theorem observer40_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer40Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer40Panel2Data) s observer40Panel2Data.anchor ≤
        (observer40Panel2Endpoints.energyUpper : ℝ) ∧
      (observer40Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer40Panel2Data) s observer40Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer40Panel2Data) s observer40Panel2Data.anchor ≤
        (observer40Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer40Panel2Data) s observer40Panel2Data.anchor ≤
        (observer40Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer40Panel2Data) s observer40Panel2Data.anchor ≤
        (observer40Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer40Panel2Data observer40Panel2Endpoints
    observer40_panel2_kernel_check s hs
def observer40Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer40Panel2Endpoints
theorem observer40_panel2_recurrence_field_kernel_check :
    observer40Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer40_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer40Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer40Panel2Endpoints
    observer40_panel2_recurrence_field_kernel_check

def observer40Panel3Data : MainPanelData :=
  {
    observer := 40, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((5215638481935422455384 : ℚ) / 8622181715836845526771520595372359026725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer40Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510206795495926561124138415, ellLower := 351497802425166604721181155584,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806508819094240803856207572, offsetUpper := 6822009984235961151051420569,
    supportELower := 42885023023939273796450605475, supportEUpper := 44261752860961370489088921280,
    supportLambdaLower := 351497802425166604721181155584,
    supportLambdaUpper := 360396376869719260424846435447,
    supportJLower := 46400001048190939843662417030, supportJUpper := 47865716629658563093337385635,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer40Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer40Panel3Data observer40Panel3Endpoints
theorem observer40_panel3_kernel_check : observer40Panel3Check = true := by
  decide +kernel
theorem observer40_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer40Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer40Panel3Data) s observer40Panel3Data.anchor ≤
        (observer40Panel3Endpoints.energyUpper : ℝ) ∧
      (observer40Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer40Panel3Data) s observer40Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer40Panel3Data) s observer40Panel3Data.anchor ≤
        (observer40Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer40Panel3Data) s observer40Panel3Data.anchor ≤
        (observer40Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer40Panel3Data) s observer40Panel3Data.anchor ≤
        (observer40Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer40Panel3Data observer40Panel3Endpoints
    observer40_panel3_kernel_check s hs
def observer40Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer40Panel3Endpoints
theorem observer40_panel3_recurrence_field_kernel_check :
    observer40Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer40_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer40Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer40Panel3Endpoints
    observer40_panel3_recurrence_field_kernel_check

def observer40Panel4Data : MainPanelData :=
  {
    observer := 40, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((5215638481935422455384 : ℚ) / 8622181715836845526771520595372359026725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer40Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196113461607577176437887387, ellLower := 351326768355799634451374053277,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020438445896152317526693970, offsetUpper := 7036426815060066868416190332,
    supportELower := 44261689349415915489590161591, supportEUpper := 45631668576085458047449550439,
    supportLambdaLower := 351326768355799634451374053277,
    supportLambdaUpper := 359926343603679248572832833205,
    supportJLower := 47774957032973911834103902123, supportJUpper := 49230932012122250533177878772,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer40Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer40Panel4Data observer40Panel4Endpoints
theorem observer40_panel4_kernel_check : observer40Panel4Check = true := by
  decide +kernel
theorem observer40_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer40Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer40Panel4Data) s observer40Panel4Data.anchor ≤
        (observer40Panel4Endpoints.energyUpper : ℝ) ∧
      (observer40Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer40Panel4Data) s observer40Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer40Panel4Data) s observer40Panel4Data.anchor ≤
        (observer40Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer40Panel4Data) s observer40Panel4Data.anchor ≤
        (observer40Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer40Panel4Data) s observer40Panel4Data.anchor ≤
        (observer40Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer40Panel4Data observer40Panel4Endpoints
    observer40_panel4_kernel_check s hs
def observer40Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer40Panel4Endpoints
theorem observer40_panel4_recurrence_field_kernel_check :
    observer40Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer40_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer40Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer40Panel4Endpoints
    observer40_panel4_recurrence_field_kernel_check

def observer40Panel5Data : MainPanelData :=
  {
    observer := 40, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((5215638481935422455384 : ℚ) / 8622181715836845526771520595372359026725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer40Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877490365478016591568151927, ellLower := 351161217418641497361180605561,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217422827104638763543429982, offsetUpper := 7233897344727859038453272336,
    supportELower := 45631600292247145761155938853, supportEUpper := 46996640409017607226042222727,
    supportLambdaLower := 351161217418641497361180605561,
    supportLambdaUpper := 359481391157855220173017923595,
    supportJLower := 49143212466433560734767744908, supportJUpper := 50591454320596159427772401963,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer40Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer40Panel5Data observer40Panel5Endpoints
theorem observer40_panel5_kernel_check : observer40Panel5Check = true := by
  decide +kernel
theorem observer40_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer40Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer40Panel5Data) s observer40Panel5Data.anchor ≤
        (observer40Panel5Endpoints.energyUpper : ℝ) ∧
      (observer40Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer40Panel5Data) s observer40Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer40Panel5Data) s observer40Panel5Data.anchor ≤
        (observer40Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer40Panel5Data) s observer40Panel5Data.anchor ≤
        (observer40Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer40Panel5Data) s observer40Panel5Data.anchor ≤
        (observer40Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer40Panel5Data observer40Panel5Endpoints
    observer40_panel5_kernel_check s hs
def observer40Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer40Panel5Endpoints
theorem observer40_panel5_recurrence_field_kernel_check :
    observer40Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer40_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer40Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer40Panel5Endpoints
    observer40_panel5_recurrence_field_kernel_check

def observer40Panel6Data : MainPanelData :=
  {
    observer := 40, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((5215638481935422455384 : ℚ) / 8622181715836845526771520595372359026725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer40Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554911915447211685699937688, ellLower := 351001111002932153232195126069,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429987771873286429000605870, offsetUpper := 7446947491072271215989177753,
    supportELower := 46996567362964669477250426198, supportEUpper := 48357743379112612672183042088,
    supportLambdaLower := 351001111002932153232195126069,
    supportLambdaUpper := 359059538538956634163551466293,
    supportJLower := 50506578472993991009572377458, supportJUpper := 51948338764502179013818556751,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer40Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer40Panel6Data observer40Panel6Endpoints
theorem observer40_panel6_kernel_check : observer40Panel6Check = true := by
  decide +kernel
theorem observer40_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer40Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer40Panel6Data) s observer40Panel6Data.anchor ≤
        (observer40Panel6Endpoints.energyUpper : ℝ) ∧
      (observer40Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer40Panel6Data) s observer40Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer40Panel6Data) s observer40Panel6Data.anchor ≤
        (observer40Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer40Panel6Data) s observer40Panel6Data.anchor ≤
        (observer40Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer40Panel6Data) s observer40Panel6Data.anchor ≤
        (observer40Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer40Panel6Data observer40Panel6Endpoints
    observer40_panel6_kernel_check s hs
def observer40Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer40Panel6Endpoints
theorem observer40_panel6_recurrence_field_kernel_check :
    observer40Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer40_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer40Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer40Panel6Endpoints
    observer40_panel6_recurrence_field_kernel_check

def observer40Panel7Data : MainPanelData :=
  {
    observer := 40, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((5215638481935422455384 : ℚ) / 8622181715836845526771520595372359026725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer40Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229302803161117473482936348, ellLower := 350846298842662619621693282812,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642253128063906718543446138, offsetUpper := 7659697364996594015615400510,
    supportELower := 48357665579101744827727288591, supportEUpper := 49715679720246808738577453400,
    supportLambdaLower := 350846298842662619621693282812,
    supportLambdaUpper := 358658978125452476012343289921,
    supportJLower := 51866128567528371023944221419, supportJUpper := 53302269501501333498700886300,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer40Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer40Panel7Data observer40Panel7Endpoints
theorem observer40_panel7_kernel_check : observer40Panel7Check = true := by
  decide +kernel
theorem observer40_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer40Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer40Panel7Data) s observer40Panel7Data.anchor ≤
        (observer40Panel7Endpoints.energyUpper : ℝ) ∧
      (observer40Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer40Panel7Data) s observer40Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer40Panel7Data) s observer40Panel7Data.anchor ≤
        (observer40Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer40Panel7Data) s observer40Panel7Data.anchor ≤
        (observer40Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer40Panel7Data) s observer40Panel7Data.anchor ≤
        (observer40Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer40Panel7Data observer40Panel7Endpoints
    observer40_panel7_kernel_check s hs
def observer40Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer40Panel7Endpoints
theorem observer40_panel7_recurrence_field_kernel_check :
    observer40Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer40_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer40Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer40Panel7Endpoints
    observer40_panel7_recurrence_field_kernel_check

def observer40InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 40, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer40Panel0Endpoints, observer40Panel1Endpoints, observer40Panel2Endpoints, observer40Panel3Endpoints, observer40Panel4Endpoints, observer40Panel5Endpoints, observer40Panel6Endpoints, observer40Panel7Endpoints]
  }
def observer40FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer40InsertionEndpoints.frameLower
    observer40InsertionEndpoints.frameUpper
theorem observer40_frame_recurrence_field_kernel_check :
    observer40FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer40_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer40InsertionEndpoints.frameLower
      observer40InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer40InsertionEndpoints.frameLower
    observer40InsertionEndpoints.frameUpper
    observer40_frame_recurrence_field_kernel_check
def observer40RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer40Panel0Endpoints ∧
  panelRecurrenceFields observer40Panel1Endpoints ∧
  panelRecurrenceFields observer40Panel2Endpoints ∧
  panelRecurrenceFields observer40Panel3Endpoints ∧
  panelRecurrenceFields observer40Panel4Endpoints ∧
  panelRecurrenceFields observer40Panel5Endpoints ∧
  panelRecurrenceFields observer40Panel6Endpoints ∧
  panelRecurrenceFields observer40Panel7Endpoints ∧ insertionFrameRecurrenceFields observer40InsertionEndpoints.frameLower
      observer40InsertionEndpoints.frameUpper
theorem observer40_all_recurrence_fields :
    observer40RecurrenceFieldBounds := by
  exact ⟨observer40_panel0_recurrence_fields_sound,
    observer40_panel1_recurrence_fields_sound,
    observer40_panel2_recurrence_fields_sound,
    observer40_panel3_recurrence_fields_sound,
    observer40_panel4_recurrence_fields_sound,
    observer40_panel5_recurrence_fields_sound,
    observer40_panel6_recurrence_fields_sound,
    observer40_panel7_recurrence_fields_sound,
    observer40_frame_recurrence_fields_sound⟩
def observer40PanelFormulaBounds : Prop :=
  panelFormulaBounds observer40Panel0Data observer40Panel0Endpoints ∧
  panelFormulaBounds observer40Panel1Data observer40Panel1Endpoints ∧
  panelFormulaBounds observer40Panel2Data observer40Panel2Endpoints ∧
  panelFormulaBounds observer40Panel3Data observer40Panel3Endpoints ∧
  panelFormulaBounds observer40Panel4Data observer40Panel4Endpoints ∧
  panelFormulaBounds observer40Panel5Data observer40Panel5Endpoints ∧
  panelFormulaBounds observer40Panel6Data observer40Panel6Endpoints ∧
  panelFormulaBounds observer40Panel7Data observer40Panel7Endpoints
theorem observer40_all_panel_formula_bounds : observer40PanelFormulaBounds := by
  exact ⟨observer40_panel0_formula_sound,
    observer40_panel1_formula_sound,
    observer40_panel2_formula_sound,
    observer40_panel3_formula_sound,
    observer40_panel4_formula_sound,
    observer40_panel5_formula_sound,
    observer40_panel6_formula_sound,
    observer40_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
