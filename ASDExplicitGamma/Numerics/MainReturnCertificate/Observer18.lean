module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer18Panel0Data : MainPanelData :=
  {
    observer := 18, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((166203389536 : ℚ) / 8755520392324948725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer18Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49418027315039193971255071173, ellLower := 352087399592923459346287519449,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6174361559156778626996098615, offsetUpper := 6188391105094792663789061664,
    supportELower := 38589634567363317919402942878, supportEUpper := 40115620927938375399110857765,
    supportLambdaLower := 352087399592923459346287519449,
    supportLambdaUpper := 362044953579671040431773948819,
    supportJLower := 42110508563292552512865818072, supportJUpper := 43736070463735085803428597254,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer18Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer18Panel0Data observer18Panel0Endpoints
theorem observer18_panel0_kernel_check : observer18Panel0Check = true := by
  decide +kernel
theorem observer18_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer18Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer18Panel0Data) s observer18Panel0Data.anchor ≤
        (observer18Panel0Endpoints.energyUpper : ℝ) ∧
      (observer18Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer18Panel0Data) s observer18Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer18Panel0Data) s observer18Panel0Data.anchor ≤
        (observer18Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer18Panel0Data) s observer18Panel0Data.anchor ≤
        (observer18Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer18Panel0Data) s observer18Panel0Data.anchor ≤
        (observer18Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer18Panel0Data observer18Panel0Endpoints
    observer18_panel0_kernel_check s hs
def observer18Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer18Panel0Endpoints
theorem observer18_panel0_recurrence_field_kernel_check :
    observer18Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer18_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer18Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer18Panel0Endpoints
    observer18_panel0_recurrence_field_kernel_check

def observer18Panel1Data : MainPanelData :=
  {
    observer := 18, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((166203389536 : ℚ) / 8755520392324948725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer18Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51140170330691582680417324549, ellLower := 351920127734185772398865992037,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6378040309413611060984576254, offsetUpper := 6392565678989188282149151902,
    supportELower := 40115571822146402523271833254, supportEUpper := 41522421104288527071787584308,
    supportLambdaLower := 351920127734185772398865992037,
    supportLambdaUpper := 361486970187676535560161327542,
    supportJLower := 43634773099488260247260493174, supportJUpper := 45137290806165292427389197584,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer18Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer18Panel1Data observer18Panel1Endpoints
theorem observer18_panel1_kernel_check : observer18Panel1Check = true := by
  decide +kernel
theorem observer18_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer18Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer18Panel1Data) s observer18Panel1Data.anchor ≤
        (observer18Panel1Endpoints.energyUpper : ℝ) ∧
      (observer18Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer18Panel1Data) s observer18Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer18Panel1Data) s observer18Panel1Data.anchor ≤
        (observer18Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer18Panel1Data) s observer18Panel1Data.anchor ≤
        (observer18Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer18Panel1Data) s observer18Panel1Data.anchor ≤
        (observer18Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer18Panel1Data observer18Panel1Endpoints
    observer18_panel1_kernel_check s hs
def observer18Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer18Panel1Endpoints
theorem observer18_panel1_recurrence_field_kernel_check :
    observer18Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer18_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer18Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer18Panel1Endpoints
    observer18_panel1_recurrence_field_kernel_check

def observer18Panel2Data : MainPanelData :=
  {
    observer := 18, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((166203389536 : ℚ) / 8755520392324948725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer18Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52842982565500453146114185090, ellLower := 351739319151072231391487958226,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6593797409699278603581382544, offsetUpper := 6608814145191057180681691189,
    supportELower := 41522367157441488370829957832, supportEUpper := 42909659842355009158819372973,
    supportLambdaLower := 351739319151072231391487958226,
    supportLambdaUpper := 360959769891466012586440377265,
    supportJLower := 45039760348952210684744837414, supportJUpper := 46519257541269669284683776746,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer18Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer18Panel2Data observer18Panel2Endpoints
theorem observer18_panel2_kernel_check : observer18Panel2Check = true := by
  decide +kernel
theorem observer18_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer18Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer18Panel2Data) s observer18Panel2Data.anchor ≤
        (observer18Panel2Endpoints.energyUpper : ℝ) ∧
      (observer18Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer18Panel2Data) s observer18Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer18Panel2Data) s observer18Panel2Data.anchor ≤
        (observer18Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer18Panel2Data) s observer18Panel2Data.anchor ≤
        (observer18Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer18Panel2Data) s observer18Panel2Data.anchor ≤
        (observer18Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer18Panel2Data observer18Panel2Endpoints
    observer18_panel2_kernel_check s hs
def observer18Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer18Panel2Endpoints
theorem observer18_panel2_recurrence_field_kernel_check :
    observer18Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer18_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer18Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer18Panel2Endpoints
    observer18_panel2_recurrence_field_kernel_check

def observer18Panel3Data : MainPanelData :=
  {
    observer := 18, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((166203389536 : ℚ) / 8755520392324948725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer18Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54535703982273926795462632950, ellLower := 351562479926412302110892935191,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6808439778452739023556643176, offsetUpper := 6823945341167531495916419030,
    supportELower := 42909601090032539847534731723, supportEUpper := 44286591356173001912414452000,
    supportLambdaLower := 351562479926412302110892935191,
    supportLambdaUpper := 360461923201548404618032217230,
    supportJLower := 46425225889296662868643661074, supportJUpper := 47891210588188485958594774173,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer18Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer18Panel3Data observer18Panel3Endpoints
theorem observer18_panel3_kernel_check : observer18Panel3Check = true := by
  decide +kernel
theorem observer18_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer18Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer18Panel3Data) s observer18Panel3Data.anchor ≤
        (observer18Panel3Endpoints.energyUpper : ℝ) ∧
      (observer18Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer18Panel3Data) s observer18Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer18Panel3Data) s observer18Panel3Data.anchor ≤
        (observer18Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer18Panel3Data) s observer18Panel3Data.anchor ≤
        (observer18Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer18Panel3Data) s observer18Panel3Data.anchor ≤
        (observer18Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer18Panel3Data observer18Panel3Endpoints
    observer18_panel3_kernel_check s hs
def observer18Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer18Panel3Endpoints
theorem observer18_panel3_recurrence_field_kernel_check :
    observer18Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer18_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer18Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer18Panel3Endpoints
    observer18_panel3_recurrence_field_kernel_check

def observer18Panel4Data : MainPanelData :=
  {
    observer := 18, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((166203389536 : ℚ) / 8755520392324948725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer18Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56221863442435779723450099306, ellLower := 351390886897776671018979523165,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7022373714608935400540834188, offsetUpper := 7038366491160059426487530130,
    supportELower := 44286527817620122329561217168, supportEUpper := 45656765726633323375043556317,
    supportLambdaLower := 351390886897776671018979523165,
    supportLambdaUpper := 359991303806905233606542837666,
    supportJLower := 47800436686597889039751012399, supportJUpper := 49256678764702375711108984694,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer18Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer18Panel4Data observer18Panel4Endpoints
theorem observer18_panel4_kernel_check : observer18Panel4Check = true := by
  decide +kernel
theorem observer18_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer18Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer18Panel4Data) s observer18Panel4Data.anchor ≤
        (observer18Panel4Endpoints.energyUpper : ℝ) ∧
      (observer18Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer18Panel4Data) s observer18Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer18Panel4Data) s observer18Panel4Data.anchor ≤
        (observer18Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer18Panel4Data) s observer18Panel4Data.anchor ≤
        (observer18Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer18Panel4Data) s observer18Panel4Data.anchor ≤
        (observer18Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer18Panel4Data observer18Panel4Endpoints
    observer18_panel4_kernel_check s hs
def observer18Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer18Panel4Endpoints
theorem observer18_panel4_recurrence_field_kernel_check :
    observer18Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer18_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer18Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer18Panel4Endpoints
    observer18_panel4_recurrence_field_kernel_check

def observer18Panel5Data : MainPanelData :=
  {
    observer := 18, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((166203389536 : ℚ) / 8755520392324948725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer18Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57903491650857881846280315789, ellLower := 351224795752233778980995292604,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7235837090397396056712395601, offsetUpper := 7252316009129152174341045326,
    supportELower := 45656697415004502995248607196, supportEUpper := 47021994521898720096985013648,
    supportLambdaLower := 351224795752233778980995292604,
    supportLambdaUpper := 359545785582922721641844617990,
    supportJLower := 49168945372526840785058560122, supportJUpper := 50617452377727947313403459828,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer18Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer18Panel5Data observer18Panel5Endpoints
theorem observer18_panel5_kernel_check : observer18Panel5Check = true := by
  decide +kernel
theorem observer18_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer18Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer18Panel5Data) s observer18Panel5Data.anchor ≤
        (observer18Panel5Endpoints.energyUpper : ℝ) ∧
      (observer18Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer18Panel5Data) s observer18Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer18Panel5Data) s observer18Panel5Data.anchor ≤
        (observer18Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer18Panel5Data) s observer18Panel5Data.anchor ≤
        (observer18Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer18Panel5Data) s observer18Panel5Data.anchor ≤
        (observer18Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer18Panel5Data observer18Panel5Endpoints
    observer18_panel5_kernel_check s hs
def observer18Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer18Panel5Endpoints
theorem observer18_panel5_recurrence_field_kernel_check :
    observer18Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer18_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer18Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer18Panel5Endpoints
    observer18_panel5_recurrence_field_kernel_check

def observer18Panel6Data : MainPanelData :=
  {
    observer := 18, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((166203389536 : ℚ) / 8755520392324948725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer18Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59581163054675024875088320244, ellLower := 351064166760800808747685949521,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7431927715289140411589960710, offsetUpper := 7448891862610566981248579117,
    supportELower := 47021921447280369157286969332, supportEUpper := 48383352812714698373349140273,
    supportLambdaLower := 351064166760800808747685949521,
    supportLambdaUpper := 359123386276721646077669303691,
    supportJLower := 50532563114888377244763828827, supportJUpper := 51974586675481914834125833310,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer18Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer18Panel6Data observer18Panel6Endpoints
theorem observer18_panel6_kernel_check : observer18Panel6Check = true := by
  decide +kernel
theorem observer18_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer18Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer18Panel6Data) s observer18Panel6Data.anchor ≤
        (observer18Panel6Endpoints.energyUpper : ℝ) ∧
      (observer18Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer18Panel6Data) s observer18Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer18Panel6Data) s observer18Panel6Data.anchor ≤
        (observer18Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer18Panel6Data) s observer18Panel6Data.anchor ≤
        (observer18Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer18Panel6Data) s observer18Panel6Data.anchor ≤
        (observer18Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer18Panel6Data observer18Panel6Endpoints
    observer18_panel6_kernel_check s hs
def observer18Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer18Panel6Endpoints
theorem observer18_panel6_recurrence_field_kernel_check :
    observer18Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer18_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer18Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer18Panel6Endpoints
    observer18_panel6_recurrence_field_kernel_check

def observer18Panel7Data : MainPanelData :=
  {
    observer := 18, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((166203389536 : ℚ) / 8755520392324948725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer18Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61255802382592301981047904053, ellLower := 350908848637927387539755102544,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7644197809883856541267802259, offsetUpper := 7661646485754885375378686848,
    supportELower := 48383274983371361711508150594, supportEUpper := 49741542881458523597924904315,
    supportLambdaLower := 350908848637927387539755102544,
    supportLambdaUpper := 358722297122591703925984369299,
    supportJLower := 51892363469750635586905701619, supportJUpper := 53328765852684440637184748008,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer18Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer18Panel7Data observer18Panel7Endpoints
theorem observer18_panel7_kernel_check : observer18Panel7Check = true := by
  decide +kernel
theorem observer18_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer18Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer18Panel7Data) s observer18Panel7Data.anchor ≤
        (observer18Panel7Endpoints.energyUpper : ℝ) ∧
      (observer18Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer18Panel7Data) s observer18Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer18Panel7Data) s observer18Panel7Data.anchor ≤
        (observer18Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer18Panel7Data) s observer18Panel7Data.anchor ≤
        (observer18Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer18Panel7Data) s observer18Panel7Data.anchor ≤
        (observer18Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer18Panel7Data observer18Panel7Endpoints
    observer18_panel7_kernel_check s hs
def observer18Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer18Panel7Endpoints
theorem observer18_panel7_recurrence_field_kernel_check :
    observer18Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer18_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer18Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer18Panel7Endpoints
    observer18_panel7_recurrence_field_kernel_check

def observer18InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 18, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer18Panel0Endpoints, observer18Panel1Endpoints, observer18Panel2Endpoints, observer18Panel3Endpoints, observer18Panel4Endpoints, observer18Panel5Endpoints, observer18Panel6Endpoints, observer18Panel7Endpoints]
  }
def observer18FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer18InsertionEndpoints.frameLower
    observer18InsertionEndpoints.frameUpper
theorem observer18_frame_recurrence_field_kernel_check :
    observer18FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer18_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer18InsertionEndpoints.frameLower
      observer18InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer18InsertionEndpoints.frameLower
    observer18InsertionEndpoints.frameUpper
    observer18_frame_recurrence_field_kernel_check
def observer18RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer18Panel0Endpoints ∧
  panelRecurrenceFields observer18Panel1Endpoints ∧
  panelRecurrenceFields observer18Panel2Endpoints ∧
  panelRecurrenceFields observer18Panel3Endpoints ∧
  panelRecurrenceFields observer18Panel4Endpoints ∧
  panelRecurrenceFields observer18Panel5Endpoints ∧
  panelRecurrenceFields observer18Panel6Endpoints ∧
  panelRecurrenceFields observer18Panel7Endpoints ∧ insertionFrameRecurrenceFields observer18InsertionEndpoints.frameLower
      observer18InsertionEndpoints.frameUpper
theorem observer18_all_recurrence_fields :
    observer18RecurrenceFieldBounds := by
  exact ⟨observer18_panel0_recurrence_fields_sound,
    observer18_panel1_recurrence_fields_sound,
    observer18_panel2_recurrence_fields_sound,
    observer18_panel3_recurrence_fields_sound,
    observer18_panel4_recurrence_fields_sound,
    observer18_panel5_recurrence_fields_sound,
    observer18_panel6_recurrence_fields_sound,
    observer18_panel7_recurrence_fields_sound,
    observer18_frame_recurrence_fields_sound⟩
def observer18PanelFormulaBounds : Prop :=
  panelFormulaBounds observer18Panel0Data observer18Panel0Endpoints ∧
  panelFormulaBounds observer18Panel1Data observer18Panel1Endpoints ∧
  panelFormulaBounds observer18Panel2Data observer18Panel2Endpoints ∧
  panelFormulaBounds observer18Panel3Data observer18Panel3Endpoints ∧
  panelFormulaBounds observer18Panel4Data observer18Panel4Endpoints ∧
  panelFormulaBounds observer18Panel5Data observer18Panel5Endpoints ∧
  panelFormulaBounds observer18Panel6Data observer18Panel6Endpoints ∧
  panelFormulaBounds observer18Panel7Data observer18Panel7Endpoints
theorem observer18_all_panel_formula_bounds : observer18PanelFormulaBounds := by
  exact ⟨observer18_panel0_formula_sound,
    observer18_panel1_formula_sound,
    observer18_panel2_formula_sound,
    observer18_panel3_formula_sound,
    observer18_panel4_formula_sound,
    observer18_panel5_formula_sound,
    observer18_panel6_formula_sound,
    observer18_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
