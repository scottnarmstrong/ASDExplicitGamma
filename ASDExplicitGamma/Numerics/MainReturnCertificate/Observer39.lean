module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer39Panel0Data : MainPanelData :=
  {
    observer := 39, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1738546160645140818298 : ℚ) / 958020190648538391863502288374706558525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer39Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393297965195625503686461315, ellLower := 352020920010920339326898984853,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172437289790895887021978391, offsetUpper := 6186462463353692322868165347,
    supportELower := 38565848890801539480153642015, supportEUpper := 40091569218809924643478524925,
    supportLambdaLower := 352020920010920339326898984853,
    supportLambdaUpper := 361977512332966985571756670754,
    supportJLower := 42086058090910742873422631863, supportJUpper := 43711344342139594499196091633,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer39Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer39Panel0Data observer39Panel0Endpoints
theorem observer39_panel0_kernel_check : observer39Panel0Check = true := by
  decide +kernel
theorem observer39_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer39Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer39Panel0Data) s observer39Panel0Data.anchor ≤
        (observer39Panel0Endpoints.energyUpper : ℝ) ∧
      (observer39Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer39Panel0Data) s observer39Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer39Panel0Data) s observer39Panel0Data.anchor ≤
        (observer39Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer39Panel0Data) s observer39Panel0Data.anchor ≤
        (observer39Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer39Panel0Data) s observer39Panel0Data.anchor ≤
        (observer39Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer39Panel0Data observer39Panel0Endpoints
    observer39_panel0_kernel_check s hs
def observer39Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer39Panel0Endpoints
theorem observer39_panel0_recurrence_field_kernel_check :
    observer39Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer39_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer39Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer39Panel0Endpoints
    observer39_panel0_recurrence_field_kernel_check

def observer39Panel1Data : MainPanelData :=
  {
    observer := 39, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1738546160645140818298 : ℚ) / 958020190648538391863502288374706558525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer39Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115183467423465199116002999, ellLower := 351854271278232039997727369764,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376117219422775159504330705, offsetUpper := 6390638209347003555459062171,
    supportELower := 40091520137623271697574360594, supportEUpper := 41498105320148281922420260860,
    supportLambdaLower := 351854271278232039997727369764,
    supportLambdaUpper := 361420185099697018700371941032,
    supportJLower := 43610062850405592097551634291, supportJUpper := 45112307171145252109423980271,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer39Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer39Panel1Data observer39Panel1Endpoints
theorem observer39_panel1_kernel_check : observer39Panel1Check = true := by
  decide +kernel
theorem observer39_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer39Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer39Panel1Data) s observer39Panel1Data.anchor ≤
        (observer39Panel1Endpoints.energyUpper : ℝ) ∧
      (observer39Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer39Panel1Data) s observer39Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer39Panel1Data) s observer39Panel1Data.anchor ≤
        (observer39Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer39Panel1Data) s observer39Panel1Data.anchor ≤
        (observer39Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer39Panel1Data) s observer39Panel1Data.anchor ≤
        (observer39Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer39Panel1Data observer39Panel1Endpoints
    observer39_panel1_kernel_check s hs
def observer39Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer39Panel1Endpoints
theorem observer39_panel1_recurrence_field_kernel_check :
    observer39Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer39_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer39Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer39Panel1Endpoints
    observer39_panel1_recurrence_field_kernel_check

def observer39Panel2Data : MainPanelData :=
  {
    observer := 39, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1738546160645140818298 : ℚ) / 958020190648538391863502288374706558525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer39Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817739806303782075785778210, ellLower := 351674062973904204518085555288,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591870546210607678523834095, offsetUpper := 6606882893457261288005866764,
    supportELower := 41498051398716417784044058239, supportEUpper := 42885081850748014092764168579,
    supportLambdaLower := 351674062973904204518085555288,
    supportLambdaUpper := 360893615957306128492730552329,
    supportJLower := 45014792028455459829224913791, supportJUpper := 46494018010321075377691474103,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer39Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer39Panel2Data observer39Panel2Endpoints
theorem observer39_panel2_kernel_check : observer39Panel2Check = true := by
  decide +kernel
theorem observer39_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer39Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer39Panel2Data) s observer39Panel2Data.anchor ≤
        (observer39Panel2Endpoints.energyUpper : ℝ) ∧
      (observer39Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer39Panel2Data) s observer39Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer39Panel2Data) s observer39Panel2Data.anchor ≤
        (observer39Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer39Panel2Data) s observer39Panel2Data.anchor ≤
        (observer39Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer39Panel2Data) s observer39Panel2Data.anchor ≤
        (observer39Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer39Panel2Data observer39Panel2Endpoints
    observer39_panel2_kernel_check s hs
def observer39Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer39Panel2Endpoints
theorem observer39_panel2_recurrence_field_kernel_check :
    observer39Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer39_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer39Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer39Panel2Endpoints
    observer39_panel2_recurrence_field_kernel_check

def observer39Panel3Data : MainPanelData :=
  {
    observer := 39, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1738546160645140818298 : ℚ) / 958020190648538391863502288374706558525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer39Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510206899911157974685742361, ellLower := 351497802687606726907471361125,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806508827050255402963462670, offsetUpper := 6822009992210094803471987899,
    supportELower := 42885023124641246242816362143, supportEUpper := 44261752962717526839981711677,
    supportLambdaLower := 351497802687606726907471361125,
    supportLambdaUpper := 360396377135626746117227614373,
    supportJLower := 46400001151517313511891075754, supportJUpper := 47865716734073794301153987821,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer39Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer39Panel3Data observer39Panel3Endpoints
theorem observer39_panel3_kernel_check : observer39Panel3Check = true := by
  decide +kernel
theorem observer39_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer39Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer39Panel3Data) s observer39Panel3Data.anchor ≤
        (observer39Panel3Endpoints.energyUpper : ℝ) ∧
      (observer39Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer39Panel3Data) s observer39Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer39Panel3Data) s observer39Panel3Data.anchor ≤
        (observer39Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer39Panel3Data) s observer39Panel3Data.anchor ≤
        (observer39Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer39Panel3Data) s observer39Panel3Data.anchor ≤
        (observer39Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer39Panel3Data observer39Panel3Endpoints
    observer39_panel3_kernel_check s hs
def observer39Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer39Panel3Endpoints
theorem observer39_panel3_recurrence_field_kernel_check :
    observer39Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer39_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer39Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer39Panel3Endpoints
    observer39_panel3_recurrence_field_kernel_check

def observer39Panel4Data : MainPanelData :=
  {
    observer := 39, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1738546160645140818298 : ℚ) / 958020190648538391863502288374706558525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer39Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196113567045965591482200300, ellLower := 351326768615970847798498854518,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020438453869394472786044573, offsetUpper := 7036426823051467311080808388,
    supportELower := 44261689451171961369071746966, supportEUpper := 45631668678888538815163621936,
    supportLambdaLower := 351326768615970847798498854518,
    supportLambdaUpper := 359926343867209992731356798815,
    supportJLower := 47774957137331669847056735511, supportJUpper := 49230932117560638742477189925,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer39Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer39Panel4Data observer39Panel4Endpoints
theorem observer39_panel4_kernel_check : observer39Panel4Check = true := by
  decide +kernel
theorem observer39_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer39Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer39Panel4Data) s observer39Panel4Data.anchor ≤
        (observer39Panel4Endpoints.energyUpper : ℝ) ∧
      (observer39Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer39Panel4Data) s observer39Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer39Panel4Data) s observer39Panel4Data.anchor ≤
        (observer39Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer39Panel4Data) s observer39Panel4Data.anchor ≤
        (observer39Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer39Panel4Data) s observer39Panel4Data.anchor ≤
        (observer39Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer39Panel4Data observer39Panel4Endpoints
    observer39_panel4_kernel_check s hs
def observer39Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer39Panel4Endpoints
theorem observer39_panel4_recurrence_field_kernel_check :
    observer39Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer39_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer39Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer39Panel4Endpoints
    observer39_panel4_recurrence_field_kernel_check

def observer39Panel5Data : MainPanelData :=
  {
    observer := 39, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1738546160645140818298 : ℚ) / 958020190648538391863502288374706558525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer39Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877490471933445621067553991, ellLower := 351161217676619028777159829137,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217422835077597432494800310, offsetUpper := 7233897352719016814100673468,
    supportELower := 45631600395050112887599018911, supportEUpper := 46996640512860680754877029323,
    supportLambdaLower := 351161217676619028777159829137,
    supportLambdaUpper := 359481391419090749664977294375,
    supportJLower := 49143212571816303175370617202, supportJUpper := 50591454427051588251526802267,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer39Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer39Panel5Data observer39Panel5Endpoints
theorem observer39_panel5_kernel_check : observer39Panel5Check = true := by
  decide +kernel
theorem observer39_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer39Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer39Panel5Data) s observer39Panel5Data.anchor ≤
        (observer39Panel5Endpoints.energyUpper : ℝ) ∧
      (observer39Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer39Panel5Data) s observer39Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer39Panel5Data) s observer39Panel5Data.anchor ≤
        (observer39Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer39Panel5Data) s observer39Panel5Data.anchor ≤
        (observer39Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer39Panel5Data) s observer39Panel5Data.anchor ≤
        (observer39Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer39Panel5Data observer39Panel5Endpoints
    observer39_panel5_kernel_check s hs
def observer39Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer39Panel5Endpoints
theorem observer39_panel5_recurrence_field_kernel_check :
    observer39Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer39_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer39Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer39Panel5Endpoints
    observer39_panel5_recurrence_field_kernel_check

def observer39Panel6Data : MainPanelData :=
  {
    observer := 39, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1738546160645140818298 : ℚ) / 958020190648538391863502288374706558525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer39Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554912022913722978284366296, ellLower := 351001111258786794172237349230,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429987779864730220191779144, offsetUpper := 7446947499081956308088831624,
    supportELower := 46996567466807626228516873540, supportEUpper := 48357743483988955226319672475,
    supportLambdaLower := 351001111258786794172237349230,
    supportLambdaUpper := 359059538797973487433831112348,
    supportJLower := 50506578579395494170239247032, supportJUpper := 51948338871968690100657983599,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer39Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer39Panel6Data observer39Panel6Endpoints
theorem observer39_panel6_kernel_check : observer39Panel6Check = true := by
  decide +kernel
theorem observer39_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer39Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer39Panel6Data) s observer39Panel6Data.anchor ≤
        (observer39Panel6Endpoints.energyUpper : ℝ) ∧
      (observer39Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer39Panel6Data) s observer39Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer39Panel6Data) s observer39Panel6Data.anchor ≤
        (observer39Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer39Panel6Data) s observer39Panel6Data.anchor ≤
        (observer39Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer39Panel6Data) s observer39Panel6Data.anchor ≤
        (observer39Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer39Panel6Data observer39Panel6Endpoints
    observer39_panel6_kernel_check s hs
def observer39Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer39Panel6Endpoints
theorem observer39_panel6_recurrence_field_kernel_check :
    observer39Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer39_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer39Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer39Panel6Endpoints
    observer39_panel6_recurrence_field_kernel_check

def observer39Panel7Data : MainPanelData :=
  {
    observer := 39, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1738546160645140818298 : ℚ) / 958020190648538391863502288374706558525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer39Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229302911632903710005777847, ellLower := 350846299096461113823349110472,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642253136074341991803799244, offsetUpper := 7659697373025313939815614591,
    supportELower := 48357665683977967500224612470, supportEUpper := 49715679826149892970293643422,
    supportLambdaLower := 350846299096461113823349110472,
    supportLambdaUpper := 358658978382322655918508261679,
    supportJLower := 51866128674942578638458103574, supportJUpper := 53302269609973119529478726039,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer39Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer39Panel7Data observer39Panel7Endpoints
theorem observer39_panel7_kernel_check : observer39Panel7Check = true := by
  decide +kernel
theorem observer39_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer39Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer39Panel7Data) s observer39Panel7Data.anchor ≤
        (observer39Panel7Endpoints.energyUpper : ℝ) ∧
      (observer39Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer39Panel7Data) s observer39Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer39Panel7Data) s observer39Panel7Data.anchor ≤
        (observer39Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer39Panel7Data) s observer39Panel7Data.anchor ≤
        (observer39Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer39Panel7Data) s observer39Panel7Data.anchor ≤
        (observer39Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer39Panel7Data observer39Panel7Endpoints
    observer39_panel7_kernel_check s hs
def observer39Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer39Panel7Endpoints
theorem observer39_panel7_recurrence_field_kernel_check :
    observer39Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer39_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer39Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer39Panel7Endpoints
    observer39_panel7_recurrence_field_kernel_check

def observer39InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 39, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer39Panel0Endpoints, observer39Panel1Endpoints, observer39Panel2Endpoints, observer39Panel3Endpoints, observer39Panel4Endpoints, observer39Panel5Endpoints, observer39Panel6Endpoints, observer39Panel7Endpoints]
  }
def observer39FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer39InsertionEndpoints.frameLower
    observer39InsertionEndpoints.frameUpper
theorem observer39_frame_recurrence_field_kernel_check :
    observer39FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer39_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer39InsertionEndpoints.frameLower
      observer39InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer39InsertionEndpoints.frameLower
    observer39InsertionEndpoints.frameUpper
    observer39_frame_recurrence_field_kernel_check
def observer39RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer39Panel0Endpoints ∧
  panelRecurrenceFields observer39Panel1Endpoints ∧
  panelRecurrenceFields observer39Panel2Endpoints ∧
  panelRecurrenceFields observer39Panel3Endpoints ∧
  panelRecurrenceFields observer39Panel4Endpoints ∧
  panelRecurrenceFields observer39Panel5Endpoints ∧
  panelRecurrenceFields observer39Panel6Endpoints ∧
  panelRecurrenceFields observer39Panel7Endpoints ∧ insertionFrameRecurrenceFields observer39InsertionEndpoints.frameLower
      observer39InsertionEndpoints.frameUpper
theorem observer39_all_recurrence_fields :
    observer39RecurrenceFieldBounds := by
  exact ⟨observer39_panel0_recurrence_fields_sound,
    observer39_panel1_recurrence_fields_sound,
    observer39_panel2_recurrence_fields_sound,
    observer39_panel3_recurrence_fields_sound,
    observer39_panel4_recurrence_fields_sound,
    observer39_panel5_recurrence_fields_sound,
    observer39_panel6_recurrence_fields_sound,
    observer39_panel7_recurrence_fields_sound,
    observer39_frame_recurrence_fields_sound⟩
def observer39PanelFormulaBounds : Prop :=
  panelFormulaBounds observer39Panel0Data observer39Panel0Endpoints ∧
  panelFormulaBounds observer39Panel1Data observer39Panel1Endpoints ∧
  panelFormulaBounds observer39Panel2Data observer39Panel2Endpoints ∧
  panelFormulaBounds observer39Panel3Data observer39Panel3Endpoints ∧
  panelFormulaBounds observer39Panel4Data observer39Panel4Endpoints ∧
  panelFormulaBounds observer39Panel5Data observer39Panel5Endpoints ∧
  panelFormulaBounds observer39Panel6Data observer39Panel6Endpoints ∧
  panelFormulaBounds observer39Panel7Data observer39Panel7Endpoints
theorem observer39_all_panel_formula_bounds : observer39PanelFormulaBounds := by
  exact ⟨observer39_panel0_formula_sound,
    observer39_panel1_formula_sound,
    observer39_panel2_formula_sound,
    observer39_panel3_formula_sound,
    observer39_panel4_formula_sound,
    observer39_panel5_formula_sound,
    observer39_panel6_formula_sound,
    observer39_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
