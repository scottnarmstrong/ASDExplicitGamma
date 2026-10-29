module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer32Panel0Data : MainPanelData :=
  {
    observer := 32, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((794945661017439544 : ℚ) / 200298222850396561605041196874725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer32Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393308935267059893109513827, ellLower := 352020949221680385866746576704,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172438148476677197617673885, offsetUpper := 6186463323990601940381752444,
    supportELower := 38565859447972723798334125968, supportEUpper := 40091579892619519169007357025,
    supportLambdaLower := 352020949221680385866746576704,
    supportLambdaUpper := 361977541959083508175101847930,
    supportJLower := 42086068940189527657001591735, supportJUpper := 43711355312210354250758375505,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer32Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer32Panel0Data observer32Panel0Endpoints
theorem observer32_panel0_kernel_check : observer32Panel0Check = true := by
  decide +kernel
theorem observer32_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer32Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer32Panel0Data) s observer32Panel0Data.anchor ≤
        (observer32Panel0Endpoints.energyUpper : ℝ) ∧
      (observer32Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer32Panel0Data) s observer32Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer32Panel0Data) s observer32Panel0Data.anchor ≤
        (observer32Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer32Panel0Data) s observer32Panel0Data.anchor ≤
        (observer32Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer32Panel0Data) s observer32Panel0Data.anchor ≤
        (observer32Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer32Panel0Data observer32Panel0Endpoints
    observer32_panel0_kernel_check s hs
def observer32Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer32Panel0Endpoints
theorem observer32_panel0_recurrence_field_kernel_check :
    observer32Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer32_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer32Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer32Panel0Endpoints
    observer32_panel0_recurrence_field_kernel_check

def observer32Panel1Data : MainPanelData :=
  {
    observer := 32, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((794945661017439544 : ℚ) / 200298222850396561605041196874725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer32Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115194550389854946530387909, ellLower := 351854300215461201757160094114,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376118077528754799850242600, offsetUpper := 6390639069407236522001766304,
    supportELower := 40091530811421949471148090836, supportEUpper := 41498116109729893245895439616,
    supportLambdaLower := 351854300215461201757160094114,
    supportLambdaUpper := 361420214438107397308215692430,
    supportJLower := 43610073813576561488719691777, supportJUpper := 45112318254110967218977596541,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer32Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer32Panel1Data observer32Panel1Endpoints
theorem observer32_panel1_kernel_check : observer32Panel1Check = true := by
  decide +kernel
theorem observer32_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer32Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer32Panel1Data) s observer32Panel1Data.anchor ≤
        (observer32Panel1Endpoints.energyUpper : ℝ) ∧
      (observer32Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer32Panel1Data) s observer32Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer32Panel1Data) s observer32Panel1Data.anchor ≤
        (observer32Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer32Panel1Data) s observer32Panel1Data.anchor ≤
        (observer32Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer32Panel1Data) s observer32Panel1Data.anchor ≤
        (observer32Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer32Panel1Data observer32Panel1Endpoints
    observer32_panel1_kernel_check s hs
def observer32Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer32Panel1Endpoints
theorem observer32_panel1_recurrence_field_kernel_check :
    observer32Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer32_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer32Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer32Panel1Endpoints
    observer32_panel1_recurrence_field_kernel_check

def observer32Panel2Data : MainPanelData :=
  {
    observer := 32, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((794945661017439544 : ℚ) / 200298222850396561605041196874725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer32Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817751001446406773886384449, ellLower := 351674091647505169954160521897,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591871405944780816354980873, offsetUpper := 6606883755149395805157367698,
    supportELower := 41498062188286757005446615924, supportEUpper := 42885092755274711325352642768,
    supportLambdaLower := 351674091647505169954160521897,
    supportLambdaUpper := 360893645018831411257866893388,
    supportJLower := 45014803104761808704988221142, supportJUpper := 46494029205463025437931311702,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer32Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer32Panel2Data observer32Panel2Endpoints
theorem observer32_panel2_kernel_check : observer32Panel2Check = true := by
  decide +kernel
theorem observer32_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer32Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer32Panel2Data) s observer32Panel2Data.anchor ≤
        (observer32Panel2Endpoints.energyUpper : ℝ) ∧
      (observer32Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer32Panel2Data) s observer32Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer32Panel2Data) s observer32Panel2Data.anchor ≤
        (observer32Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer32Panel2Data) s observer32Panel2Data.anchor ≤
        (observer32Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer32Panel2Data) s observer32Panel2Data.anchor ≤
        (observer32Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer32Panel2Data observer32Panel2Endpoints
    observer32_panel2_kernel_check s hs
def observer32Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer32Panel2Endpoints
theorem observer32_panel2_recurrence_field_kernel_check :
    observer32Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer32_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer32Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer32Panel2Endpoints
    observer32_panel2_recurrence_field_kernel_check

def observer32Panel3Data : MainPanelData :=
  {
    observer := 32, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((794945661017439544 : ℚ) / 200298222850396561605041196874725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer32Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510218206531002534969108860, ellLower := 351497831106836790714328012536,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806509688551832020560812451, offsetUpper := 6822010855673657890775977925,
    supportELower := 42885034029156320162626097646, supportEUpper := 44261763981389436606665227352,
    supportLambdaLower := 351497831106836790714328012536,
    supportLambdaUpper := 360396405930352761691135832750,
    supportJLower := 46400012340224688069769377771, supportJUpper := 47865728040692964223576585680,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer32Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer32Panel3Data observer32Panel3Endpoints
theorem observer32_panel3_kernel_check : observer32Panel3Check = true := by
  decide +kernel
theorem observer32_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer32Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer32Panel3Data) s observer32Panel3Data.anchor ≤
        (observer32Panel3Endpoints.energyUpper : ℝ) ∧
      (observer32Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer32Panel3Data) s observer32Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer32Panel3Data) s observer32Panel3Data.anchor ≤
        (observer32Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer32Panel3Data) s observer32Panel3Data.anchor ≤
        (observer32Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer32Panel3Data) s observer32Panel3Data.anchor ≤
        (observer32Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer32Panel3Data observer32Panel3Endpoints
    observer32_panel3_kernel_check s hs
def observer32Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer32Panel3Endpoints
theorem observer32_panel3_recurrence_field_kernel_check :
    observer32Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer32_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer32Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer32Panel3Endpoints
    observer32_panel3_recurrence_field_kernel_check

def observer32Panel4Data : MainPanelData :=
  {
    observer := 32, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((794945661017439544 : ℚ) / 200298222850396561605041196874725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer32Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196124984462799701489547610, ellLower := 351326796789504620090700696418,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020439317236604748358828237, offsetUpper := 7036427688384912856471252395,
    supportELower := 44261700469831900570371423965, supportEUpper := 45631679810931179918452716701,
    supportLambdaLower := 351326796789504620090700696418,
    supportLambdaUpper := 359926372404561829617105189396,
    supportJLower := 47774968437726946771278430929, supportJUpper := 49230943534976798214623768595,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer32Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer32Panel4Data observer32Panel4Endpoints
theorem observer32_panel4_kernel_check : observer32Panel4Check = true := by
  decide +kernel
theorem observer32_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer32Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer32Panel4Data) s observer32Panel4Data.anchor ≤
        (observer32Panel4Endpoints.energyUpper : ℝ) ∧
      (observer32Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer32Panel4Data) s observer32Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer32Panel4Data) s observer32Panel4Data.anchor ≤
        (observer32Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer32Panel4Data) s observer32Panel4Data.anchor ≤
        (observer32Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer32Panel4Data) s observer32Panel4Data.anchor ≤
        (observer32Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer32Panel4Data observer32Panel4Endpoints
    observer32_panel4_kernel_check s hs
def observer32Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer32Panel4Endpoints
theorem observer32_panel4_recurrence_field_kernel_check :
    observer32Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer32_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer32Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer32Panel4Endpoints
    observer32_panel4_recurrence_field_kernel_check

def observer32Panel5Data : MainPanelData :=
  {
    observer := 32, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((794945661017439544 : ℚ) / 200298222850396561605041196874725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer32Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877501999484960944032088671, ellLower := 351161245612603017188949550423,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217423698414292364230623224, offsetUpper := 7233898218026367468265798771,
    supportELower := 45631611527080439963326157398, supportEUpper := 46996651757523456980171323978,
    supportLambdaLower := 351161245612603017188949550423,
    supportLambdaUpper := 359481419707897195645924432887,
    supportJLower := 49143223983206470135215652902, supportJUpper := 50591465954602428936630568307,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer32Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer32Panel5Data observer32Panel5Endpoints
theorem observer32_panel5_kernel_check : observer32Panel5Check = true := by
  decide +kernel
theorem observer32_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer32Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer32Panel5Data) s observer32Panel5Data.anchor ≤
        (observer32Panel5Endpoints.energyUpper : ℝ) ∧
      (observer32Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer32Panel5Data) s observer32Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer32Panel5Data) s observer32Panel5Data.anchor ≤
        (observer32Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer32Panel5Data) s observer32Panel5Data.anchor ≤
        (observer32Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer32Panel5Data) s observer32Panel5Data.anchor ≤
        (observer32Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer32Panel5Data observer32Panel5Endpoints
    observer32_panel5_kernel_check s hs
def observer32Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer32Panel5Endpoints
theorem observer32_panel5_recurrence_field_kernel_check :
    observer32Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer32_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer32Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer32Panel5Endpoints
    observer32_panel5_recurrence_field_kernel_check

def observer32Panel6Data : MainPanelData :=
  {
    observer := 32, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((794945661017439544 : ℚ) / 200298222850396561605041196874725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer32Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554923659954724392515825628, ellLower := 351001138964887162040493402567,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429988645203233301537134860, offsetUpper := 7446948366395684446988930238,
    supportELower := 46996578711457748598949020987, supportEUpper := 48357754840543785892242989703,
    supportLambdaLower := 351001138964887162040493402567,
    supportLambdaUpper := 359059566846523098478568458733,
    supportJLower := 50506590101106620219353955012, supportJUpper := 51948350509009016877028674291,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer32Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer32Panel6Data observer32Panel6Endpoints
theorem observer32_panel6_kernel_check : observer32Panel6Check = true := by
  decide +kernel
theorem observer32_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer32Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer32Panel6Data) s observer32Panel6Data.anchor ≤
        (observer32Panel6Endpoints.energyUpper : ℝ) ∧
      (observer32Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer32Panel6Data) s observer32Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer32Panel6Data) s observer32Panel6Data.anchor ≤
        (observer32Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer32Panel6Data) s observer32Panel6Data.anchor ≤
        (observer32Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer32Panel6Data) s observer32Panel6Data.anchor ≤
        (observer32Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer32Panel6Data observer32Panel6Endpoints
    observer32_panel6_kernel_check s hs
def observer32Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer32Panel6Endpoints
theorem observer32_panel6_recurrence_field_kernel_check :
    observer32Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer32_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer32Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer32Panel6Endpoints
    observer32_panel6_recurrence_field_kernel_check

def observer32Panel7Data : MainPanelData :=
  {
    observer := 32, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((794945661017439544 : ℚ) / 200298222850396561605041196874725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer32Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229314657534550904029449893, ellLower := 350846326579905671906241567298,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642254003469483789739573128, offsetUpper := 7659698242400375286898590691,
    supportELower := 48357677040519807974150229803, supportEUpper := 49715691293889964101121633814,
    supportLambdaLower := 350846326579905671906241567298,
    supportLambdaUpper := 358659006198412798451999563001,
    supportJLower := 51866140306318864693212645475, supportJUpper := 53302281355874092085641629445,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer32Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer32Panel7Data observer32Panel7Endpoints
theorem observer32_panel7_kernel_check : observer32Panel7Check = true := by
  decide +kernel
theorem observer32_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer32Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer32Panel7Data) s observer32Panel7Data.anchor ≤
        (observer32Panel7Endpoints.energyUpper : ℝ) ∧
      (observer32Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer32Panel7Data) s observer32Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer32Panel7Data) s observer32Panel7Data.anchor ≤
        (observer32Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer32Panel7Data) s observer32Panel7Data.anchor ≤
        (observer32Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer32Panel7Data) s observer32Panel7Data.anchor ≤
        (observer32Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer32Panel7Data observer32Panel7Endpoints
    observer32_panel7_kernel_check s hs
def observer32Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer32Panel7Endpoints
theorem observer32_panel7_recurrence_field_kernel_check :
    observer32Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer32_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer32Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer32Panel7Endpoints
    observer32_panel7_recurrence_field_kernel_check

def observer32InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 32, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer32Panel0Endpoints, observer32Panel1Endpoints, observer32Panel2Endpoints, observer32Panel3Endpoints, observer32Panel4Endpoints, observer32Panel5Endpoints, observer32Panel6Endpoints, observer32Panel7Endpoints]
  }
def observer32FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer32InsertionEndpoints.frameLower
    observer32InsertionEndpoints.frameUpper
theorem observer32_frame_recurrence_field_kernel_check :
    observer32FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer32_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer32InsertionEndpoints.frameLower
      observer32InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer32InsertionEndpoints.frameLower
    observer32InsertionEndpoints.frameUpper
    observer32_frame_recurrence_field_kernel_check
def observer32RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer32Panel0Endpoints ∧
  panelRecurrenceFields observer32Panel1Endpoints ∧
  panelRecurrenceFields observer32Panel2Endpoints ∧
  panelRecurrenceFields observer32Panel3Endpoints ∧
  panelRecurrenceFields observer32Panel4Endpoints ∧
  panelRecurrenceFields observer32Panel5Endpoints ∧
  panelRecurrenceFields observer32Panel6Endpoints ∧
  panelRecurrenceFields observer32Panel7Endpoints ∧ insertionFrameRecurrenceFields observer32InsertionEndpoints.frameLower
      observer32InsertionEndpoints.frameUpper
theorem observer32_all_recurrence_fields :
    observer32RecurrenceFieldBounds := by
  exact ⟨observer32_panel0_recurrence_fields_sound,
    observer32_panel1_recurrence_fields_sound,
    observer32_panel2_recurrence_fields_sound,
    observer32_panel3_recurrence_fields_sound,
    observer32_panel4_recurrence_fields_sound,
    observer32_panel5_recurrence_fields_sound,
    observer32_panel6_recurrence_fields_sound,
    observer32_panel7_recurrence_fields_sound,
    observer32_frame_recurrence_fields_sound⟩
def observer32PanelFormulaBounds : Prop :=
  panelFormulaBounds observer32Panel0Data observer32Panel0Endpoints ∧
  panelFormulaBounds observer32Panel1Data observer32Panel1Endpoints ∧
  panelFormulaBounds observer32Panel2Data observer32Panel2Endpoints ∧
  panelFormulaBounds observer32Panel3Data observer32Panel3Endpoints ∧
  panelFormulaBounds observer32Panel4Data observer32Panel4Endpoints ∧
  panelFormulaBounds observer32Panel5Data observer32Panel5Endpoints ∧
  panelFormulaBounds observer32Panel6Data observer32Panel6Endpoints ∧
  panelFormulaBounds observer32Panel7Data observer32Panel7Endpoints
theorem observer32_all_panel_formula_bounds : observer32PanelFormulaBounds := by
  exact ⟨observer32_panel0_formula_sound,
    observer32_panel1_formula_sound,
    observer32_panel2_formula_sound,
    observer32_panel3_formula_sound,
    observer32_panel4_formula_sound,
    observer32_panel5_formula_sound,
    observer32_panel6_formula_sound,
    observer32_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
