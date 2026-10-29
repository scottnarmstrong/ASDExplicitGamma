module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer29Panel0Data : MainPanelData :=
  {
    observer := 29, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((29442431889534562 : ℚ) / 274757507339364282037093548525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer29Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393355979919629473555956261, ellLower := 352021074511063937587147626817,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172441830552867592512842935, offsetUpper := 6186467014433302227105757067,
    supportELower := 38565904721595070434904182073, supportEUpper := 40091625666540211937326079785,
    supportLambdaLower := 352021074511063937587147626817,
    supportLambdaUpper := 361977669030516328544368502346,
    supportJLower := 42086115466705709810775658341, supportJUpper := 43711402356845375222769764809,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer29Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer29Panel0Data observer29Panel0Endpoints
theorem observer29_panel0_kernel_check : observer29Panel0Check = true := by
  decide +kernel
theorem observer29_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer29Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer29Panel0Data) s observer29Panel0Data.anchor ≤
        (observer29Panel0Endpoints.energyUpper : ℝ) ∧
      (observer29Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer29Panel0Data) s observer29Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer29Panel0Data) s observer29Panel0Data.anchor ≤
        (observer29Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer29Panel0Data) s observer29Panel0Data.anchor ≤
        (observer29Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer29Panel0Data) s observer29Panel0Data.anchor ≤
        (observer29Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer29Panel0Data observer29Panel0Endpoints
    observer29_panel0_kernel_check s hs
def observer29Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer29Panel0Endpoints
theorem observer29_panel0_recurrence_field_kernel_check :
    observer29Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer29_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer29Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer29Panel0Endpoints
    observer29_panel0_recurrence_field_kernel_check

def observer29Panel1Data : MainPanelData :=
  {
    observer := 29, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((29442431889534562 : ℚ) / 274757507339364282037093548525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer29Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115242079284538021490434339, ellLower := 351854424331609867557390287591,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376121757122484597323301355, offsetUpper := 6390642757380884949716096704,
    supportELower := 40091576585295825801321663843, supportEUpper := 41498162380233292966055511314,
    supportLambdaLower := 351854424331609867557390287591,
    supportLambdaUpper := 361420340275480871944707852630,
    supportJLower := 43610120828611924476895566718, supportJUpper := 45112365782988101685502589841,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer29Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer29Panel1Data observer29Panel1Endpoints
theorem observer29_panel1_kernel_check : observer29Panel1Check = true := by
  decide +kernel
theorem observer29_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer29Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer29Panel1Data) s observer29Panel1Data.anchor ≤
        (observer29Panel1Endpoints.energyUpper : ℝ) ∧
      (observer29Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer29Panel1Data) s observer29Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer29Panel1Data) s observer29Panel1Data.anchor ≤
        (observer29Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer29Panel1Data) s observer29Panel1Data.anchor ≤
        (observer29Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer29Panel1Data) s observer29Panel1Data.anchor ≤
        (observer29Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer29Panel1Data observer29Panel1Endpoints
    observer29_panel1_kernel_check s hs
def observer29Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer29Panel1Endpoints
theorem observer29_panel1_recurrence_field_kernel_check :
    observer29Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer29_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer29Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer29Panel1Endpoints
    observer29_panel1_recurrence_field_kernel_check

def observer29Panel2Data : MainPanelData :=
  {
    observer := 29, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((29442431889534562 : ℚ) / 274757507339364282037093548525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer29Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817799011501083388681750867, ellLower := 351674214632902977755571592159,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591875092524176185813784142, offsetUpper := 6606887450124618982166140152,
    supportELower := 41498108458741816087988258391, supportEUpper := 42885139518814446361484963975,
    supportLambdaLower := 351674214632902977755571592159,
    supportLambdaUpper := 360893769668570708280666101422,
    supportJLower := 45014850605070845865543974312, supportJUpper := 46494077215500153444291624990,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer29Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer29Panel2Data observer29Panel2Endpoints
theorem observer29_panel2_kernel_check : observer29Panel2Check = true := by
  decide +kernel
theorem observer29_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer29Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer29Panel2Data) s observer29Panel2Data.anchor ≤
        (observer29Panel2Endpoints.energyUpper : ℝ) ∧
      (observer29Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer29Panel2Data) s observer29Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer29Panel2Data) s observer29Panel2Data.anchor ≤
        (observer29Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer29Panel2Data) s observer29Panel2Data.anchor ≤
        (observer29Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer29Panel2Data) s observer29Panel2Data.anchor ≤
        (observer29Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer29Panel2Data observer29Panel2Endpoints
    observer29_panel2_kernel_check s hs
def observer29Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer29Panel2Endpoints
theorem observer29_panel2_recurrence_field_kernel_check :
    observer29Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer29_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer29Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer29Panel2Endpoints
    observer29_panel2_recurrence_field_kernel_check

def observer29Panel3Data : MainPanelData :=
  {
    observer := 29, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((29442431889534562 : ℚ) / 274757507339364282037093548525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer29Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510266694748068233308568608, ellLower := 351497953001198363867312580768,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806513382713913336303691130, offsetUpper := 6822014558248835847503877776,
    supportELower := 42885080792646208113311230986, supportEUpper := 44261811234535200198127404869,
    supportLambdaLower := 351497953001198363867312580768,
    supportLambdaUpper := 360396529435728111535358742875,
    supportJLower := 46400060322658191751984356793, supportJUpper := 47865776528892481313480992298,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer29Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer29Panel3Data observer29Panel3Endpoints
theorem observer29_panel3_kernel_check : observer29Panel3Check = true := by
  decide +kernel
theorem observer29_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer29Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer29Panel3Data) s observer29Panel3Data.anchor ≤
        (observer29Panel3Endpoints.energyUpper : ℝ) ∧
      (observer29Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer29Panel3Data) s observer29Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer29Panel3Data) s observer29Panel3Data.anchor ≤
        (observer29Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer29Panel3Data) s observer29Panel3Data.anchor ≤
        (observer29Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer29Panel3Data) s observer29Panel3Data.anchor ≤
        (observer29Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer29Panel3Data observer29Panel3Endpoints
    observer29_panel3_kernel_check s hs
def observer29Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer29Panel3Endpoints
theorem observer29_panel3_recurrence_field_kernel_check :
    observer29Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer29_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer29Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer29Panel3Endpoints
    observer29_panel3_recurrence_field_kernel_check

def observer29Panel4Data : MainPanelData :=
  {
    observer := 29, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((29442431889534562 : ℚ) / 274757507339364282037093548525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer29Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196173947925216695812730103, ellLower := 351326917630044308088074806051,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020443019402631766393466339, offsetUpper := 7036431398982264727253237431,
    supportELower := 44261747722926327602503820306, supportEUpper := 45631727550361584823994067963,
    supportLambdaLower := 351326917630044308088074806051,
    supportLambdaUpper := 359926494806008177651782999413,
    supportJLower := 47775016899226770683384568366, supportJUpper := 49230992498421666600511897958,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer29Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer29Panel4Data observer29Panel4Endpoints
theorem observer29_panel4_kernel_check : observer29Panel4Check = true := by
  decide +kernel
theorem observer29_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer29Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer29Panel4Data) s observer29Panel4Data.anchor ≤
        (observer29Panel4Endpoints.energyUpper : ℝ) ∧
      (observer29Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer29Panel4Data) s observer29Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer29Panel4Data) s observer29Panel4Data.anchor ≤
        (observer29Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer29Panel4Data) s observer29Panel4Data.anchor ≤
        (observer29Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer29Panel4Data) s observer29Panel4Data.anchor ≤
        (observer29Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer29Panel4Data observer29Panel4Endpoints
    observer29_panel4_kernel_check s hs
def observer29Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer29Panel4Endpoints
theorem observer29_panel4_recurrence_field_kernel_check :
    observer29Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer29_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer29Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer29Panel4Endpoints
    observer29_panel4_recurrence_field_kernel_check

def observer29Panel5Data : MainPanelData :=
  {
    observer := 29, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((29442431889534562 : ℚ) / 274757507339364282037093548525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer29Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877551435352557013948103481, ellLower := 351161365434269143286459666982,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217427400453487121543371910, offsetUpper := 7233901928515851396228146610,
    supportELower := 45631659266458035090408047532, supportEUpper := 46996699980019568791539932257,
    supportLambdaLower := 351161365434269143286459666982,
    supportLambdaUpper := 359481541043290760657159772944,
    supportJLower := 49143272920800726523272644201, supportJUpper := 50591515390452476398111529987,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer29Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer29Panel5Data observer29Panel5Endpoints
theorem observer29_panel5_kernel_check : observer29Panel5Check = true := by
  decide +kernel
theorem observer29_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer29Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer29Panel5Data) s observer29Panel5Data.anchor ≤
        (observer29Panel5Endpoints.energyUpper : ℝ) ∧
      (observer29Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer29Panel5Data) s observer29Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer29Panel5Data) s observer29Panel5Data.anchor ≤
        (observer29Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer29Panel5Data) s observer29Panel5Data.anchor ≤
        (observer29Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer29Panel5Data) s observer29Panel5Data.anchor ≤
        (observer29Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer29Panel5Data observer29Panel5Endpoints
    observer29_panel5_kernel_check s hs
def observer29Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer29Panel5Endpoints
theorem observer29_panel5_recurrence_field_kernel_check :
    observer29Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer29_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer29Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer29Panel5Endpoints
    observer29_panel5_recurrence_field_kernel_check

def observer29Panel6Data : MainPanelData :=
  {
    observer := 29, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((29442431889534562 : ℚ) / 274757507339364282037093548525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer29Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554973565460723626095698202, ellLower := 351001257800566981628634900274,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429992355830327664634996818, offsetUpper := 7446952085492670754024195689,
    supportELower := 46996626933899593000307477123, supportEUpper := 48357803542983247472196041901,
    supportLambdaLower := 351001257800566981628634900274,
    supportLambdaUpper := 359059687151422002997745183347,
    supportJLower := 50506639511905262816593826125, supportJUpper := 51948400414497467502173493735,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer29Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer29Panel6Data observer29Panel6Endpoints
theorem observer29_panel6_kernel_check : observer29Panel6Check = true := by
  decide +kernel
theorem observer29_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer29Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer29Panel6Data) s observer29Panel6Data.anchor ≤
        (observer29Panel6Endpoints.energyUpper : ℝ) ∧
      (observer29Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer29Panel6Data) s observer29Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer29Panel6Data) s observer29Panel6Data.anchor ≤
        (observer29Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer29Panel6Data) s observer29Panel6Data.anchor ≤
        (observer29Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer29Panel6Data) s observer29Panel6Data.anchor ≤
        (observer29Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer29Panel6Data observer29Panel6Endpoints
    observer29_panel6_kernel_check s hs
def observer29Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer29Panel6Endpoints
theorem observer29_panel6_recurrence_field_kernel_check :
    observer29Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer29_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer29Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer29Panel6Endpoints
    observer29_panel6_recurrence_field_kernel_check

def observer29Panel7Data : MainPanelData :=
  {
    observer := 29, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((29442431889534562 : ℚ) / 274757507339364282037093548525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer29Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229365029982320476172550827, ellLower := 350846444460605580700782722298,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642257722919602337128607467, offsetUpper := 7659701970340525247796954933,
    supportELower := 48357725742903559479434551533, supportEUpper := 49715740473241637653455618026,
    supportLambdaLower := 350846444460605580700782722298,
    supportLambdaUpper := 358659125506267539589405922210,
    supportJLower := 51866190187509615286442378755, supportJUpper := 53302331728304313049349677249,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer29Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer29Panel7Data observer29Panel7Endpoints
theorem observer29_panel7_kernel_check : observer29Panel7Check = true := by
  decide +kernel
theorem observer29_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer29Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer29Panel7Data) s observer29Panel7Data.anchor ≤
        (observer29Panel7Endpoints.energyUpper : ℝ) ∧
      (observer29Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer29Panel7Data) s observer29Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer29Panel7Data) s observer29Panel7Data.anchor ≤
        (observer29Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer29Panel7Data) s observer29Panel7Data.anchor ≤
        (observer29Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer29Panel7Data) s observer29Panel7Data.anchor ≤
        (observer29Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer29Panel7Data observer29Panel7Endpoints
    observer29_panel7_kernel_check s hs
def observer29Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer29Panel7Endpoints
theorem observer29_panel7_recurrence_field_kernel_check :
    observer29Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer29_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer29Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer29Panel7Endpoints
    observer29_panel7_recurrence_field_kernel_check

def observer29InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 29, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer29Panel0Endpoints, observer29Panel1Endpoints, observer29Panel2Endpoints, observer29Panel3Endpoints, observer29Panel4Endpoints, observer29Panel5Endpoints, observer29Panel6Endpoints, observer29Panel7Endpoints]
  }
def observer29FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer29InsertionEndpoints.frameLower
    observer29InsertionEndpoints.frameUpper
theorem observer29_frame_recurrence_field_kernel_check :
    observer29FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer29_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer29InsertionEndpoints.frameLower
      observer29InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer29InsertionEndpoints.frameLower
    observer29InsertionEndpoints.frameUpper
    observer29_frame_recurrence_field_kernel_check
def observer29RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer29Panel0Endpoints ∧
  panelRecurrenceFields observer29Panel1Endpoints ∧
  panelRecurrenceFields observer29Panel2Endpoints ∧
  panelRecurrenceFields observer29Panel3Endpoints ∧
  panelRecurrenceFields observer29Panel4Endpoints ∧
  panelRecurrenceFields observer29Panel5Endpoints ∧
  panelRecurrenceFields observer29Panel6Endpoints ∧
  panelRecurrenceFields observer29Panel7Endpoints ∧ insertionFrameRecurrenceFields observer29InsertionEndpoints.frameLower
      observer29InsertionEndpoints.frameUpper
theorem observer29_all_recurrence_fields :
    observer29RecurrenceFieldBounds := by
  exact ⟨observer29_panel0_recurrence_fields_sound,
    observer29_panel1_recurrence_fields_sound,
    observer29_panel2_recurrence_fields_sound,
    observer29_panel3_recurrence_fields_sound,
    observer29_panel4_recurrence_fields_sound,
    observer29_panel5_recurrence_fields_sound,
    observer29_panel6_recurrence_fields_sound,
    observer29_panel7_recurrence_fields_sound,
    observer29_frame_recurrence_fields_sound⟩
def observer29PanelFormulaBounds : Prop :=
  panelFormulaBounds observer29Panel0Data observer29Panel0Endpoints ∧
  panelFormulaBounds observer29Panel1Data observer29Panel1Endpoints ∧
  panelFormulaBounds observer29Panel2Data observer29Panel2Endpoints ∧
  panelFormulaBounds observer29Panel3Data observer29Panel3Endpoints ∧
  panelFormulaBounds observer29Panel4Data observer29Panel4Endpoints ∧
  panelFormulaBounds observer29Panel5Data observer29Panel5Endpoints ∧
  panelFormulaBounds observer29Panel6Data observer29Panel6Endpoints ∧
  panelFormulaBounds observer29Panel7Data observer29Panel7Endpoints
theorem observer29_all_panel_formula_bounds : observer29PanelFormulaBounds := by
  exact ⟨observer29_panel0_formula_sound,
    observer29_panel1_formula_sound,
    observer29_panel2_formula_sound,
    observer29_panel3_formula_sound,
    observer29_panel4_formula_sound,
    observer29_panel5_formula_sound,
    observer29_panel6_formula_sound,
    observer29_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
