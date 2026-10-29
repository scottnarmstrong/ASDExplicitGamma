module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer33Panel0Data : MainPanelData :=
  {
    observer := 33, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2384836983052319122 : ℚ) / 1802684005653569054445370771872525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer33Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393304197385382669173030258, ellLower := 352020936605575404847656715166,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172437777621433706086530584, offsetUpper := 6186462952292691458090778668,
    supportELower := 38565854888422768170172594988, supportEUpper := 40091575282693320399488831504,
    supportLambdaLower := 352020936605575404847656715166,
    supportLambdaUpper := 361977529163580659165190795122,
    supportJLower := 42086064254478522218649162139, supportJUpper := 43711350574329126991140739456,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer33Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer33Panel0Data observer33Panel0Endpoints
theorem observer33_panel0_kernel_check : observer33Panel0Check = true := by
  decide +kernel
theorem observer33_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer33Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer33Panel0Data) s observer33Panel0Data.anchor ≤
        (observer33Panel0Endpoints.energyUpper : ℝ) ∧
      (observer33Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer33Panel0Data) s observer33Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer33Panel0Data) s observer33Panel0Data.anchor ≤
        (observer33Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer33Panel0Data) s observer33Panel0Data.anchor ≤
        (observer33Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer33Panel0Data) s observer33Panel0Data.anchor ≤
        (observer33Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer33Panel0Data observer33Panel0Endpoints
    observer33_panel0_kernel_check s hs
def observer33Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer33Panel0Endpoints
theorem observer33_panel0_recurrence_field_kernel_check :
    observer33Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer33_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer33Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer33Panel0Endpoints
    observer33_panel0_recurrence_field_kernel_check

def observer33Panel1Data : MainPanelData :=
  {
    observer := 33, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2384836983052319122 : ℚ) / 1802684005653569054445370771872525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer33Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115189763748729770441234692, ellLower := 351854287717494213810444507942,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376117706923879035786133203, offsetUpper := 6390638697958344018338399603,
    supportELower := 40091526201500465603383997526, supportEUpper := 41498111449801641059407374138,
    supportLambdaLower := 351854287717494213810444507942,
    supportLambdaUpper := 361420201766865094779991670518,
    supportJLower := 43610069078675407741488442605, supportJUpper := 45112313467470292007207290844,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer33Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer33Panel1Data observer33Panel1Endpoints
theorem observer33_panel1_kernel_check : observer33Panel1Check = true := by
  decide +kernel
theorem observer33_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer33Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer33Panel1Data) s observer33Panel1Data.anchor ≤
        (observer33Panel1Endpoints.energyUpper : ℝ) ∧
      (observer33Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer33Panel1Data) s observer33Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer33Panel1Data) s observer33Panel1Data.anchor ≤
        (observer33Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer33Panel1Data) s observer33Panel1Data.anchor ≤
        (observer33Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer33Panel1Data) s observer33Panel1Data.anchor ≤
        (observer33Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer33Panel1Data observer33Panel1Endpoints
    observer33_panel1_kernel_check s hs
def observer33Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer33Panel1Endpoints
theorem observer33_panel1_recurrence_field_kernel_check :
    observer33Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer33_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer33Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer33Panel1Endpoints
    observer33_panel1_recurrence_field_kernel_check

def observer33Panel2Data : MainPanelData :=
  {
    observer := 33, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2384836983052319122 : ℚ) / 1802684005653569054445370771872525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer33Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817746166356242075988948855, ellLower := 351674079263399103085158344811,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591871034636666553643058157, offsetUpper := 6606883382995663245220790342,
    supportELower := 41498057528363373197866145847, supportEUpper := 42885088045701551496937794499,
    supportLambdaLower := 351674079263399103085158344811,
    supportLambdaUpper := 360893632467175920741492912890,
    supportJLower := 45014798320997364228717729295, supportJUpper := 46494024370373310704352723628,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer33Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer33Panel2Data observer33Panel2Endpoints
theorem observer33_panel2_kernel_check : observer33Panel2Check = true := by
  decide +kernel
theorem observer33_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer33Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer33Panel2Data) s observer33Panel2Data.anchor ≤
        (observer33Panel2Endpoints.energyUpper : ℝ) ∧
      (observer33Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer33Panel2Data) s observer33Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer33Panel2Data) s observer33Panel2Data.anchor ≤
        (observer33Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer33Panel2Data) s observer33Panel2Data.anchor ≤
        (observer33Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer33Panel2Data) s observer33Panel2Data.anchor ≤
        (observer33Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer33Panel2Data observer33Panel2Endpoints
    observer33_panel2_kernel_check s hs
def observer33Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer33Panel2Endpoints
theorem observer33_panel2_recurrence_field_kernel_check :
    observer33Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer33_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer33Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer33Panel2Endpoints
    observer33_panel2_recurrence_field_kernel_check

def observer33Panel3Data : MainPanelData :=
  {
    observer := 33, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2384836983052319122 : ℚ) / 1802684005653569054445370771872525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer33Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510213323293696072946167432, ellLower := 351497818832593331289861636230,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806509316480355366865607403, offsetUpper := 6822010482754824455884362643,
    supportELower := 42885029319588180402491082011, supportEUpper := 44261759222516828670265039719,
    supportLambdaLower := 351497818832593331289861636230,
    supportLambdaUpper := 360396393493927905560745205300,
    supportJLower := 46400007507914113715389698373, supportJUpper := 47865723157456107725872491772,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer33Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer33Panel3Data observer33Panel3Endpoints
theorem observer33_panel3_kernel_check : observer33Panel3Check = true := by
  decide +kernel
theorem observer33_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer33Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer33Panel3Data) s observer33Panel3Data.anchor ≤
        (observer33Panel3Endpoints.energyUpper : ℝ) ∧
      (observer33Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer33Panel3Data) s observer33Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer33Panel3Data) s observer33Panel3Data.anchor ≤
        (observer33Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer33Panel3Data) s observer33Panel3Data.anchor ≤
        (observer33Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer33Panel3Data) s observer33Panel3Data.anchor ≤
        (observer33Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer33Panel3Data observer33Panel3Endpoints
    observer33_panel3_kernel_check s hs
def observer33Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer33Panel3Endpoints
theorem observer33_panel3_recurrence_field_kernel_check :
    observer33Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer33_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer33Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer33Panel3Endpoints
    observer33_panel3_recurrence_field_kernel_check

def observer33Panel4Data : MainPanelData :=
  {
    observer := 33, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2384836983052319122 : ℚ) / 1802684005653569054445370771872525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer33Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196120053372136147358344628, ellLower := 351326784621377127021068868372,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020438944359340870029323214, offsetUpper := 7036427314658457094520566310,
    supportELower := 44261695710964462682150851903, supportEUpper := 45631675003093616451504244773,
    supportLambdaLower := 351326784621377127021068868372,
    supportLambdaUpper := 359926360079296817330716835968,
    supportJLower := 47774963557178233952361540586, supportJUpper := 49230938603886584624811413133,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer33Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer33Panel4Data observer33Panel4Endpoints
theorem observer33_panel4_kernel_check : observer33Panel4Check = true := by
  decide +kernel
theorem observer33_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer33Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer33Panel4Data) s observer33Panel4Data.anchor ≤
        (observer33Panel4Endpoints.energyUpper : ℝ) ∧
      (observer33Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer33Panel4Data) s observer33Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer33Panel4Data) s observer33Panel4Data.anchor ≤
        (observer33Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer33Panel4Data) s observer33Panel4Data.anchor ≤
        (observer33Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer33Panel4Data) s observer33Panel4Data.anchor ≤
        (observer33Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer33Panel4Data observer33Panel4Endpoints
    observer33_panel4_kernel_check s hs
def observer33Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer33Panel4Endpoints
theorem observer33_panel4_recurrence_field_kernel_check :
    observer33Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer33_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer33Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer33Panel4Endpoints
    observer33_panel4_recurrence_field_kernel_check

def observer33Panel5Data : MainPanelData :=
  {
    observer := 33, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2384836983052319122 : ℚ) / 1802684005653569054445370771872525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer33Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877497020826984531559016842, ellLower := 351161233547072946463011326181,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217423325550163637619873211, offsetUpper := 7233897844311137620531254278,
    supportELower := 45631606719248194887403357384, supportEUpper := 46996646901045114582829017330,
    supportLambdaLower := 351161233547072946463011326181,
    supportLambdaUpper := 359481407489978790564732666713,
    supportJLower := 49143219054718924352033470645, supportJUpper := 50591460975944902488476343998,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer33Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer33Panel5Data observer33Panel5Endpoints
theorem observer33_panel5_kernel_check : observer33Panel5Check = true := by
  decide +kernel
theorem observer33_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer33Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer33Panel5Data) s observer33Panel5Data.anchor ≤
        (observer33Panel5Endpoints.energyUpper : ℝ) ∧
      (observer33Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer33Panel5Data) s observer33Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer33Panel5Data) s observer33Panel5Data.anchor ≤
        (observer33Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer33Panel5Data) s observer33Panel5Data.anchor ≤
        (observer33Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer33Panel5Data) s observer33Panel5Data.anchor ≤
        (observer33Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer33Panel5Data observer33Panel5Endpoints
    observer33_panel5_kernel_check s hs
def observer33Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer33Panel5Endpoints
theorem observer33_panel5_recurrence_field_kernel_check :
    observer33Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer33_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer33Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer33Panel5Endpoints
    observer33_panel5_recurrence_field_kernel_check

def observer33Panel6Data : MainPanelData :=
  {
    observer := 33, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2384836983052319122 : ℚ) / 1802684005653569054445370771872525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer33Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554918634008088224271945606, ellLower := 351001126998643438728901896313,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429988271474504996668694333, offsetUpper := 7446947991813881482611838480,
    supportELower := 46996573854984871365606498935, supportEUpper := 48357749935739116671196352968,
    supportLambdaLower := 351001126998643438728901896313,
    supportLambdaUpper := 359059554732371400190728882085,
    supportJLower := 50506585124971305752895517898, supportJUpper := 51948345483062830673103641789,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer33Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer33Panel6Data observer33Panel6Endpoints
theorem observer33_panel6_kernel_check : observer33Panel6Check = true := by
  decide +kernel
theorem observer33_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer33Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer33Panel6Data) s observer33Panel6Data.anchor ≤
        (observer33Panel6Endpoints.energyUpper : ℝ) ∧
      (observer33Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer33Panel6Data) s observer33Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer33Panel6Data) s observer33Panel6Data.anchor ≤
        (observer33Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer33Panel6Data) s observer33Panel6Data.anchor ≤
        (observer33Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer33Panel6Data) s observer33Panel6Data.anchor ≤
        (observer33Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer33Panel6Data observer33Panel6Endpoints
    observer33_panel6_kernel_check s hs
def observer33Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer33Panel6Endpoints
theorem observer33_panel6_recurrence_field_kernel_check :
    observer33Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer33_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer33Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer33Panel6Endpoints
    observer33_panel6_recurrence_field_kernel_check

def observer33Panel7Data : MainPanelData :=
  {
    observer := 33, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2384836983052319122 : ℚ) / 1802684005653569054445370771872525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer33Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229309584570844509246797911, ellLower := 350846314709826552881820404017,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642253628852475196737906534, offsetUpper := 7659697866928264442322272059,
    supportELower := 48357672135720749182707227085, supportEUpper := 49715686341064235053913576962,
    supportLambdaLower := 350846314709826552881820404017,
    supportLambdaUpper := 358658994184660060126424802021,
    supportJLower := 51866135282819014711525431125, supportJUpper := 53302276282910835655177824983,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer33Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer33Panel7Data observer33Panel7Endpoints
theorem observer33_panel7_kernel_check : observer33Panel7Check = true := by
  decide +kernel
theorem observer33_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer33Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer33Panel7Data) s observer33Panel7Data.anchor ≤
        (observer33Panel7Endpoints.energyUpper : ℝ) ∧
      (observer33Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer33Panel7Data) s observer33Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer33Panel7Data) s observer33Panel7Data.anchor ≤
        (observer33Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer33Panel7Data) s observer33Panel7Data.anchor ≤
        (observer33Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer33Panel7Data) s observer33Panel7Data.anchor ≤
        (observer33Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer33Panel7Data observer33Panel7Endpoints
    observer33_panel7_kernel_check s hs
def observer33Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer33Panel7Endpoints
theorem observer33_panel7_recurrence_field_kernel_check :
    observer33Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer33_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer33Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer33Panel7Endpoints
    observer33_panel7_recurrence_field_kernel_check

def observer33InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 33, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer33Panel0Endpoints, observer33Panel1Endpoints, observer33Panel2Endpoints, observer33Panel3Endpoints, observer33Panel4Endpoints, observer33Panel5Endpoints, observer33Panel6Endpoints, observer33Panel7Endpoints]
  }
def observer33FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer33InsertionEndpoints.frameLower
    observer33InsertionEndpoints.frameUpper
theorem observer33_frame_recurrence_field_kernel_check :
    observer33FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer33_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer33InsertionEndpoints.frameLower
      observer33InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer33InsertionEndpoints.frameLower
    observer33InsertionEndpoints.frameUpper
    observer33_frame_recurrence_field_kernel_check
def observer33RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer33Panel0Endpoints ∧
  panelRecurrenceFields observer33Panel1Endpoints ∧
  panelRecurrenceFields observer33Panel2Endpoints ∧
  panelRecurrenceFields observer33Panel3Endpoints ∧
  panelRecurrenceFields observer33Panel4Endpoints ∧
  panelRecurrenceFields observer33Panel5Endpoints ∧
  panelRecurrenceFields observer33Panel6Endpoints ∧
  panelRecurrenceFields observer33Panel7Endpoints ∧ insertionFrameRecurrenceFields observer33InsertionEndpoints.frameLower
      observer33InsertionEndpoints.frameUpper
theorem observer33_all_recurrence_fields :
    observer33RecurrenceFieldBounds := by
  exact ⟨observer33_panel0_recurrence_fields_sound,
    observer33_panel1_recurrence_fields_sound,
    observer33_panel2_recurrence_fields_sound,
    observer33_panel3_recurrence_fields_sound,
    observer33_panel4_recurrence_fields_sound,
    observer33_panel5_recurrence_fields_sound,
    observer33_panel6_recurrence_fields_sound,
    observer33_panel7_recurrence_fields_sound,
    observer33_frame_recurrence_fields_sound⟩
def observer33PanelFormulaBounds : Prop :=
  panelFormulaBounds observer33Panel0Data observer33Panel0Endpoints ∧
  panelFormulaBounds observer33Panel1Data observer33Panel1Endpoints ∧
  panelFormulaBounds observer33Panel2Data observer33Panel2Endpoints ∧
  panelFormulaBounds observer33Panel3Data observer33Panel3Endpoints ∧
  panelFormulaBounds observer33Panel4Data observer33Panel4Endpoints ∧
  panelFormulaBounds observer33Panel5Data observer33Panel5Endpoints ∧
  panelFormulaBounds observer33Panel6Data observer33Panel6Endpoints ∧
  panelFormulaBounds observer33Panel7Data observer33Panel7Endpoints
theorem observer33_all_panel_formula_bounds : observer33PanelFormulaBounds := by
  exact ⟨observer33_panel0_formula_sound,
    observer33_panel1_formula_sound,
    observer33_panel2_formula_sound,
    observer33_panel3_formula_sound,
    observer33_panel4_formula_sound,
    observer33_panel5_formula_sound,
    observer33_panel6_formula_sound,
    observer33_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
