module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer25Panel0Data : MainPanelData :=
  {
    observer := 25, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((363486813450802 : ℚ) / 41877382615358067678264525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer25Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393822551696582202958960153, ellLower := 352022318668338207173698026722,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172478320154091053036191068, offsetUpper := 6186503586947152640150219213,
    supportELower := 38566353703438355033974101373, supportEUpper := 40092079617918359546450035926,
    supportLambdaLower := 352022318668338207173698026722,
    supportLambdaUpper := 361978930924608401265776267947,
    supportJLower := 42086576890121737105711081640, supportJUpper := 43711868927164443559107798606,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer25Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer25Panel0Data observer25Panel0Endpoints
theorem observer25_panel0_kernel_check : observer25Panel0Check = true := by
  decide +kernel
theorem observer25_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer25Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer25Panel0Data) s observer25Panel0Data.anchor ≤
        (observer25Panel0Endpoints.energyUpper : ℝ) ∧
      (observer25Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer25Panel0Data) s observer25Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer25Panel0Data) s observer25Panel0Data.anchor ≤
        (observer25Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer25Panel0Data) s observer25Panel0Data.anchor ≤
        (observer25Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer25Panel0Data) s observer25Panel0Data.anchor ≤
        (observer25Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer25Panel0Data observer25Panel0Endpoints
    observer25_panel0_kernel_check s hs
def observer25Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer25Panel0Endpoints
theorem observer25_panel0_recurrence_field_kernel_check :
    observer25Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer25_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer25Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer25Panel0Endpoints
    observer25_panel0_recurrence_field_kernel_check

def observer25Panel1Data : MainPanelData :=
  {
    observer := 25, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((363486813450802 : ℚ) / 41877382615358067678264525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer25Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115713461154724116029067620, ellLower := 351855656836838269033170280570,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376158222414017148166653973, offsetUpper := 6390679305718590070165714088,
    supportELower := 40092030536209668421864817184, supportEUpper := 41498621264284299188642830729,
    supportLambdaLower := 351855656836838269033170280570,
    supportLambdaUpper := 361421589911610419833342229759,
    supportJLower := 43610587104578051112196519989, supportJUpper := 45112837163400403386976253027,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer25Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer25Panel1Data observer25Panel1Endpoints
theorem observer25_panel1_kernel_check : observer25Panel1Check = true := by
  decide +kernel
theorem observer25_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer25Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer25Panel1Data) s observer25Panel1Data.anchor ≤
        (observer25Panel1Endpoints.energyUpper : ℝ) ∧
      (observer25Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer25Panel1Data) s observer25Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer25Panel1Data) s observer25Panel1Data.anchor ≤
        (observer25Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer25Panel1Data) s observer25Panel1Data.anchor ≤
        (observer25Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer25Panel1Data) s observer25Panel1Data.anchor ≤
        (observer25Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer25Panel1Data observer25Panel1Endpoints
    observer25_panel1_kernel_check s hs
def observer25Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer25Panel1Endpoints
theorem observer25_panel1_recurrence_field_kernel_check :
    observer25Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer25_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer25Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer25Panel1Endpoints
    observer25_panel1_recurrence_field_kernel_check

def observer25Panel2Data : MainPanelData :=
  {
    observer := 25, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((363486813450802 : ℚ) / 41877382615358067678264525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer25Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52818275172903371256071948434, ellLower := 351675435908732234289677049559,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591911627348291860234391493, offsetUpper := 6606924068153260955303789550,
    supportELower := 41498567342313378832493682661, supportEUpper := 42885603300357671000754302466,
    supportLambdaLower := 351675435908732234289677049559,
    supportLambdaUpper := 360895007508688591786254999583,
    supportJLower := 45015321701400701175390453156, supportJUpper := 46494553375444556918616852462,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer25Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer25Panel2Data observer25Panel2Endpoints
theorem observer25_panel2_kernel_check : observer25Panel2Check = true := by
  decide +kernel
theorem observer25_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer25Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer25Panel2Data) s observer25Panel2Data.anchor ≤
        (observer25Panel2Endpoints.energyUpper : ℝ) ∧
      (observer25Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer25Panel2Data) s observer25Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer25Panel2Data) s observer25Panel2Data.anchor ≤
        (observer25Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer25Panel2Data) s observer25Panel2Data.anchor ≤
        (observer25Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer25Panel2Data) s observer25Panel2Data.anchor ≤
        (observer25Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer25Panel2Data observer25Panel2Endpoints
    observer25_panel2_kernel_check s hs
def observer25Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer25Panel2Endpoints
theorem observer25_panel2_recurrence_field_kernel_check :
    observer25Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer25_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer25Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer25Panel2Endpoints
    observer25_panel2_recurrence_field_kernel_check

def observer25Panel3Data : MainPanelData :=
  {
    observer := 25, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((363486813450802 : ℚ) / 41877382615358067678264525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer25Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510747605960307761798758366, ellLower := 351499163442680018743780906207,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806549992993553725088536387, offsetUpper := 6822051251904845190402217073,
    supportELower := 42885544573695026833009432325, supportEUpper := 44262279879543420446792870559,
    supportLambdaLower := 351499163442680018743780906207,
    supportLambdaUpper := 360397755910341600211334140110,
    supportJLower := 46400536208121827020447241387, supportJUpper := 47866257438646836448906211961,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer25Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer25Panel3Data observer25Panel3Endpoints
theorem observer25_panel3_kernel_check : observer25Panel3Check = true := by
  decide +kernel
theorem observer25_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer25Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer25Panel3Data) s observer25Panel3Data.anchor ≤
        (observer25Panel3Endpoints.energyUpper : ℝ) ∧
      (observer25Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer25Panel3Data) s observer25Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer25Panel3Data) s observer25Panel3Data.anchor ≤
        (observer25Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer25Panel3Data) s observer25Panel3Data.anchor ≤
        (observer25Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer25Panel3Data) s observer25Panel3Data.anchor ≤
        (observer25Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer25Panel3Data observer25Panel3Endpoints
    observer25_panel3_kernel_check s hs
def observer25Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer25Panel3Endpoints
theorem observer25_panel3_recurrence_field_kernel_check :
    observer25Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer25_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer25Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer25Panel3Endpoints
    observer25_panel3_recurrence_field_kernel_check

def observer25Panel4Data : MainPanelData :=
  {
    observer := 25, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((363486813450802 : ℚ) / 41877382615358067678264525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer25Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196659580024988852136504463, ellLower := 351328117607319816371804784096,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020479709316009632792962885, offsetUpper := 7036468172453369678388201787,
    supportELower := 44262216367425347813267205311, supportEUpper := 45632201025889847561772262615,
    supportLambdaLower := 351328117607319816371804784096,
    supportLambdaUpper := 359927710317370680199843960733,
    supportJLower := 47775497543498545976985253151, supportJUpper := 49231478129063554363770702223,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer25Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer25Panel4Data observer25Panel4Endpoints
theorem observer25_panel4_kernel_check : observer25Panel4Check = true := by
  decide +kernel
theorem observer25_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer25Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer25Panel4Data) s observer25Panel4Data.anchor ≤
        (observer25Panel4Endpoints.energyUpper : ℝ) ∧
      (observer25Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer25Panel4Data) s observer25Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer25Panel4Data) s observer25Panel4Data.anchor ≤
        (observer25Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer25Panel4Data) s observer25Panel4Data.anchor ≤
        (observer25Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer25Panel4Data) s observer25Panel4Data.anchor ≤
        (observer25Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer25Panel4Data observer25Panel4Endpoints
    observer25_panel4_kernel_check s hs
def observer25Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer25Panel4Endpoints
theorem observer25_panel4_recurrence_field_kernel_check :
    observer25Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer25_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer25Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer25Panel4Endpoints
    observer25_panel4_recurrence_field_kernel_check

def observer25Panel5Data : MainPanelData :=
  {
    observer := 25, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((363486813450802 : ℚ) / 41877382615358067678264525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer25Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57878041760180388278427660510, ellLower := 351162555294906638042473671590,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217464089422426893742549867, offsetUpper := 7233938701231175418791996088,
    supportELower := 45632132741462464852501997617, supportEUpper := 46997178254140811466540034746,
    supportLambdaLower := 351162555294906638042473671590,
    supportLambdaUpper := 359482745968161180298608217414,
    supportJLower := 49143758294411531232926734332, supportJUpper := 50592005713822423269526116921,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer25Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer25Panel5Data observer25Panel5Endpoints
theorem observer25_panel5_kernel_check : observer25Panel5Check = true := by
  decide +kernel
theorem observer25_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer25Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer25Panel5Data) s observer25Panel5Data.anchor ≤
        (observer25Panel5Endpoints.energyUpper : ℝ) ∧
      (observer25Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer25Panel5Data) s observer25Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer25Panel5Data) s observer25Panel5Data.anchor ≤
        (observer25Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer25Panel5Data) s observer25Panel5Data.anchor ≤
        (observer25Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer25Panel5Data) s observer25Panel5Data.anchor ≤
        (observer25Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer25Panel5Data observer25Panel5Endpoints
    observer25_panel5_kernel_check s hs
def observer25Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer25Panel5Endpoints
theorem observer25_panel5_recurrence_field_kernel_check :
    observer25Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer25_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer25Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer25Panel5Endpoints
    observer25_panel5_recurrence_field_kernel_check

def observer25Panel6Data : MainPanelData :=
  {
    observer := 25, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((363486813450802 : ℚ) / 41877382615358067678264525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer25Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59555468555585607213981897304, ellLower := 351002437871605601881928861838,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7430029130222553396678532316, offsetUpper := 7446988943826268263655246437,
    supportELower := 46997105207482524317367235370, supportEUpper := 48358286584729813509516272948,
    supportLambdaLower := 351002437871605601881928861838,
    supportLambdaUpper := 359060881843465318747844979389,
    supportJLower := 50507129586198580336186523988, supportJUpper := 51948895403164466696994722742,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer25Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer25Panel6Data observer25Panel6Endpoints
theorem observer25_panel6_kernel_check : observer25Panel6Check = true := by
  decide +kernel
theorem observer25_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer25Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer25Panel6Data) s observer25Panel6Data.anchor ≤
        (observer25Panel6Endpoints.energyUpper : ℝ) ∧
      (observer25Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer25Panel6Data) s observer25Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer25Panel6Data) s observer25Panel6Data.anchor ≤
        (observer25Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer25Panel6Data) s observer25Panel6Data.anchor ≤
        (observer25Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer25Panel6Data) s observer25Panel6Data.anchor ≤
        (observer25Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer25Panel6Data observer25Panel6Endpoints
    observer25_panel6_kernel_check s hs
def observer25Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer25Panel6Endpoints
theorem observer25_panel6_recurrence_field_kernel_check :
    observer25Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer25_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer25Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer25Panel6Endpoints
    observer25_panel6_recurrence_field_kernel_check

def observer25Panel7Data : MainPanelData :=
  {
    observer := 25, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((363486813450802 : ℚ) / 41877382615358067678264525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer25Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229864658669387030652883805, ellLower := 350847615050352706925750746621,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642294585065915217093580534, offsetUpper := 7659738916628517728496338545,
    supportELower := 48358208784097484169508310221, supportEUpper := 49716228252551952726225822668,
    supportLambdaLower := 350847615050352706925750746621,
    supportLambdaUpper := 358660310298154248453921746314,
    supportJLower := 51866684934601011238765817687, supportJUpper := 53302831355533495210765040132,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer25Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer25Panel7Data observer25Panel7Endpoints
theorem observer25_panel7_kernel_check : observer25Panel7Check = true := by
  decide +kernel
theorem observer25_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer25Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer25Panel7Data) s observer25Panel7Data.anchor ≤
        (observer25Panel7Endpoints.energyUpper : ℝ) ∧
      (observer25Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer25Panel7Data) s observer25Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer25Panel7Data) s observer25Panel7Data.anchor ≤
        (observer25Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer25Panel7Data) s observer25Panel7Data.anchor ≤
        (observer25Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer25Panel7Data) s observer25Panel7Data.anchor ≤
        (observer25Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer25Panel7Data observer25Panel7Endpoints
    observer25_panel7_kernel_check s hs
def observer25Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer25Panel7Endpoints
theorem observer25_panel7_recurrence_field_kernel_check :
    observer25Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer25_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer25Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer25Panel7Endpoints
    observer25_panel7_recurrence_field_kernel_check

def observer25InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 25, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer25Panel0Endpoints, observer25Panel1Endpoints, observer25Panel2Endpoints, observer25Panel3Endpoints, observer25Panel4Endpoints, observer25Panel5Endpoints, observer25Panel6Endpoints, observer25Panel7Endpoints]
  }
def observer25FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer25InsertionEndpoints.frameLower
    observer25InsertionEndpoints.frameUpper
theorem observer25_frame_recurrence_field_kernel_check :
    observer25FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer25_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer25InsertionEndpoints.frameLower
      observer25InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer25InsertionEndpoints.frameLower
    observer25InsertionEndpoints.frameUpper
    observer25_frame_recurrence_field_kernel_check
def observer25RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer25Panel0Endpoints ∧
  panelRecurrenceFields observer25Panel1Endpoints ∧
  panelRecurrenceFields observer25Panel2Endpoints ∧
  panelRecurrenceFields observer25Panel3Endpoints ∧
  panelRecurrenceFields observer25Panel4Endpoints ∧
  panelRecurrenceFields observer25Panel5Endpoints ∧
  panelRecurrenceFields observer25Panel6Endpoints ∧
  panelRecurrenceFields observer25Panel7Endpoints ∧ insertionFrameRecurrenceFields observer25InsertionEndpoints.frameLower
      observer25InsertionEndpoints.frameUpper
theorem observer25_all_recurrence_fields :
    observer25RecurrenceFieldBounds := by
  exact ⟨observer25_panel0_recurrence_fields_sound,
    observer25_panel1_recurrence_fields_sound,
    observer25_panel2_recurrence_fields_sound,
    observer25_panel3_recurrence_fields_sound,
    observer25_panel4_recurrence_fields_sound,
    observer25_panel5_recurrence_fields_sound,
    observer25_panel6_recurrence_fields_sound,
    observer25_panel7_recurrence_fields_sound,
    observer25_frame_recurrence_fields_sound⟩
def observer25PanelFormulaBounds : Prop :=
  panelFormulaBounds observer25Panel0Data observer25Panel0Endpoints ∧
  panelFormulaBounds observer25Panel1Data observer25Panel1Endpoints ∧
  panelFormulaBounds observer25Panel2Data observer25Panel2Endpoints ∧
  panelFormulaBounds observer25Panel3Data observer25Panel3Endpoints ∧
  panelFormulaBounds observer25Panel4Data observer25Panel4Endpoints ∧
  panelFormulaBounds observer25Panel5Data observer25Panel5Endpoints ∧
  panelFormulaBounds observer25Panel6Data observer25Panel6Endpoints ∧
  panelFormulaBounds observer25Panel7Data observer25Panel7Endpoints
theorem observer25_all_panel_formula_bounds : observer25PanelFormulaBounds := by
  exact ⟨observer25_panel0_formula_sound,
    observer25_panel1_formula_sound,
    observer25_panel2_formula_sound,
    observer25_panel3_formula_sound,
    observer25_panel4_formula_sound,
    observer25_panel5_formula_sound,
    observer25_panel6_formula_sound,
    observer25_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
