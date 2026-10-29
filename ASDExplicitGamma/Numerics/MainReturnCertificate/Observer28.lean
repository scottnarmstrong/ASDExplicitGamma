module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer28Panel0Data : MainPanelData :=
  {
    observer := 28, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((9814143963178024 : ℚ) / 30528611926596031337454838725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer28Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393398635506167312679530736, ellLower := 352021188139341291291276963362,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172445168616227015456798182, offsetUpper := 6186470360081496583399703488,
    supportELower := 38565945770934171778079086784, supportEUpper := 40091667169638506201555122826,
    supportLambdaLower := 352021188139341291291276963362,
    supportLambdaUpper := 361977784275695975051156854948,
    supportJLower := 42086157652327584690991856417, supportJUpper := 43711445012395465952066691376,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer28Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer28Panel0Data observer28Panel0Endpoints
theorem observer28_panel0_kernel_check : observer28Panel0Check = true := by
  decide +kernel
theorem observer28_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer28Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer28Panel0Data) s observer28Panel0Data.anchor ≤
        (observer28Panel0Endpoints.energyUpper : ℝ) ∧
      (observer28Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer28Panel0Data) s observer28Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer28Panel0Data) s observer28Panel0Data.anchor ≤
        (observer28Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer28Panel0Data) s observer28Panel0Data.anchor ≤
        (observer28Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer28Panel0Data) s observer28Panel0Data.anchor ≤
        (observer28Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer28Panel0Data observer28Panel0Endpoints
    observer28_panel0_kernel_check s hs
def observer28Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer28Panel0Endpoints
theorem observer28_panel0_recurrence_field_kernel_check :
    observer28Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer28_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer28Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer28Panel0Endpoints
    observer28_panel0_recurrence_field_kernel_check

def observer28Panel1Data : MainPanelData :=
  {
    observer := 28, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((9814143963178024 : ℚ) / 30528611926596031337454838725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer28Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115285174068462942381740686, ellLower := 351854536895822730462460497198,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376125092940448515152934686, offsetUpper := 6390646100795851459586543457,
    supportELower := 40091618088351671459214662056, supportEUpper := 41498204333721589198376109719,
    supportLambdaLower := 351854536895822730462460497198,
    supportLambdaUpper := 361420454401399029819113856022,
    supportJLower := 43610163457309898763839267027, supportJUpper := 45112408877735579496567248280,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer28Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer28Panel1Data observer28Panel1Endpoints
theorem observer28_panel1_kernel_check : observer28Panel1Check = true := by
  decide +kernel
theorem observer28_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer28Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer28Panel1Data) s observer28Panel1Data.anchor ≤
        (observer28Panel1Endpoints.energyUpper : ℝ) ∧
      (observer28Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer28Panel1Data) s observer28Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer28Panel1Data) s observer28Panel1Data.anchor ≤
        (observer28Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer28Panel1Data) s observer28Panel1Data.anchor ≤
        (observer28Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer28Panel1Data) s observer28Panel1Data.anchor ≤
        (observer28Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer28Panel1Data observer28Panel1Endpoints
    observer28_panel1_kernel_check s hs
def observer28Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer28Panel1Endpoints
theorem observer28_panel1_recurrence_field_kernel_check :
    observer28Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer28_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer28Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer28Panel1Endpoints
    observer28_panel1_recurrence_field_kernel_check

def observer28Panel2Data : MainPanelData :=
  {
    observer := 28, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((9814143963178024 : ℚ) / 30528611926596031337454838725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer28Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817842542687933364625813651, ellLower := 351674326171594778389717132604,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591878434680494101346954886, offsetUpper := 6606890799892374477581388867,
    supportELower := 41498150412186281327952050798, supportEUpper := 42885181919477075510608521602,
    supportLambdaLower := 351674326171594778389717132604,
    supportLambdaUpper := 360893882717348079980051826337,
    supportJLower := 45014893673902229111849222124, supportJUpper := 46494120746650556310409039866,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer28Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer28Panel2Data observer28Panel2Endpoints
theorem observer28_panel2_kernel_check : observer28Panel2Check = true := by
  decide +kernel
theorem observer28_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer28Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer28Panel2Data) s observer28Panel2Data.anchor ≤
        (observer28Panel2Endpoints.energyUpper : ℝ) ∧
      (observer28Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer28Panel2Data) s observer28Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer28Panel2Data) s observer28Panel2Data.anchor ≤
        (observer28Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer28Panel2Data) s observer28Panel2Data.anchor ≤
        (observer28Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer28Panel2Data) s observer28Panel2Data.anchor ≤
        (observer28Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer28Panel2Data observer28Panel2Endpoints
    observer28_panel2_kernel_check s hs
def observer28Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer28Panel2Endpoints
theorem observer28_panel2_recurrence_field_kernel_check :
    observer28Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer28_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer28Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer28Panel2Endpoints
    observer28_panel2_recurrence_field_kernel_check

def observer28Panel3Data : MainPanelData :=
  {
    observer := 28, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((9814143963178024 : ℚ) / 30528611926596031337454838725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer28Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510310659620025662420025478, ellLower := 351498063550399225271751761493,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806516731749939912943773083, offsetUpper := 6822017914911967874724093013,
    supportELower := 42885123193263639979437925492, supportEUpper := 44261854079261770708471298231,
    supportLambdaLower := 351498063550399225271751761493,
    supportLambdaUpper := 360396641446622092429450302826,
    supportJLower := 46400103828767632232155443106, supportJUpper := 47865820493727991632765801260,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer28Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer28Panel3Data observer28Panel3Endpoints
theorem observer28_panel3_kernel_check : observer28Panel3Check = true := by
  decide +kernel
theorem observer28_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer28Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer28Panel3Data) s observer28Panel3Data.anchor ≤
        (observer28Panel3Endpoints.energyUpper : ℝ) ∧
      (observer28Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer28Panel3Data) s observer28Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer28Panel3Data) s observer28Panel3Data.anchor ≤
        (observer28Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer28Panel3Data) s observer28Panel3Data.anchor ≤
        (observer28Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer28Panel3Data) s observer28Panel3Data.anchor ≤
        (observer28Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer28Panel3Data observer28Panel3Endpoints
    observer28_panel3_kernel_check s hs
def observer28Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer28Panel3Endpoints
theorem observer28_panel3_recurrence_field_kernel_check :
    observer28Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer28_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer28Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer28Panel3Endpoints
    observer28_panel3_recurrence_field_kernel_check

def observer28Panel4Data : MainPanelData :=
  {
    observer := 28, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((9814143963178024 : ℚ) / 30528611926596031337454838725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer28Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196218343837526442974536550, ellLower := 351327027223515350528168819868,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020446375700330604152317699, offsetUpper := 7036434762923606771425120859,
    supportELower := 44261790567606349929239190667, supportEUpper := 45631770836140498936068129090,
    supportLambdaLower := 351327027223515350528168819868,
    supportLambdaUpper := 359926605815703030177892740679,
    supportJLower := 47775060839841503434520878865, supportJUpper := 49231036894297529237847056497,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer28Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer28Panel4Data observer28Panel4Endpoints
theorem observer28_panel4_kernel_check : observer28Panel4Check = true := by
  decide +kernel
theorem observer28_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer28Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer28Panel4Data) s observer28Panel4Data.anchor ≤
        (observer28Panel4Endpoints.energyUpper : ℝ) ∧
      (observer28Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer28Panel4Data) s observer28Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer28Panel4Data) s observer28Panel4Data.anchor ≤
        (observer28Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer28Panel4Data) s observer28Panel4Data.anchor ≤
        (observer28Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer28Panel4Data) s observer28Panel4Data.anchor ≤
        (observer28Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer28Panel4Data observer28Panel4Endpoints
    observer28_panel4_kernel_check s hs
def observer28Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer28Panel4Endpoints
theorem observer28_panel4_recurrence_field_kernel_check :
    observer28Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer28_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer28Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer28Panel4Endpoints
    observer28_panel4_recurrence_field_kernel_check

def observer28Panel5Data : MainPanelData :=
  {
    observer := 28, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((9814143963178024 : ℚ) / 30528611926596031337454838725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer28Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877596259730169208971746861, ellLower := 351161474103715116642906134286,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217430756641701774180997778, offsetUpper := 7233905292364914417274304982,
    supportELower := 45631702552189064856020251131, supportEUpper := 46996743703932154859878911665,
    supportLambdaLower := 351161474103715116642906134286,
    supportLambdaUpper := 359481651086148662342961379357,
    supportJLower := 49143317293226216022449312473, supportJUpper := 50591560214793641483308525459,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer28Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer28Panel5Data observer28Panel5Endpoints
theorem observer28_panel5_kernel_check : observer28Panel5Check = true := by
  decide +kernel
theorem observer28_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer28Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer28Panel5Data) s observer28Panel5Data.anchor ≤
        (observer28Panel5Endpoints.energyUpper : ℝ) ∧
      (observer28Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer28Panel5Data) s observer28Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer28Panel5Data) s observer28Panel5Data.anchor ≤
        (observer28Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer28Panel5Data) s observer28Panel5Data.anchor ≤
        (observer28Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer28Panel5Data) s observer28Panel5Data.anchor ≤
        (observer28Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer28Panel5Data observer28Panel5Endpoints
    observer28_panel5_kernel_check s hs
def observer28Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer28Panel5Endpoints
theorem observer28_panel5_recurrence_field_kernel_check :
    observer28Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer28_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer28Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer28Panel5Endpoints
    observer28_panel5_recurrence_field_kernel_check

def observer28Panel6Data : MainPanelData :=
  {
    observer := 28, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((9814143963178024 : ℚ) / 30528611926596031337454838725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer28Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59555018815795146805965870550, ellLower := 351001365575822306638049388631,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429995719809654902542686996, offsetUpper := 7446955457150630384453360021,
    supportELower := 46996670657762972692015199400, supportEUpper := 48357847702198428821000204023,
    supportLambdaLower := 351001365575822306638049388631,
    supportLambdaUpper := 359059796259701475121681415131,
    supportJLower := 50506684313521195758395693286, supportJUpper := 51948445664795443572217018175,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer28Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer28Panel6Data observer28Panel6Endpoints
theorem observer28_panel6_kernel_check : observer28Panel6Check = true := by
  decide +kernel
theorem observer28_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer28Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer28Panel6Data) s observer28Panel6Data.anchor ≤
        (observer28Panel6Endpoints.energyUpper : ℝ) ∧
      (observer28Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer28Panel6Data) s observer28Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer28Panel6Data) s observer28Panel6Data.anchor ≤
        (observer28Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer28Panel6Data) s observer28Panel6Data.anchor ≤
        (observer28Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer28Panel6Data) s observer28Panel6Data.anchor ≤
        (observer28Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer28Panel6Data observer28Panel6Endpoints
    observer28_panel6_kernel_check s hs
def observer28Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer28Panel6Endpoints
theorem observer28_panel6_recurrence_field_kernel_check :
    observer28Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer28_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer28Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer28Panel6Endpoints
    observer28_panel6_recurrence_field_kernel_check

def observer28Panel7Data : MainPanelData :=
  {
    observer := 28, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((9814143963178024 : ℚ) / 30528611926596031337454838725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer28Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229410703828670730376735581, ellLower := 350846551369797920427384869831,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642261094903211699428045535, offsetUpper := 7659705350021037608356012490,
    supportELower := 48357769902068225991222335755, supportEUpper := 49715785065011071249705566837,
    supportLambdaLower := 350846551369797920427384869831,
    supportLambdaUpper := 358659233710314494402164725756,
    supportJLower := 51866235415766205195496184453, supportJUpper := 53302377402114216193727214095,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer28Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer28Panel7Data observer28Panel7Endpoints
theorem observer28_panel7_kernel_check : observer28Panel7Check = true := by
  decide +kernel
theorem observer28_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer28Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer28Panel7Data) s observer28Panel7Data.anchor ≤
        (observer28Panel7Endpoints.energyUpper : ℝ) ∧
      (observer28Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer28Panel7Data) s observer28Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer28Panel7Data) s observer28Panel7Data.anchor ≤
        (observer28Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer28Panel7Data) s observer28Panel7Data.anchor ≤
        (observer28Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer28Panel7Data) s observer28Panel7Data.anchor ≤
        (observer28Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer28Panel7Data observer28Panel7Endpoints
    observer28_panel7_kernel_check s hs
def observer28Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer28Panel7Endpoints
theorem observer28_panel7_recurrence_field_kernel_check :
    observer28Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer28_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer28Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer28Panel7Endpoints
    observer28_panel7_recurrence_field_kernel_check

def observer28InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 28, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer28Panel0Endpoints, observer28Panel1Endpoints, observer28Panel2Endpoints, observer28Panel3Endpoints, observer28Panel4Endpoints, observer28Panel5Endpoints, observer28Panel6Endpoints, observer28Panel7Endpoints]
  }
def observer28FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer28InsertionEndpoints.frameLower
    observer28InsertionEndpoints.frameUpper
theorem observer28_frame_recurrence_field_kernel_check :
    observer28FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer28_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer28InsertionEndpoints.frameLower
      observer28InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer28InsertionEndpoints.frameLower
    observer28InsertionEndpoints.frameUpper
    observer28_frame_recurrence_field_kernel_check
def observer28RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer28Panel0Endpoints ∧
  panelRecurrenceFields observer28Panel1Endpoints ∧
  panelRecurrenceFields observer28Panel2Endpoints ∧
  panelRecurrenceFields observer28Panel3Endpoints ∧
  panelRecurrenceFields observer28Panel4Endpoints ∧
  panelRecurrenceFields observer28Panel5Endpoints ∧
  panelRecurrenceFields observer28Panel6Endpoints ∧
  panelRecurrenceFields observer28Panel7Endpoints ∧ insertionFrameRecurrenceFields observer28InsertionEndpoints.frameLower
      observer28InsertionEndpoints.frameUpper
theorem observer28_all_recurrence_fields :
    observer28RecurrenceFieldBounds := by
  exact ⟨observer28_panel0_recurrence_fields_sound,
    observer28_panel1_recurrence_fields_sound,
    observer28_panel2_recurrence_fields_sound,
    observer28_panel3_recurrence_fields_sound,
    observer28_panel4_recurrence_fields_sound,
    observer28_panel5_recurrence_fields_sound,
    observer28_panel6_recurrence_fields_sound,
    observer28_panel7_recurrence_fields_sound,
    observer28_frame_recurrence_fields_sound⟩
def observer28PanelFormulaBounds : Prop :=
  panelFormulaBounds observer28Panel0Data observer28Panel0Endpoints ∧
  panelFormulaBounds observer28Panel1Data observer28Panel1Endpoints ∧
  panelFormulaBounds observer28Panel2Data observer28Panel2Endpoints ∧
  panelFormulaBounds observer28Panel3Data observer28Panel3Endpoints ∧
  panelFormulaBounds observer28Panel4Data observer28Panel4Endpoints ∧
  panelFormulaBounds observer28Panel5Data observer28Panel5Endpoints ∧
  panelFormulaBounds observer28Panel6Data observer28Panel6Endpoints ∧
  panelFormulaBounds observer28Panel7Data observer28Panel7Endpoints
theorem observer28_all_panel_formula_bounds : observer28PanelFormulaBounds := by
  exact ⟨observer28_panel0_formula_sound,
    observer28_panel1_formula_sound,
    observer28_panel2_formula_sound,
    observer28_panel3_formula_sound,
    observer28_panel4_formula_sound,
    observer28_panel5_formula_sound,
    observer28_panel6_formula_sound,
    observer28_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
