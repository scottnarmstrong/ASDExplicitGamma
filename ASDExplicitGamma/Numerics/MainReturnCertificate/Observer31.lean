module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer31Panel0Data : MainPanelData :=
  {
    observer := 31, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((264981887005813018 : ℚ) / 22255358094488506845004577430525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer31Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393317141782984911482446298, ellLower := 352020971074917623129944933052,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172438790823402720738322461, offsetUpper := 6186463967796884505557166139,
    supportELower := 38565867345586308205938589967, supportEUpper := 40091587877494041156711881195,
    supportLambdaLower := 352020971074917623129944933052,
    supportLambdaUpper := 361977564123088821946288422182,
    supportJLower := 42086077056335484437238039297, supportJUpper := 43711363518724929376174765417,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer31Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer31Panel0Data observer31Panel0Endpoints
theorem observer31_panel0_kernel_check : observer31Panel0Check = true := by
  decide +kernel
theorem observer31_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer31Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer31Panel0Data) s observer31Panel0Data.anchor ≤
        (observer31Panel0Endpoints.energyUpper : ℝ) ∧
      (observer31Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer31Panel0Data) s observer31Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer31Panel0Data) s observer31Panel0Data.anchor ≤
        (observer31Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer31Panel0Data) s observer31Panel0Data.anchor ≤
        (observer31Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer31Panel0Data) s observer31Panel0Data.anchor ≤
        (observer31Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer31Panel0Data observer31Panel0Endpoints
    observer31_panel0_kernel_check s hs
def observer31Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer31Panel0Endpoints
theorem observer31_panel0_recurrence_field_kernel_check :
    observer31Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer31_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer31Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer31Panel0Endpoints
    observer31_panel0_recurrence_field_kernel_check

def observer31Panel1Data : MainPanelData :=
  {
    observer := 31, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((264981887005813018 : ℚ) / 22255358094488506845004577430525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer31Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115202841366154137140849182, ellLower := 351854321864062602761646292962,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376118719441973370514923178, offsetUpper := 6390639712782350327386972092,
    supportELower := 40091538796288304748616071627, supportEUpper := 41498124181217210454708872842,
    supportLambdaLower := 351854321864062602761646292962,
    supportLambdaUpper := 361420236386870606192264241271,
    supportJLower := 43610082014928930776232534556, supportJUpper := 45112326545085916516631515255,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer31Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer31Panel1Data observer31Panel1Endpoints
theorem observer31_panel1_kernel_check : observer31Panel1Check = true := by
  decide +kernel
theorem observer31_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer31Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer31Panel1Data) s observer31Panel1Data.anchor ≤
        (observer31Panel1Endpoints.energyUpper : ℝ) ∧
      (observer31Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer31Panel1Data) s observer31Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer31Panel1Data) s observer31Panel1Data.anchor ≤
        (observer31Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer31Panel1Data) s observer31Panel1Data.anchor ≤
        (observer31Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer31Panel1Data) s observer31Panel1Data.anchor ≤
        (observer31Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer31Panel1Data observer31Panel1Endpoints
    observer31_panel1_kernel_check s hs
def observer31Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer31Panel1Endpoints
theorem observer31_panel1_recurrence_field_kernel_check :
    observer31Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer31_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer31Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer31Panel1Endpoints
    observer31_panel1_recurrence_field_kernel_check

def observer31Panel2Data : MainPanelData :=
  {
    observer := 31, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((264981887005813018 : ℚ) / 22255358094488506845004577430525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer31Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817759376345422790581257459, ellLower := 351674113098879738204945625627,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591872049076210189309604523, offsetUpper := 6606884399745494770043477877,
    supportELower := 41498070259765641654126016304, supportEUpper := 42885100912756204660236647157,
    supportLambdaLower := 351674113098879738204945625627,
    supportLambdaUpper := 360893666760448690143299499596,
    supportJLower := 45014811390754439036175472560, supportJUpper := 46494037580360691561669642153,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer31Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer31Panel2Data observer31Panel2Endpoints
theorem observer31_panel2_kernel_check : observer31Panel2Check = true := by
  decide +kernel
theorem observer31_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer31Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer31Panel2Data) s observer31Panel2Data.anchor ≤
        (observer31Panel2Endpoints.energyUpper : ℝ) ∧
      (observer31Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer31Panel2Data) s observer31Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer31Panel2Data) s observer31Panel2Data.anchor ≤
        (observer31Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer31Panel2Data) s observer31Panel2Data.anchor ≤
        (observer31Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer31Panel2Data) s observer31Panel2Data.anchor ≤
        (observer31Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer31Panel2Data observer31Panel2Endpoints
    observer31_panel2_kernel_check s hs
def observer31Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer31Panel2Endpoints
theorem observer31_panel2_recurrence_field_kernel_check :
    observer31Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer31_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer31Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer31Panel2Endpoints
    observer31_panel2_recurrence_field_kernel_check

def observer31Panel3Data : MainPanelData :=
  {
    observer := 31, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((264981887005813018 : ℚ) / 22255358094488506845004577430525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer31Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510226664829819821138638854, ellLower := 351497852367910625296392619714,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806510333005614153129839153, offsetUpper := 6822011501595121145717014287,
    supportELower := 42885042186629118184102434930, supportEUpper := 44261772224266729962738708934,
    supportLambdaLower := 351497852367910625296392619714,
    supportLambdaUpper := 360396427472370165405086418006,
    supportJLower := 46400020710308224437066361127, supportJUpper := 47865736498990431616789573115,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer31Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer31Panel3Data observer31Panel3Endpoints
theorem observer31_panel3_kernel_check : observer31Panel3Check = true := by
  decide +kernel
theorem observer31_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer31Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer31Panel3Data) s observer31Panel3Data.anchor ≤
        (observer31Panel3Endpoints.energyUpper : ℝ) ∧
      (observer31Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer31Panel3Data) s observer31Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer31Panel3Data) s observer31Panel3Data.anchor ≤
        (observer31Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer31Panel3Data) s observer31Panel3Data.anchor ≤
        (observer31Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer31Panel3Data) s observer31Panel3Data.anchor ≤
        (observer31Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer31Panel3Data observer31Panel3Endpoints
    observer31_panel3_kernel_check s hs
def observer31Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer31Panel3Endpoints
theorem observer31_panel3_recurrence_field_kernel_check :
    observer31Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer31_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer31Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer31Panel3Endpoints
    observer31_panel3_recurrence_field_kernel_check

def observer31Panel4Data : MainPanelData :=
  {
    observer := 31, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((264981887005813018 : ℚ) / 22255358094488506845004577430525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer31Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196133525652555782930753553, ellLower := 351326817866767839243701365201,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020439963086224134336343966, offsetUpper := 7036428335705392249084521573,
    supportELower := 44261708712700238820742824881, supportEUpper := 45631688138624894160740743956,
    supportLambdaLower := 351326817866767839243701365201,
    supportLambdaUpper := 359926393754031024236768802271,
    supportJLower := 47774976891367917213179838533, supportJUpper := 49230952076165204403108431979,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer31Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer31Panel4Data observer31Panel4Endpoints
theorem observer31_panel4_kernel_check : observer31Panel4Check = true := by
  decide +kernel
theorem observer31_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer31Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer31Panel4Data) s observer31Panel4Data.anchor ≤
        (observer31Panel4Endpoints.energyUpper : ℝ) ∧
      (observer31Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer31Panel4Data) s observer31Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer31Panel4Data) s observer31Panel4Data.anchor ≤
        (observer31Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer31Panel4Data) s observer31Panel4Data.anchor ≤
        (observer31Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer31Panel4Data) s observer31Panel4Data.anchor ≤
        (observer31Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer31Panel4Data observer31Panel4Endpoints
    observer31_panel4_kernel_check s hs
def observer31Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer31Panel4Endpoints
theorem observer31_panel4_recurrence_field_kernel_check :
    observer31Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer31_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer31Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer31Panel4Endpoints
    observer31_panel4_recurrence_field_kernel_check

def observer31Panel5Data : MainPanelData :=
  {
    observer := 31, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((264981887005813018 : ℚ) / 22255358094488506845004577430525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer31Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877510623070200923842827365, ellLower := 351161266512150600381212017312,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217424344241318425303402424, offsetUpper := 7233898865327560829394535630,
    supportELower := 45631619854764942143154955983, supportEUpper := 46996660169472082254616303398,
    supportLambdaLower := 351161266512150600381212017312,
    supportLambdaUpper := 359481440871423676886846104331,
    supportJLower := 49143232519886448146967076156, supportJUpper := 50591474578186319023484764442,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer31Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer31Panel5Data observer31Panel5Endpoints
theorem observer31_panel5_kernel_check : observer31Panel5Check = true := by
  decide +kernel
theorem observer31_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer31Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer31Panel5Data) s observer31Panel5Data.anchor ≤
        (observer31Panel5Endpoints.energyUpper : ℝ) ∧
      (observer31Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer31Panel5Data) s observer31Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer31Panel5Data) s observer31Panel5Data.anchor ≤
        (observer31Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer31Panel5Data) s observer31Panel5Data.anchor ≤
        (observer31Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer31Panel5Data) s observer31Panel5Data.anchor ≤
        (observer31Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer31Panel5Data observer31Panel5Endpoints
    observer31_panel5_kernel_check s hs
def observer31Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer31Panel5Endpoints
theorem observer31_panel5_recurrence_field_kernel_check :
    observer31Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer31_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer31Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer31Panel5Endpoints
    observer31_panel5_recurrence_field_kernel_check

def observer31Panel6Data : MainPanelData :=
  {
    observer := 31, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((264981887005813018 : ℚ) / 22255358094488506845004577430525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer31Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554932365452795877740319375, ellLower := 351001159692454685725680657799,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429989292527964929906621401, offsetUpper := 7446949015198002044010339927,
    supportELower := 46996587123396907573344727378, supportEUpper := 48357763336202657005233356508,
    supportLambdaLower := 351001159692454685725680657799,
    supportLambdaUpper := 359059587830308146406326897063,
    supportJLower := 50506598720321454430601533955, supportJUpper := 51948359214505738469296625479,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer31Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer31Panel6Data observer31Panel6Endpoints
theorem observer31_panel6_kernel_check : observer31Panel6Check = true := by
  decide +kernel
theorem observer31_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer31Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer31Panel6Data) s observer31Panel6Data.anchor ≤
        (observer31Panel6Endpoints.energyUpper : ℝ) ∧
      (observer31Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer31Panel6Data) s observer31Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer31Panel6Data) s observer31Panel6Data.anchor ≤
        (observer31Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer31Panel6Data) s observer31Panel6Data.anchor ≤
        (observer31Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer31Panel6Data) s observer31Panel6Data.anchor ≤
        (observer31Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer31Panel6Data observer31Panel6Endpoints
    observer31_panel6_kernel_check s hs
def observer31Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer31Panel6Endpoints
theorem observer31_panel6_recurrence_field_kernel_check :
    observer31Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer31_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer31Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer31Panel6Endpoints
    observer31_panel6_recurrence_field_kernel_check

def observer31Panel7Data : MainPanelData :=
  {
    observer := 31, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((264981887005813018 : ℚ) / 22255358094488506845004577430525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer31Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229323444475036607714722682, ellLower := 350846347140900730270165132760,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642254652332937956452043652, offsetUpper := 7659698892744927716357765335,
    supportELower := 48357685536168961160405366239, supportEUpper := 49715699872730326154622941827,
    supportLambdaLower := 350846347140900730270165132760,
    supportLambdaUpper := 358659027008290174174741784737,
    supportJLower := 51866149007577968463107017566, supportJUpper := 53302290142813227896370359675,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer31Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer31Panel7Data observer31Panel7Endpoints
theorem observer31_panel7_kernel_check : observer31Panel7Check = true := by
  decide +kernel
theorem observer31_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer31Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer31Panel7Data) s observer31Panel7Data.anchor ≤
        (observer31Panel7Endpoints.energyUpper : ℝ) ∧
      (observer31Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer31Panel7Data) s observer31Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer31Panel7Data) s observer31Panel7Data.anchor ≤
        (observer31Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer31Panel7Data) s observer31Panel7Data.anchor ≤
        (observer31Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer31Panel7Data) s observer31Panel7Data.anchor ≤
        (observer31Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer31Panel7Data observer31Panel7Endpoints
    observer31_panel7_kernel_check s hs
def observer31Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer31Panel7Endpoints
theorem observer31_panel7_recurrence_field_kernel_check :
    observer31Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer31_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer31Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer31Panel7Endpoints
    observer31_panel7_recurrence_field_kernel_check

def observer31InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 31, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer31Panel0Endpoints, observer31Panel1Endpoints, observer31Panel2Endpoints, observer31Panel3Endpoints, observer31Panel4Endpoints, observer31Panel5Endpoints, observer31Panel6Endpoints, observer31Panel7Endpoints]
  }
def observer31FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer31InsertionEndpoints.frameLower
    observer31InsertionEndpoints.frameUpper
theorem observer31_frame_recurrence_field_kernel_check :
    observer31FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer31_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer31InsertionEndpoints.frameLower
      observer31InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer31InsertionEndpoints.frameLower
    observer31InsertionEndpoints.frameUpper
    observer31_frame_recurrence_field_kernel_check
def observer31RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer31Panel0Endpoints ∧
  panelRecurrenceFields observer31Panel1Endpoints ∧
  panelRecurrenceFields observer31Panel2Endpoints ∧
  panelRecurrenceFields observer31Panel3Endpoints ∧
  panelRecurrenceFields observer31Panel4Endpoints ∧
  panelRecurrenceFields observer31Panel5Endpoints ∧
  panelRecurrenceFields observer31Panel6Endpoints ∧
  panelRecurrenceFields observer31Panel7Endpoints ∧ insertionFrameRecurrenceFields observer31InsertionEndpoints.frameLower
      observer31InsertionEndpoints.frameUpper
theorem observer31_all_recurrence_fields :
    observer31RecurrenceFieldBounds := by
  exact ⟨observer31_panel0_recurrence_fields_sound,
    observer31_panel1_recurrence_fields_sound,
    observer31_panel2_recurrence_fields_sound,
    observer31_panel3_recurrence_fields_sound,
    observer31_panel4_recurrence_fields_sound,
    observer31_panel5_recurrence_fields_sound,
    observer31_panel6_recurrence_fields_sound,
    observer31_panel7_recurrence_fields_sound,
    observer31_frame_recurrence_fields_sound⟩
def observer31PanelFormulaBounds : Prop :=
  panelFormulaBounds observer31Panel0Data observer31Panel0Endpoints ∧
  panelFormulaBounds observer31Panel1Data observer31Panel1Endpoints ∧
  panelFormulaBounds observer31Panel2Data observer31Panel2Endpoints ∧
  panelFormulaBounds observer31Panel3Data observer31Panel3Endpoints ∧
  panelFormulaBounds observer31Panel4Data observer31Panel4Endpoints ∧
  panelFormulaBounds observer31Panel5Data observer31Panel5Endpoints ∧
  panelFormulaBounds observer31Panel6Data observer31Panel6Endpoints ∧
  panelFormulaBounds observer31Panel7Data observer31Panel7Endpoints
theorem observer31_all_panel_formula_bounds : observer31PanelFormulaBounds := by
  exact ⟨observer31_panel0_formula_sound,
    observer31_panel1_formula_sound,
    observer31_panel2_formula_sound,
    observer31_panel3_formula_sound,
    observer31_panel4_formula_sound,
    observer31_panel5_formula_sound,
    observer31_panel6_formula_sound,
    observer31_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
