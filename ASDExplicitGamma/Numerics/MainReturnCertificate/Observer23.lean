module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer23Panel0Data : MainPanelData :=
  {
    observer := 23, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((40387423716538 : ℚ) / 517004723646395897262525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer23Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49394874856745885101641317307, ellLower := 352025132329995319494011655685,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172560484662005760632993035, offsetUpper := 6186585938151412746271834985,
    supportELower := 38567366211501385949107444333, supportEUpper := 40093103371477957196913031637,
    supportLambdaLower := 352025132329995319494011655685,
    supportLambdaUpper := 361981784892692567712240354710,
    supportJLower := 42087617534801339144047560889, supportJUpper := 43712921220404882874035435185,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer23Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer23Panel0Data observer23Panel0Endpoints
theorem observer23_panel0_kernel_check : observer23Panel0Check = true := by
  decide +kernel
theorem observer23_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer23Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer23Panel0Data) s observer23Panel0Data.anchor ≤
        (observer23Panel0Endpoints.energyUpper : ℝ) ∧
      (observer23Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer23Panel0Data) s observer23Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer23Panel0Data) s observer23Panel0Data.anchor ≤
        (observer23Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer23Panel0Data) s observer23Panel0Data.anchor ≤
        (observer23Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer23Panel0Data) s observer23Panel0Data.anchor ≤
        (observer23Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer23Panel0Data observer23Panel0Endpoints
    observer23_panel0_kernel_check s hs
def observer23Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer23Panel0Endpoints
theorem observer23_panel0_recurrence_field_kernel_check :
    observer23Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer23_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer23Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer23Panel0Endpoints
    observer23_panel0_recurrence_field_kernel_check

def observer23Panel1Data : MainPanelData :=
  {
    observer := 23, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((40387423716538 : ℚ) / 517004723646395897262525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer23Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51116776651128522423689445800, ellLower := 351858444140163794922185911819,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376240333586452416655268038, offsetUpper := 6390761603891274325145720562,
    supportELower := 40093054288722092484164526345, supportEUpper := 41499656180146255770874405811,
    supportLambdaLower := 351858444140163794922185911819,
    supportLambdaUpper := 361424416141908234000750482050,
    supportJLower := 43611638730123730433386385463, supportJUpper := 45113900341565338110881910632,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer23Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer23Panel1Data observer23Panel1Endpoints
theorem observer23_panel1_kernel_check : observer23Panel1Check = true := by
  decide +kernel
theorem observer23_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer23Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer23Panel1Data) s observer23Panel1Data.anchor ≤
        (observer23Panel1Endpoints.energyUpper : ℝ) ∧
      (observer23Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer23Panel1Data) s observer23Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer23Panel1Data) s observer23Panel1Data.anchor ≤
        (observer23Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer23Panel1Data) s observer23Panel1Data.anchor ≤
        (observer23Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer23Panel1Data) s observer23Panel1Data.anchor ≤
        (observer23Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer23Panel1Data observer23Panel1Endpoints
    observer23_panel1_kernel_check s hs
def observer23Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer23Panel1Endpoints
theorem observer23_panel1_recurrence_field_kernel_check :
    observer23Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer23_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer23Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer23Panel1Endpoints
    observer23_panel1_recurrence_field_kernel_check

def observer23Panel2Data : MainPanelData :=
  {
    observer := 23, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((40387423716538 : ℚ) / 517004723646395897262525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer23Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52819349178904139973924629712, ellLower := 351678197813228384200632734178,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591993896552327236895657453, offsetUpper := 6607006524717446994336900108,
    supportELower := 41499602257093912811473724358, supportEUpper := 42886649299132542569926503292,
    supportLambdaLower := 351678197813228384200632734178,
    supportLambdaUpper := 360897807050391948278830987289,
    supportJLower := 45016384235226196653480051699, supportJUpper := 46495627369636462052714813165,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer23Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer23Panel2Data observer23Panel2Endpoints
theorem observer23_panel2_kernel_check : observer23Panel2Check = true := by
  decide +kernel
theorem observer23_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer23Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer23Panel2Data) s observer23Panel2Data.anchor ≤
        (observer23Panel2Endpoints.energyUpper : ℝ) ∧
      (observer23Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer23Panel2Data) s observer23Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer23Panel2Data) s observer23Panel2Data.anchor ≤
        (observer23Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer23Panel2Data) s observer23Panel2Data.anchor ≤
        (observer23Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer23Panel2Data) s observer23Panel2Data.anchor ≤
        (observer23Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer23Panel2Data observer23Panel2Endpoints
    observer23_panel2_kernel_check s hs
def observer23Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer23Panel2Endpoints
theorem observer23_panel2_recurrence_field_kernel_check :
    observer23Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer23_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer23Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer23Panel2Endpoints
    observer23_panel2_recurrence_field_kernel_check

def observer23Panel3Data : MainPanelData :=
  {
    observer := 23, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((40387423716538 : ℚ) / 517004723646395897262525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer23Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54511832360986535270515706702, ellLower := 351501900844990614029693037616,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806632433596803582815567196, offsetUpper := 6822133880258590834476955243,
    supportELower := 42886590571354623810786568249, supportEUpper := 44263336884454349335283781431,
    supportLambdaLower := 351501900844990614029693037616,
    supportLambdaUpper := 360400529740985103858465829033,
    supportJLower := 46401609579804529951083498625, supportJUpper := 47867342181864200373868439722,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer23Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer23Panel3Data observer23Panel3Endpoints
theorem observer23_panel3_kernel_check : observer23Panel3Check = true := by
  decide +kernel
theorem observer23_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer23Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer23Panel3Data) s observer23Panel3Data.anchor ≤
        (observer23Panel3Endpoints.energyUpper : ℝ) ∧
      (observer23Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer23Panel3Data) s observer23Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer23Panel3Data) s observer23Panel3Data.anchor ≤
        (observer23Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer23Panel3Data) s observer23Panel3Data.anchor ≤
        (observer23Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer23Panel3Data) s observer23Panel3Data.anchor ≤
        (observer23Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer23Panel3Data observer23Panel3Endpoints
    observer23_panel3_kernel_check s hs
def observer23Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer23Panel3Endpoints
theorem observer23_panel3_recurrence_field_kernel_check :
    observer23Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer23_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer23Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer23Panel3Endpoints
    observer23_panel3_recurrence_field_kernel_check

def observer23Panel4Data : MainPanelData :=
  {
    observer := 23, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((40387423716538 : ℚ) / 517004723646395897262525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer23Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56197755018882232510844105763, ellLower := 351330831347362803882540891921,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020562330743381676528846470, offsetUpper := 7036550982043046947658700827,
    supportELower := 44263273371187529669341094160, supportEUpper := 45633268962610739361601072349,
    supportLambdaLower := 351330831347362803882540891921,
    supportLambdaUpper := 359930459350119507712251059809,
    supportJLower := 47776581684661157708166503079, supportJUpper := 49232573556111934438723582948,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer23Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer23Panel4Data observer23Panel4Endpoints
theorem observer23_panel4_kernel_check : observer23Panel4Check = true := by
  decide +kernel
theorem observer23_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer23Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer23Panel4Data) s observer23Panel4Data.anchor ≤
        (observer23Panel4Endpoints.energyUpper : ℝ) ∧
      (observer23Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer23Panel4Data) s observer23Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer23Panel4Data) s observer23Panel4Data.anchor ≤
        (observer23Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer23Panel4Data) s observer23Panel4Data.anchor ≤
        (observer23Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer23Panel4Data) s observer23Panel4Data.anchor ≤
        (observer23Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer23Panel4Data observer23Panel4Endpoints
    observer23_panel4_kernel_check s hs
def observer23Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer23Panel4Endpoints
theorem observer23_panel4_recurrence_field_kernel_check :
    observer23Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer23_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer23Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer23Panel4Endpoints
    observer23_panel4_recurrence_field_kernel_check

def observer23Panel5Data : MainPanelData :=
  {
    observer := 23, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((40387423716538 : ℚ) / 517004723646395897262525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer23Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57879147819397927413944046959, ellLower := 351165246161209627551642612232,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217546710225999318266795806, offsetUpper := 7234021510625317788428671440,
    supportELower := 45633200677001500569036914594, supportEUpper := 46998257050649959235824291829,
    supportLambdaLower := 351165246161209627551642612232,
    supportLambdaUpper := 359485471058113958546349096592,
    supportJLower := 49144853138613596844553340716, supportJUpper := 50593111761231098821287782795,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer23Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer23Panel5Data observer23Panel5Endpoints
theorem observer23_panel5_kernel_check : observer23Panel5Check = true := by
  decide +kernel
theorem observer23_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer23Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer23Panel5Data) s observer23Panel5Data.anchor ≤
        (observer23Panel5Endpoints.energyUpper : ℝ) ∧
      (observer23Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer23Panel5Data) s observer23Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer23Panel5Data) s observer23Panel5Data.anchor ≤
        (observer23Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer23Panel5Data) s observer23Panel5Data.anchor ≤
        (observer23Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer23Panel5Data) s observer23Panel5Data.anchor ≤
        (observer23Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer23Panel5Data observer23Panel5Endpoints
    observer23_panel5_kernel_check s hs
def observer23Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer23Panel5Endpoints
theorem observer23_panel5_recurrence_field_kernel_check :
    observer23Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer23_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer23Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer23Panel5Endpoints
    observer23_panel5_recurrence_field_kernel_check

def observer23Panel6Data : MainPanelData :=
  {
    observer := 23, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((40387423716538 : ℚ) / 517004723646395897262525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer23Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59556585173338334600020935672, ellLower := 351005106605972439712207512668,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7430111944898689891068198397, offsetUpper := 7447071947535508977501526139,
    supportELower := 46998184002777055361066693068, supportEUpper := 48359376171176969936409961381,
    supportLambdaLower := 351005106605972439712207512668,
    supportLambdaUpper := 359063583793136056286907915395,
    supportJLower := 50508235068836779758188768194, supportJUpper := 51950012009108330499279040535,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer23Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer23Panel6Data observer23Panel6Endpoints
theorem observer23_panel6_kernel_check : observer23Panel6Check = true := by
  decide +kernel
theorem observer23_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer23Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer23Panel6Data) s observer23Panel6Data.anchor ≤
        (observer23Panel6Endpoints.energyUpper : ℝ) ∧
      (observer23Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer23Panel6Data) s observer23Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer23Panel6Data) s observer23Panel6Data.anchor ≤
        (observer23Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer23Panel6Data) s observer23Panel6Data.anchor ≤
        (observer23Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer23Panel6Data) s observer23Panel6Data.anchor ≤
        (observer23Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer23Panel6Data observer23Panel6Endpoints
    observer23_panel6_kernel_check s hs
def observer23Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer23Panel6Endpoints
theorem observer23_panel6_recurrence_field_kernel_check :
    observer23Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer23_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer23Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer23Panel6Endpoints
    observer23_panel6_recurrence_field_kernel_check

def observer23Panel7Data : MainPanelData :=
  {
    observer := 23, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((40387423716538 : ℚ) / 517004723646395897262525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer23Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61230991774704581369162345802, ellLower := 350850262351964937655789907016,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642377598866235490360571425, offsetUpper := 7659822119916463863287915446,
    supportELower := 48359298369297597705296903260, supportEUpper := 49717328561137172532934664433,
    supportLambdaLower := 350850262351964937655789907016,
    supportLambdaUpper := 358662989862265343258511712087,
    supportJLower := 51867800992817247081854802330, supportJUpper := 53303958459759825965519781554,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer23Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer23Panel7Data observer23Panel7Endpoints
theorem observer23_panel7_kernel_check : observer23Panel7Check = true := by
  decide +kernel
theorem observer23_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer23Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer23Panel7Data) s observer23Panel7Data.anchor ≤
        (observer23Panel7Endpoints.energyUpper : ℝ) ∧
      (observer23Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer23Panel7Data) s observer23Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer23Panel7Data) s observer23Panel7Data.anchor ≤
        (observer23Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer23Panel7Data) s observer23Panel7Data.anchor ≤
        (observer23Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer23Panel7Data) s observer23Panel7Data.anchor ≤
        (observer23Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer23Panel7Data observer23Panel7Endpoints
    observer23_panel7_kernel_check s hs
def observer23Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer23Panel7Endpoints
theorem observer23_panel7_recurrence_field_kernel_check :
    observer23Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer23_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer23Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer23Panel7Endpoints
    observer23_panel7_recurrence_field_kernel_check

def observer23InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 23, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer23Panel0Endpoints, observer23Panel1Endpoints, observer23Panel2Endpoints, observer23Panel3Endpoints, observer23Panel4Endpoints, observer23Panel5Endpoints, observer23Panel6Endpoints, observer23Panel7Endpoints]
  }
def observer23FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer23InsertionEndpoints.frameLower
    observer23InsertionEndpoints.frameUpper
theorem observer23_frame_recurrence_field_kernel_check :
    observer23FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer23_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer23InsertionEndpoints.frameLower
      observer23InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer23InsertionEndpoints.frameLower
    observer23InsertionEndpoints.frameUpper
    observer23_frame_recurrence_field_kernel_check
def observer23RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer23Panel0Endpoints ∧
  panelRecurrenceFields observer23Panel1Endpoints ∧
  panelRecurrenceFields observer23Panel2Endpoints ∧
  panelRecurrenceFields observer23Panel3Endpoints ∧
  panelRecurrenceFields observer23Panel4Endpoints ∧
  panelRecurrenceFields observer23Panel5Endpoints ∧
  panelRecurrenceFields observer23Panel6Endpoints ∧
  panelRecurrenceFields observer23Panel7Endpoints ∧ insertionFrameRecurrenceFields observer23InsertionEndpoints.frameLower
      observer23InsertionEndpoints.frameUpper
theorem observer23_all_recurrence_fields :
    observer23RecurrenceFieldBounds := by
  exact ⟨observer23_panel0_recurrence_fields_sound,
    observer23_panel1_recurrence_fields_sound,
    observer23_panel2_recurrence_fields_sound,
    observer23_panel3_recurrence_fields_sound,
    observer23_panel4_recurrence_fields_sound,
    observer23_panel5_recurrence_fields_sound,
    observer23_panel6_recurrence_fields_sound,
    observer23_panel7_recurrence_fields_sound,
    observer23_frame_recurrence_fields_sound⟩
def observer23PanelFormulaBounds : Prop :=
  panelFormulaBounds observer23Panel0Data observer23Panel0Endpoints ∧
  panelFormulaBounds observer23Panel1Data observer23Panel1Endpoints ∧
  panelFormulaBounds observer23Panel2Data observer23Panel2Endpoints ∧
  panelFormulaBounds observer23Panel3Data observer23Panel3Endpoints ∧
  panelFormulaBounds observer23Panel4Data observer23Panel4Endpoints ∧
  panelFormulaBounds observer23Panel5Data observer23Panel5Endpoints ∧
  panelFormulaBounds observer23Panel6Data observer23Panel6Endpoints ∧
  panelFormulaBounds observer23Panel7Data observer23Panel7Endpoints
theorem observer23_all_panel_formula_bounds : observer23PanelFormulaBounds := by
  exact ⟨observer23_panel0_formula_sound,
    observer23_panel1_formula_sound,
    observer23_panel2_formula_sound,
    observer23_panel3_formula_sound,
    observer23_panel4_formula_sound,
    observer23_panel5_formula_sound,
    observer23_panel6_formula_sound,
    observer23_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
