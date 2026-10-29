module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer27Panel0Data : MainPanelData :=
  {
    observer := 27, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3271381321059178 : ℚ) / 3392067991844003481939426525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer27Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393472537091231802721070844, ellLower := 352021385062701952788271897413,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172450950809925099618023185, offsetUpper := 6186476155413646527326269108,
    supportELower := 38566016888697509052864653050, supportEUpper := 40091739073843459414270420583,
    supportLambdaLower := 352021385062701952788271897413,
    supportLambdaUpper := 361977984002772969835787445295,
    supportJLower := 42086230739324528580747372024, supportJUpper := 43711518913871189112628295036,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer27Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer27Panel0Data observer27Panel0Endpoints
theorem observer27_panel0_kernel_check : observer27Panel0Check = true := by
  decide +kernel
theorem observer27_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer27Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer27Panel0Data) s observer27Panel0Data.anchor ≤
        (observer27Panel0Endpoints.energyUpper : ℝ) ∧
      (observer27Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer27Panel0Data) s observer27Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer27Panel0Data) s observer27Panel0Data.anchor ≤
        (observer27Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer27Panel0Data) s observer27Panel0Data.anchor ≤
        (observer27Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer27Panel0Data) s observer27Panel0Data.anchor ≤
        (observer27Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer27Panel0Data observer27Panel0Endpoints
    observer27_panel0_kernel_check s hs
def observer27Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer27Panel0Endpoints
theorem observer27_panel0_recurrence_field_kernel_check :
    observer27Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer27_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer27Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer27Panel0Endpoints
    observer27_panel0_recurrence_field_kernel_check

def observer27Panel1Data : MainPanelData :=
  {
    observer := 27, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3271381321059178 : ℚ) / 3392067991844003481939426525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer27Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115359836858862905932969526, ellLower := 351854731975050180530710373775,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376130871255779894357671689, offsetUpper := 6390651892270736814740285831,
    supportELower := 40091689992483081812669642220, supportEUpper := 41498277018530529568725599684,
    supportLambdaLower := 351854731975050180530710373775,
    supportLambdaUpper := 361420652188610856191294098780,
    supportJLower := 43610237312233583617976745957, supportJUpper := 45112483540416638130638540672,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer27Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer27Panel1Data observer27Panel1Endpoints
theorem observer27_panel1_kernel_check : observer27Panel1Check = true := by
  decide +kernel
theorem observer27_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer27Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer27Panel1Data) s observer27Panel1Data.anchor ≤
        (observer27Panel1Endpoints.energyUpper : ℝ) ∧
      (observer27Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer27Panel1Data) s observer27Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer27Panel1Data) s observer27Panel1Data.anchor ≤
        (observer27Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer27Panel1Data) s observer27Panel1Data.anchor ≤
        (observer27Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer27Panel1Data) s observer27Panel1Data.anchor ≤
        (observer27Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer27Panel1Data observer27Panel1Endpoints
    observer27_panel1_kernel_check s hs
def observer27Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer27Panel1Endpoints
theorem observer27_panel1_recurrence_field_kernel_check :
    observer27Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer27_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer27Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer27Panel1Endpoints
    observer27_panel1_recurrence_field_kernel_check

def observer27Panel2Data : MainPanelData :=
  {
    observer := 27, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3271381321059178 : ℚ) / 3392067991844003481939426525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer27Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817917961842448678464526746, ellLower := 351674519473515942239232238590,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591884223986709288949124107, offsetUpper := 6606896602383174315373296935,
    supportELower := 41498223096919282990671807274, supportEUpper := 42885255379318453953608548737,
    supportLambdaLower := 351674519473515942239232238590,
    supportLambdaUpper := 360894078637727634115926777519,
    supportJLower := 45014968291654442413064129659, supportJUpper := 46494196165695730294767816513,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer27Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer27Panel2Data observer27Panel2Endpoints
theorem observer27_panel2_kernel_check : observer27Panel2Check = true := by
  decide +kernel
theorem observer27_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer27Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer27Panel2Data) s observer27Panel2Data.anchor ≤
        (observer27Panel2Endpoints.energyUpper : ℝ) ∧
      (observer27Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer27Panel2Data) s observer27Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer27Panel2Data) s observer27Panel2Data.anchor ≤
        (observer27Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer27Panel2Data) s observer27Panel2Data.anchor ≤
        (observer27Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer27Panel2Data) s observer27Panel2Data.anchor ≤
        (observer27Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer27Panel2Data observer27Panel2Endpoints
    observer27_panel2_kernel_check s hs
def observer27Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer27Panel2Endpoints
theorem observer27_panel2_recurrence_field_kernel_check :
    observer27Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer27_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer27Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer27Panel2Endpoints
    observer27_panel2_recurrence_field_kernel_check

def observer27Panel3Data : MainPanelData :=
  {
    observer := 27, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3271381321059178 : ℚ) / 3392067991844003481939426525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer27Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510386830430254071422115615, ellLower := 351498255137481757956029252598,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806522532985018711869990998, offsetUpper := 6822023729358798156309797609,
    supportELower := 42885196653026711751739797948, supportEUpper := 44261928308746522009583059986,
    supportLambdaLower := 351498255137481757956029252598,
    supportLambdaUpper := 360396835568235670270489496249,
    supportJLower := 46400179204401529331300090473, supportJUpper := 47865896664428878712287954949,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer27Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer27Panel3Data observer27Panel3Endpoints
theorem observer27_panel3_kernel_check : observer27Panel3Check = true := by
  decide +kernel
theorem observer27_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer27Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer27Panel3Data) s observer27Panel3Data.anchor ≤
        (observer27Panel3Endpoints.energyUpper : ℝ) ∧
      (observer27Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer27Panel3Data) s observer27Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer27Panel3Data) s observer27Panel3Data.anchor ≤
        (observer27Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer27Panel3Data) s observer27Panel3Data.anchor ≤
        (observer27Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer27Panel3Data) s observer27Panel3Data.anchor ≤
        (observer27Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer27Panel3Data observer27Panel3Endpoints
    observer27_panel3_kernel_check s hs
def observer27Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer27Panel3Endpoints
theorem observer27_panel3_recurrence_field_kernel_check :
    observer27Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer27_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer27Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer27Panel3Endpoints
    observer27_panel3_recurrence_field_kernel_check

def observer27Panel4Data : MainPanelData :=
  {
    observer := 27, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3271381321059178 : ℚ) / 3392067991844003481939426525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer27Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196295261721674425151270236, ellLower := 351327217154291503428789737440,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020452189526043951532820100, offsetUpper := 7036440589989745553201884416,
    supportELower := 44261864797010453259395382378, supportEUpper := 45631845830050797856441991125,
    supportLambdaLower := 351327217154291503428789737440,
    supportLambdaUpper := 359926798202153803410186260947,
    supportJLower := 47775136968553368293683279752, supportJUpper := 49231113812072335890543853735,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer27Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer27Panel4Data observer27Panel4Endpoints
theorem observer27_panel4_kernel_check : observer27Panel4Check = true := by
  decide +kernel
theorem observer27_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer27Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer27Panel4Data) s observer27Panel4Data.anchor ≤
        (observer27Panel4Endpoints.energyUpper : ℝ) ∧
      (observer27Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer27Panel4Data) s observer27Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer27Panel4Data) s observer27Panel4Data.anchor ≤
        (observer27Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer27Panel4Data) s observer27Panel4Data.anchor ≤
        (observer27Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer27Panel4Data) s observer27Panel4Data.anchor ≤
        (observer27Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer27Panel4Data observer27Panel4Endpoints
    observer27_panel4_kernel_check s hs
def observer27Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer27Panel4Endpoints
theorem observer27_panel4_recurrence_field_kernel_check :
    observer27Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer27_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer27Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer27Panel4Endpoints
    observer27_panel4_recurrence_field_kernel_check

def observer27Panel5Data : MainPanelData :=
  {
    observer := 27, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3271381321059178 : ℚ) / 3392067991844003481939426525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer27Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877673920227232537970903985, ellLower := 351161662433150644364832784715,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217436570289668349609598628, offsetUpper := 7233911119283136619248731706,
    supportELower := 45631777546016400037544713097, supportEUpper := 46996819457211240942558789759,
    supportLambdaLower := 351161662433150644364832784715,
    supportLambdaUpper := 359481841797012254026895637550,
    supportJLower := 49143394170347906481193040944, supportJUpper := 50591637875181363482827746135,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer27Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer27Panel5Data observer27Panel5Endpoints
theorem observer27_panel5_kernel_check : observer27Panel5Check = true := by
  decide +kernel
theorem observer27_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer27Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer27Panel5Data) s observer27Panel5Data.anchor ≤
        (observer27Panel5Endpoints.energyUpper : ℝ) ∧
      (observer27Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer27Panel5Data) s observer27Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer27Panel5Data) s observer27Panel5Data.anchor ≤
        (observer27Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer27Panel5Data) s observer27Panel5Data.anchor ≤
        (observer27Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer27Panel5Data) s observer27Panel5Data.anchor ≤
        (observer27Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer27Panel5Data observer27Panel5Endpoints
    observer27_panel5_kernel_check s hs
def observer27Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer27Panel5Endpoints
theorem observer27_panel5_recurrence_field_kernel_check :
    observer27Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer27_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer27Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer27Panel5Endpoints
    observer27_panel5_recurrence_field_kernel_check

def observer27Panel6Data : MainPanelData :=
  {
    observer := 27, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3271381321059178 : ℚ) / 3392067991844003481939426525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer27Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59555097214559455822438803610, ellLower := 351001552355639229665834955076,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7430001546965449168176250462, offsetUpper := 7446961297607513297042470586,
    supportELower := 46996746410956803751699310103, supportEUpper := 48357924209941361976256566478,
    supportLambdaLower := 351001552355639229665834955076,
    supportLambdaUpper := 359059985350904928295344830861,
    supportJLower := 50506761934513196048357659653, supportJUpper := 51948524063450411259210014787,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer27Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer27Panel6Data observer27Panel6Endpoints
theorem observer27_panel6_kernel_check : observer27Panel6Check = true := by
  decide +kernel
theorem observer27_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer27Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer27Panel6Data) s observer27Panel6Data.anchor ≤
        (observer27Panel6Endpoints.energyUpper : ℝ) ∧
      (observer27Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer27Panel6Data) s observer27Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer27Panel6Data) s observer27Panel6Data.anchor ≤
        (observer27Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer27Panel6Data) s observer27Panel6Data.anchor ≤
        (observer27Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer27Panel6Data) s observer27Panel6Data.anchor ≤
        (observer27Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer27Panel6Data observer27Panel6Endpoints
    observer27_panel6_kernel_check s hs
def observer27Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer27Panel6Endpoints
theorem observer27_panel6_recurrence_field_kernel_check :
    observer27Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer27_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer27Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer27Panel6Endpoints
    observer27_panel6_recurrence_field_kernel_check

def observer27Panel7Data : MainPanelData :=
  {
    observer := 27, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3271381321059178 : ℚ) / 3392067991844003481939426525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer27Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229489836624775454890443331, ellLower := 350846736648758296441688030330,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642266935936112787235697906, offsetUpper := 7659711204386703281522412109,
    supportELower := 48357846409723636347589918503, supportEUpper := 49715862322456302342870150452,
    supportLambdaLower := 350846736648758296441688030330,
    supportLambdaUpper := 358659421234467724589083494435,
    supportJLower := 51866313776211219312006798806, supportJUpper := 53302456534800979588760985397,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer27Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer27Panel7Data observer27Panel7Endpoints
theorem observer27_panel7_kernel_check : observer27Panel7Check = true := by
  decide +kernel
theorem observer27_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer27Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer27Panel7Data) s observer27Panel7Data.anchor ≤
        (observer27Panel7Endpoints.energyUpper : ℝ) ∧
      (observer27Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer27Panel7Data) s observer27Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer27Panel7Data) s observer27Panel7Data.anchor ≤
        (observer27Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer27Panel7Data) s observer27Panel7Data.anchor ≤
        (observer27Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer27Panel7Data) s observer27Panel7Data.anchor ≤
        (observer27Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer27Panel7Data observer27Panel7Endpoints
    observer27_panel7_kernel_check s hs
def observer27Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer27Panel7Endpoints
theorem observer27_panel7_recurrence_field_kernel_check :
    observer27Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer27_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer27Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer27Panel7Endpoints
    observer27_panel7_recurrence_field_kernel_check

def observer27InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 27, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer27Panel0Endpoints, observer27Panel1Endpoints, observer27Panel2Endpoints, observer27Panel3Endpoints, observer27Panel4Endpoints, observer27Panel5Endpoints, observer27Panel6Endpoints, observer27Panel7Endpoints]
  }
def observer27FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer27InsertionEndpoints.frameLower
    observer27InsertionEndpoints.frameUpper
theorem observer27_frame_recurrence_field_kernel_check :
    observer27FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer27_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer27InsertionEndpoints.frameLower
      observer27InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer27InsertionEndpoints.frameLower
    observer27InsertionEndpoints.frameUpper
    observer27_frame_recurrence_field_kernel_check
def observer27RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer27Panel0Endpoints ∧
  panelRecurrenceFields observer27Panel1Endpoints ∧
  panelRecurrenceFields observer27Panel2Endpoints ∧
  panelRecurrenceFields observer27Panel3Endpoints ∧
  panelRecurrenceFields observer27Panel4Endpoints ∧
  panelRecurrenceFields observer27Panel5Endpoints ∧
  panelRecurrenceFields observer27Panel6Endpoints ∧
  panelRecurrenceFields observer27Panel7Endpoints ∧ insertionFrameRecurrenceFields observer27InsertionEndpoints.frameLower
      observer27InsertionEndpoints.frameUpper
theorem observer27_all_recurrence_fields :
    observer27RecurrenceFieldBounds := by
  exact ⟨observer27_panel0_recurrence_fields_sound,
    observer27_panel1_recurrence_fields_sound,
    observer27_panel2_recurrence_fields_sound,
    observer27_panel3_recurrence_fields_sound,
    observer27_panel4_recurrence_fields_sound,
    observer27_panel5_recurrence_fields_sound,
    observer27_panel6_recurrence_fields_sound,
    observer27_panel7_recurrence_fields_sound,
    observer27_frame_recurrence_fields_sound⟩
def observer27PanelFormulaBounds : Prop :=
  panelFormulaBounds observer27Panel0Data observer27Panel0Endpoints ∧
  panelFormulaBounds observer27Panel1Data observer27Panel1Endpoints ∧
  panelFormulaBounds observer27Panel2Data observer27Panel2Endpoints ∧
  panelFormulaBounds observer27Panel3Data observer27Panel3Endpoints ∧
  panelFormulaBounds observer27Panel4Data observer27Panel4Endpoints ∧
  panelFormulaBounds observer27Panel5Data observer27Panel5Endpoints ∧
  panelFormulaBounds observer27Panel6Data observer27Panel6Endpoints ∧
  panelFormulaBounds observer27Panel7Data observer27Panel7Endpoints
theorem observer27_all_panel_formula_bounds : observer27PanelFormulaBounds := by
  exact ⟨observer27_panel0_formula_sound,
    observer27_panel1_formula_sound,
    observer27_panel2_formula_sound,
    observer27_panel3_formula_sound,
    observer27_panel4_formula_sound,
    observer27_panel5_formula_sound,
    observer27_panel6_formula_sound,
    observer27_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
