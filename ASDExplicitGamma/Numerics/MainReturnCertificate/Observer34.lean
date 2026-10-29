module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer34Panel0Data : MainPanelData :=
  {
    observer := 34, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((7154510949156957856 : ℚ) / 16224156050882121490008336946852725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer34Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393301462019146346639884605, ellLower := 352020929321954030762141836477,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172437563509334309130753633, offsetUpper := 6186462737694080944869167880,
    supportELower := 38565852256012007226073929729, supportEUpper := 40091572621199121026582174352,
    supportLambdaLower := 352020929321954030762141836477,
    supportLambdaUpper := 361977521776391963013170195741,
    supportJLower := 42086061549231547533695348093, supportJUpper := 43711347838963040656713876310,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer34Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer34Panel0Data observer34Panel0Endpoints
theorem observer34_panel0_kernel_check : observer34Panel0Check = true := by
  decide +kernel
theorem observer34_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer34Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer34Panel0Data) s observer34Panel0Data.anchor ≤
        (observer34Panel0Endpoints.energyUpper : ℝ) ∧
      (observer34Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer34Panel0Data) s observer34Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer34Panel0Data) s observer34Panel0Data.anchor ≤
        (observer34Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer34Panel0Data) s observer34Panel0Data.anchor ≤
        (observer34Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer34Panel0Data) s observer34Panel0Data.anchor ≤
        (observer34Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer34Panel0Data observer34Panel0Endpoints
    observer34_panel0_kernel_check s hs
def observer34Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer34Panel0Endpoints
theorem observer34_panel0_recurrence_field_kernel_check :
    observer34Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer34_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer34Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer34Panel0Endpoints
    observer34_panel0_recurrence_field_kernel_check

def observer34Panel1Data : MainPanelData :=
  {
    observer := 34, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((7154510949156957856 : ℚ) / 16224156050882121490008336946852725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer34Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115187000232475068963207808, ellLower := 351854280502076977015843470278,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376117492956357074338897111, offsetUpper := 6390638483503531732138387313,
    supportELower := 40091523540008988331099910254, supportEUpper := 41498108759440036630511279953,
    supportLambdaLower := 351854280502076977015843470278,
    supportLambdaUpper := 361420194451415066332426651301,
    supportJLower := 43610066345029758101258344956, supportJUpper := 45112310703954187293835546467,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer34Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer34Panel1Data observer34Panel1Endpoints
theorem observer34_panel1_kernel_check : observer34Panel1Check = true := by
  decide +kernel
theorem observer34_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer34Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer34Panel1Data) s observer34Panel1Data.anchor ≤
        (observer34Panel1Endpoints.energyUpper : ℝ) ∧
      (observer34Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer34Panel1Data) s observer34Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer34Panel1Data) s observer34Panel1Data.anchor ≤
        (observer34Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer34Panel1Data) s observer34Panel1Data.anchor ≤
        (observer34Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer34Panel1Data) s observer34Panel1Data.anchor ≤
        (observer34Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer34Panel1Data observer34Panel1Endpoints
    observer34_panel1_kernel_check s hs
def observer34Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer34Panel1Endpoints
theorem observer34_panel1_recurrence_field_kernel_check :
    observer34Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer34_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer34Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer34Panel1Endpoints
    observer34_panel1_recurrence_field_kernel_check

def observer34Panel2Data : MainPanelData :=
  {
    observer := 34, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((7154510949156957856 : ℚ) / 16224156050882121490008336946852725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer34Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817743374869180648346693446, ellLower := 351674072113716808291183345101,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591870820263161721403451469, offsetUpper := 6606883168133943501528804737,
    supportELower := 41498054838004579475901231984, supportEUpper := 42885085326678735494951782716,
    supportLambdaLower := 351674072113716808291183345101,
    supportLambdaUpper := 360893625220766376986496800960,
    supportJLower := 45014795559141747558813065435, supportJUpper := 46494021578886399264816750726,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer34Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer34Panel2Data observer34Panel2Endpoints
theorem observer34_panel2_kernel_check : observer34Panel2Check = true := by
  decide +kernel
theorem observer34_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer34Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer34Panel2Data) s observer34Panel2Data.anchor ≤
        (observer34Panel2Endpoints.energyUpper : ℝ) ∧
      (observer34Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer34Panel2Data) s observer34Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer34Panel2Data) s observer34Panel2Data.anchor ≤
        (observer34Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer34Panel2Data) s observer34Panel2Data.anchor ≤
        (observer34Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer34Panel2Data) s observer34Panel2Data.anchor ≤
        (observer34Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer34Panel2Data observer34Panel2Endpoints
    observer34_panel2_kernel_check s hs
def observer34Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer34Panel2Endpoints
theorem observer34_panel2_recurrence_field_kernel_check :
    observer34Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer34_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer34Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer34Panel2Endpoints
    observer34_panel2_recurrence_field_kernel_check

def observer34Panel3Data : MainPanelData :=
  {
    observer := 34, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((7154510949156957856 : ℚ) / 16224156050882121490008336946852725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer34Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510210504010126101235589081, ellLower := 351497811746337708817384215106,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806509101666155953158805546, offsetUpper := 6822010267451406491463712046,
    supportELower := 42885026600568262681587575967, supportEUpper := 44261756475032247876543247525,
    supportLambdaLower := 351497811746337708817384215106,
    supportLambdaUpper := 360396386314043986572494840257,
    supportJLower := 46400004718031639769761418118, supportJUpper := 47865720338172687742268195928,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer34Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer34Panel3Data observer34Panel3Endpoints
theorem observer34_panel3_kernel_check : observer34Panel3Check = true := by
  decide +kernel
theorem observer34_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer34Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer34Panel3Data) s observer34Panel3Data.anchor ≤
        (observer34Panel3Endpoints.energyUpper : ℝ) ∧
      (observer34Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer34Panel3Data) s observer34Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer34Panel3Data) s observer34Panel3Data.anchor ≤
        (observer34Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer34Panel3Data) s observer34Panel3Data.anchor ≤
        (observer34Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer34Panel3Data) s observer34Panel3Data.anchor ≤
        (observer34Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer34Panel3Data observer34Panel3Endpoints
    observer34_panel3_kernel_check s hs
def observer34Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer34Panel3Endpoints
theorem observer34_panel3_recurrence_field_kernel_check :
    observer34Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer34_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer34Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer34Panel3Endpoints
    observer34_panel3_recurrence_field_kernel_check

def observer34Panel4Data : MainPanelData :=
  {
    observer := 34, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((7154510949156957856 : ℚ) / 16224156050882121490008336946852725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer34Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196117206461671877150086038, ellLower := 351326777596385196644916617215,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020438729079953373788845906, offsetUpper := 7036427098888791626726427863,
    supportELower := 44261692963482866756715026244, supportEUpper := 45631672227340386189701339102,
    supportLambdaLower := 351326777596385196644916617215,
    supportLambdaUpper := 359926352963588415300809794772,
    supportJLower := 47774960739446718723164192416, supportJUpper := 49230935756976270342709437050,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer34Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer34Panel4Data observer34Panel4Endpoints
theorem observer34_panel4_kernel_check : observer34Panel4Check = true := by
  decide +kernel
theorem observer34_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer34Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer34Panel4Data) s observer34Panel4Data.anchor ≤
        (observer34Panel4Endpoints.energyUpper : ℝ) ∧
      (observer34Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer34Panel4Data) s observer34Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer34Panel4Data) s observer34Panel4Data.anchor ≤
        (observer34Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer34Panel4Data) s observer34Panel4Data.anchor ≤
        (observer34Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer34Panel4Data) s observer34Panel4Data.anchor ≤
        (observer34Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer34Panel4Data observer34Panel4Endpoints
    observer34_panel4_kernel_check s hs
def observer34Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer34Panel4Endpoints
theorem observer34_panel4_recurrence_field_kernel_check :
    observer34Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer34_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer34Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer34Panel4Endpoints
    observer34_panel4_recurrence_field_kernel_check

def observer34Panel5Data : MainPanelData :=
  {
    observer := 34, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((7154510949156957856 : ℚ) / 16224156050882121490008336946852725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer34Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877494146454771408228718338, ellLower := 351161226581313407689394083483,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217423110278390135477772599, offsetUpper := 7233897628547983924752134156,
    supportELower := 45631603943498035135951248203, supportEUpper := 46996644097210394531039680564,
    supportLambdaLower := 351161226581313407689394083483,
    supportLambdaUpper := 359481400436244482221264743670,
    supportJLower := 49143216209311169212845189037, supportJUpper := 50591458101572839353252328001,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer34Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer34Panel5Data observer34Panel5Endpoints
theorem observer34_panel5_kernel_check : observer34Panel5Check = true := by
  decide +kernel
theorem observer34_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer34Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer34Panel5Data) s observer34Panel5Data.anchor ≤
        (observer34Panel5Endpoints.energyUpper : ℝ) ∧
      (observer34Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer34Panel5Data) s observer34Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer34Panel5Data) s observer34Panel5Data.anchor ≤
        (observer34Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer34Panel5Data) s observer34Panel5Data.anchor ≤
        (observer34Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer34Panel5Data) s observer34Panel5Data.anchor ≤
        (observer34Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer34Panel5Data observer34Panel5Endpoints
    observer34_panel5_kernel_check s hs
def observer34Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer34Panel5Endpoints
theorem observer34_panel5_recurrence_field_kernel_check :
    observer34Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer34_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer34Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer34Panel5Endpoints
    observer34_panel5_recurrence_field_kernel_check

def observer34Panel6Data : MainPanelData :=
  {
    observer := 34, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((7154510949156957856 : ℚ) / 16224156050882121490008336946852725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer34Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554915732335004554746020082, ellLower := 351001120090204762571685180020,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429988055703588533794857961, offsetUpper := 7446947775550445480423159809,
    supportELower := 46996571051153306559880059289, supportEUpper := 48357747104004452328165401512,
    supportLambdaLower := 351001120090204762571685180020,
    supportLambdaUpper := 359059547738544466351859725982,
    supportJLower := 50506582252055354185596911089, supportJUpper := 51948342581389896991683998772,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer34Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer34Panel6Data observer34Panel6Endpoints
theorem observer34_panel6_kernel_check : observer34Panel6Check = true := by
  decide +kernel
theorem observer34_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer34Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer34Panel6Data) s observer34Panel6Data.anchor ≤
        (observer34Panel6Endpoints.energyUpper : ℝ) ∧
      (observer34Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer34Panel6Data) s observer34Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer34Panel6Data) s observer34Panel6Data.anchor ≤
        (observer34Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer34Panel6Data) s observer34Panel6Data.anchor ≤
        (observer34Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer34Panel6Data) s observer34Panel6Data.anchor ≤
        (observer34Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer34Panel6Data observer34Panel6Endpoints
    observer34_panel6_kernel_check s hs
def observer34Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer34Panel6Endpoints
theorem observer34_panel6_recurrence_field_kernel_check :
    observer34Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer34_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer34Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer34Panel6Endpoints
    observer34_panel6_recurrence_field_kernel_check

def observer34Panel7Data : MainPanelData :=
  {
    observer := 34, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((7154510949156957856 : ℚ) / 16224156050882121490008336946852725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer34Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229306655753690567748738348, ellLower := 350846307856906511469326049897,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642253412568743859289797641, offsetUpper := 7659697650150843012317393865,
    supportELower := 48357669303989323951182573814, supportEUpper := 49715683481605869128797227386,
    supportLambdaLower := 350846307856906511469326049897,
    supportLambdaUpper := 358658987248796257298882054008,
    supportJLower := 51866132382558389065875834312, supportJUpper := 53302273354093831701786047927,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer34Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer34Panel7Data observer34Panel7Endpoints
theorem observer34_panel7_kernel_check : observer34Panel7Check = true := by
  decide +kernel
theorem observer34_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer34Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer34Panel7Data) s observer34Panel7Data.anchor ≤
        (observer34Panel7Endpoints.energyUpper : ℝ) ∧
      (observer34Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer34Panel7Data) s observer34Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer34Panel7Data) s observer34Panel7Data.anchor ≤
        (observer34Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer34Panel7Data) s observer34Panel7Data.anchor ≤
        (observer34Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer34Panel7Data) s observer34Panel7Data.anchor ≤
        (observer34Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer34Panel7Data observer34Panel7Endpoints
    observer34_panel7_kernel_check s hs
def observer34Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer34Panel7Endpoints
theorem observer34_panel7_recurrence_field_kernel_check :
    observer34Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer34_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer34Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer34Panel7Endpoints
    observer34_panel7_recurrence_field_kernel_check

def observer34InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 34, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer34Panel0Endpoints, observer34Panel1Endpoints, observer34Panel2Endpoints, observer34Panel3Endpoints, observer34Panel4Endpoints, observer34Panel5Endpoints, observer34Panel6Endpoints, observer34Panel7Endpoints]
  }
def observer34FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer34InsertionEndpoints.frameLower
    observer34InsertionEndpoints.frameUpper
theorem observer34_frame_recurrence_field_kernel_check :
    observer34FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer34_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer34InsertionEndpoints.frameLower
      observer34InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer34InsertionEndpoints.frameLower
    observer34InsertionEndpoints.frameUpper
    observer34_frame_recurrence_field_kernel_check
def observer34RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer34Panel0Endpoints ∧
  panelRecurrenceFields observer34Panel1Endpoints ∧
  panelRecurrenceFields observer34Panel2Endpoints ∧
  panelRecurrenceFields observer34Panel3Endpoints ∧
  panelRecurrenceFields observer34Panel4Endpoints ∧
  panelRecurrenceFields observer34Panel5Endpoints ∧
  panelRecurrenceFields observer34Panel6Endpoints ∧
  panelRecurrenceFields observer34Panel7Endpoints ∧ insertionFrameRecurrenceFields observer34InsertionEndpoints.frameLower
      observer34InsertionEndpoints.frameUpper
theorem observer34_all_recurrence_fields :
    observer34RecurrenceFieldBounds := by
  exact ⟨observer34_panel0_recurrence_fields_sound,
    observer34_panel1_recurrence_fields_sound,
    observer34_panel2_recurrence_fields_sound,
    observer34_panel3_recurrence_fields_sound,
    observer34_panel4_recurrence_fields_sound,
    observer34_panel5_recurrence_fields_sound,
    observer34_panel6_recurrence_fields_sound,
    observer34_panel7_recurrence_fields_sound,
    observer34_frame_recurrence_fields_sound⟩
def observer34PanelFormulaBounds : Prop :=
  panelFormulaBounds observer34Panel0Data observer34Panel0Endpoints ∧
  panelFormulaBounds observer34Panel1Data observer34Panel1Endpoints ∧
  panelFormulaBounds observer34Panel2Data observer34Panel2Endpoints ∧
  panelFormulaBounds observer34Panel3Data observer34Panel3Endpoints ∧
  panelFormulaBounds observer34Panel4Data observer34Panel4Endpoints ∧
  panelFormulaBounds observer34Panel5Data observer34Panel5Endpoints ∧
  panelFormulaBounds observer34Panel6Data observer34Panel6Endpoints ∧
  panelFormulaBounds observer34Panel7Data observer34Panel7Endpoints
theorem observer34_all_panel_formula_bounds : observer34PanelFormulaBounds := by
  exact ⟨observer34_panel0_formula_sound,
    observer34_panel1_formula_sound,
    observer34_panel2_formula_sound,
    observer34_panel3_formula_sound,
    observer34_panel4_formula_sound,
    observer34_panel5_formula_sound,
    observer34_panel6_formula_sound,
    observer34_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
