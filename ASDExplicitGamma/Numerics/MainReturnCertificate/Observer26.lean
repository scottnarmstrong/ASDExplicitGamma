module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer26Panel0Data : MainPanelData :=
  {
    observer := 26, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1090460440352896 : ℚ) / 376896443538222609104380725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer26Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393600594919643602297254332, ellLower := 352021726465404205278945463880,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172460967275764878372095258, offsetUpper := 6186486194639162150997304968,
    supportELower := 38566140119923919739228963640, supportEUpper := 40091863668665487427502102188,
    supportLambdaLower := 352021726465404205278945463880,
    supportLambdaUpper := 361978330270608949626263250328,
    supportJLower := 42086357384577961792018418278, supportJUpper := 43711646971371576923764734692,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer26Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer26Panel0Data observer26Panel0Endpoints
theorem observer26_panel0_kernel_check : observer26Panel0Check = true := by
  decide +kernel
theorem observer26_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer26Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer26Panel0Data) s observer26Panel0Data.anchor ≤
        (observer26Panel0Endpoints.energyUpper : ℝ) ∧
      (observer26Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer26Panel0Data) s observer26Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer26Panel0Data) s observer26Panel0Data.anchor ≤
        (observer26Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer26Panel0Data) s observer26Panel0Data.anchor ≤
        (observer26Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer26Panel0Data) s observer26Panel0Data.anchor ≤
        (observer26Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer26Panel0Data observer26Panel0Endpoints
    observer26_panel0_kernel_check s hs
def observer26Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer26Panel0Endpoints
theorem observer26_panel0_recurrence_field_kernel_check :
    observer26Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer26_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer26Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer26Panel0Endpoints
    observer26_panel0_recurrence_field_kernel_check

def observer26Panel1Data : MainPanelData :=
  {
    observer := 26, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1090460440352896 : ℚ) / 376896443538222609104380725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer26Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115489214531295448295840379, ellLower := 351855070180447201939274429139,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376140881034629750496032048, offsetUpper := 6390661924845889314084142331,
    supportELower := 40091814587177673976907931714, supportEUpper := 41498402966831383268762719919,
    supportLambdaLower := 351855070180447201939274429139,
    supportLambdaUpper := 361420995092966341579894777315,
    supportJLower := 43610365288982145996300676005, supportJUpper := 45112612917761046684561667693,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer26Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer26Panel1Data observer26Panel1Endpoints
theorem observer26_panel1_kernel_check : observer26Panel1Check = true := by
  decide +kernel
theorem observer26_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer26Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer26Panel1Data) s observer26Panel1Data.anchor ≤
        (observer26Panel1Endpoints.energyUpper : ℝ) ∧
      (observer26Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer26Panel1Data) s observer26Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer26Panel1Data) s observer26Panel1Data.anchor ≤
        (observer26Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer26Panel1Data) s observer26Panel1Data.anchor ≤
        (observer26Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer26Panel1Data) s observer26Panel1Data.anchor ≤
        (observer26Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer26Panel1Data observer26Panel1Endpoints
    observer26_panel1_kernel_check s hs
def observer26Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer26Panel1Endpoints
theorem observer26_panel1_recurrence_field_kernel_check :
    observer26Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer26_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer26Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer26Panel1Endpoints
    observer26_panel1_recurrence_field_kernel_check

def observer26Panel2Data : MainPanelData :=
  {
    observer := 26, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1090460440352896 : ℚ) / 376896443538222609104380725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer26Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52818048650970630328860675656, ellLower := 351674854597547379670846078462,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591894252837855291509485205, offsetUpper := 6606906654074058269908330976,
    supportELower := 41498349045088546900221007794, supportEUpper := 42885382671442692633925689101,
    supportLambdaLower := 351674854597547379670846078462,
    supportLambdaUpper := 360894418305319532279853248959,
    supportJLower := 45015097591064020696929468578, supportJUpper := 46494326854495887956724221591,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer26Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer26Panel2Data observer26Panel2Endpoints
theorem observer26_panel2_kernel_check : observer26Panel2Check = true := by
  decide +kernel
theorem observer26_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer26Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer26Panel2Data) s observer26Panel2Data.anchor ≤
        (observer26Panel2Endpoints.energyUpper : ℝ) ∧
      (observer26Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer26Panel2Data) s observer26Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer26Panel2Data) s observer26Panel2Data.anchor ≤
        (observer26Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer26Panel2Data) s observer26Panel2Data.anchor ≤
        (observer26Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer26Panel2Data) s observer26Panel2Data.anchor ≤
        (observer26Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer26Panel2Data observer26Panel2Endpoints
    observer26_panel2_kernel_check s hs
def observer26Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer26Panel2Endpoints
theorem observer26_panel2_recurrence_field_kernel_check :
    observer26Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer26_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer26Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer26Panel2Endpoints
    observer26_panel2_recurrence_field_kernel_check

def observer26Panel3Data : MainPanelData :=
  {
    observer := 26, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1090460440352896 : ℚ) / 376896443538222609104380725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer26Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510518822856147070538729114, ellLower := 351498587288519499631898372219,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806532582534013181673919238, offsetUpper := 6822033801794667924956883411,
    supportELower := 42885323945015255019476800474, supportEUpper := 44262056935355167140207062483,
    supportLambdaLower := 351498587288519499631898372219,
    supportLambdaUpper := 360397172117158058275776213243,
    supportJLower := 46400309817900450015795784196, supportJUpper := 47866028656526747722964824616,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer26Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer26Panel3Data observer26Panel3Endpoints
theorem observer26_panel3_kernel_check : observer26Panel3Check = true := by
  decide +kernel
theorem observer26_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer26Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer26Panel3Data) s observer26Panel3Data.anchor ≤
        (observer26Panel3Endpoints.energyUpper : ℝ) ∧
      (observer26Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer26Panel3Data) s observer26Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer26Panel3Data) s observer26Panel3Data.anchor ≤
        (observer26Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer26Panel3Data) s observer26Panel3Data.anchor ≤
        (observer26Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer26Panel3Data) s observer26Panel3Data.anchor ≤
        (observer26Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer26Panel3Data observer26Panel3Endpoints
    observer26_panel3_kernel_check s hs
def observer26Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer26Panel3Endpoints
theorem observer26_panel3_recurrence_field_kernel_check :
    observer26Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer26_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer26Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer26Panel3Endpoints
    observer26_panel3_recurrence_field_kernel_check

def observer26Panel4Data : MainPanelData :=
  {
    observer := 26, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1090460440352896 : ℚ) / 376896443538222609104380725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer26Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196428549506706176034022468, ellLower := 351327546433875882674569760491,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020462260919647591318093299, offsetUpper := 7036450684319973475222550257,
    supportELower := 44261993423479343555112639251, supportEUpper := 45631975782101818980984195164,
    supportLambdaLower := 351327546433875882674569760491,
    supportLambdaUpper := 359927131742752467200266697094,
    supportJLower := 47775268887818102381858336855, supportJUpper := 49231247099529343652986862135,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer26Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer26Panel4Data observer26Panel4Endpoints
theorem observer26_panel4_kernel_check : observer26Panel4Check = true := by
  decide +kernel
theorem observer26_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer26Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer26Panel4Data) s observer26Panel4Data.anchor ≤
        (observer26Panel4Endpoints.energyUpper : ℝ) ∧
      (observer26Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer26Panel4Data) s observer26Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer26Panel4Data) s observer26Panel4Data.anchor ≤
        (observer26Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer26Panel4Data) s observer26Panel4Data.anchor ≤
        (observer26Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer26Panel4Data) s observer26Panel4Data.anchor ≤
        (observer26Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer26Panel4Data observer26Panel4Endpoints
    observer26_panel4_kernel_check s hs
def observer26Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer26Panel4Endpoints
theorem observer26_panel4_recurrence_field_kernel_check :
    observer26Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer26_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer26Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer26Panel4Endpoints
    observer26_panel4_recurrence_field_kernel_check

def observer26Panel5Data : MainPanelData :=
  {
    observer := 26, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1090460440352896 : ℚ) / 376896443538222609104380725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer26Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877808495642203025888409008, ellLower := 351161988936631153239979360039,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217446641409096783768569816, offsetUpper := 7233921213390941719688498956,
    supportELower := 45631907497923651144692387749, supportEUpper := 46996950725941897515143656140,
    supportLambdaLower := 351161988936631153239979360039,
    supportLambdaUpper := 359482172432641246716185118562,
    supportJLower := 49143527387289962677092181349, supportJUpper := 50591772450268309982305507326,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer26Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer26Panel5Data observer26Panel5Endpoints
theorem observer26_panel5_kernel_check : observer26Panel5Check = true := by
  decide +kernel
theorem observer26_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer26Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer26Panel5Data) s observer26Panel5Data.anchor ≤
        (observer26Panel5Endpoints.energyUpper : ℝ) ∧
      (observer26Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer26Panel5Data) s observer26Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer26Panel5Data) s observer26Panel5Data.anchor ≤
        (observer26Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer26Panel5Data) s observer26Panel5Data.anchor ≤
        (observer26Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer26Panel5Data) s observer26Panel5Data.anchor ≤
        (observer26Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer26Panel5Data observer26Panel5Endpoints
    observer26_panel5_kernel_check s hs
def observer26Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer26Panel5Endpoints
theorem observer26_panel5_recurrence_field_kernel_check :
    observer26Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer26_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer26Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer26Panel5Endpoints
    observer26_panel5_recurrence_field_kernel_check

def observer26Panel6Data : MainPanelData :=
  {
    observer := 26, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1090460440352896 : ℚ) / 376896443538222609104380725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer26Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59555233070075077812356026168, ellLower := 351001876172735061802824410690,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7430011641518609036289527460, offsetUpper := 7446971415202539758621724659,
    supportELower := 46996877679539717546293554441, supportEUpper := 48358056786852161517464485922,
    supportLambdaLower := 351001876172735061802824410690,
    supportLambdaUpper := 359060313178584774322300759071,
    supportJLower := 50506896441267068164321798547, supportJUpper := 51948659918638009260687493513,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer26Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer26Panel6Data observer26Panel6Endpoints
theorem observer26_panel6_kernel_check : observer26Panel6Check = true := by
  decide +kernel
theorem observer26_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer26Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer26Panel6Data) s observer26Panel6Data.anchor ≤
        (observer26Panel6Endpoints.energyUpper : ℝ) ∧
      (observer26Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer26Panel6Data) s observer26Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer26Panel6Data) s observer26Panel6Data.anchor ≤
        (observer26Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer26Panel6Data) s observer26Panel6Data.anchor ≤
        (observer26Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer26Panel6Data) s observer26Panel6Data.anchor ≤
        (observer26Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer26Panel6Data observer26Panel6Endpoints
    observer26_panel6_kernel_check s hs
def observer26Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer26Panel6Endpoints
theorem observer26_panel6_recurrence_field_kernel_check :
    observer26Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer26_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer26Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer26Panel6Endpoints
    observer26_panel6_recurrence_field_kernel_check

def observer26Panel7Data : MainPanelData :=
  {
    observer := 26, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1090460440352896 : ℚ) / 376896443538222609104380725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer26Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229626964902804315782250228, ellLower := 350847057864051149254761985245,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642277054562780327743682886, offsetUpper := 7659721346110187698430081237,
    supportELower := 48357978986482761081014285064, supportEUpper := 49715996199296373777752822835,
    supportLambdaLower := 350847057864051149254761985245,
    supportLambdaUpper := 358659746345461068346022562629,
    supportJLower := 51866449565123272573561904916, supportJUpper := 53302593662750984461213048462,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer26Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer26Panel7Data observer26Panel7Endpoints
theorem observer26_panel7_kernel_check : observer26Panel7Check = true := by
  decide +kernel
theorem observer26_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer26Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer26Panel7Data) s observer26Panel7Data.anchor ≤
        (observer26Panel7Endpoints.energyUpper : ℝ) ∧
      (observer26Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer26Panel7Data) s observer26Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer26Panel7Data) s observer26Panel7Data.anchor ≤
        (observer26Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer26Panel7Data) s observer26Panel7Data.anchor ≤
        (observer26Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer26Panel7Data) s observer26Panel7Data.anchor ≤
        (observer26Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer26Panel7Data observer26Panel7Endpoints
    observer26_panel7_kernel_check s hs
def observer26Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer26Panel7Endpoints
theorem observer26_panel7_recurrence_field_kernel_check :
    observer26Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer26_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer26Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer26Panel7Endpoints
    observer26_panel7_recurrence_field_kernel_check

def observer26InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 26, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer26Panel0Endpoints, observer26Panel1Endpoints, observer26Panel2Endpoints, observer26Panel3Endpoints, observer26Panel4Endpoints, observer26Panel5Endpoints, observer26Panel6Endpoints, observer26Panel7Endpoints]
  }
def observer26FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer26InsertionEndpoints.frameLower
    observer26InsertionEndpoints.frameUpper
theorem observer26_frame_recurrence_field_kernel_check :
    observer26FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer26_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer26InsertionEndpoints.frameLower
      observer26InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer26InsertionEndpoints.frameLower
    observer26InsertionEndpoints.frameUpper
    observer26_frame_recurrence_field_kernel_check
def observer26RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer26Panel0Endpoints ∧
  panelRecurrenceFields observer26Panel1Endpoints ∧
  panelRecurrenceFields observer26Panel2Endpoints ∧
  panelRecurrenceFields observer26Panel3Endpoints ∧
  panelRecurrenceFields observer26Panel4Endpoints ∧
  panelRecurrenceFields observer26Panel5Endpoints ∧
  panelRecurrenceFields observer26Panel6Endpoints ∧
  panelRecurrenceFields observer26Panel7Endpoints ∧ insertionFrameRecurrenceFields observer26InsertionEndpoints.frameLower
      observer26InsertionEndpoints.frameUpper
theorem observer26_all_recurrence_fields :
    observer26RecurrenceFieldBounds := by
  exact ⟨observer26_panel0_recurrence_fields_sound,
    observer26_panel1_recurrence_fields_sound,
    observer26_panel2_recurrence_fields_sound,
    observer26_panel3_recurrence_fields_sound,
    observer26_panel4_recurrence_fields_sound,
    observer26_panel5_recurrence_fields_sound,
    observer26_panel6_recurrence_fields_sound,
    observer26_panel7_recurrence_fields_sound,
    observer26_frame_recurrence_fields_sound⟩
def observer26PanelFormulaBounds : Prop :=
  panelFormulaBounds observer26Panel0Data observer26Panel0Endpoints ∧
  panelFormulaBounds observer26Panel1Data observer26Panel1Endpoints ∧
  panelFormulaBounds observer26Panel2Data observer26Panel2Endpoints ∧
  panelFormulaBounds observer26Panel3Data observer26Panel3Endpoints ∧
  panelFormulaBounds observer26Panel4Data observer26Panel4Endpoints ∧
  panelFormulaBounds observer26Panel5Data observer26Panel5Endpoints ∧
  panelFormulaBounds observer26Panel6Data observer26Panel6Endpoints ∧
  panelFormulaBounds observer26Panel7Data observer26Panel7Endpoints
theorem observer26_all_panel_formula_bounds : observer26PanelFormulaBounds := by
  exact ⟨observer26_panel0_formula_sound,
    observer26_panel1_formula_sound,
    observer26_panel2_formula_sound,
    observer26_panel3_formula_sound,
    observer26_panel4_formula_sound,
    observer26_panel5_formula_sound,
    observer26_panel6_formula_sound,
    observer26_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
