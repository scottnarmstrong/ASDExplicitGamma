module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer24Panel0Data : MainPanelData :=
  {
    observer := 24, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((121162271150104 : ℚ) / 4653042512817563075362725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer24Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49394207386628190025299815034, ellLower := 352023346635646461433120353897,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172508386075888669362965129, offsetUpper := 6186533721185524688830420164,
    supportELower := 38566724001129995519994843080, supportEUpper := 40092454023223417226397443364,
    supportLambdaLower := 352023346635646461433120353897,
    supportLambdaUpper := 361979973592041825910059073698,
    supportJLower := 42086957467486460134326046618, supportJUpper := 43712253759143835485498034101,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer24Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer24Panel0Data observer24Panel0Endpoints
theorem observer24_panel0_kernel_check : observer24Panel0Check = true := by
  decide +kernel
theorem observer24_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer24Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer24Panel0Data) s observer24Panel0Data.anchor ≤
        (observer24Panel0Endpoints.energyUpper : ℝ) ∧
      (observer24Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer24Panel0Data) s observer24Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer24Panel0Data) s observer24Panel0Data.anchor ≤
        (observer24Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer24Panel0Data) s observer24Panel0Data.anchor ≤
        (observer24Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer24Panel0Data) s observer24Panel0Data.anchor ≤
        (observer24Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer24Panel0Data observer24Panel0Endpoints
    observer24_panel0_kernel_check s hs
def observer24Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer24Panel0Endpoints
theorem observer24_panel0_recurrence_field_kernel_check :
    observer24Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer24_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer24Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer24Panel0Endpoints
    observer24_panel0_recurrence_field_kernel_check

def observer24Panel1Data : MainPanelData :=
  {
    observer := 24, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((121162271150104 : ℚ) / 4653042512817563075362725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer24Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51116102271964567845508891062, ellLower := 351856675175124753620419333377,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376188268632285135696882097, offsetUpper := 6390709420364212467298854408,
    supportELower := 40092404941131765029356114019, supportEUpper := 41498999746785480312683021827,
    supportLambdaLower := 351856675175124753620419333377,
    supportLambdaUpper := 361422622447255090782243525584,
    supportJLower := 43610971692883012565560307352, supportJUpper := 45113225971258031220505457083,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer24Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer24Panel1Data observer24Panel1Endpoints
theorem observer24_panel1_kernel_check : observer24Panel1Check = true := by
  decide +kernel
theorem observer24_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer24Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer24Panel1Data) s observer24Panel1Data.anchor ≤
        (observer24Panel1Endpoints.energyUpper : ℝ) ∧
      (observer24Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer24Panel1Data) s observer24Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer24Panel1Data) s observer24Panel1Data.anchor ≤
        (observer24Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer24Panel1Data) s observer24Panel1Data.anchor ≤
        (observer24Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer24Panel1Data) s observer24Panel1Data.anchor ≤
        (observer24Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer24Panel1Data observer24Panel1Endpoints
    observer24_panel1_kernel_check s hs
def observer24Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer24Panel1Endpoints
theorem observer24_panel1_recurrence_field_kernel_check :
    observer24Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer24_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer24Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer24Panel1Endpoints
    observer24_panel1_recurrence_field_kernel_check

def observer24Panel2Data : MainPanelData :=
  {
    observer := 24, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((121162271150104 : ℚ) / 4653042512817563075362725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer24Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52818667934391171899408999955, ellLower := 351676444968061534914148440225,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591941731199217493422685433, offsetUpper := 6606954240562793798534393445,
    supportELower := 41498945824419087818868646631, supportEUpper := 42885985831027434567276465650,
    supportLambdaLower := 351676444968061534914148440225,
    supportLambdaUpper := 360896030295270709872681894603,
    supportJLower := 45015710274099703168010131033, supportJUpper := 46494946133980141666003284597,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer24Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer24Panel2Data observer24Panel2Endpoints
theorem observer24_panel2_kernel_check : observer24Panel2Check = true := by
  decide +kernel
theorem observer24_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer24Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer24Panel2Data) s observer24Panel2Data.anchor ≤
        (observer24Panel2Endpoints.energyUpper : ℝ) ∧
      (observer24Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer24Panel2Data) s observer24Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer24Panel2Data) s observer24Panel2Data.anchor ≤
        (observer24Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer24Panel2Data) s observer24Panel2Data.anchor ≤
        (observer24Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer24Panel2Data) s observer24Panel2Data.anchor ≤
        (observer24Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer24Panel2Data observer24Panel2Endpoints
    observer24_panel2_kernel_check s hs
def observer24Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer24Panel2Endpoints
theorem observer24_panel2_recurrence_field_kernel_check :
    observer24Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer24_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer24Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer24Panel2Endpoints
    observer24_panel2_recurrence_field_kernel_check

def observer24Panel3Data : MainPanelData :=
  {
    observer := 24, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((121162271150104 : ℚ) / 4653042512817563075362725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer24Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54511144293618670004248928255, ellLower := 351500163550211337292618830610,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806580159364578717259017449, offsetUpper := 6822081486976860868578727193,
    supportELower := 42885927103956952396298939222, supportEUpper := 44262666430308182877774686356,
    supportLambdaLower := 351500163550211337292618830610,
    supportLambdaUpper := 360398769304479991763107610795,
    supportJLower := 46400928739459065769225127528, supportJUpper := 47866654123352982795405762464,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer24Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer24Panel3Data observer24Panel3Endpoints
theorem observer24_panel3_kernel_check : observer24Panel3Check = true := by
  decide +kernel
theorem observer24_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer24Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer24Panel3Data) s observer24Panel3Data.anchor ≤
        (observer24Panel3Endpoints.energyUpper : ℝ) ∧
      (observer24Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer24Panel3Data) s observer24Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer24Panel3Data) s observer24Panel3Data.anchor ≤
        (observer24Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer24Panel3Data) s observer24Panel3Data.anchor ≤
        (observer24Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer24Panel3Data) s observer24Panel3Data.anchor ≤
        (observer24Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer24Panel3Data observer24Panel3Endpoints
    observer24_panel3_kernel_check s hs
def observer24Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer24Panel3Endpoints
theorem observer24_panel3_recurrence_field_kernel_check :
    observer24Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer24_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer24Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer24Panel3Endpoints
    observer24_panel3_recurrence_field_kernel_check

def observer24Panel4Data : MainPanelData :=
  {
    observer := 24, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((121162271150104 : ℚ) / 4653042512817563075362725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer24Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56197060170006929131469208237, ellLower := 351329109069539507372238724992,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020509941653714637539008616, offsetUpper := 7036498473642298099002812989,
    supportELower := 44262602917770045190195030339, supportEUpper := 45632591569570983049114837916,
    supportLambdaLower := 351329109069539507372238724992,
    supportLambdaUpper := 359928714652229569803794869453,
    supportJLower := 47775894008465440263917417588, supportJUpper := 49231878716093278747152786611,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer24Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer24Panel4Data observer24Panel4Endpoints
theorem observer24_panel4_kernel_check : observer24Panel4Check = true := by
  decide +kernel
theorem observer24_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer24Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer24Panel4Data) s observer24Panel4Data.anchor ≤
        (observer24Panel4Endpoints.energyUpper : ℝ) ∧
      (observer24Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer24Panel4Data) s observer24Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer24Panel4Data) s observer24Panel4Data.anchor ≤
        (observer24Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer24Panel4Data) s observer24Panel4Data.anchor ≤
        (observer24Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer24Panel4Data) s observer24Panel4Data.anchor ≤
        (observer24Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer24Panel4Data observer24Panel4Endpoints
    observer24_panel4_kernel_check s hs
def observer24Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer24Panel4Endpoints
theorem observer24_panel4_recurrence_field_kernel_check :
    observer24Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer24_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer24Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer24Panel4Endpoints
    observer24_panel4_recurrence_field_kernel_check

def observer24Panel5Data : MainPanelData :=
  {
    observer := 24, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((121162271150104 : ℚ) / 4653042512817563075362725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer24Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57878446229268904790500143146, ellLower := 351163538399570794103198425374,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217494321331849231758669990, offsetUpper := 7233969002148072653731717141,
    supportELower := 45632523284711441147311899853, supportEUpper := 46997572764401277391424594430,
    supportLambdaLower := 351163538399570794103198425374,
    supportLambdaUpper := 359483741555744649422338574028,
    supportJLower := 49144158668707149088343884106, supportJUpper := 50592410179958723885647980171,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer24Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer24Panel5Data observer24Panel5Endpoints
theorem observer24_panel5_kernel_check : observer24Panel5Check = true := by
  decide +kernel
theorem observer24_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer24Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer24Panel5Data) s observer24Panel5Data.anchor ≤
        (observer24Panel5Endpoints.energyUpper : ℝ) ∧
      (observer24Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer24Panel5Data) s observer24Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer24Panel5Data) s observer24Panel5Data.anchor ≤
        (observer24Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer24Panel5Data) s observer24Panel5Data.anchor ≤
        (observer24Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer24Panel5Data) s observer24Panel5Data.anchor ≤
        (observer24Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer24Panel5Data observer24Panel5Endpoints
    observer24_panel5_kernel_check s hs
def observer24Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer24Panel5Endpoints
theorem observer24_panel5_recurrence_field_kernel_check :
    observer24Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer24_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer24Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer24Panel5Endpoints
    observer24_panel5_recurrence_field_kernel_check

def observer24Panel6Data : MainPanelData :=
  {
    observer := 24, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((121162271150104 : ℚ) / 4653042512817563075362725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer24Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59555876881165160920616147498, ellLower := 351003412889439242499407281315,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7430059432871811464387720101, offsetUpper := 7447019315644472254485353511,
    supportELower := 46997499717298864349968545201, supportEUpper := 48358685036025673496622395544,
    supportLambdaLower := 351003412889439242499407281315,
    supportLambdaUpper := 359061868976613101105595800548,
    supportJLower := 50507533846193256774962618014, supportJUpper := 51949303725791804507678353550,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer24Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer24Panel6Data observer24Panel6Endpoints
theorem observer24_panel6_kernel_check : observer24Panel6Check = true := by
  decide +kernel
theorem observer24_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer24Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer24Panel6Data) s observer24Panel6Data.anchor ≤
        (observer24Panel6Endpoints.energyUpper : ℝ) ∧
      (observer24Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer24Panel6Data) s observer24Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer24Panel6Data) s observer24Panel6Data.anchor ≤
        (observer24Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer24Panel6Data) s observer24Panel6Data.anchor ≤
        (observer24Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer24Panel6Data) s observer24Panel6Data.anchor ≤
        (observer24Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer24Panel6Data observer24Panel6Endpoints
    observer24_panel6_kernel_check s hs
def observer24Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer24Panel6Endpoints
theorem observer24_panel6_recurrence_field_kernel_check :
    observer24Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer24_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer24Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer24Panel6Endpoints
    observer24_panel6_recurrence_field_kernel_check

def observer24Panel7Data : MainPanelData :=
  {
    observer := 24, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((121162271150104 : ℚ) / 4653042512817563075362725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer24Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61230276818699163290029374204, ellLower := 350848582236543340331355615694,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642324960376268616749903444, offsetUpper := 7659769361273673552166554891,
    supportELower := 48358607234937373912697378526, supportEUpper := 49716630620088186835495176487,
    supportLambdaLower := 350848582236543340331355615694,
    supportLambdaUpper := 358661289252286873869573465721,
    supportJLower := 51867093057302807316010934682, supportJUpper := 53303243512611055574190911145,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer24Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer24Panel7Data observer24Panel7Endpoints
theorem observer24_panel7_kernel_check : observer24Panel7Check = true := by
  decide +kernel
theorem observer24_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer24Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer24Panel7Data) s observer24Panel7Data.anchor ≤
        (observer24Panel7Endpoints.energyUpper : ℝ) ∧
      (observer24Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer24Panel7Data) s observer24Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer24Panel7Data) s observer24Panel7Data.anchor ≤
        (observer24Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer24Panel7Data) s observer24Panel7Data.anchor ≤
        (observer24Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer24Panel7Data) s observer24Panel7Data.anchor ≤
        (observer24Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer24Panel7Data observer24Panel7Endpoints
    observer24_panel7_kernel_check s hs
def observer24Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer24Panel7Endpoints
theorem observer24_panel7_recurrence_field_kernel_check :
    observer24Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer24_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer24Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer24Panel7Endpoints
    observer24_panel7_recurrence_field_kernel_check

def observer24InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 24, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer24Panel0Endpoints, observer24Panel1Endpoints, observer24Panel2Endpoints, observer24Panel3Endpoints, observer24Panel4Endpoints, observer24Panel5Endpoints, observer24Panel6Endpoints, observer24Panel7Endpoints]
  }
def observer24FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer24InsertionEndpoints.frameLower
    observer24InsertionEndpoints.frameUpper
theorem observer24_frame_recurrence_field_kernel_check :
    observer24FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer24_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer24InsertionEndpoints.frameLower
      observer24InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer24InsertionEndpoints.frameLower
    observer24InsertionEndpoints.frameUpper
    observer24_frame_recurrence_field_kernel_check
def observer24RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer24Panel0Endpoints ∧
  panelRecurrenceFields observer24Panel1Endpoints ∧
  panelRecurrenceFields observer24Panel2Endpoints ∧
  panelRecurrenceFields observer24Panel3Endpoints ∧
  panelRecurrenceFields observer24Panel4Endpoints ∧
  panelRecurrenceFields observer24Panel5Endpoints ∧
  panelRecurrenceFields observer24Panel6Endpoints ∧
  panelRecurrenceFields observer24Panel7Endpoints ∧ insertionFrameRecurrenceFields observer24InsertionEndpoints.frameLower
      observer24InsertionEndpoints.frameUpper
theorem observer24_all_recurrence_fields :
    observer24RecurrenceFieldBounds := by
  exact ⟨observer24_panel0_recurrence_fields_sound,
    observer24_panel1_recurrence_fields_sound,
    observer24_panel2_recurrence_fields_sound,
    observer24_panel3_recurrence_fields_sound,
    observer24_panel4_recurrence_fields_sound,
    observer24_panel5_recurrence_fields_sound,
    observer24_panel6_recurrence_fields_sound,
    observer24_panel7_recurrence_fields_sound,
    observer24_frame_recurrence_fields_sound⟩
def observer24PanelFormulaBounds : Prop :=
  panelFormulaBounds observer24Panel0Data observer24Panel0Endpoints ∧
  panelFormulaBounds observer24Panel1Data observer24Panel1Endpoints ∧
  panelFormulaBounds observer24Panel2Data observer24Panel2Endpoints ∧
  panelFormulaBounds observer24Panel3Data observer24Panel3Endpoints ∧
  panelFormulaBounds observer24Panel4Data observer24Panel4Endpoints ∧
  panelFormulaBounds observer24Panel5Data observer24Panel5Endpoints ∧
  panelFormulaBounds observer24Panel6Data observer24Panel6Endpoints ∧
  panelFormulaBounds observer24Panel7Data observer24Panel7Endpoints
theorem observer24_all_panel_formula_bounds : observer24PanelFormulaBounds := by
  exact ⟨observer24_panel0_formula_sound,
    observer24_panel1_formula_sound,
    observer24_panel2_formula_sound,
    observer24_panel3_formula_sound,
    observer24_panel4_formula_sound,
    observer24_panel5_formula_sound,
    observer24_panel6_formula_sound,
    observer24_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
