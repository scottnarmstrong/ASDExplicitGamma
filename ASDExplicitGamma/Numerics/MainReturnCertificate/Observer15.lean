module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer15Panel0Data : MainPanelData :=
  {
    observer := 15, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((6155680858 : ℚ) / 12010316038854525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer15Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49522002275042864006669012972, ellLower := 352367132351465220541335485967,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6182440407771219080894106472, offsetUpper := 6196488310680504821508342647,
    supportELower := 38689567918436750737346756936, supportEUpper := 40216674057653047005569696326,
    supportLambdaLower := 352367132351465220541335485967,
    supportLambdaUpper := 362328743163903520666444705462,
    supportJLower := 42213239241951402942760111795, supportJUpper := 43839961489292082212234143381,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer15Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer15Panel0Data observer15Panel0Endpoints
theorem observer15_panel0_kernel_check : observer15Panel0Check = true := by
  decide +kernel
theorem observer15_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer15Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer15Panel0Data) s observer15Panel0Data.anchor ≤
        (observer15Panel0Endpoints.energyUpper : ℝ) ∧
      (observer15Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer15Panel0Data) s observer15Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer15Panel0Data) s observer15Panel0Data.anchor ≤
        (observer15Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer15Panel0Data) s observer15Panel0Data.anchor ≤
        (observer15Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer15Panel0Data) s observer15Panel0Data.anchor ≤
        (observer15Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer15Panel0Data observer15Panel0Endpoints
    observer15_panel0_kernel_check s hs
def observer15Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer15Panel0Endpoints
theorem observer15_panel0_recurrence_field_kernel_check :
    observer15Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer15_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer15Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer15Panel0Endpoints
    observer15_panel0_recurrence_field_kernel_check

def observer15Panel1Data : MainPanelData :=
  {
    observer := 15, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((6155680858 : ℚ) / 12010316038854525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer15Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51245229222764423803227305388, ellLower := 352197238119295842162971932503,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6400658099328263879884104333, offsetUpper := 6415201842187778424506885285,
    supportELower := 40216624848478175260408628052, supportEUpper := 41624585784626683385229967255,
    supportLambdaLower := 352197238119295842162971932503,
    supportLambdaUpper := 361767997916477653836081549587,
    supportJLower := 43738597229671133682038347377, supportJUpper := 45242265763791459923590782751,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer15Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer15Panel1Data observer15Panel1Endpoints
theorem observer15_panel1_kernel_check : observer15Panel1Check = true := by
  decide +kernel
theorem observer15_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer15Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer15Panel1Data) s observer15Panel1Data.anchor ≤
        (observer15Panel1Endpoints.energyUpper : ℝ) ∧
      (observer15Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer15Panel1Data) s observer15Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer15Panel1Data) s observer15Panel1Data.anchor ≤
        (observer15Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer15Panel1Data) s observer15Panel1Data.anchor ≤
        (observer15Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer15Panel1Data) s observer15Panel1Data.anchor ≤
        (observer15Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer15Panel1Data observer15Panel1Endpoints
    observer15_panel1_kernel_check s hs
def observer15Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer15Panel1Endpoints
theorem observer15_panel1_recurrence_field_kernel_check :
    observer15Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer15_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer15Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer15Panel1Endpoints
    observer15_panel1_recurrence_field_kernel_check

def observer15Panel2Data : MainPanelData :=
  {
    observer := 15, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((6155680858 : ℚ) / 12010316038854525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer15Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52949118595033811379447661532, ellLower := 352013903495206534484657696614,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6616922578203124957148613208, offsetUpper := 6631957722871889864201555813,
    supportELower := 41624531730988329707889756255, supportEUpper := 43012928224167651120500191642,
    supportLambdaLower := 352013903495206534484657696614,
    supportLambdaUpper := 361238141218870277090866587338,
    supportJLower := 45144670765940395052736333221, supportJUpper := 46625309636356353891408857516,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer15Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer15Panel2Data observer15Panel2Endpoints
theorem observer15_panel2_kernel_check : observer15Panel2Check = true := by
  decide +kernel
theorem observer15_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer15Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer15Panel2Data) s observer15Panel2Data.anchor ≤
        (observer15Panel2Endpoints.energyUpper : ℝ) ∧
      (observer15Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer15Panel2Data) s observer15Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer15Panel2Data) s observer15Panel2Data.anchor ≤
        (observer15Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer15Panel2Data) s observer15Panel2Data.anchor ≤
        (observer15Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer15Panel2Data) s observer15Panel2Data.anchor ≤
        (observer15Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer15Panel2Data observer15Panel2Endpoints
    observer15_panel2_kernel_check s hs
def observer15Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer15Panel2Endpoints
theorem observer15_panel2_recurrence_field_kernel_check :
    observer15Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer15_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer15Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer15Panel2Endpoints
    observer15_panel2_recurrence_field_kernel_check

def observer15Panel3Data : MainPanelData :=
  {
    observer := 15, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((6155680858 : ℚ) / 12010316038854525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer15Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54642910542817686239543372718, ellLower := 351834628197550349238417549420,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6816547081622428805272049721, offsetUpper := 6832071107935613276439115245,
    supportELower := 43012869361684641274536248252, supportEUpper := 44390955851106118163162577899,
    supportLambdaLower := 351834628197550349238417549420,
    supportLambdaUpper := 360737736317945361290454036926,
    supportJLower := 46531215643660144766920423746, supportJUpper := 47998333214285571776067118269,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer15Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer15Panel3Data observer15Panel3Endpoints
theorem observer15_panel3_kernel_check : observer15Panel3Check = true := by
  decide +kernel
theorem observer15_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer15Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer15Panel3Data) s observer15Panel3Data.anchor ≤
        (observer15Panel3Endpoints.energyUpper : ℝ) ∧
      (observer15Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer15Panel3Data) s observer15Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer15Panel3Data) s observer15Panel3Data.anchor ≤
        (observer15Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer15Panel3Data) s observer15Panel3Data.anchor ≤
        (observer15Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer15Panel3Data) s observer15Panel3Data.anchor ≤
        (observer15Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer15Panel3Data observer15Panel3Endpoints
    observer15_panel3_kernel_check s hs
def observer15Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer15Panel3Endpoints
theorem observer15_panel3_recurrence_field_kernel_check :
    observer15Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer15_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer15Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer15Panel3Endpoints
    observer15_panel3_recurrence_field_kernel_check

def observer15Panel4Data : MainPanelData :=
  {
    observer := 15, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((6155680858 : ℚ) / 12010316038854525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer15Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56330134106809791744435731987, ellLower := 351660683324445002357441747956,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7030499239632639374490593540, offsetUpper := 7046510521280664513040350382,
    supportELower := 44390892199060922635788197553, supportEUpper := 45762218990804503560633849572,
    supportLambdaLower := 351660683324445002357441747956,
    supportLambdaUpper := 360264650382521054485237213028,
    supportJLower := 47907499032305372659362615032, supportJUpper := 49364865494629714105486221703,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer15Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer15Panel4Data observer15Panel4Endpoints
theorem observer15_panel4_kernel_check : observer15Panel4Check = true := by
  decide +kernel
theorem observer15_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer15Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer15Panel4Data) s observer15Panel4Data.anchor ≤
        (observer15Panel4Endpoints.energyUpper : ℝ) ∧
      (observer15Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer15Panel4Data) s observer15Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer15Panel4Data) s observer15Panel4Data.anchor ≤
        (observer15Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer15Panel4Data) s observer15Panel4Data.anchor ≤
        (observer15Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer15Panel4Data) s observer15Panel4Data.anchor ≤
        (observer15Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer15Panel4Data observer15Panel4Endpoints
    observer15_panel4_kernel_check s hs
def observer15Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer15Panel4Endpoints
theorem observer15_panel4_recurrence_field_kernel_check :
    observer15Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer15_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer15Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer15Panel4Endpoints
    observer15_panel4_recurrence_field_kernel_check

def observer15Panel5Data : MainPanelData :=
  {
    observer := 15, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((6155680858 : ℚ) / 12010316038854525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer15Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 58012820162825784840086537409, ellLower := 351492319366940483252796619516,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7243981538747879728685300381, offsetUpper := 7260479005672582411756487121,
    supportELower := 45762150562387434645932840202, supportEUpper := 47128529441145209460926766490,
    supportLambdaLower := 351492319366940483252796619516,
    supportLambdaUpper := 359816751410396721967451928555,
    supportJLower := 49277073756056839478460806397, supportJUpper := 50726696955249176680601285776,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer15Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer15Panel5Data observer15Panel5Endpoints
theorem observer15_panel5_kernel_check : observer15Panel5Check = true := by
  decide +kernel
theorem observer15_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer15Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer15Panel5Data) s observer15Panel5Data.anchor ≤
        (observer15Panel5Endpoints.energyUpper : ℝ) ∧
      (observer15Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer15Panel5Data) s observer15Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer15Panel5Data) s observer15Panel5Data.anchor ≤
        (observer15Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer15Panel5Data) s observer15Panel5Data.anchor ≤
        (observer15Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer15Panel5Data) s observer15Panel5Data.anchor ≤
        (observer15Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer15Panel5Data observer15Panel5Endpoints
    observer15_panel5_kernel_check s hs
def observer15Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer15Panel5Endpoints
theorem observer15_panel5_recurrence_field_kernel_check :
    observer15Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer15_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer15Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer15Panel5Endpoints
    observer15_panel5_recurrence_field_kernel_check

def observer15Panel6Data : MainPanelData :=
  {
    observer := 15, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((6155680858 : ℚ) / 12010316038854525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer15Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59691543321144398876905125075, ellLower := 351329491875022013770943200850,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7457055857395889420075320947, offsetUpper := 7474038580461237472467705229,
    supportELower := 47128456246477030992864052307, supportEUpper := 48490962489208372987263013553,
    supportLambdaLower := 351329491875022013770943200850,
    supportLambdaUpper := 359392051829624222207122891587,
    supportJLower := 50641751165227251130573484315, supportJUpper := 52084883007504615209334242469,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer15Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer15Panel6Data observer15Panel6Endpoints
theorem observer15_panel6_kernel_check : observer15Panel6Check = true := by
  decide +kernel
theorem observer15_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer15Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer15Panel6Data) s observer15Panel6Data.anchor ≤
        (observer15Panel6Endpoints.energyUpper : ℝ) ∧
      (observer15Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer15Panel6Data) s observer15Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer15Panel6Data) s observer15Panel6Data.anchor ≤
        (observer15Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer15Panel6Data) s observer15Panel6Data.anchor ≤
        (observer15Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer15Panel6Data) s observer15Panel6Data.anchor ≤
        (observer15Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer15Panel6Data observer15Panel6Endpoints
    observer15_panel6_kernel_check s hs
def observer15Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer15Panel6Endpoints
theorem observer15_panel6_recurrence_field_kernel_check :
    observer15Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer15_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer15Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer15Panel6Endpoints
    observer15_panel6_recurrence_field_kernel_check

def observer15Panel7Data : MainPanelData :=
  {
    observer := 15, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((6155680858 : ℚ) / 12010316038854525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer15Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61367228466305178409643818126, ellLower := 351172045259302430867823184565,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7652363228525233215610096995, offsetUpper := 7669830542812845202342534803,
    supportELower := 48490884536586599541889540522, supportEUpper := 49850220621516266367871370726,
    supportLambdaLower := 351172045259302430867823184565,
    supportLambdaUpper := 358988738043437707130089568294,
    supportJLower := 52002604989179623850567772367, supportJUpper := 53440108001950643439172266409,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer15Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer15Panel7Data observer15Panel7Endpoints
theorem observer15_panel7_kernel_check : observer15Panel7Check = true := by
  decide +kernel
theorem observer15_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer15Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer15Panel7Data) s observer15Panel7Data.anchor ≤
        (observer15Panel7Endpoints.energyUpper : ℝ) ∧
      (observer15Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer15Panel7Data) s observer15Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer15Panel7Data) s observer15Panel7Data.anchor ≤
        (observer15Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer15Panel7Data) s observer15Panel7Data.anchor ≤
        (observer15Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer15Panel7Data) s observer15Panel7Data.anchor ≤
        (observer15Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer15Panel7Data observer15Panel7Endpoints
    observer15_panel7_kernel_check s hs
def observer15Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer15Panel7Endpoints
theorem observer15_panel7_recurrence_field_kernel_check :
    observer15Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer15_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer15Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer15Panel7Endpoints
    observer15_panel7_recurrence_field_kernel_check

def observer15InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 15, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer15Panel0Endpoints, observer15Panel1Endpoints, observer15Panel2Endpoints, observer15Panel3Endpoints, observer15Panel4Endpoints, observer15Panel5Endpoints, observer15Panel6Endpoints, observer15Panel7Endpoints]
  }
def observer15FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer15InsertionEndpoints.frameLower
    observer15InsertionEndpoints.frameUpper
theorem observer15_frame_recurrence_field_kernel_check :
    observer15FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer15_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer15InsertionEndpoints.frameLower
      observer15InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer15InsertionEndpoints.frameLower
    observer15InsertionEndpoints.frameUpper
    observer15_frame_recurrence_field_kernel_check
def observer15RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer15Panel0Endpoints ∧
  panelRecurrenceFields observer15Panel1Endpoints ∧
  panelRecurrenceFields observer15Panel2Endpoints ∧
  panelRecurrenceFields observer15Panel3Endpoints ∧
  panelRecurrenceFields observer15Panel4Endpoints ∧
  panelRecurrenceFields observer15Panel5Endpoints ∧
  panelRecurrenceFields observer15Panel6Endpoints ∧
  panelRecurrenceFields observer15Panel7Endpoints ∧ insertionFrameRecurrenceFields observer15InsertionEndpoints.frameLower
      observer15InsertionEndpoints.frameUpper
theorem observer15_all_recurrence_fields :
    observer15RecurrenceFieldBounds := by
  exact ⟨observer15_panel0_recurrence_fields_sound,
    observer15_panel1_recurrence_fields_sound,
    observer15_panel2_recurrence_fields_sound,
    observer15_panel3_recurrence_fields_sound,
    observer15_panel4_recurrence_fields_sound,
    observer15_panel5_recurrence_fields_sound,
    observer15_panel6_recurrence_fields_sound,
    observer15_panel7_recurrence_fields_sound,
    observer15_frame_recurrence_fields_sound⟩
def observer15PanelFormulaBounds : Prop :=
  panelFormulaBounds observer15Panel0Data observer15Panel0Endpoints ∧
  panelFormulaBounds observer15Panel1Data observer15Panel1Endpoints ∧
  panelFormulaBounds observer15Panel2Data observer15Panel2Endpoints ∧
  panelFormulaBounds observer15Panel3Data observer15Panel3Endpoints ∧
  panelFormulaBounds observer15Panel4Data observer15Panel4Endpoints ∧
  panelFormulaBounds observer15Panel5Data observer15Panel5Endpoints ∧
  panelFormulaBounds observer15Panel6Data observer15Panel6Endpoints ∧
  panelFormulaBounds observer15Panel7Data observer15Panel7Endpoints
theorem observer15_all_panel_formula_bounds : observer15PanelFormulaBounds := by
  exact ⟨observer15_panel0_formula_sound,
    observer15_panel1_formula_sound,
    observer15_panel2_formula_sound,
    observer15_panel3_formula_sound,
    observer15_panel4_formula_sound,
    observer15_panel5_formula_sound,
    observer15_panel6_formula_sound,
    observer15_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
