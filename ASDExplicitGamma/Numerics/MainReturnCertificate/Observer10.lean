module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer10Panel0Data : MainPanelData :=
  {
    observer := 10, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((25331776 : ℚ) / 203395756725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer10Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 51419985891123864858647930015, ellLower := 357420944175393639193147574648,
    rhoLower := 99955309988961589283614890770898, rhoUpper := 99955409944321555916857877676731,
    offsetLower := 6414901172509044313959743652, offsetUpper := 6429281144592337599947223510,
    supportELower := 40494956241072551128995692686, supportEUpper := 42042293399044514010865010984,
    supportLambdaLower := 357420944175393639193147574648,
    supportLambdaUpper := 367455853820449139642984517063,
    supportJLower := 44069165682826487520927168432, supportJUpper := 45716851937249005407294856155,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer10Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer10Panel0Data observer10Panel0Endpoints
theorem observer10_panel0_kernel_check : observer10Panel0Check = true := by
  decide +kernel
theorem observer10_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer10Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer10Panel0Data) s observer10Panel0Data.anchor ≤
        (observer10Panel0Endpoints.energyUpper : ℝ) ∧
      (observer10Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer10Panel0Data) s observer10Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer10Panel0Data) s observer10Panel0Data.anchor ≤
        (observer10Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer10Panel0Data) s observer10Panel0Data.anchor ≤
        (observer10Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer10Panel0Data) s observer10Panel0Data.anchor ≤
        (observer10Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer10Panel0Data observer10Panel0Endpoints
    observer10_panel0_kernel_check s hs
def observer10Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer10Panel0Endpoints
theorem observer10_panel0_recurrence_field_kernel_check :
    observer10Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer10_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer10Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer10Panel0Endpoints
    observer10_panel0_recurrence_field_kernel_check

def observer10Panel1Data : MainPanelData :=
  {
    observer := 10, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((25331776 : ℚ) / 203395756725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer10Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 53162796232029324494900911050, ellLower := 357203672427409758591656081373,
    rhoLower := 99955309988961589283614890770898, rhoUpper := 99955409944321555916857877676731,
    offsetLower := 6636359665338266750128641079, offsetUpper := 6651236070158223203330008684,
    supportELower := 42042242322158663847116189351, supportEUpper := 43470287496757384584501294660,
    supportLambdaLower := 357203672427409758591656081373,
    supportLambdaUpper := 366845210817489837384488948399,
    supportJLower := 45614279046432761433032750164, supportJUpper := 47138739604932282958346184144,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer10Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer10Panel1Data observer10Panel1Endpoints
theorem observer10_panel1_kernel_check : observer10Panel1Check = true := by
  decide +kernel
theorem observer10_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer10Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer10Panel1Data) s observer10Panel1Data.anchor ≤
        (observer10Panel1Endpoints.energyUpper : ℝ) ∧
      (observer10Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer10Panel1Data) s observer10Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer10Panel1Data) s observer10Panel1Data.anchor ≤
        (observer10Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer10Panel1Data) s observer10Panel1Data.anchor ≤
        (observer10Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer10Panel1Data) s observer10Panel1Data.anchor ≤
        (observer10Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer10Panel1Data observer10Panel1Endpoints
    observer10_panel1_kernel_check s hs
def observer10Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer10Panel1Endpoints
theorem observer10_panel1_recurrence_field_kernel_check :
    observer10Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer10_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer10Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer10Panel1Endpoints
    observer10_panel1_recurrence_field_kernel_check

def observer10Panel2Data : MainPanelData :=
  {
    observer := 10, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((25331776 : ℚ) / 203395756725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer10Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 54886146247735236739908878907, ellLower := 356974700796493724881231996813,
    rhoLower := 99955309988961589283614890770898, rhoUpper := 99955409944321555916857877676731,
    offsetLower := 6855881696100794399287533185, offsetUpper := 6871250192784544650771250382,
    supportELower := 43470231513828477814385392503, supportEUpper := 44878570504000194965796390036,
    supportLambdaLower := 356974700796493724881231996813,
    supportLambdaUpper := 366267361693350662915548058558,
    supportJLower := 47039978521793415063197712471, supportJUpper := 48541244120933701594951870622,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer10Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer10Panel2Data observer10Panel2Endpoints
theorem observer10_panel2_kernel_check : observer10Panel2Check = true := by
  decide +kernel
theorem observer10_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer10Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer10Panel2Data) s observer10Panel2Data.anchor ≤
        (observer10Panel2Endpoints.energyUpper : ℝ) ∧
      (observer10Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer10Panel2Data) s observer10Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer10Panel2Data) s observer10Panel2Data.anchor ≤
        (observer10Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer10Panel2Data) s observer10Panel2Data.anchor ≤
        (observer10Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer10Panel2Data) s observer10Panel2Data.anchor ≤
        (observer10Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer10Panel2Data observer10Panel2Endpoints
    observer10_panel2_kernel_check s hs
def observer10Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer10Panel2Endpoints
theorem observer10_panel2_recurrence_field_kernel_check :
    observer10Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer10_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer10Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer10Panel2Endpoints
    observer10_panel2_recurrence_field_kernel_check

def observer10Panel3Data : MainPanelData :=
  {
    observer := 10, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((25331776 : ℚ) / 203395756725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer10Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 56599279488572077225342936487, ellLower := 356751414003027229225042227453,
    rhoLower := 99955409944321555916857877676729, rhoUpper := 99955509899781477960045194468098,
    offsetLower := 7058437662482097626677319485, offsetUpper := 7074295783264454164516950868,
    supportELower := 44878509651355068022459035968, supportEUpper := 46276401607424598453866497491,
    supportLambdaLower := 356751414003027229225042227453,
    supportLambdaUpper := 365720738449128665108198027742,
    supportJLower := 48446023791385340314709458242, supportJUpper := 49933608991915885104948477769,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer10Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer10Panel3Data observer10Panel3Endpoints
theorem observer10_panel3_kernel_check : observer10Panel3Check = true := by
  decide +kernel
theorem observer10_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer10Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer10Panel3Data) s observer10Panel3Data.anchor ≤
        (observer10Panel3Endpoints.energyUpper : ℝ) ∧
      (observer10Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer10Panel3Data) s observer10Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer10Panel3Data) s observer10Panel3Data.anchor ≤
        (observer10Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer10Panel3Data) s observer10Panel3Data.anchor ≤
        (observer10Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer10Panel3Data) s observer10Panel3Data.anchor ≤
        (observer10Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer10Panel3Data observer10Panel3Endpoints
    observer10_panel3_kernel_check s hs
def observer10Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer10Panel3Endpoints
theorem observer10_panel3_recurrence_field_kernel_check :
    observer10Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer10_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer10Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer10Panel3Endpoints
    observer10_panel3_recurrence_field_kernel_check

def observer10Panel4Data : MainPanelData :=
  {
    observer := 10, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((25331776 : ℚ) / 203395756725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer10Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 58305728234004972476413746661, ellLower := 356534979441012305323357707739,
    rhoLower := 99955409944321555916857877676729, rhoUpper := 99955509899781477960045194468098,
    offsetLower := 7275661132918280121228496912, offsetUpper := 7292007287483133547921458120,
    supportELower := 46276335905022288942295990623, supportEUpper := 47667335549277906160971723355,
    supportLambdaLower := 356534979441012305323357707739,
    supportLambdaUpper := 365203090442291101957430875285,
    supportJLower := 49841685699432411995529567700, supportJUpper := 51319366453700817180546032108,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer10Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer10Panel4Data observer10Panel4Endpoints
theorem observer10_panel4_kernel_check : observer10Panel4Check = true := by
  decide +kernel
theorem observer10_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer10Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer10Panel4Data) s observer10Panel4Data.anchor ≤
        (observer10Panel4Endpoints.energyUpper : ℝ) ∧
      (observer10Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer10Panel4Data) s observer10Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer10Panel4Data) s observer10Panel4Data.anchor ≤
        (observer10Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer10Panel4Data) s observer10Panel4Data.anchor ≤
        (observer10Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer10Panel4Data) s observer10Panel4Data.anchor ≤
        (observer10Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer10Panel4Data observer10Panel4Endpoints
    observer10_panel4_kernel_check s hs
def observer10Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer10Panel4Endpoints
theorem observer10_panel4_recurrence_field_kernel_check :
    observer10Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer10_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer10Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer10Panel4Endpoints
    observer10_panel4_recurrence_field_kernel_check

def observer10Panel5Data : MainPanelData :=
  {
    observer := 10, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((25331776 : ℚ) / 203395756725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer10Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 60007526448189755411435395629, ellLower := 356325553716926621417549904093,
    rhoLower := 99955409944321555916857877676729, rhoUpper := 99955509899781477960045194468098,
    offsetLower := 7492420450054162828545680068, offsetUpper := 7509253595592969717064187959,
    supportELower := 47667265010956254277715163908, supportEUpper := 49053188277785676976419812514,
    supportLambdaLower := 356325553716926621417549904093,
    supportLambdaUpper := 364712179470339261861212721233,
    supportJLower := 51230520548125520491890662948, supportJUpper := 52700310072489069595031939727,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer10Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer10Panel5Data observer10Panel5Endpoints
theorem observer10_panel5_kernel_check : observer10Panel5Check = true := by
  decide +kernel
theorem observer10_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer10Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer10Panel5Data) s observer10Panel5Data.anchor ≤
        (observer10Panel5Endpoints.energyUpper : ℝ) ∧
      (observer10Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer10Panel5Data) s observer10Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer10Panel5Data) s observer10Panel5Data.anchor ≤
        (observer10Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer10Panel5Data) s observer10Panel5Data.anchor ≤
        (observer10Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer10Panel5Data) s observer10Panel5Data.anchor ≤
        (observer10Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer10Panel5Data observer10Panel5Endpoints
    observer10_panel5_kernel_check s hs
def observer10Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer10Panel5Endpoints
theorem observer10_panel5_recurrence_field_kernel_check :
    observer10Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer10_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer10Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer10Panel5Endpoints
    observer10_panel5_recurrence_field_kernel_check

def observer10Panel6Data : MainPanelData :=
  {
    observer := 10, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((25331776 : ℚ) / 203395756725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer10Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 61705251688823902273230543674, ellLower := 356123007078874321243076303098,
    rhoLower := 99955409944321555916857877676729, rhoUpper := 99955509899781477960045194468098,
    offsetLower := 7708776959296194023246606905, offsetUpper := 7726096190824517557345014073,
    supportELower := 49053112914286069178473092004, supportEUpper := 50435038988528651759312420584,
    supportLambdaLower := 356123007078874321243076303098,
    supportLambdaUpper := 364245921853138918942903621411,
    supportJLower := 52614342985074812390903855034, supportJUpper := 54077498207060040948741456799,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer10Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer10Panel6Data observer10Panel6Endpoints
theorem observer10_panel6_kernel_check : observer10Panel6Check = true := by
  decide +kernel
theorem observer10_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer10Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer10Panel6Data) s observer10Panel6Data.anchor ≤
        (observer10Panel6Endpoints.energyUpper : ℝ) ∧
      (observer10Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer10Panel6Data) s observer10Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer10Panel6Data) s observer10Panel6Data.anchor ≤
        (observer10Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer10Panel6Data) s observer10Panel6Data.anchor ≤
        (observer10Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer10Panel6Data) s observer10Panel6Data.anchor ≤
        (observer10Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer10Panel6Data observer10Panel6Endpoints
    observer10_panel6_kernel_check s hs
def observer10Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer10Panel6Endpoints
theorem observer10_panel6_recurrence_field_kernel_check :
    observer10Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer10_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer10Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer10Panel6Endpoints
    observer10_panel6_recurrence_field_kernel_check

def observer10Panel7Data : MainPanelData :=
  {
    observer := 10, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((25331776 : ℚ) / 203395756725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer10Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 63399831655803955917324393978, ellLower := 355927106173995972028040054605,
    rhoLower := 99955509899781477960045194468096, rhoUpper := 99955609855341355513132301067050,
    offsetLower := 7907033911485947844858718003, offsetUpper := 7924838584294993629215658676,
    supportELower := 50434958808744223657518205410, supportEUpper := 51813593856286994458998937098,
    supportLambdaLower := 355927106173995972028040054605,
    supportLambdaUpper := 363802416703834883093570089340,
    supportJLower := 53994229870484183377798605956, supportJUpper := 55451618023325343289934637992,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer10Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer10Panel7Data observer10Panel7Endpoints
theorem observer10_panel7_kernel_check : observer10Panel7Check = true := by
  decide +kernel
theorem observer10_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer10Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer10Panel7Data) s observer10Panel7Data.anchor ≤
        (observer10Panel7Endpoints.energyUpper : ℝ) ∧
      (observer10Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer10Panel7Data) s observer10Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer10Panel7Data) s observer10Panel7Data.anchor ≤
        (observer10Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer10Panel7Data) s observer10Panel7Data.anchor ≤
        (observer10Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer10Panel7Data) s observer10Panel7Data.anchor ≤
        (observer10Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer10Panel7Data observer10Panel7Endpoints
    observer10_panel7_kernel_check s hs
def observer10Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer10Panel7Endpoints
theorem observer10_panel7_recurrence_field_kernel_check :
    observer10Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer10_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer10Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer10Panel7Endpoints
    observer10_panel7_recurrence_field_kernel_check

def observer10InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 10, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer10Panel0Endpoints, observer10Panel1Endpoints, observer10Panel2Endpoints, observer10Panel3Endpoints, observer10Panel4Endpoints, observer10Panel5Endpoints, observer10Panel6Endpoints, observer10Panel7Endpoints]
  }
def observer10FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer10InsertionEndpoints.frameLower
    observer10InsertionEndpoints.frameUpper
theorem observer10_frame_recurrence_field_kernel_check :
    observer10FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer10_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer10InsertionEndpoints.frameLower
      observer10InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer10InsertionEndpoints.frameLower
    observer10InsertionEndpoints.frameUpper
    observer10_frame_recurrence_field_kernel_check
def observer10RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer10Panel0Endpoints ∧
  panelRecurrenceFields observer10Panel1Endpoints ∧
  panelRecurrenceFields observer10Panel2Endpoints ∧
  panelRecurrenceFields observer10Panel3Endpoints ∧
  panelRecurrenceFields observer10Panel4Endpoints ∧
  panelRecurrenceFields observer10Panel5Endpoints ∧
  panelRecurrenceFields observer10Panel6Endpoints ∧
  panelRecurrenceFields observer10Panel7Endpoints ∧ insertionFrameRecurrenceFields observer10InsertionEndpoints.frameLower
      observer10InsertionEndpoints.frameUpper
theorem observer10_all_recurrence_fields :
    observer10RecurrenceFieldBounds := by
  exact ⟨observer10_panel0_recurrence_fields_sound,
    observer10_panel1_recurrence_fields_sound,
    observer10_panel2_recurrence_fields_sound,
    observer10_panel3_recurrence_fields_sound,
    observer10_panel4_recurrence_fields_sound,
    observer10_panel5_recurrence_fields_sound,
    observer10_panel6_recurrence_fields_sound,
    observer10_panel7_recurrence_fields_sound,
    observer10_frame_recurrence_fields_sound⟩
def observer10PanelFormulaBounds : Prop :=
  panelFormulaBounds observer10Panel0Data observer10Panel0Endpoints ∧
  panelFormulaBounds observer10Panel1Data observer10Panel1Endpoints ∧
  panelFormulaBounds observer10Panel2Data observer10Panel2Endpoints ∧
  panelFormulaBounds observer10Panel3Data observer10Panel3Endpoints ∧
  panelFormulaBounds observer10Panel4Data observer10Panel4Endpoints ∧
  panelFormulaBounds observer10Panel5Data observer10Panel5Endpoints ∧
  panelFormulaBounds observer10Panel6Data observer10Panel6Endpoints ∧
  panelFormulaBounds observer10Panel7Data observer10Panel7Endpoints
theorem observer10_all_panel_formula_bounds : observer10PanelFormulaBounds := by
  exact ⟨observer10_panel0_formula_sound,
    observer10_panel1_formula_sound,
    observer10_panel2_formula_sound,
    observer10_panel3_formula_sound,
    observer10_panel4_formula_sound,
    observer10_panel5_formula_sound,
    observer10_panel6_formula_sound,
    observer10_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
