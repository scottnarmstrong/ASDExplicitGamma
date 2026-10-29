module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer16Panel0Data : MainPanelData :=
  {
    observer := 16, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((18467043064 : ℚ) / 108092844349690725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer16Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49467569088154844998193908705, ellLower := 352220720306211967100347761464,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6178211952270239683563861750, offsetUpper := 6192250247172263546192146905,
    supportELower := 38637264290428908073800214046, supportEUpper := 40163784334096246230795717624,
    supportLambdaLower := 352220720306211967100347761464,
    supportLambdaUpper := 362180207677021345411572195973,
    supportJLower := 42159471493491027744803691660, supportJUpper := 43785586410866459684911439584,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer16Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer16Panel0Data observer16Panel0Endpoints
theorem observer16_panel0_kernel_check : observer16Panel0Check = true := by
  decide +kernel
theorem observer16_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer16Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer16Panel0Data) s observer16Panel0Data.anchor ≤
        (observer16Panel0Endpoints.energyUpper : ℝ) ∧
      (observer16Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer16Panel0Data) s observer16Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer16Panel0Data) s observer16Panel0Data.anchor ≤
        (observer16Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer16Panel0Data) s observer16Panel0Data.anchor ≤
        (observer16Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer16Panel0Data) s observer16Panel0Data.anchor ≤
        (observer16Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer16Panel0Data observer16Panel0Endpoints
    observer16_panel0_kernel_check s hs
def observer16Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer16Panel0Endpoints
theorem observer16_panel0_recurrence_field_kernel_check :
    observer16Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer16_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer16Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer16Panel0Endpoints
    observer16_panel0_recurrence_field_kernel_check

def observer16Panel1Data : MainPanelData :=
  {
    observer := 16, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((18467043064 : ℚ) / 108092844349690725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer16Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51190228702411060074046944446, ellLower := 352052198627265090547178407948,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6396422527515294960265497434, offsetUpper := 6410956646197677267078794550,
    supportELower := 40163735179030501683401474577, supportEUpper := 41571114271976678696898383386,
    supportLambdaLower := 352052198627265090547178407948,
    supportLambdaUpper := 361620907992381397866443889218,
    supportJLower := 43684257165303152588873258656, supportJUpper := 45187323351900492675562822279,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer16Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer16Panel1Data observer16Panel1Endpoints
theorem observer16_panel1_kernel_check : observer16Panel1Check = true := by
  decide +kernel
theorem observer16_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer16Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer16Panel1Data) s observer16Panel1Data.anchor ≤
        (observer16Panel1Endpoints.energyUpper : ℝ) ∧
      (observer16Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer16Panel1Data) s observer16Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer16Panel1Data) s observer16Panel1Data.anchor ≤
        (observer16Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer16Panel1Data) s observer16Panel1Data.anchor ≤
        (observer16Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer16Panel1Data) s observer16Panel1Data.anchor ≤
        (observer16Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer16Panel1Data observer16Panel1Endpoints
    observer16_panel1_kernel_check s hs
def observer16Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer16Panel1Endpoints
theorem observer16_panel1_recurrence_field_kernel_check :
    observer16Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer16_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer16Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer16Panel1Endpoints
    observer16_panel1_recurrence_field_kernel_check

def observer16Panel2Data : MainPanelData :=
  {
    observer := 16, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((18467043064 : ℚ) / 108092844349690725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer16Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52893554297400572576612664411, ellLower := 351870186134119884101675130401,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6597653097022637951691681299, offsetUpper := 6612678613469164808158210989,
    supportELower := 41571060274231423650201575532, supportEUpper := 42958879030579149797516777016,
    supportLambdaLower := 351870186134119884101675130401,
    supportLambdaUpper := 361092441660636177220948384810,
    supportJLower := 45089762135572622491218326836, supportJUpper := 46569803447185511569726260865,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer16Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer16Panel2Data observer16Panel2Endpoints
theorem observer16_panel2_kernel_check : observer16Panel2Check = true := by
  decide +kernel
theorem observer16_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer16Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer16Panel2Data) s observer16Panel2Data.anchor ≤
        (observer16Panel2Endpoints.energyUpper : ℝ) ∧
      (observer16Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer16Panel2Data) s observer16Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer16Panel2Data) s observer16Panel2Data.anchor ≤
        (observer16Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer16Panel2Data) s observer16Panel2Data.anchor ≤
        (observer16Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer16Panel2Data) s observer16Panel2Data.anchor ≤
        (observer16Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer16Panel2Data observer16Panel2Endpoints
    observer16_panel2_kernel_check s hs
def observer16Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer16Panel2Endpoints
theorem observer16_panel2_recurrence_field_kernel_check :
    observer16Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer16_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer16Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer16Panel2Endpoints
    observer16_panel2_recurrence_field_kernel_check

def observer16Panel3Data : MainPanelData :=
  {
    observer := 16, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((18467043064 : ℚ) / 108092844349690725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer16Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54586785925608591132291761618, ellLower := 351692185876527255893502160480,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6812303697130948177676717345, offsetUpper := 6827818059546603017876503354,
    supportELower := 42958820225752698258685768084, supportEUpper := 44336332948231659474031549070,
    supportLambdaLower := 351692185876527255893502160480,
    supportLambdaUpper := 360593375730721367593635856855,
    supportJLower := 46475742084517970817620789688, supportJUpper := 47942266705538873149967907639,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer16Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer16Panel3Data observer16Panel3Endpoints
theorem observer16_panel3_kernel_check : observer16Panel3Check = true := by
  decide +kernel
theorem observer16_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer16Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer16Panel3Data) s observer16Panel3Data.anchor ≤
        (observer16Panel3Endpoints.energyUpper : ℝ) ∧
      (observer16Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer16Panel3Data) s observer16Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer16Panel3Data) s observer16Panel3Data.anchor ≤
        (observer16Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer16Panel3Data) s observer16Panel3Data.anchor ≤
        (observer16Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer16Panel3Data) s observer16Panel3Data.anchor ≤
        (observer16Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer16Panel3Data observer16Panel3Endpoints
    observer16_panel3_kernel_check s hs
def observer16Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer16Panel3Endpoints
theorem observer16_panel3_recurrence_field_kernel_check :
    observer16Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer16_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer16Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer16Panel3Endpoints
    observer16_panel3_recurrence_field_kernel_check

def observer16Panel4Data : MainPanelData :=
  {
    observer := 16, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((18467043064 : ℚ) / 108092844349690725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer16Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56273452533899776848895758162, ellLower := 351519471956834693862532663552,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7026246307289342755239329887, offsetUpper := 7042247903295529736669588283,
    supportELower := 44336269355586881104228255340, supportEUpper := 45707026222338590477257410120,
    supportLambdaLower := 351519471956834693862532663552,
    supportLambdaUpper := 360121580784350521384123822779,
    supportJLower := 47851464075155228042853581975, supportJUpper := 49308242030182095691098648348,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer16Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer16Panel4Data observer16Panel4Endpoints
theorem observer16_panel4_kernel_check : observer16Panel4Check = true := by
  decide +kernel
theorem observer16_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer16Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer16Panel4Data) s observer16Panel4Data.anchor ≤
        (observer16Panel4Endpoints.energyUpper : ℝ) ∧
      (observer16Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer16Panel4Data) s observer16Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer16Panel4Data) s observer16Panel4Data.anchor ≤
        (observer16Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer16Panel4Data) s observer16Panel4Data.anchor ≤
        (observer16Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer16Panel4Data) s observer16Panel4Data.anchor ≤
        (observer16Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer16Panel4Data observer16Panel4Endpoints
    observer16_panel4_kernel_check s hs
def observer16Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer16Panel4Endpoints
theorem observer16_panel4_recurrence_field_kernel_check :
    observer16Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer16_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer16Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer16Panel4Endpoints
    observer16_panel4_recurrence_field_kernel_check

def observer16Panel5Data : MainPanelData :=
  {
    observer := 16, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((18467043064 : ℚ) / 108092844349690725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer16Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57955584908618706011445979439, ellLower := 351352297585862252993913469860,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7239718691936418915238263114, offsetUpper := 7256206450640041660973680841,
    supportELower := 45706957855047038022214902976, supportEUpper := 47072770530545876275824092225,
    supportLambdaLower := 351352297585862252993913469860,
    supportLambdaUpper := 359674927895861805728903605004,
    supportJLower := 49220480830905660552154037674, supportJUpper := 50669519809504494333113128276,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer16Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer16Panel5Data observer16Panel5Endpoints
theorem observer16_panel5_kernel_check : observer16Panel5Check = true := by
  decide +kernel
theorem observer16_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer16Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer16Panel5Data) s observer16Panel5Data.anchor ≤
        (observer16Panel5Endpoints.energyUpper : ℝ) ∧
      (observer16Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer16Panel5Data) s observer16Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer16Panel5Data) s observer16Panel5Data.anchor ≤
        (observer16Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer16Panel5Data) s observer16Panel5Data.anchor ≤
        (observer16Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer16Panel5Data) s observer16Panel5Data.anchor ≤
        (observer16Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer16Panel5Data observer16Panel5Endpoints
    observer16_panel5_kernel_check s hs
def observer16Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer16Panel5Endpoints
theorem observer16_panel5_recurrence_field_kernel_check :
    observer16Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer16_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer16Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer16Panel5Endpoints
    observer16_panel5_recurrence_field_kernel_check

def observer16Panel6Data : MainPanelData :=
  {
    observer := 16, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((18467043064 : ℚ) / 108092844349690725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer16Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59633757574655538186201050803, ellLower := 351190620784735114436255224625,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7435809761977650670536264259, offsetUpper := 7452782770474058404832102640,
    supportELower := 47072697398710333479439103056, supportEUpper := 48434641046703246519170341481,
    supportLambdaLower := 351190620784735114436255224625,
    supportLambdaUpper := 359251432277490448061222718551,
    supportJLower := 50584603606557684623801655302, supportJUpper := 52027155369478150999782568667,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer16Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer16Panel6Data observer16Panel6Endpoints
theorem observer16_panel6_kernel_check : observer16Panel6Check = true := by
  decide +kernel
theorem observer16_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer16Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer16Panel6Data) s observer16Panel6Data.anchor ≤
        (observer16Panel6Endpoints.energyUpper : ℝ) ∧
      (observer16Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer16Panel6Data) s observer16Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer16Panel6Data) s observer16Panel6Data.anchor ≤
        (observer16Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer16Panel6Data) s observer16Panel6Data.anchor ≤
        (observer16Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer16Panel6Data) s observer16Panel6Data.anchor ≤
        (observer16Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer16Panel6Data observer16Panel6Endpoints
    observer16_panel6_kernel_check s hs
def observer16Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer16Panel6Endpoints
theorem observer16_panel6_recurrence_field_kernel_check :
    observer16Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer16_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer16Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer16Panel6Endpoints
    observer16_panel6_recurrence_field_kernel_check

def observer16Panel7Data : MainPanelData :=
  {
    observer := 16, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((18467043064 : ℚ) / 108092844349690725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer16Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61308895334987088964298195626, ellLower := 351034288216827179358838535674,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7648089387437892646323938883, offsetUpper := 7665546946239093636574954542,
    supportELower := 48434563158603972176250768670, supportEUpper := 49793340150482903750125028165,
    supportLambdaLower := 351034288216827179358838535674,
    supportLambdaUpper := 358849282861204672485401621323,
    supportJLower := 51944906040772243969839154026, supportJUpper := 53381832979094950474979044379,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer16Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer16Panel7Data observer16Panel7Endpoints
theorem observer16_panel7_kernel_check : observer16Panel7Check = true := by
  decide +kernel
theorem observer16_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer16Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer16Panel7Data) s observer16Panel7Data.anchor ≤
        (observer16Panel7Endpoints.energyUpper : ℝ) ∧
      (observer16Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer16Panel7Data) s observer16Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer16Panel7Data) s observer16Panel7Data.anchor ≤
        (observer16Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer16Panel7Data) s observer16Panel7Data.anchor ≤
        (observer16Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer16Panel7Data) s observer16Panel7Data.anchor ≤
        (observer16Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer16Panel7Data observer16Panel7Endpoints
    observer16_panel7_kernel_check s hs
def observer16Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer16Panel7Endpoints
theorem observer16_panel7_recurrence_field_kernel_check :
    observer16Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer16_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer16Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer16Panel7Endpoints
    observer16_panel7_recurrence_field_kernel_check

def observer16InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 16, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer16Panel0Endpoints, observer16Panel1Endpoints, observer16Panel2Endpoints, observer16Panel3Endpoints, observer16Panel4Endpoints, observer16Panel5Endpoints, observer16Panel6Endpoints, observer16Panel7Endpoints]
  }
def observer16FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer16InsertionEndpoints.frameLower
    observer16InsertionEndpoints.frameUpper
theorem observer16_frame_recurrence_field_kernel_check :
    observer16FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer16_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer16InsertionEndpoints.frameLower
      observer16InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer16InsertionEndpoints.frameLower
    observer16InsertionEndpoints.frameUpper
    observer16_frame_recurrence_field_kernel_check
def observer16RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer16Panel0Endpoints ∧
  panelRecurrenceFields observer16Panel1Endpoints ∧
  panelRecurrenceFields observer16Panel2Endpoints ∧
  panelRecurrenceFields observer16Panel3Endpoints ∧
  panelRecurrenceFields observer16Panel4Endpoints ∧
  panelRecurrenceFields observer16Panel5Endpoints ∧
  panelRecurrenceFields observer16Panel6Endpoints ∧
  panelRecurrenceFields observer16Panel7Endpoints ∧ insertionFrameRecurrenceFields observer16InsertionEndpoints.frameLower
      observer16InsertionEndpoints.frameUpper
theorem observer16_all_recurrence_fields :
    observer16RecurrenceFieldBounds := by
  exact ⟨observer16_panel0_recurrence_fields_sound,
    observer16_panel1_recurrence_fields_sound,
    observer16_panel2_recurrence_fields_sound,
    observer16_panel3_recurrence_fields_sound,
    observer16_panel4_recurrence_fields_sound,
    observer16_panel5_recurrence_fields_sound,
    observer16_panel6_recurrence_fields_sound,
    observer16_panel7_recurrence_fields_sound,
    observer16_frame_recurrence_fields_sound⟩
def observer16PanelFormulaBounds : Prop :=
  panelFormulaBounds observer16Panel0Data observer16Panel0Endpoints ∧
  panelFormulaBounds observer16Panel1Data observer16Panel1Endpoints ∧
  panelFormulaBounds observer16Panel2Data observer16Panel2Endpoints ∧
  panelFormulaBounds observer16Panel3Data observer16Panel3Endpoints ∧
  panelFormulaBounds observer16Panel4Data observer16Panel4Endpoints ∧
  panelFormulaBounds observer16Panel5Data observer16Panel5Endpoints ∧
  panelFormulaBounds observer16Panel6Data observer16Panel6Endpoints ∧
  panelFormulaBounds observer16Panel7Data observer16Panel7Endpoints
theorem observer16_all_panel_formula_bounds : observer16PanelFormulaBounds := by
  exact ⟨observer16_panel0_formula_sound,
    observer16_panel1_formula_sound,
    observer16_panel2_formula_sound,
    observer16_panel3_formula_sound,
    observer16_panel4_formula_sound,
    observer16_panel5_formula_sound,
    observer16_panel6_formula_sound,
    observer16_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
