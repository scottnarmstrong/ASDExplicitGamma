module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer9Panel0Data : MainPanelData :=
  {
    observer := 9, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((8443762 : ℚ) / 22599528525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer9Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 52930514086784685678136082100, ellLower := 361374162640084070869525448472,
    rhoLower := 99954810213661083768130804126051, rhoUpper := 99954910168521274850980541999136,
    offsetLower := 6604312668120676863947832183, offsetUpper := 6618953067690847622367644861,
    supportELower := 41907193881863098688978642604, supportEUpper := 43470356607683644512782271587,
    supportLambdaLower := 361374162640084070869525448472,
    supportLambdaUpper := 371466409268064564285846114898,
    supportJLower := 45520935508263939397673897088, supportJUpper := 47185020700364290155640732736,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer9Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer9Panel0Data observer9Panel0Endpoints
theorem observer9_panel0_kernel_check : observer9Panel0Check = true := by
  decide +kernel
theorem observer9_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer9Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer9Panel0Data) s observer9Panel0Data.anchor ≤
        (observer9Panel0Endpoints.energyUpper : ℝ) ∧
      (observer9Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer9Panel0Data) s observer9Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer9Panel0Data) s observer9Panel0Data.anchor ≤
        (observer9Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer9Panel0Data) s observer9Panel0Data.anchor ≤
        (observer9Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer9Panel0Data) s observer9Panel0Data.anchor ≤
        (observer9Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer9Panel0Data observer9Panel0Endpoints
    observer9_panel0_kernel_check s hs
def observer9Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer9Panel0Endpoints
theorem observer9_panel0_recurrence_field_kernel_check :
    observer9Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer9_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer9Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer9Panel0Endpoints
    observer9_panel0_recurrence_field_kernel_check

def observer9Panel1Data : MainPanelData :=
  {
    observer := 9, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((8443762 : ℚ) / 22599528525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer9Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 54688643405156486668817885051, ellLower := 361119830980426041814525684738,
    rhoLower := 99954810213661083768130804126051, rhoUpper := 99954910168521274850980541999136,
    offsetLower := 6828486013198926136927499540, offsetUpper := 6843623358857184100346249348,
    supportELower := 43470304069808722690552853445, supportEUpper := 44914059996302608977476605667,
    supportLambdaLower := 361119830980426041814525684738,
    supportLambdaUpper := 370816734921130008364427697342,
    supportJLower := 47081502379612983108698110292, supportJUpper := 48622227345513909061120882641,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer9Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer9Panel1Data observer9Panel1Endpoints
theorem observer9_panel1_kernel_check : observer9Panel1Check = true := by
  decide +kernel
theorem observer9_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer9Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer9Panel1Data) s observer9Panel1Data.anchor ≤
        (observer9Panel1Endpoints.energyUpper : ℝ) ∧
      (observer9Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer9Panel1Data) s observer9Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer9Panel1Data) s observer9Panel1Data.anchor ≤
        (observer9Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer9Panel1Data) s observer9Panel1Data.anchor ≤
        (observer9Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer9Panel1Data) s observer9Panel1Data.anchor ≤
        (observer9Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer9Panel1Data observer9Panel1Endpoints
    observer9_panel1_kernel_check s hs
def observer9Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer9Panel1Endpoints
theorem observer9_panel1_recurrence_field_kernel_check :
    observer9Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer9_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer9Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer9Panel1Endpoints
    observer9_panel1_recurrence_field_kernel_check

def observer9Panel2Data : MainPanelData :=
  {
    observer := 9, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((8443762 : ℚ) / 22599528525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer9Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 56427216379919300817739465149, ellLower := 360855160922736966043276463557,
    rhoLower := 99954810213661083768130804126051, rhoUpper := 99954910168521274850980541999136,
    offsetLower := 7050733792688866994435036105, offsetUpper := 7066363815853297880442742392,
    supportELower := 44914002504214459261113573474, supportEUpper := 46337941371896676193525743286,
    supportLambdaLower := 360855160922736966043276463557,
    supportLambdaUpper := 370201344867555340811443807356,
    supportJLower := 48522554113441828921546338109, supportJUpper := 50039954820572229601640181360,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer9Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer9Panel2Data observer9Panel2Endpoints
theorem observer9_panel2_kernel_check : observer9Panel2Check = true := by
  decide +kernel
theorem observer9_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer9Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer9Panel2Data) s observer9Panel2Data.anchor ≤
        (observer9Panel2Endpoints.energyUpper : ℝ) ∧
      (observer9Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer9Panel2Data) s observer9Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer9Panel2Data) s observer9Panel2Data.anchor ≤
        (observer9Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer9Panel2Data) s observer9Panel2Data.anchor ≤
        (observer9Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer9Panel2Data) s observer9Panel2Data.anchor ≤
        (observer9Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer9Panel2Data observer9Panel2Endpoints
    observer9_panel2_kernel_check s hs
def observer9Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer9Panel2Endpoints
theorem observer9_panel2_recurrence_field_kernel_check :
    observer9Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer9_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer9Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer9Panel2Endpoints
    observer9_panel2_recurrence_field_kernel_check

def observer9Panel3Data : MainPanelData :=
  {
    observer := 9, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((8443762 : ℚ) / 22599528525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer9Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 58155479220498716538973930617, ellLower := 360597447231250063581962728412,
    rhoLower := 99954910168521274850980541999134, rhoUpper := 99955010123481420843998809476645,
    offsetLower := 7255758045705572443650253419, offsetUpper := 7271878316806738228151200638,
    supportELower := 46337878962475961286532323905, supportEUpper := 47751263606872348118638914681,
    supportLambdaLower := 360597447231250063581962728412,
    supportLambdaUpper := 369618568442464022879828171375,
    supportJLower := 49943853434788461922351951189, supportJUpper := 51447449291296988347437196395,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer9Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer9Panel3Data observer9Panel3Endpoints
theorem observer9_panel3_kernel_check : observer9Panel3Check = true := by
  decide +kernel
theorem observer9_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer9Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer9Panel3Data) s observer9Panel3Data.anchor ≤
        (observer9Panel3Endpoints.energyUpper : ℝ) ∧
      (observer9Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer9Panel3Data) s observer9Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer9Panel3Data) s observer9Panel3Data.anchor ≤
        (observer9Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer9Panel3Data) s observer9Panel3Data.anchor ≤
        (observer9Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer9Panel3Data) s observer9Panel3Data.anchor ≤
        (observer9Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer9Panel3Data observer9Panel3Endpoints
    observer9_panel3_kernel_check s hs
def observer9Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer9Panel3Endpoints
theorem observer9_panel3_recurrence_field_kernel_check :
    observer9Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer9_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer9Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer9Panel3Endpoints
    observer9_panel3_recurrence_field_kernel_check

def observer9Panel4Data : MainPanelData :=
  {
    observer := 9, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((8443762 : ℚ) / 22599528525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer9Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 59876966739833501890602333534, ellLower := 360347776178402494600927203838,
    rhoLower := 99954910168521274850980541999134, rhoUpper := 99955010123481420843998809476645,
    offsetLower := 7475715178546000377645055925, offsetUpper := 7492324133061040671022607890,
    supportELower := 47751196300607335681579467704, supportEUpper := 49157584898519899770234432049,
    supportLambdaLower := 360347776178402494600927203838,
    supportLambdaUpper := 369066062846391075335791142744,
    supportJLower := 51354674062391360627588739742, supportJUpper := 52848245526983810523592343477,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer9Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer9Panel4Data observer9Panel4Endpoints
theorem observer9_panel4_kernel_check : observer9Panel4Check = true := by
  decide +kernel
theorem observer9_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer9Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer9Panel4Data) s observer9Panel4Data.anchor ≤
        (observer9Panel4Endpoints.energyUpper : ℝ) ∧
      (observer9Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer9Panel4Data) s observer9Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer9Panel4Data) s observer9Panel4Data.anchor ≤
        (observer9Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer9Panel4Data) s observer9Panel4Data.anchor ≤
        (observer9Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer9Panel4Data) s observer9Panel4Data.anchor ≤
        (observer9Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer9Panel4Data observer9Panel4Endpoints
    observer9_panel4_kernel_check s hs
def observer9Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer9Panel4Endpoints
theorem observer9_panel4_recurrence_field_kernel_check :
    observer9Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer9_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer9Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer9Panel4Endpoints
    observer9_panel4_recurrence_field_kernel_check

def observer9Panel5Data : MainPanelData :=
  {
    observer := 9, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((8443762 : ℚ) / 22599528525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer9Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 61593715317880191941841484456, ellLower := 360106230930408752175725283584,
    rhoLower := 99954910168521274850980541999134, rhoUpper := 99955010123481420843998809476645,
    offsetLower := 7695211602732491181330180955, offsetUpper := 7712308217095246067965227073,
    supportELower := 49157512709754944609833943423, supportEUpper := 50558724441607784123927083097,
    supportLambdaLower := 360106230930408752175725283584,
    supportLambdaUpper := 368541506802618593036866995297,
    supportJLower := 52758575019059032131591196258, supportJUpper := 54244139509633970054295753050,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer9Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer9Panel5Data observer9Panel5Endpoints
theorem observer9_panel5_kernel_check : observer9Panel5Check = true := by
  decide +kernel
theorem observer9_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer9Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer9Panel5Data) s observer9Panel5Data.anchor ≤
        (observer9Panel5Endpoints.energyUpper : ℝ) ∧
      (observer9Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer9Panel5Data) s observer9Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer9Panel5Data) s observer9Panel5Data.anchor ≤
        (observer9Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer9Panel5Data) s observer9Panel5Data.anchor ≤
        (observer9Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer9Panel5Data) s observer9Panel5Data.anchor ≤
        (observer9Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer9Panel5Data observer9Panel5Endpoints
    observer9_panel5_kernel_check s hs
def observer9Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer9Panel5Endpoints
theorem observer9_panel5_recurrence_field_kernel_check :
    observer9Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer9_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer9Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer9Panel5Endpoints
    observer9_panel5_recurrence_field_kernel_check

def observer9Panel6Data : MainPanelData :=
  {
    observer := 9, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((8443762 : ℚ) / 22599528525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer9Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 63306304817902964797237499057, ellLower := 359872615008883578247901461654,
    rhoLower := 99955010123481420843998809476643, rhoUpper := 99955110078541521847140566704584,
    offsetLower := 7896724931492745006038028735, offsetUpper := 7914308335283249354518941649,
    supportELower := 50558647381569741111451795584, supportEUpper := 51955764489080433654706933703,
    supportLambdaLower := 359872615008883578247901461654,
    supportLambdaUpper := 368042741451313374689920297499,
    supportJLower := 54157373531658576893930810200, supportJUpper := 55636191903593567401606136678,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer9Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer9Panel6Data observer9Panel6Endpoints
theorem observer9_panel6_kernel_check : observer9Panel6Check = true := by
  decide +kernel
theorem observer9_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer9Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer9Panel6Data) s observer9Panel6Data.anchor ≤
        (observer9Panel6Endpoints.energyUpper : ℝ) ∧
      (observer9Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer9Panel6Data) s observer9Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer9Panel6Data) s observer9Panel6Data.anchor ≤
        (observer9Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer9Panel6Data) s observer9Panel6Data.anchor ≤
        (observer9Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer9Panel6Data) s observer9Panel6Data.anchor ≤
        (observer9Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer9Panel6Data observer9Panel6Endpoints
    observer9_panel6_kernel_check s hs
def observer9Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer9Panel6Endpoints
theorem observer9_panel6_recurrence_field_kernel_check :
    observer9Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer9_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer9Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer9Panel6Endpoints
    observer9_panel6_recurrence_field_kernel_check

def observer9Panel7Data : MainPanelData :=
  {
    observer := 9, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((8443762 : ℚ) / 22599528525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer9Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 65015665142061479126266873182, ellLower := 359646634231362154734938220034,
    rhoLower := 99955010123481420843998809476643, rhoUpper := 99955110078541521847140566704584,
    offsetLower := 8115043556671634728386293062, offsetUpper := 8133113084086149180132489022,
    supportELower := 51955682567128349760960378527, supportEUpper := 53349414100798905878791215895,
    supportLambdaLower := 359646634231362154734938220034,
    supportLambdaUpper := 367567797623842454894362579671,
    supportJLower := 55552148909441971308309760727, supportJUpper := 57025092077037330427734841692,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer9Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer9Panel7Data observer9Panel7Endpoints
theorem observer9_panel7_kernel_check : observer9Panel7Check = true := by
  decide +kernel
theorem observer9_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer9Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer9Panel7Data) s observer9Panel7Data.anchor ≤
        (observer9Panel7Endpoints.energyUpper : ℝ) ∧
      (observer9Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer9Panel7Data) s observer9Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer9Panel7Data) s observer9Panel7Data.anchor ≤
        (observer9Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer9Panel7Data) s observer9Panel7Data.anchor ≤
        (observer9Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer9Panel7Data) s observer9Panel7Data.anchor ≤
        (observer9Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer9Panel7Data observer9Panel7Endpoints
    observer9_panel7_kernel_check s hs
def observer9Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer9Panel7Endpoints
theorem observer9_panel7_recurrence_field_kernel_check :
    observer9Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer9_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer9Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer9Panel7Endpoints
    observer9_panel7_recurrence_field_kernel_check

def observer9InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 9, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer9Panel0Endpoints, observer9Panel1Endpoints, observer9Panel2Endpoints, observer9Panel3Endpoints, observer9Panel4Endpoints, observer9Panel5Endpoints, observer9Panel6Endpoints, observer9Panel7Endpoints]
  }
def observer9FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer9InsertionEndpoints.frameLower
    observer9InsertionEndpoints.frameUpper
theorem observer9_frame_recurrence_field_kernel_check :
    observer9FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer9_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer9InsertionEndpoints.frameLower
      observer9InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer9InsertionEndpoints.frameLower
    observer9InsertionEndpoints.frameUpper
    observer9_frame_recurrence_field_kernel_check
def observer9RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer9Panel0Endpoints ∧
  panelRecurrenceFields observer9Panel1Endpoints ∧
  panelRecurrenceFields observer9Panel2Endpoints ∧
  panelRecurrenceFields observer9Panel3Endpoints ∧
  panelRecurrenceFields observer9Panel4Endpoints ∧
  panelRecurrenceFields observer9Panel5Endpoints ∧
  panelRecurrenceFields observer9Panel6Endpoints ∧
  panelRecurrenceFields observer9Panel7Endpoints ∧ insertionFrameRecurrenceFields observer9InsertionEndpoints.frameLower
      observer9InsertionEndpoints.frameUpper
theorem observer9_all_recurrence_fields :
    observer9RecurrenceFieldBounds := by
  exact ⟨observer9_panel0_recurrence_fields_sound,
    observer9_panel1_recurrence_fields_sound,
    observer9_panel2_recurrence_fields_sound,
    observer9_panel3_recurrence_fields_sound,
    observer9_panel4_recurrence_fields_sound,
    observer9_panel5_recurrence_fields_sound,
    observer9_panel6_recurrence_fields_sound,
    observer9_panel7_recurrence_fields_sound,
    observer9_frame_recurrence_fields_sound⟩
def observer9PanelFormulaBounds : Prop :=
  panelFormulaBounds observer9Panel0Data observer9Panel0Endpoints ∧
  panelFormulaBounds observer9Panel1Data observer9Panel1Endpoints ∧
  panelFormulaBounds observer9Panel2Data observer9Panel2Endpoints ∧
  panelFormulaBounds observer9Panel3Data observer9Panel3Endpoints ∧
  panelFormulaBounds observer9Panel4Data observer9Panel4Endpoints ∧
  panelFormulaBounds observer9Panel5Data observer9Panel5Endpoints ∧
  panelFormulaBounds observer9Panel6Data observer9Panel6Endpoints ∧
  panelFormulaBounds observer9Panel7Data observer9Panel7Endpoints
theorem observer9_all_panel_formula_bounds : observer9PanelFormulaBounds := by
  exact ⟨observer9_panel0_formula_sound,
    observer9_panel1_formula_sound,
    observer9_panel2_formula_sound,
    observer9_panel3_formula_sound,
    observer9_panel4_formula_sound,
    observer9_panel5_formula_sound,
    observer9_panel6_formula_sound,
    observer9_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
