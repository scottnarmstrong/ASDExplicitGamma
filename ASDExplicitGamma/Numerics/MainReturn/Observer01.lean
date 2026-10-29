module

public import ASDExplicitGamma.Numerics.MainReturn.Formula
public import ASDExplicitGamma.Numerics.MainReturn.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturn

open ASDExplicitGamma.Numerics

def observer1Panel0Data : MainPanelData :=
  {
    observer := 1, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 429751250729782081652393162900, ellLower := 863850379041103891494675417759,
    rhoLower := 99892058299010467479780301211660, rhoUpper := 99892158191118712536045966771041,
    offsetLower := 53649513124182127900557049860, offsetUpper := 53699207792955671452955836424,
    supportELower := 221577656998106174088776506014, supportEUpper := 224989849040646956482797012932,
    supportLambdaLower := 863850379041103891494675417759,
    supportLambdaUpper := 881200700468992293636661855491,
    supportJLower := 230216160788517213003723260191, supportJUpper := 233801856045336879419163631487,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer1Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel0Data observer1Panel0Endpoints
theorem observer1_panel0_kernel_check : observer1Panel0Check = true := by
  decide +kernel
theorem observer1_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel0Data) s observer1Panel0Data.anchor ≤
        (observer1Panel0Endpoints.energyUpper : ℝ) ∧
      (observer1Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel0Data) s observer1Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel0Data) s observer1Panel0Data.anchor ≤
        (observer1Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel0Data) s observer1Panel0Data.anchor ≤
        (observer1Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel0Data) s observer1Panel0Data.anchor ≤
        (observer1Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel0Data observer1Panel0Endpoints
    observer1_panel0_kernel_check s hs
def observer1Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel0Endpoints
theorem observer1_panel0_recurrence_field_kernel_check :
    observer1Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel0Endpoints
    observer1_panel0_recurrence_field_kernel_check

def observer1Panel1Data : MainPanelData :=
  {
    observer := 1, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 433291883171060575715619255244, ellLower := 858856996537289020778635538946,
    rhoLower := 99892657653158322188086861250101, rhoUpper := 99892757545865921691884408935779,
    offsetLower := 54103634359370802415491161412, offsetUpper := 54154030059196676638405394605,
    supportELower := 224989611816597988488258863980, supportEUpper := 228265951991088724402143241987,
    supportLambdaLower := 858856996537289020778635538946,
    supportLambdaUpper := 875561382230446699504482879793,
    supportJLower := 233578181781970878696045219369, supportJUpper := 237021565813393191397188070785,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer1Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel1Data observer1Panel1Endpoints
theorem observer1_panel1_kernel_check : observer1Panel1Check = true := by
  decide +kernel
theorem observer1_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel1Data) s observer1Panel1Data.anchor ≤
        (observer1Panel1Endpoints.energyUpper : ℝ) ∧
      (observer1Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel1Data) s observer1Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel1Data) s observer1Panel1Data.anchor ≤
        (observer1Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel1Data) s observer1Panel1Data.anchor ≤
        (observer1Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel1Data) s observer1Panel1Data.anchor ≤
        (observer1Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel1Data observer1Panel1Endpoints
    observer1_panel1_kernel_check s hs
def observer1Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel1Endpoints
theorem observer1_panel1_recurrence_field_kernel_check :
    observer1Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel1Endpoints
    observer1_panel1_recurrence_field_kernel_check

def observer1Panel2Data : MainPanelData :=
  {
    observer := 1, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 436799698222756628240798624882, ellLower := 854027277440766669690674194703,
    rhoLower := 99893257010902312571917909294339, rhoUpper := 99893356904209270119384812699240,
    offsetLower := 54543541277183778351277700076, offsetUpper := 54594632580103615401362488885,
    supportELower := 228265704882300574625740547194, supportEUpper := 231507066756567495909532458013,
    supportLambdaLower := 854027277440766669690674194703,
    supportLambdaUpper := 870146860881725440443270103003,
    supportJLower := 236805977656708241322647289141, supportJUpper := 240208535365384750313965159044,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer1Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel2Data observer1Panel2Endpoints
theorem observer1_panel2_kernel_check : observer1Panel2Check = true := by
  decide +kernel
theorem observer1_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel2Data) s observer1Panel2Data.anchor ≤
        (observer1Panel2Endpoints.energyUpper : ℝ) ∧
      (observer1Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel2Data) s observer1Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel2Data) s observer1Panel2Data.anchor ≤
        (observer1Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel2Data) s observer1Panel2Data.anchor ≤
        (observer1Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel2Data) s observer1Panel2Data.anchor ≤
        (observer1Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel2Data observer1Panel2Endpoints
    observer1_panel2_kernel_check s hs
def observer1Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel2Endpoints
theorem observer1_panel2_recurrence_field_kernel_check :
    observer1Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel2Endpoints
    observer1_panel2_recurrence_field_kernel_check

def observer1Panel3Data : MainPanelData :=
  {
    observer := 1, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 440284560821992283433114938092, ellLower := 849367103368943750146194213784,
    rhoLower := 99893856372242460208152229062924, rhoUpper := 99893956266148779395447538669545,
    offsetLower := 54969657526668052127646252834, offsetUpper := 55021439311597191362402231475,
    supportELower := 231506809875918803733387986038, supportEUpper := 234723205940367224740499537051,
    supportLambdaLower := 849367103368943750146194213784,
    supportLambdaUpper := 864942365439852379034448476907,
    supportJLower := 240000480909608241234849928175, supportJUpper := 243372629594765748530844021821,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer1Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel3Data observer1Panel3Endpoints
theorem observer1_panel3_kernel_check : observer1Panel3Check = true := by
  decide +kernel
theorem observer1_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel3Data) s observer1Panel3Data.anchor ≤
        (observer1Panel3Endpoints.energyUpper : ℝ) ∧
      (observer1Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel3Data) s observer1Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel3Data) s observer1Panel3Data.anchor ≤
        (observer1Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel3Data) s observer1Panel3Data.anchor ≤
        (observer1Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel3Data) s observer1Panel3Data.anchor ≤
        (observer1Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel3Data observer1Panel3Endpoints
    observer1_panel3_kernel_check s hs
def observer1Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel3Endpoints
theorem observer1_panel3_recurrence_field_kernel_check :
    observer1Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel3Endpoints
    observer1_panel3_recurrence_field_kernel_check

def observer1Panel4Data : MainPanelData :=
  {
    observer := 1, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 443750488739417402721594067638, ellLower := 844867210517801074080112131937,
    rhoLower := 99894355842772996706230909736835, rhoUpper := 99894455737178786673798065935494,
    offsetLower := 55435123564388974710278961481, offsetUpper := 55487591207634904438665717367,
    supportELower := 234722939379233308885171741874, supportEUpper := 237918528421452966469991805447,
    supportLambdaLower := 844867210517801074080112131937,
    supportLambdaUpper := 859933780708993817385809008433,
    supportJLower := 243171611484411319625972863193, supportJUpper := 246517866228542904643849895532,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer1Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel4Data observer1Panel4Endpoints
theorem observer1_panel4_kernel_check : observer1Panel4Check = true := by
  decide +kernel
theorem observer1_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel4Data) s observer1Panel4Data.anchor ≤
        (observer1Panel4Endpoints.energyUpper : ℝ) ∧
      (observer1Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel4Data) s observer1Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel4Data) s observer1Panel4Data.anchor ≤
        (observer1Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel4Data) s observer1Panel4Data.anchor ≤
        (observer1Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel4Data) s observer1Panel4Data.anchor ≤
        (observer1Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel4Data observer1Panel4Endpoints
    observer1_panel4_kernel_check s hs
def observer1Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel4Endpoints
theorem observer1_panel4_recurrence_field_kernel_check :
    observer1Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel4Endpoints
    observer1_panel4_recurrence_field_kernel_check

def observer1Panel5Data : MainPanelData :=
  {
    observer := 1, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 447199932428773312604142954569, ellLower := 840518299213920355963232396581,
    rhoLower := 99894955210706155345583265704522, rhoUpper := 99895055105711313545993127729537,
    offsetLower := 55836202113073614753725193808, offsetUpper := 55889351508629308000078245260,
    supportELower := 237918252261083953220313599826, supportEUpper := 241095373642878396896746174348,
    supportLambdaLower := 840518299213920355963232396581,
    supportLambdaUpper := 855108167962388710911686676584,
    supportJLower := 246323435253223156779945923791, supportJUpper := 249646455322502284005863041114,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer1Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel5Data observer1Panel5Endpoints
theorem observer1_panel5_kernel_check : observer1Panel5Check = true := by
  decide +kernel
theorem observer1_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel5Data) s observer1Panel5Data.anchor ≤
        (observer1Panel5Endpoints.energyUpper : ℝ) ∧
      (observer1Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel5Data) s observer1Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel5Data) s observer1Panel5Data.anchor ≤
        (observer1Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel5Data) s observer1Panel5Data.anchor ≤
        (observer1Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel5Data) s observer1Panel5Data.anchor ≤
        (observer1Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel5Data observer1Panel5Endpoints
    observer1_panel5_kernel_check s hs
def observer1Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel5Endpoints
theorem observer1_panel5_recurrence_field_kernel_check :
    observer1Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel5Endpoints
    observer1_panel5_recurrence_field_kernel_check

def observer1Panel6Data : MainPanelData :=
  {
    observer := 1, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 450633841888234281352786985918, ellLower := 836311642654795207424457951903,
    rhoLower := 99895454686730897897641322219442, rhoUpper := 99895554582235532372531831919815,
    offsetLower := 56278828936800300344824642118, offsetUpper := 56332656114068689435351364330,
    supportELower := 241095087958036604703158563542, supportEUpper := 244255290103191816280989832598,
    supportLambdaLower := 836311642654795207424457951903,
    supportLambdaUpper := 850453757270826096543160889138,
    supportJLower := 249458204384584556777403143061, supportJUpper := 252759827675900077246421441490,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer1Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel6Data observer1Panel6Endpoints
theorem observer1_panel6_kernel_check : observer1Panel6Check = true := by
  decide +kernel
theorem observer1_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel6Data) s observer1Panel6Data.anchor ≤
        (observer1Panel6Endpoints.energyUpper : ℝ) ∧
      (observer1Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel6Data) s observer1Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel6Data) s observer1Panel6Data.anchor ≤
        (observer1Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel6Data) s observer1Panel6Data.anchor ≤
        (observer1Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel6Data) s observer1Panel6Data.anchor ≤
        (observer1Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel6Data observer1Panel6Endpoints
    observer1_panel6_kernel_check s hs
def observer1Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel6Endpoints
theorem observer1_panel6_recurrence_field_kernel_check :
    observer1Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel6Endpoints
    observer1_panel6_recurrence_field_kernel_check

def observer1Panel7Data : MainPanelData :=
  {
    observer := 1, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 454053485365110791841541679440, ellLower := 832239167603800764507948338356,
    rhoLower := 99895954165253026816872854070067, rhoUpper := 99896054061257140063631627312873,
    offsetLower := 56710880252889833200366845044, offsetUpper := 56765381567664843301665885878,
    supportELower := 244254994963809466567738660173, supportEUpper := 247399412513504580884573684920,
    supportLambdaLower := 832239167603800764507948338356,
    supportLambdaUpper := 845959848855725554770178098051,
    supportJLower := 252577386639847474212818143556, supportJUpper := 255859011002061836432275465901,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer1Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel7Data observer1Panel7Endpoints
theorem observer1_panel7_kernel_check : observer1Panel7Check = true := by
  decide +kernel
theorem observer1_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel7Data) s observer1Panel7Data.anchor ≤
        (observer1Panel7Endpoints.energyUpper : ℝ) ∧
      (observer1Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel7Data) s observer1Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel7Data) s observer1Panel7Data.anchor ≤
        (observer1Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel7Data) s observer1Panel7Data.anchor ≤
        (observer1Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel7Data) s observer1Panel7Data.anchor ≤
        (observer1Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel7Data observer1Panel7Endpoints
    observer1_panel7_kernel_check s hs
def observer1Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel7Endpoints
theorem observer1_panel7_recurrence_field_kernel_check :
    observer1Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel7Endpoints
    observer1_panel7_recurrence_field_kernel_check

def observer1InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 1, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer1Panel0Endpoints, observer1Panel1Endpoints, observer1Panel2Endpoints, observer1Panel3Endpoints, observer1Panel4Endpoints, observer1Panel5Endpoints, observer1Panel6Endpoints, observer1Panel7Endpoints]
  }
def observer1FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer1InsertionEndpoints.frameLower
    observer1InsertionEndpoints.frameUpper
theorem observer1_frame_recurrence_field_kernel_check :
    observer1FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer1InsertionEndpoints.frameLower
      observer1InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer1InsertionEndpoints.frameLower
    observer1InsertionEndpoints.frameUpper
    observer1_frame_recurrence_field_kernel_check
def observer1RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer1Panel0Endpoints ∧
  panelRecurrenceFields observer1Panel1Endpoints ∧
  panelRecurrenceFields observer1Panel2Endpoints ∧
  panelRecurrenceFields observer1Panel3Endpoints ∧
  panelRecurrenceFields observer1Panel4Endpoints ∧
  panelRecurrenceFields observer1Panel5Endpoints ∧
  panelRecurrenceFields observer1Panel6Endpoints ∧
  panelRecurrenceFields observer1Panel7Endpoints ∧ insertionFrameRecurrenceFields observer1InsertionEndpoints.frameLower
      observer1InsertionEndpoints.frameUpper
theorem observer1_all_recurrence_fields :
    observer1RecurrenceFieldBounds := by
  exact ⟨observer1_panel0_recurrence_fields_sound,
    observer1_panel1_recurrence_fields_sound,
    observer1_panel2_recurrence_fields_sound,
    observer1_panel3_recurrence_fields_sound,
    observer1_panel4_recurrence_fields_sound,
    observer1_panel5_recurrence_fields_sound,
    observer1_panel6_recurrence_fields_sound,
    observer1_panel7_recurrence_fields_sound,
    observer1_frame_recurrence_fields_sound⟩
def observer1PanelFormulaBounds : Prop :=
  panelFormulaBounds observer1Panel0Data observer1Panel0Endpoints ∧
  panelFormulaBounds observer1Panel1Data observer1Panel1Endpoints ∧
  panelFormulaBounds observer1Panel2Data observer1Panel2Endpoints ∧
  panelFormulaBounds observer1Panel3Data observer1Panel3Endpoints ∧
  panelFormulaBounds observer1Panel4Data observer1Panel4Endpoints ∧
  panelFormulaBounds observer1Panel5Data observer1Panel5Endpoints ∧
  panelFormulaBounds observer1Panel6Data observer1Panel6Endpoints ∧
  panelFormulaBounds observer1Panel7Data observer1Panel7Endpoints
theorem observer1_all_panel_formula_bounds : observer1PanelFormulaBounds := by
  exact ⟨observer1_panel0_formula_sound,
    observer1_panel1_formula_sound,
    observer1_panel2_formula_sound,
    observer1_panel3_formula_sound,
    observer1_panel4_formula_sound,
    observer1_panel5_formula_sound,
    observer1_panel6_formula_sound,
    observer1_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturn
