module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer8Panel0Data : MainPanelData :=
  {
    observer := 8, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2814424 : ℚ) / 2511058725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer8Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 55600466149005419178413881663, ellLower := 368221073301077643219838512636,
    rhoLower := 99953910624417318487548048978659, rhoUpper := 99954010578377919876837734454770,
    offsetLower := 6944288270052468826366302764, offsetUpper := 6959381069476070696300092545,
    supportELower := 44353204924089946238749297063, supportEUpper := 45943778015729410961798529557,
    supportLambdaLower := 368221073301077643219838512636,
    supportLambdaUpper := 378412628195597599923828129072,
    supportJLower := 48035415657100722670947682189, supportJUpper := 49727904297685386961036810848,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer8Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer8Panel0Data observer8Panel0Endpoints
theorem observer8_panel0_kernel_check : observer8Panel0Check = true := by
  decide +kernel
theorem observer8_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer8Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer8Panel0Data) s observer8Panel0Data.anchor ≤
        (observer8Panel0Endpoints.energyUpper : ℝ) ∧
      (observer8Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer8Panel0Data) s observer8Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer8Panel0Data) s observer8Panel0Data.anchor ≤
        (observer8Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer8Panel0Data) s observer8Panel0Data.anchor ≤
        (observer8Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer8Panel0Data) s observer8Panel0Data.anchor ≤
        (observer8Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer8Panel0Data observer8Panel0Endpoints
    observer8_panel0_kernel_check s hs
def observer8Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer8Panel0Endpoints
theorem observer8_panel0_recurrence_field_kernel_check :
    observer8Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer8_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer8Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer8Panel0Endpoints
    observer8_panel0_recurrence_field_kernel_check

def observer8Panel1Data : MainPanelData :=
  {
    observer := 8, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2814424 : ℚ) / 2511058725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer8Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 57385128423901737709139436384, ellLower := 367902554414674759375896000101,
    rhoLower := 99954010578377919876837734454768, rhoUpper := 99954110532438475276705806180257,
    offsetLower := 7157800231945141849808483323, offsetUpper := 7173390981540745315349934784,
    supportELower := 45943722947404508819967688542, supportEUpper := 47414690378754255264335262329,
    supportLambdaLower := 367902554414674759375896000101,
    supportLambdaUpper := 377695352060526814222545019384,
    supportJLower := 49622748491551256413726648543, supportJUpper := 51191643899359523406560712523,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer8Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer8Panel1Data observer8Panel1Endpoints
theorem observer8_panel1_kernel_check : observer8Panel1Check = true := by
  decide +kernel
theorem observer8_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer8Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer8Panel1Data) s observer8Panel1Data.anchor ≤
        (observer8Panel1Endpoints.energyUpper : ℝ) ∧
      (observer8Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer8Panel1Data) s observer8Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer8Panel1Data) s observer8Panel1Data.anchor ≤
        (observer8Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer8Panel1Data) s observer8Panel1Data.anchor ≤
        (observer8Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer8Panel1Data) s observer8Panel1Data.anchor ≤
        (observer8Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer8Panel1Data observer8Panel1Endpoints
    observer8_panel1_kernel_check s hs
def observer8Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer8Panel1Endpoints
theorem observer8_panel1_recurrence_field_kernel_check :
    observer8Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer8_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer8Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer8Panel1Endpoints
    observer8_panel1_recurrence_field_kernel_check

def observer8Panel2Data : MainPanelData :=
  {
    observer := 8, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2814424 : ℚ) / 2511058725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer8Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 59150068051733804403787317077, ellLower := 367576055229247227387683112664,
    rhoLower := 99954010578377919876837734454768, rhoUpper := 99954110532438475276705806180257,
    offsetLower := 7384499317914335609474106948, offsetUpper := 7400583851712957744979134329,
    supportELower := 47414630272783926001923908346, supportEUpper := 48865588611204893985513107010,
    supportLambdaLower := 367576055229247227387683112664,
    supportLambdaUpper := 377014941628220250729320482636,
    supportJLower := 51090390825076398275800739472, supportJUpper := 52635738027487096492806311837,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer8Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer8Panel2Data observer8Panel2Endpoints
theorem observer8_panel2_kernel_check : observer8Panel2Check = true := by
  decide +kernel
theorem observer8_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer8Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer8Panel2Data) s observer8Panel2Data.anchor ≤
        (observer8Panel2Endpoints.energyUpper : ℝ) ∧
      (observer8Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer8Panel2Data) s observer8Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer8Panel2Data) s observer8Panel2Data.anchor ≤
        (observer8Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer8Panel2Data) s observer8Panel2Data.anchor ≤
        (observer8Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer8Panel2Data) s observer8Panel2Data.anchor ≤
        (observer8Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer8Panel2Data observer8Panel2Endpoints
    observer8_panel2_kernel_check s hs
def observer8Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer8Panel2Endpoints
theorem observer8_panel2_recurrence_field_kernel_check :
    observer8Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer8_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer8Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer8Panel2Endpoints
    observer8_panel2_recurrence_field_kernel_check

def observer8Panel3Data : MainPanelData :=
  {
    observer := 8, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2814424 : ℚ) / 2511058725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer8Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 60904535847494790659247618285, ellLower := 367258714702861812104162642175,
    rhoLower := 99954010578377919876837734454768, rhoUpper := 99954110532438475276705806180257,
    offsetLower := 7610103205813874679682168278, offsetUpper := 7626679138311826045860191283,
    supportELower := 48865523505429024442154446119, supportEUpper := 50305741969256755161249856194,
    supportLambdaLower := 367258714702861812104162642175,
    supportLambdaUpper := 376369548413667061157930641766,
    supportJLower := 52538110652457642563196072540, supportJUpper := 54069437453393425772829162612,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer8Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer8Panel3Data observer8Panel3Endpoints
theorem observer8_panel3_kernel_check : observer8Panel3Check = true := by
  decide +kernel
theorem observer8_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer8Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer8Panel3Data) s observer8Panel3Data.anchor ≤
        (observer8Panel3Endpoints.energyUpper : ℝ) ∧
      (observer8Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer8Panel3Data) s observer8Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer8Panel3Data) s observer8Panel3Data.anchor ≤
        (observer8Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer8Panel3Data) s observer8Panel3Data.anchor ≤
        (observer8Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer8Panel3Data) s observer8Panel3Data.anchor ≤
        (observer8Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer8Panel3Data observer8Panel3Endpoints
    observer8_panel3_kernel_check s hs
def observer8Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer8Panel3Endpoints
theorem observer8_panel3_recurrence_field_kernel_check :
    observer8Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer8_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer8Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer8Panel3Endpoints
    observer8_panel3_recurrence_field_kernel_check

def observer8Panel4Data : MainPanelData :=
  {
    observer := 8, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2814424 : ℚ) / 2511058725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer8Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 62652071012112558277084835295, ellLower := 366951478603620674210976146056,
    rhoLower := 99954110532438475276705806180255, rhoUpper := 99954210486598984787106324710530,
    offsetLower := 7817948727519253262121480555, offsetUpper := 7835014567357338472487338707,
    supportELower := 50305671885080236312291804940, supportEUpper := 51738714634369784061906915667,
    supportLambdaLower := 366951478603620674210976146056,
    supportLambdaUpper := 375756669999344615328620811991,
    supportJLower := 53975186671116443054401566400, supportJUpper := 55496281334363230215193123787,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer8Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer8Panel4Data observer8Panel4Endpoints
theorem observer8_panel4_kernel_check : observer8Panel4Check = true := by
  decide +kernel
theorem observer8_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer8Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer8Panel4Data) s observer8Panel4Data.anchor ≤
        (observer8Panel4Endpoints.energyUpper : ℝ) ∧
      (observer8Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer8Panel4Data) s observer8Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer8Panel4Data) s observer8Panel4Data.anchor ≤
        (observer8Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer8Panel4Data) s observer8Panel4Data.anchor ≤
        (observer8Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer8Panel4Data) s observer8Panel4Data.anchor ≤
        (observer8Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer8Panel4Data observer8Panel4Endpoints
    observer8_panel4_kernel_check s hs
def observer8Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer8Panel4Endpoints
theorem observer8_panel4_recurrence_field_kernel_check :
    observer8Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer8_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer8Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer8Panel4Endpoints
    observer8_panel4_recurrence_field_kernel_check

def observer8Panel5Data : MainPanelData :=
  {
    observer := 8, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2814424 : ℚ) / 2511058725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer8Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 64394714109721306685272328495, ellLower := 366654302897696167805757642093,
    rhoLower := 99954110532438475276705806180255, rhoUpper := 99954210486598984787106324710530,
    offsetLower := 8041914690155281984407990143, offsetUpper := 8059469426426529384482433219,
    supportELower := 51738639587014250742966850768, supportEUpper := 53166331424354607217234622871,
    supportLambdaLower := 366654302897696167805757642093,
    supportLambdaUpper := 375173841222084088561025276613,
    supportJLower := 55405182615991212421024427188, supportJUpper := 56918069836575448102844875638,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer8Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer8Panel5Data observer8Panel5Endpoints
theorem observer8_panel5_kernel_check : observer8Panel5Check = true := by
  decide +kernel
theorem observer8_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer8Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer8Panel5Data) s observer8Panel5Data.anchor ≤
        (observer8Panel5Endpoints.energyUpper : ℝ) ∧
      (observer8Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer8Panel5Data) s observer8Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer8Panel5Data) s observer8Panel5Data.anchor ≤
        (observer8Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer8Panel5Data) s observer8Panel5Data.anchor ≤
        (observer8Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer8Panel5Data) s observer8Panel5Data.anchor ≤
        (observer8Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer8Panel5Data observer8Panel5Endpoints
    observer8_panel5_kernel_check s hs
def observer8Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer8Panel5Endpoints
theorem observer8_panel5_recurrence_field_kernel_check :
    observer8Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer8_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer8Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer8Panel5Endpoints
    observer8_panel5_recurrence_field_kernel_check

def observer8Panel6Data : MainPanelData :=
  {
    observer := 8, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2814424 : ℚ) / 2511058725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer8Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 66133048996835880522948481618, ellLower := 366366875535150874408032742494,
    rhoLower := 99954210486598984787106324710528, rhoUpper := 99954310440859448507993450555108,
    offsetLower := 8247442809539744150620304228, offsetUpper := 8265485597919654684153122352,
    supportELower := 53166251425887742217802800232, supportEUpper := 54589679887534829923373640795,
    supportLambdaLower := 366366875535150874408032742494,
    supportLambdaUpper := 374618773009201650906175699285,
    supportJLower := 56829920181239250961883127656, supportJUpper := 58335867617626846432435397788,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer8Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer8Panel6Data observer8Panel6Endpoints
theorem observer8_panel6_kernel_check : observer8Panel6Check = true := by
  decide +kernel
theorem observer8_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer8Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer8Panel6Data) s observer8Panel6Data.anchor ≤
        (observer8Panel6Endpoints.energyUpper : ℝ) ∧
      (observer8Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer8Panel6Data) s observer8Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer8Panel6Data) s observer8Panel6Data.anchor ≤
        (observer8Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer8Panel6Data) s observer8Panel6Data.anchor ≤
        (observer8Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer8Panel6Data) s observer8Panel6Data.anchor ≤
        (observer8Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer8Panel6Data observer8Panel6Endpoints
    observer8_panel6_kernel_check s hs
def observer8Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer8Panel6Endpoints
theorem observer8_panel6_recurrence_field_kernel_check :
    observer8Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer8_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer8Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer8Panel6Endpoints
    observer8_panel6_recurrence_field_kernel_check

def observer8Panel7Data : MainPanelData :=
  {
    observer := 8, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2814424 : ℚ) / 2511058725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer8Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 67868009389943258918911854851, ellLower := 366088796975568072328861501324,
    rhoLower := 99954210486598984787106324710528, rhoUpper := 99954310440859448507993450555108,
    offsetLower := 8470238516969042265182485394, offsetUpper := 8488768711675244574306389147,
    supportELower := 54589594948122635243850569914, supportEUpper := 56009474080752891345694687815,
    supportLambdaLower := 366088796975568072328861501324,
    supportLambdaUpper := 374089377926658217980341409440,
    supportJLower := 58250482917878315967139184927, supportJUpper := 59750367860019473525498101910,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer8Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer8Panel7Data observer8Panel7Endpoints
theorem observer8_panel7_kernel_check : observer8Panel7Check = true := by
  decide +kernel
theorem observer8_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer8Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer8Panel7Data) s observer8Panel7Data.anchor ≤
        (observer8Panel7Endpoints.energyUpper : ℝ) ∧
      (observer8Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer8Panel7Data) s observer8Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer8Panel7Data) s observer8Panel7Data.anchor ≤
        (observer8Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer8Panel7Data) s observer8Panel7Data.anchor ≤
        (observer8Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer8Panel7Data) s observer8Panel7Data.anchor ≤
        (observer8Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer8Panel7Data observer8Panel7Endpoints
    observer8_panel7_kernel_check s hs
def observer8Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer8Panel7Endpoints
theorem observer8_panel7_recurrence_field_kernel_check :
    observer8Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer8_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer8Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer8Panel7Endpoints
    observer8_panel7_recurrence_field_kernel_check

def observer8InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 8, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer8Panel0Endpoints, observer8Panel1Endpoints, observer8Panel2Endpoints, observer8Panel3Endpoints, observer8Panel4Endpoints, observer8Panel5Endpoints, observer8Panel6Endpoints, observer8Panel7Endpoints]
  }
def observer8FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer8InsertionEndpoints.frameLower
    observer8InsertionEndpoints.frameUpper
theorem observer8_frame_recurrence_field_kernel_check :
    observer8FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer8_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer8InsertionEndpoints.frameLower
      observer8InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer8InsertionEndpoints.frameLower
    observer8InsertionEndpoints.frameUpper
    observer8_frame_recurrence_field_kernel_check
def observer8RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer8Panel0Endpoints ∧
  panelRecurrenceFields observer8Panel1Endpoints ∧
  panelRecurrenceFields observer8Panel2Endpoints ∧
  panelRecurrenceFields observer8Panel3Endpoints ∧
  panelRecurrenceFields observer8Panel4Endpoints ∧
  panelRecurrenceFields observer8Panel5Endpoints ∧
  panelRecurrenceFields observer8Panel6Endpoints ∧
  panelRecurrenceFields observer8Panel7Endpoints ∧ insertionFrameRecurrenceFields observer8InsertionEndpoints.frameLower
      observer8InsertionEndpoints.frameUpper
theorem observer8_all_recurrence_fields :
    observer8RecurrenceFieldBounds := by
  exact ⟨observer8_panel0_recurrence_fields_sound,
    observer8_panel1_recurrence_fields_sound,
    observer8_panel2_recurrence_fields_sound,
    observer8_panel3_recurrence_fields_sound,
    observer8_panel4_recurrence_fields_sound,
    observer8_panel5_recurrence_fields_sound,
    observer8_panel6_recurrence_fields_sound,
    observer8_panel7_recurrence_fields_sound,
    observer8_frame_recurrence_fields_sound⟩
def observer8PanelFormulaBounds : Prop :=
  panelFormulaBounds observer8Panel0Data observer8Panel0Endpoints ∧
  panelFormulaBounds observer8Panel1Data observer8Panel1Endpoints ∧
  panelFormulaBounds observer8Panel2Data observer8Panel2Endpoints ∧
  panelFormulaBounds observer8Panel3Data observer8Panel3Endpoints ∧
  panelFormulaBounds observer8Panel4Data observer8Panel4Endpoints ∧
  panelFormulaBounds observer8Panel5Data observer8Panel5Endpoints ∧
  panelFormulaBounds observer8Panel6Data observer8Panel6Endpoints ∧
  panelFormulaBounds observer8Panel7Data observer8Panel7Endpoints
theorem observer8_all_panel_formula_bounds : observer8PanelFormulaBounds := by
  exact ⟨observer8_panel0_formula_sound,
    observer8_panel1_formula_sound,
    observer8_panel2_formula_sound,
    observer8_panel3_formula_sound,
    observer8_panel4_formula_sound,
    observer8_panel5_formula_sound,
    observer8_panel6_formula_sound,
    observer8_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
