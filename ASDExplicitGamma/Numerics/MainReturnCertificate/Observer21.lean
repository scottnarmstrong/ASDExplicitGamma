module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer21Panel0Data : MainPanelData :=
  {
    observer := 21, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((4487491523842 : ℚ) / 6382774366004887620525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer21Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49398041535067277384076517769, ellLower := 352033628563499566451298552763,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172807221550035790878425168, offsetUpper := 6186833235681457672172385765,
    supportELower := 38570412612835751287313813739, supportEUpper := 40096183756600564290084304099,
    supportLambdaLower := 352033628563499566451298552763,
    supportLambdaUpper := 361990403584593861832468296892,
    supportJLower := 42090748898470746951826799266, supportJUpper := 43716087792446502908408987068,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer21Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer21Panel0Data observer21Panel0Endpoints
theorem observer21_panel0_kernel_check : observer21Panel0Check = true := by
  decide +kernel
theorem observer21_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer21Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer21Panel0Data) s observer21Panel0Data.anchor ≤
        (observer21Panel0Endpoints.energyUpper : ℝ) ∧
      (observer21Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer21Panel0Data) s observer21Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer21Panel0Data) s observer21Panel0Data.anchor ≤
        (observer21Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer21Panel0Data) s observer21Panel0Data.anchor ≤
        (observer21Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer21Panel0Data) s observer21Panel0Data.anchor ≤
        (observer21Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer21Panel0Data observer21Panel0Endpoints
    observer21_panel0_kernel_check s hs
def observer21Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer21Panel0Endpoints
theorem observer21_panel0_recurrence_field_kernel_check :
    observer21Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer21_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer21Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer21Panel0Endpoints
    observer21_panel0_recurrence_field_kernel_check

def observer21Panel1Data : MainPanelData :=
  {
    observer := 21, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((4487491523842 : ℚ) / 6382774366004887620525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer21Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51119976224461683493472321383, ellLower := 351866860753329733739869096098,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376486915756940670916138794, offsetUpper := 6391008747628793098719894072,
    supportELower := 40096134670693573987779124629, supportEUpper := 41502770298490980907743978444,
    supportLambdaLower := 351866860753329733739869096098,
    supportLambdaUpper := 361432951012774602485915919127,
    supportJLower := 43614803278226871325177815589, supportJUpper := 45117099808618726932603137636,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer21Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer21Panel1Data observer21Panel1Endpoints
theorem observer21_panel1_kernel_check : observer21Panel1Check = true := by
  decide +kernel
theorem observer21_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer21Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer21Panel1Data) s observer21Panel1Data.anchor ≤
        (observer21Panel1Endpoints.energyUpper : ℝ) ∧
      (observer21Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer21Panel1Data) s observer21Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer21Panel1Data) s observer21Panel1Data.anchor ≤
        (observer21Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer21Panel1Data) s observer21Panel1Data.anchor ≤
        (observer21Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer21Panel1Data) s observer21Panel1Data.anchor ≤
        (observer21Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer21Panel1Data observer21Panel1Endpoints
    observer21_panel1_kernel_check s hs
def observer21Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer21Panel1Endpoints
theorem observer21_panel1_recurrence_field_kernel_check :
    observer21Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer21_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer21Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer21Panel1Endpoints
    observer21_panel1_recurrence_field_kernel_check

def observer21Panel2Data : MainPanelData :=
  {
    observer := 21, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((4487491523842 : ℚ) / 6382774366004887620525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer21Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52822581440035281174067891744, ellLower := 351686537717566612258232832907,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6592240958962088302205289713, offsetUpper := 6607254149787937048063469479,
    supportELower := 41502716372184041627082086912, supportEUpper := 42889796911631325154832249489,
    supportLambdaLower := 351686537717566612258232832907,
    supportLambdaUpper := 360906261285650584996417712885,
    supportJLower := 45019581749359707749664415241, supportJUpper := 46498859524487831004796426618,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer21Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer21Panel2Data observer21Panel2Endpoints
theorem observer21_panel2_kernel_check : observer21Panel2Check = true := by
  decide +kernel
theorem observer21_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer21Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer21Panel2Data) s observer21Panel2Data.anchor ≤
        (observer21Panel2Endpoints.energyUpper : ℝ) ∧
      (observer21Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer21Panel2Data) s observer21Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer21Panel2Data) s observer21Panel2Data.anchor ≤
        (observer21Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer21Panel2Data) s observer21Panel2Data.anchor ≤
        (observer21Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer21Panel2Data) s observer21Panel2Data.anchor ≤
        (observer21Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer21Panel2Data observer21Panel2Endpoints
    observer21_panel2_kernel_check s hs
def observer21Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer21Panel2Endpoints
theorem observer21_panel2_recurrence_field_kernel_check :
    observer21Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer21_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer21Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer21Panel2Endpoints
    observer21_panel2_recurrence_field_kernel_check

def observer21Panel3Data : MainPanelData :=
  {
    observer := 21, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((4487491523842 : ℚ) / 6382774366004887620525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer21Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54515097108421977495079492343, ellLower := 351510166760466216587875225650,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806880016505092893534296919, offsetUpper := 6822382027012994160914790937,
    supportELower := 42889738180496533971908886505, supportEUpper := 44266517759944065536751800742,
    supportLambdaLower := 351510166760466216587875225650,
    supportLambdaUpper := 360408906307580481361877604146,
    supportJLower := 46404839848101196137787638761, supportJUpper := 47870606823019870350370576784,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer21Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer21Panel3Data observer21Panel3Endpoints
theorem observer21_panel3_kernel_check : observer21Panel3Check = true := by
  decide +kernel
theorem observer21_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer21Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer21Panel3Data) s observer21Panel3Data.anchor ≤
        (observer21Panel3Endpoints.energyUpper : ℝ) ∧
      (observer21Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer21Panel3Data) s observer21Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer21Panel3Data) s observer21Panel3Data.anchor ≤
        (observer21Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer21Panel3Data) s observer21Panel3Data.anchor ≤
        (observer21Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer21Panel3Data) s observer21Panel3Data.anchor ≤
        (observer21Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer21Panel3Data observer21Panel3Endpoints
    observer21_panel3_kernel_check s hs
def observer21Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer21Panel3Endpoints
theorem observer21_panel3_recurrence_field_kernel_check :
    observer21Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer21_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer21Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer21Panel3Endpoints
    observer21_panel3_recurrence_field_kernel_check

def observer21Panel4Data : MainPanelData :=
  {
    observer := 21, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((4487491523842 : ℚ) / 6382774366004887620525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer21Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56201052056579136451446186694, ellLower := 351339025821144513336323246454,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020810462515725097034461494, offsetUpper := 7036799678911489151293467210,
    supportELower := 44266454243219239152310343757, supportEUpper := 45636482877341011516482909343,
    supportLambdaLower := 351339025821144513336323246454,
    supportLambdaUpper := 359938761018805461478110595627,
    supportJLower := 47779844501430684285673576221, supportJUpper := 49235870487529066131264015300,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer21Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer21Panel4Data observer21Panel4Endpoints
theorem observer21_panel4_kernel_check : observer21Panel4Check = true := by
  decide +kernel
theorem observer21_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer21Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer21Panel4Data) s observer21Panel4Data.anchor ≤
        (observer21Panel4Endpoints.energyUpper : ℝ) ∧
      (observer21Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer21Panel4Data) s observer21Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer21Panel4Data) s observer21Panel4Data.anchor ≤
        (observer21Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer21Panel4Data) s observer21Panel4Data.anchor ≤
        (observer21Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer21Panel4Data) s observer21Panel4Data.anchor ≤
        (observer21Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer21Panel4Data observer21Panel4Endpoints
    observer21_panel4_kernel_check s hs
def observer21Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer21Panel4Endpoints
theorem observer21_panel4_recurrence_field_kernel_check :
    observer21Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer21_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer21Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer21Panel4Endpoints
    observer21_panel4_recurrence_field_kernel_check

def observer21Panel5Data : MainPanelData :=
  {
    observer := 21, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((4487491523842 : ℚ) / 6382774366004887620525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer21Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57882476956512014866437485179, ellLower := 351173371583976906856883166565,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217794845948117450710567776, offsetUpper := 7234270212743007430652159500,
    supportELower := 45636414588173724715093006390, supportEUpper := 47001503787838148370971808104,
    supportLambdaLower := 351173371583976906856883166565,
    supportLambdaUpper := 359493700422726565474776433191,
    supportJLower := 49148148304013493783661838055, supportJUpper := 50596440792065414025719572436,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer21Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer21Panel5Data observer21Panel5Endpoints
theorem observer21_panel5_kernel_check : observer21Panel5Check = true := by
  decide +kernel
theorem observer21_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer21Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer21Panel5Data) s observer21Panel5Data.anchor ≤
        (observer21Panel5Endpoints.energyUpper : ℝ) ∧
      (observer21Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer21Panel5Data) s observer21Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer21Panel5Data) s observer21Panel5Data.anchor ≤
        (observer21Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer21Panel5Data) s observer21Panel5Data.anchor ≤
        (observer21Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer21Panel5Data) s observer21Panel5Data.anchor ≤
        (observer21Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer21Panel5Data observer21Panel5Endpoints
    observer21_panel5_kernel_check s hs
def observer21Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer21Panel5Endpoints
theorem observer21_panel5_recurrence_field_kernel_check :
    observer21Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer21_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer21Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer21Panel5Endpoints
    observer21_panel5_recurrence_field_kernel_check

def observer21Panel6Data : MainPanelData :=
  {
    observer := 21, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((4487491523842 : ℚ) / 6382774366004887620525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer21Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59559946223987511442942932564, ellLower := 351013165226173284715521999366,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7430360668712226797346907750, offsetUpper := 7447321239086997170212281940,
    supportELower := 47001430736308202966168616411, supportEUpper := 48362655520604227574961818381,
    supportLambdaLower := 351013165226173284715521999366,
    supportLambdaUpper := 359071743287350751917757046622,
    supportJLower := 50511562388569935813323836404, supportJUpper := 51953372953477735094139388848,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer21Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer21Panel6Data observer21Panel6Endpoints
theorem observer21_panel6_kernel_check : observer21Panel6Check = true := by
  decide +kernel
theorem observer21_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer21Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer21Panel6Data) s observer21Panel6Data.anchor ≤
        (observer21Panel6Endpoints.energyUpper : ℝ) ∧
      (observer21Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer21Panel6Data) s observer21Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer21Panel6Data) s observer21Panel6Data.anchor ≤
        (observer21Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer21Panel6Data) s observer21Panel6Data.anchor ≤
        (observer21Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer21Panel6Data) s observer21Panel6Data.anchor ≤
        (observer21Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer21Panel6Data observer21Panel6Endpoints
    observer21_panel6_kernel_check s hs
def observer21Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer21Panel6Endpoints
theorem observer21_panel6_recurrence_field_kernel_check :
    observer21Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer21_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer21Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer21Panel6Endpoints
    observer21_panel6_recurrence_field_kernel_check

def observer21Panel7Data : MainPanelData :=
  {
    observer := 21, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((4487491523842 : ℚ) / 6382774366004887620525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer21Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61234384557747376119397152469, ellLower := 350858256288342996677474441043,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642626926553133403022741628, offsetUpper := 7660072016719716762208583938,
    supportELower := 48362577714969826011315772076, supportEUpper := 49720640318780414483685866234,
    supportLambdaLower := 350858256288342996677474441043,
    supportLambdaUpper := 358671081774243398400707340771,
    supportJLower := 51871160277853255978090516486, supportJUpper := 53307351136522848467692939642,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer21Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer21Panel7Data observer21Panel7Endpoints
theorem observer21_panel7_kernel_check : observer21Panel7Check = true := by
  decide +kernel
theorem observer21_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer21Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer21Panel7Data) s observer21Panel7Data.anchor ≤
        (observer21Panel7Endpoints.energyUpper : ℝ) ∧
      (observer21Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer21Panel7Data) s observer21Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer21Panel7Data) s observer21Panel7Data.anchor ≤
        (observer21Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer21Panel7Data) s observer21Panel7Data.anchor ≤
        (observer21Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer21Panel7Data) s observer21Panel7Data.anchor ≤
        (observer21Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer21Panel7Data observer21Panel7Endpoints
    observer21_panel7_kernel_check s hs
def observer21Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer21Panel7Endpoints
theorem observer21_panel7_recurrence_field_kernel_check :
    observer21Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer21_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer21Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer21Panel7Endpoints
    observer21_panel7_recurrence_field_kernel_check

def observer21InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 21, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer21Panel0Endpoints, observer21Panel1Endpoints, observer21Panel2Endpoints, observer21Panel3Endpoints, observer21Panel4Endpoints, observer21Panel5Endpoints, observer21Panel6Endpoints, observer21Panel7Endpoints]
  }
def observer21FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer21InsertionEndpoints.frameLower
    observer21InsertionEndpoints.frameUpper
theorem observer21_frame_recurrence_field_kernel_check :
    observer21FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer21_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer21InsertionEndpoints.frameLower
      observer21InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer21InsertionEndpoints.frameLower
    observer21InsertionEndpoints.frameUpper
    observer21_frame_recurrence_field_kernel_check
def observer21RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer21Panel0Endpoints ∧
  panelRecurrenceFields observer21Panel1Endpoints ∧
  panelRecurrenceFields observer21Panel2Endpoints ∧
  panelRecurrenceFields observer21Panel3Endpoints ∧
  panelRecurrenceFields observer21Panel4Endpoints ∧
  panelRecurrenceFields observer21Panel5Endpoints ∧
  panelRecurrenceFields observer21Panel6Endpoints ∧
  panelRecurrenceFields observer21Panel7Endpoints ∧ insertionFrameRecurrenceFields observer21InsertionEndpoints.frameLower
      observer21InsertionEndpoints.frameUpper
theorem observer21_all_recurrence_fields :
    observer21RecurrenceFieldBounds := by
  exact ⟨observer21_panel0_recurrence_fields_sound,
    observer21_panel1_recurrence_fields_sound,
    observer21_panel2_recurrence_fields_sound,
    observer21_panel3_recurrence_fields_sound,
    observer21_panel4_recurrence_fields_sound,
    observer21_panel5_recurrence_fields_sound,
    observer21_panel6_recurrence_fields_sound,
    observer21_panel7_recurrence_fields_sound,
    observer21_frame_recurrence_fields_sound⟩
def observer21PanelFormulaBounds : Prop :=
  panelFormulaBounds observer21Panel0Data observer21Panel0Endpoints ∧
  panelFormulaBounds observer21Panel1Data observer21Panel1Endpoints ∧
  panelFormulaBounds observer21Panel2Data observer21Panel2Endpoints ∧
  panelFormulaBounds observer21Panel3Data observer21Panel3Endpoints ∧
  panelFormulaBounds observer21Panel4Data observer21Panel4Endpoints ∧
  panelFormulaBounds observer21Panel5Data observer21Panel5Endpoints ∧
  panelFormulaBounds observer21Panel6Data observer21Panel6Endpoints ∧
  panelFormulaBounds observer21Panel7Data observer21Panel7Endpoints
theorem observer21_all_panel_formula_bounds : observer21PanelFormulaBounds := by
  exact ⟨observer21_panel0_formula_sound,
    observer21_panel1_formula_sound,
    observer21_panel2_formula_sound,
    observer21_panel3_formula_sound,
    observer21_panel4_formula_sound,
    observer21_panel5_formula_sound,
    observer21_panel6_formula_sound,
    observer21_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
