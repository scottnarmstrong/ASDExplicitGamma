module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer5Panel0Data : MainPanelData :=
  {
    observer := 5, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3055492116062002119 : ℚ) / 156250000000000000000),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer5Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 77854015321596056930611316804, ellLower := 419695019125622834816785218827,
    rhoLower := 99947513778838597754852346452126, rhoUpper := 99947613726402350366997443730972,
    offsetLower := 9717727305436448524380548833, offsetUpper := 9736267718844173445093256083,
    supportELower := 62743459054916003170313051529, supportEUpper := 64540128598397315627372693102,
    supportLambdaLower := 419695019125622834816785218827,
    supportLambdaUpper := 430633219356090607192323589517,
    supportJLower := 66940409246172231518480903717, supportJUpper := 68846460791958221699295928998,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer5Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer5Panel0Data observer5Panel0Endpoints
theorem observer5_panel0_kernel_check : observer5Panel0Check = true := by
  decide +kernel
theorem observer5_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer5Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer5Panel0Data) s observer5Panel0Data.anchor ≤
        (observer5Panel0Endpoints.energyUpper : ℝ) ∧
      (observer5Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer5Panel0Data) s observer5Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer5Panel0Data) s observer5Panel0Data.anchor ≤
        (observer5Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer5Panel0Data) s observer5Panel0Data.anchor ≤
        (observer5Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer5Panel0Data) s observer5Panel0Data.anchor ≤
        (observer5Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer5Panel0Data observer5Panel0Endpoints
    observer5_panel0_kernel_check s hs
def observer5Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer5Panel0Endpoints
theorem observer5_panel0_recurrence_field_kernel_check :
    observer5Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer5_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer5Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer5Panel0Endpoints
    observer5_panel0_recurrence_field_kernel_check

def observer5Panel1Data : MainPanelData :=
  {
    observer := 5, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3055492116062002119 : ℚ) / 156250000000000000000),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer5Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 79838177711831317306070717244, ellLower := 418893948938902030386615617839,
    rhoLower := 99947613726402350366997443730970, rhoUpper := 99947713674066050592868951689151,
    offsetLower := 9965398145252876248387654113, offsetUpper := 9984447452020362782667631335,
    supportELower := 64540054504929390483416309014, supportEUpper := 66215623320162724114358431441,
    supportLambdaLower := 418893948938902030386615617839,
    supportLambdaUpper := 429407718880857587519524495078,
    supportJLower := 68728993994318410787282465192, supportJUpper := 70509700508971299989553676392,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer5Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer5Panel1Data observer5Panel1Endpoints
theorem observer5_panel1_kernel_check : observer5Panel1Check = true := by
  decide +kernel
theorem observer5_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer5Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer5Panel1Data) s observer5Panel1Data.anchor ≤
        (observer5Panel1Endpoints.energyUpper : ℝ) ∧
      (observer5Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer5Panel1Data) s observer5Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer5Panel1Data) s observer5Panel1Data.anchor ≤
        (observer5Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer5Panel1Data) s observer5Panel1Data.anchor ≤
        (observer5Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer5Panel1Data) s observer5Panel1Data.anchor ≤
        (observer5Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer5Panel1Data observer5Panel1Endpoints
    observer5_panel1_kernel_check s hs
def observer5Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer5Panel1Endpoints
theorem observer5_panel1_recurrence_field_kernel_check :
    observer5Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer5_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer5Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer5Panel1Endpoints
    observer5_panel1_recurrence_field_kernel_check

def observer5Panel2Data : MainPanelData :=
  {
    observer := 5, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3055492116062002119 : ℚ) / 156250000000000000000),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer5Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 81801367167818765464829516591, ellLower := 418102627430272680814829455070,
    rhoLower := 99947713674066050592868951689149, rhoUpper := 99947813621829698532414534026899,
    offsetLower := 10210213478219299694218148043, offsetUpper := 10229768159714648506362487976,
    supportELower := 66215543561729245247120579687, supportEUpper := 67869659543725701700378206825,
    supportLambdaLower := 418102627430272680814829455070,
    supportLambdaUpper := 428238492152855283953198753455,
    supportJLower := 70396569836031972055268874237, supportJUpper := 72152044465254254539910194360,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer5Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer5Panel2Data observer5Panel2Endpoints
theorem observer5_panel2_kernel_check : observer5Panel2Check = true := by
  decide +kernel
theorem observer5_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer5Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer5Panel2Data) s observer5Panel2Data.anchor ≤
        (observer5Panel2Endpoints.energyUpper : ℝ) ∧
      (observer5Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer5Panel2Data) s observer5Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer5Panel2Data) s observer5Panel2Data.anchor ≤
        (observer5Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer5Panel2Data) s observer5Panel2Data.anchor ≤
        (observer5Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer5Panel2Data) s observer5Panel2Data.anchor ≤
        (observer5Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer5Panel2Data observer5Panel2Endpoints
    observer5_panel2_kernel_check s hs
def observer5Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer5Panel2Endpoints
theorem observer5_panel2_recurrence_field_kernel_check :
    observer5Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer5_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer5Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer5Panel2Endpoints
    observer5_panel2_recurrence_field_kernel_check

def observer5Panel3Data : MainPanelData :=
  {
    observer := 5, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3055492116062002119 : ℚ) / 156250000000000000000),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer5Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 83752869130784190613668472397, ellLower := 417337022088396494662643592382,
    rhoLower := 99947813621829698532414534026897, rhoUpper := 99947913569693294285581954392164,
    offsetLower := 10452913952223568122448863694, offsetUpper := 10472971890763857828580203866,
    supportELower := 67869574165378086111416812197, supportEUpper := 69511554521467874973943047920,
    supportLambdaLower := 417337022088396494662643592382,
    supportLambdaUpper := 427122353689714773936865181248,
    supportJLower := 72042944386262051058043248120, supportJUpper := 73782778058365022713311699733,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer5Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer5Panel3Data observer5Panel3Endpoints
theorem observer5_panel3_kernel_check : observer5Panel3Check = true := by
  decide +kernel
theorem observer5_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer5Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer5Panel3Data) s observer5Panel3Data.anchor ≤
        (observer5Panel3Endpoints.energyUpper : ℝ) ∧
      (observer5Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer5Panel3Data) s observer5Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer5Panel3Data) s observer5Panel3Data.anchor ≤
        (observer5Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer5Panel3Data) s observer5Panel3Data.anchor ≤
        (observer5Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer5Panel3Data) s observer5Panel3Data.anchor ≤
        (observer5Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer5Panel3Data observer5Panel3Endpoints
    observer5_panel3_kernel_check s hs
def observer5Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer5Panel3Endpoints
theorem observer5_panel3_recurrence_field_kernel_check :
    observer5Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer5_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer5Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer5Panel3Endpoints
    observer5_panel3_recurrence_field_kernel_check

def observer5Panel4Data : MainPanelData :=
  {
    observer := 5, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3055492116062002119 : ℚ) / 156250000000000000000),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer5Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 85696255792001932119999613357, ellLower := 416597022267837784762697957931,
    rhoLower := 99947913569693294285581954392162, rhoUpper := 99948013517656837952319076380707,
    offsetLower := 10693899981219204017376693345, offsetUpper := 10714459816724271664693443766,
    supportELower := 69511463551502254633339754131, supportEUpper := 71144917426529864793055224233,
    supportLambdaLower := 416597022267837784762697957931,
    supportLambdaUpper := 426055600940493625111436062495,
    supportJLower := 73677433774180632480966733710, supportJUpper := 75405473435934801044169584858,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer5Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer5Panel4Data observer5Panel4Endpoints
theorem observer5_panel4_kernel_check : observer5Panel4Check = true := by
  decide +kernel
theorem observer5_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer5Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer5Panel4Data) s observer5Panel4Data.anchor ≤
        (observer5Panel4Endpoints.energyUpper : ℝ) ∧
      (observer5Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer5Panel4Data) s observer5Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer5Panel4Data) s observer5Panel4Data.anchor ≤
        (observer5Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer5Panel4Data) s observer5Panel4Data.anchor ≤
        (observer5Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer5Panel4Data) s observer5Panel4Data.anchor ≤
        (observer5Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer5Panel4Data observer5Panel4Endpoints
    observer5_panel4_kernel_check s hs
def observer5Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer5Panel4Endpoints
theorem observer5_panel4_recurrence_field_kernel_check :
    observer5Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer5_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer5Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer5Panel4Endpoints
    observer5_panel4_recurrence_field_kernel_check

def observer5Panel5Data : MainPanelData :=
  {
    observer := 5, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3055492116062002119 : ℚ) / 156250000000000000000),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer5Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 87633599173578396051857585510, ellLower := 415881627556981511030566829647,
    rhoLower := 99948013517656837952319076380705, rhoUpper := 99948113465720329632573863536204,
    offsetLower := 10933408562146126754719381677, offsetUpper := 10954469383191906648967962541,
    supportELower := 71144820886763318940048536457, supportEUpper := 72771615353152516114738753923,
    supportLambdaLower := 415881627556981511030566829647,
    supportLambdaUpper := 425034686896221834075306173842,
    supportJLower := 75303637162333134050354204753, supportJUpper := 77021962222114734455491815662,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer5Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer5Panel5Data observer5Panel5Endpoints
theorem observer5_panel5_kernel_check : observer5Panel5Check = true := by
  decide +kernel
theorem observer5_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer5Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer5Panel5Data) s observer5Panel5Data.anchor ≤
        (observer5Panel5Endpoints.energyUpper : ℝ) ∧
      (observer5Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer5Panel5Data) s observer5Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer5Panel5Data) s observer5Panel5Data.anchor ≤
        (observer5Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer5Panel5Data) s observer5Panel5Data.anchor ≤
        (observer5Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer5Panel5Data) s observer5Panel5Data.anchor ≤
        (observer5Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer5Panel5Data observer5Panel5Endpoints
    observer5_panel5_kernel_check s hs
def observer5Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer5Panel5Endpoints
theorem observer5_panel5_recurrence_field_kernel_check :
    observer5Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer5_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer5Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer5Panel5Endpoints
    observer5_panel5_recurrence_field_kernel_check

def observer5Panel6Data : MainPanelData :=
  {
    observer := 5, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3055492116062002119 : ℚ) / 156250000000000000000),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer5Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 89565513154501895181599154431, ellLower := 415189656963011458621475795582,
    rhoLower := 99948113465720329632573863536202, rhoUpper := 99948213413883769426294379350342,
    offsetLower := 11171502185164531280718224716, offsetUpper := 11193063195650234830390366815,
    supportELower := 72771513261974113238930706675, supportEUpper := 74392775662462854186643676233,
    supportLambdaLower := 415189656963011458621475795582,
    supportLambdaUpper := 424056343451220389050407737672,
    supportJLower := 76923409831604227825145464630, supportJUpper := 78633339096975058077147753610,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer5Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer5Panel6Data observer5Panel6Endpoints
theorem observer5_panel6_kernel_check : observer5Panel6Check = true := by
  decide +kernel
theorem observer5_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer5Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer5Panel6Data) s observer5Panel6Data.anchor ≤
        (observer5Panel6Endpoints.energyUpper : ℝ) ∧
      (observer5Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer5Panel6Data) s observer5Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer5Panel6Data) s observer5Panel6Data.anchor ≤
        (observer5Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer5Panel6Data) s observer5Panel6Data.anchor ≤
        (observer5Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer5Panel6Data) s observer5Panel6Data.anchor ≤
        (observer5Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer5Panel6Data observer5Panel6Endpoints
    observer5_panel6_kernel_check s hs
def observer5Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer5Panel6Endpoints
theorem observer5_panel6_recurrence_field_kernel_check :
    observer5Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer5_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer5Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer5Panel6Endpoints
    observer5_panel6_recurrence_field_kernel_check

def observer5Panel7Data : MainPanelData :=
  {
    observer := 5, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((3055492116062002119 : ℚ) / 156250000000000000000),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer5Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 91492960128487184094263514360, ellLower := 414519918798616944108748544107,
    rhoLower := 99948113465720329632573863536202, rhoUpper := 99948213413883769426294379350342,
    offsetLower := 11430350735508637440847549767, offsetUpper := 11452411323957597347335874131,
    supportELower := 74392668036105315587236141932, supportEUpper := 76009149980527756159220318766,
    supportLambdaLower := 414519918798616944108748544107,
    supportLambdaUpper := 423117593971783952769112566140,
    supportJLower := 78537867224091485028323627373, supportJUpper := 80240325920245595686911444428,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer5Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer5Panel7Data observer5Panel7Endpoints
theorem observer5_panel7_kernel_check : observer5Panel7Check = true := by
  decide +kernel
theorem observer5_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer5Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer5Panel7Data) s observer5Panel7Data.anchor ≤
        (observer5Panel7Endpoints.energyUpper : ℝ) ∧
      (observer5Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer5Panel7Data) s observer5Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer5Panel7Data) s observer5Panel7Data.anchor ≤
        (observer5Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer5Panel7Data) s observer5Panel7Data.anchor ≤
        (observer5Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer5Panel7Data) s observer5Panel7Data.anchor ≤
        (observer5Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer5Panel7Data observer5Panel7Endpoints
    observer5_panel7_kernel_check s hs
def observer5Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer5Panel7Endpoints
theorem observer5_panel7_recurrence_field_kernel_check :
    observer5Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer5_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer5Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer5Panel7Endpoints
    observer5_panel7_recurrence_field_kernel_check

def observer5InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 5, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer5Panel0Endpoints, observer5Panel1Endpoints, observer5Panel2Endpoints, observer5Panel3Endpoints, observer5Panel4Endpoints, observer5Panel5Endpoints, observer5Panel6Endpoints, observer5Panel7Endpoints]
  }
def observer5FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer5InsertionEndpoints.frameLower
    observer5InsertionEndpoints.frameUpper
theorem observer5_frame_recurrence_field_kernel_check :
    observer5FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer5_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer5InsertionEndpoints.frameLower
      observer5InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer5InsertionEndpoints.frameLower
    observer5InsertionEndpoints.frameUpper
    observer5_frame_recurrence_field_kernel_check
def observer5RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer5Panel0Endpoints ∧
  panelRecurrenceFields observer5Panel1Endpoints ∧
  panelRecurrenceFields observer5Panel2Endpoints ∧
  panelRecurrenceFields observer5Panel3Endpoints ∧
  panelRecurrenceFields observer5Panel4Endpoints ∧
  panelRecurrenceFields observer5Panel5Endpoints ∧
  panelRecurrenceFields observer5Panel6Endpoints ∧
  panelRecurrenceFields observer5Panel7Endpoints ∧ insertionFrameRecurrenceFields observer5InsertionEndpoints.frameLower
      observer5InsertionEndpoints.frameUpper
theorem observer5_all_recurrence_fields :
    observer5RecurrenceFieldBounds := by
  exact ⟨observer5_panel0_recurrence_fields_sound,
    observer5_panel1_recurrence_fields_sound,
    observer5_panel2_recurrence_fields_sound,
    observer5_panel3_recurrence_fields_sound,
    observer5_panel4_recurrence_fields_sound,
    observer5_panel5_recurrence_fields_sound,
    observer5_panel6_recurrence_fields_sound,
    observer5_panel7_recurrence_fields_sound,
    observer5_frame_recurrence_fields_sound⟩
def observer5PanelFormulaBounds : Prop :=
  panelFormulaBounds observer5Panel0Data observer5Panel0Endpoints ∧
  panelFormulaBounds observer5Panel1Data observer5Panel1Endpoints ∧
  panelFormulaBounds observer5Panel2Data observer5Panel2Endpoints ∧
  panelFormulaBounds observer5Panel3Data observer5Panel3Endpoints ∧
  panelFormulaBounds observer5Panel4Data observer5Panel4Endpoints ∧
  panelFormulaBounds observer5Panel5Data observer5Panel5Endpoints ∧
  panelFormulaBounds observer5Panel6Data observer5Panel6Endpoints ∧
  panelFormulaBounds observer5Panel7Data observer5Panel7Endpoints
theorem observer5_all_panel_formula_bounds : observer5PanelFormulaBounds := by
  exact ⟨observer5_panel0_formula_sound,
    observer5_panel1_formula_sound,
    observer5_panel2_formula_sound,
    observer5_panel3_formula_sound,
    observer5_panel4_formula_sound,
    observer5_panel5_formula_sound,
    observer5_panel6_formula_sound,
    observer5_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
