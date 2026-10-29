module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer37Panel0Data : MainPanelData :=
  {
    observer := 37, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((193171795627237868482 : ℚ) / 11827409761093066566216077634255636525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer37Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393298444587930225979044966, ellLower := 352020921287392978438050179993,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172437327316149231193461489, offsetUpper := 6186462500964211529847262871,
    supportELower := 38565849352150705827359931203, supportEUpper := 40091569685256004833622112767,
    supportLambdaLower := 352020921287392978438050179993,
    supportLambdaUpper := 361977513627589191892654140620,
    supportJLower := 42086058565024635611740433002, supportJUpper := 43711344821531896752548654174,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer37Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer37Panel0Data observer37Panel0Endpoints
theorem observer37_panel0_kernel_check : observer37Panel0Check = true := by
  decide +kernel
theorem observer37_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer37Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer37Panel0Data) s observer37Panel0Data.anchor ≤
        (observer37Panel0Endpoints.energyUpper : ℝ) ∧
      (observer37Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer37Panel0Data) s observer37Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer37Panel0Data) s observer37Panel0Data.anchor ≤
        (observer37Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer37Panel0Data) s observer37Panel0Data.anchor ≤
        (observer37Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer37Panel0Data) s observer37Panel0Data.anchor ≤
        (observer37Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer37Panel0Data observer37Panel0Endpoints
    observer37_panel0_kernel_check s hs
def observer37Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer37Panel0Endpoints
theorem observer37_panel0_recurrence_field_kernel_check :
    observer37Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer37_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer37Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer37Panel0Endpoints
    observer37_panel0_recurrence_field_kernel_check

def observer37Panel1Data : MainPanelData :=
  {
    observer := 37, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((193171795627237868482 : ℚ) / 11827409761093066566216077634255636525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer37Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115183951749099648542084144, ellLower := 351854272542751767558030525457,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376117256922683700078930905, offsetUpper := 6390638246932314508714912383,
    supportELower := 40091520604068874899036664538, supportEUpper := 41498105791653414900975504830,
    supportLambdaLower := 351854272542751767558030525457,
    supportLambdaUpper := 361420186381746918893453547538,
    supportJLower := 43610063329496392574616969792, supportJUpper := 45112307655470884089910040306,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer37Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer37Panel1Data observer37Panel1Endpoints
theorem observer37_panel1_kernel_check : observer37Panel1Check = true := by
  decide +kernel
theorem observer37_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer37Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer37Panel1Data) s observer37Panel1Data.anchor ≤
        (observer37Panel1Endpoints.energyUpper : ℝ) ∧
      (observer37Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer37Panel1Data) s observer37Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer37Panel1Data) s observer37Panel1Data.anchor ≤
        (observer37Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer37Panel1Data) s observer37Panel1Data.anchor ≤
        (observer37Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer37Panel1Data) s observer37Panel1Data.anchor ≤
        (observer37Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer37Panel1Data observer37Panel1Endpoints
    observer37_panel1_kernel_check s hs
def observer37Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer37Panel1Endpoints
theorem observer37_panel1_recurrence_field_kernel_check :
    observer37Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer37_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer37Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer37Panel1Endpoints
    observer37_panel1_recurrence_field_kernel_check

def observer37Panel2Data : MainPanelData :=
  {
    observer := 37, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((193171795627237868482 : ℚ) / 11827409761093066566216077634255636525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer37Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817740295531338009386886532, ellLower := 351674064226903736785237336796,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591870583781662262674836386, offsetUpper := 6606882931113880313067270319,
    supportELower := 41498051870221058247629730847, supportEUpper := 42885082327276063183116695518,
    supportLambdaLower := 351674064226903736785237336796,
    supportLambdaUpper := 360893617227256565923586579671,
    supportJLower := 45014792512490095615482104214, supportJUpper := 46494018499548628842352561315,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer37Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer37Panel2Data observer37Panel2Endpoints
theorem observer37_panel2_kernel_check : observer37Panel2Check = true := by
  decide +kernel
theorem observer37_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer37Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer37Panel2Data) s observer37Panel2Data.anchor ≤
        (observer37Panel2Endpoints.energyUpper : ℝ) ∧
      (observer37Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer37Panel2Data) s observer37Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer37Panel2Data) s observer37Panel2Data.anchor ≤
        (observer37Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer37Panel2Data) s observer37Panel2Data.anchor ≤
        (observer37Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer37Panel2Data) s observer37Panel2Data.anchor ≤
        (observer37Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer37Panel2Data observer37Panel2Endpoints
    observer37_panel2_kernel_check s hs
def observer37Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer37Panel2Endpoints
theorem observer37_panel2_recurrence_field_kernel_check :
    observer37Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer37_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer37Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer37Panel2Endpoints
    observer37_panel2_recurrence_field_kernel_check

def observer37Panel3Data : MainPanelData :=
  {
    observer := 37, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((193171795627237868482 : ℚ) / 11827409761093066566216077634255636525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer37Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510207394010088253323774891, ellLower := 351497803929490579528288745437,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806508864698539463068522408, offsetUpper := 6822010029944119187145121357,
    supportELower := 42885023601168787472796267421, supportEUpper := 44261753444233537723337639097,
    supportLambdaLower := 351497803929490579528288745437,
    supportLambdaUpper := 360396378393918438751436014303,
    supportJLower := 46400001640463693268079154875, supportJUpper := 47865717228172722110851999241,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer37Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer37Panel3Data observer37Panel3Endpoints
theorem observer37_panel3_kernel_check : observer37Panel3Check = true := by
  decide +kernel
theorem observer37_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer37Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer37Panel3Data) s observer37Panel3Data.anchor ≤
        (observer37Panel3Endpoints.energyUpper : ℝ) ∧
      (observer37Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer37Panel3Data) s observer37Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer37Panel3Data) s observer37Panel3Data.anchor ≤
        (observer37Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer37Panel3Data) s observer37Panel3Data.anchor ≤
        (observer37Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer37Panel3Data) s observer37Panel3Data.anchor ≤
        (observer37Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer37Panel3Data observer37Panel3Endpoints
    observer37_panel3_kernel_check s hs
def observer37Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer37Panel3Endpoints
theorem observer37_panel3_recurrence_field_kernel_check :
    observer37Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer37_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer37Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer37Panel3Endpoints
    observer37_panel3_recurrence_field_kernel_check

def observer37Panel4Data : MainPanelData :=
  {
    observer := 37, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((193171795627237868482 : ℚ) / 11827409761093066566216077634255636525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer37Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196114065986543954205925268, ellLower := 351326769847118075817745995388,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020438491599200661586281521, offsetUpper := 7036426860867199482207991549,
    supportELower := 44261689932687449219614801700, supportEUpper := 45631669165358666762122660548,
    supportLambdaLower := 351326769847118075817745995388,
    supportLambdaUpper := 359926345114254787413823323454,
    supportJLower := 47774957631158629977792261653, supportJUpper := 49230932616501214636260893783,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer37Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer37Panel4Data observer37Panel4Endpoints
theorem observer37_panel4_kernel_check : observer37Panel4Check = true := by
  decide +kernel
theorem observer37_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer37Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer37Panel4Data) s observer37Panel4Data.anchor ≤
        (observer37Panel4Endpoints.energyUpper : ℝ) ∧
      (observer37Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer37Panel4Data) s observer37Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer37Panel4Data) s observer37Panel4Data.anchor ≤
        (observer37Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer37Panel4Data) s observer37Panel4Data.anchor ≤
        (observer37Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer37Panel4Data) s observer37Panel4Data.anchor ≤
        (observer37Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer37Panel4Data observer37Panel4Endpoints
    observer37_panel4_kernel_check s hs
def observer37Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer37Panel4Endpoints
theorem observer37_panel4_recurrence_field_kernel_check :
    observer37Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer37_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer37Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer37Panel4Endpoints
    observer37_panel4_recurrence_field_kernel_check

def observer37Panel5Data : MainPanelData :=
  {
    observer := 37, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((193171795627237868482 : ℚ) / 11827409761093066566216077634255636525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer37Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877490975686728982631743885, ellLower := 351161218897385611549591767831,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217422872806062566543732808, offsetUpper := 7233897390533601090485802776,
    supportELower := 45631600881519702794941101245, supportEUpper := 46996641004252124766889596838,
    supportLambdaLower := 351161218897385611549591767831,
    supportLambdaUpper := 359481392655274437726137421211,
    supportJLower := 49143213070493558910437018923, supportJUpper := 50591454930804869144150971051,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer37Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer37Panel5Data observer37Panel5Endpoints
theorem observer37_panel5_kernel_check : observer37Panel5Check = true := by
  decide +kernel
theorem observer37_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer37Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer37Panel5Data) s observer37Panel5Data.anchor ≤
        (observer37Panel5Endpoints.energyUpper : ℝ) ∧
      (observer37Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer37Panel5Data) s observer37Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer37Panel5Data) s observer37Panel5Data.anchor ≤
        (observer37Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer37Panel5Data) s observer37Panel5Data.anchor ≤
        (observer37Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer37Panel5Data) s observer37Panel5Data.anchor ≤
        (observer37Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer37Panel5Data observer37Panel5Endpoints
    observer37_panel5_kernel_check s hs
def observer37Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer37Panel5Endpoints
theorem observer37_panel5_recurrence_field_kernel_check :
    observer37Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer37_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer37Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer37Panel5Endpoints
    observer37_panel5_recurrence_field_kernel_check

def observer37Panel6Data : MainPanelData :=
  {
    observer := 37, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((193171795627237868482 : ℚ) / 11827409761093066566216077634255636525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer37Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554912531451516088027136937, ellLower := 351001112469507722116469262277,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429987817680668355710084123, offsetUpper := 7446947536984213252159209115,
    supportELower := 46996567958198517352947710786, supportEUpper := 48357743980269898195832995992,
    supportLambdaLower := 351001112469507722116469262277,
    supportLambdaUpper := 359059540023658254562773713760,
    supportJLower := 50506579082893594574112403408, supportJUpper := 51948339380506480741460733130,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer37Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer37Panel6Data observer37Panel6Endpoints
theorem observer37_panel6_kernel_check : observer37Panel6Check = true := by
  decide +kernel
theorem observer37_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer37Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer37Panel6Data) s observer37Panel6Data.anchor ≤
        (observer37Panel6Endpoints.energyUpper : ℝ) ∧
      (observer37Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer37Panel6Data) s observer37Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer37Panel6Data) s observer37Panel6Data.anchor ≤
        (observer37Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer37Panel6Data) s observer37Panel6Data.anchor ≤
        (observer37Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer37Panel6Data) s observer37Panel6Data.anchor ≤
        (observer37Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer37Panel6Data observer37Panel6Endpoints
    observer37_panel6_kernel_check s hs
def observer37Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer37Panel6Endpoints
theorem observer37_panel6_recurrence_field_kernel_check :
    observer37Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer37_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer37Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer37Panel6Endpoints
    observer37_panel6_recurrence_field_kernel_check

def observer37Panel7Data : MainPanelData :=
  {
    observer := 37, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((193171795627237868482 : ℚ) / 11827409761093066566216077634255636525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer37Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229303424927726011107456616, ellLower := 350846300297452223220311320949,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642253173980149251287648339, offsetUpper := 7659697411017645143466010060,
    supportELower := 48357666180258342886707331228, supportEUpper := 49715680327289447111431876030,
    supportLambdaLower := 350846300297452223220311320949,
    supportLambdaUpper := 358658979597849225020850766702,
    supportJLower := 51866129183232865118910444437, supportJUpper := 53302270123267939361640383698,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer37Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer37Panel7Data observer37Panel7Endpoints
theorem observer37_panel7_kernel_check : observer37Panel7Check = true := by
  decide +kernel
theorem observer37_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer37Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer37Panel7Data) s observer37Panel7Data.anchor ≤
        (observer37Panel7Endpoints.energyUpper : ℝ) ∧
      (observer37Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer37Panel7Data) s observer37Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer37Panel7Data) s observer37Panel7Data.anchor ≤
        (observer37Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer37Panel7Data) s observer37Panel7Data.anchor ≤
        (observer37Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer37Panel7Data) s observer37Panel7Data.anchor ≤
        (observer37Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer37Panel7Data observer37Panel7Endpoints
    observer37_panel7_kernel_check s hs
def observer37Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer37Panel7Endpoints
theorem observer37_panel7_recurrence_field_kernel_check :
    observer37Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer37_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer37Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer37Panel7Endpoints
    observer37_panel7_recurrence_field_kernel_check

def observer37InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 37, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer37Panel0Endpoints, observer37Panel1Endpoints, observer37Panel2Endpoints, observer37Panel3Endpoints, observer37Panel4Endpoints, observer37Panel5Endpoints, observer37Panel6Endpoints, observer37Panel7Endpoints]
  }
def observer37FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer37InsertionEndpoints.frameLower
    observer37InsertionEndpoints.frameUpper
theorem observer37_frame_recurrence_field_kernel_check :
    observer37FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer37_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer37InsertionEndpoints.frameLower
      observer37InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer37InsertionEndpoints.frameLower
    observer37InsertionEndpoints.frameUpper
    observer37_frame_recurrence_field_kernel_check
def observer37RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer37Panel0Endpoints ∧
  panelRecurrenceFields observer37Panel1Endpoints ∧
  panelRecurrenceFields observer37Panel2Endpoints ∧
  panelRecurrenceFields observer37Panel3Endpoints ∧
  panelRecurrenceFields observer37Panel4Endpoints ∧
  panelRecurrenceFields observer37Panel5Endpoints ∧
  panelRecurrenceFields observer37Panel6Endpoints ∧
  panelRecurrenceFields observer37Panel7Endpoints ∧ insertionFrameRecurrenceFields observer37InsertionEndpoints.frameLower
      observer37InsertionEndpoints.frameUpper
theorem observer37_all_recurrence_fields :
    observer37RecurrenceFieldBounds := by
  exact ⟨observer37_panel0_recurrence_fields_sound,
    observer37_panel1_recurrence_fields_sound,
    observer37_panel2_recurrence_fields_sound,
    observer37_panel3_recurrence_fields_sound,
    observer37_panel4_recurrence_fields_sound,
    observer37_panel5_recurrence_fields_sound,
    observer37_panel6_recurrence_fields_sound,
    observer37_panel7_recurrence_fields_sound,
    observer37_frame_recurrence_fields_sound⟩
def observer37PanelFormulaBounds : Prop :=
  panelFormulaBounds observer37Panel0Data observer37Panel0Endpoints ∧
  panelFormulaBounds observer37Panel1Data observer37Panel1Endpoints ∧
  panelFormulaBounds observer37Panel2Data observer37Panel2Endpoints ∧
  panelFormulaBounds observer37Panel3Data observer37Panel3Endpoints ∧
  panelFormulaBounds observer37Panel4Data observer37Panel4Endpoints ∧
  panelFormulaBounds observer37Panel5Data observer37Panel5Endpoints ∧
  panelFormulaBounds observer37Panel6Data observer37Panel6Endpoints ∧
  panelFormulaBounds observer37Panel7Data observer37Panel7Endpoints
theorem observer37_all_panel_formula_bounds : observer37PanelFormulaBounds := by
  exact ⟨observer37_panel0_formula_sound,
    observer37_panel1_formula_sound,
    observer37_panel2_formula_sound,
    observer37_panel3_formula_sound,
    observer37_panel4_formula_sound,
    observer37_panel5_formula_sound,
    observer37_panel6_formula_sound,
    observer37_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
