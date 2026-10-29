module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer38Panel0Data : MainPanelData :=
  {
    observer := 38, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((579515386881713605936 : ℚ) / 106446687849837599095944698708300728725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer38Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393298140665253648733504698, ellLower := 352020920478140991665508195627,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172437303526088550718462736, offsetUpper := 6186462477120094450830153597,
    supportELower := 38565849059666932134140515470, supportEUpper := 40091569389540913833551846503,
    supportLambdaLower := 352020920478140991665508195627,
    supportLambdaUpper := 361977512806830819345628323570,
    supportJLower := 42086058264448342050795597426, supportJUpper := 43711344517609222027008129739,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer38Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer38Panel0Data observer38Panel0Endpoints
theorem observer38_panel0_kernel_check : observer38Panel0Check = true := by
  decide +kernel
theorem observer38_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer38Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer38Panel0Data) s observer38Panel0Data.anchor ≤
        (observer38Panel0Endpoints.energyUpper : ℝ) ∧
      (observer38Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer38Panel0Data) s observer38Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer38Panel0Data) s observer38Panel0Data.anchor ≤
        (observer38Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer38Panel0Data) s observer38Panel0Data.anchor ≤
        (observer38Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer38Panel0Data) s observer38Panel0Data.anchor ≤
        (observer38Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer38Panel0Data observer38Panel0Endpoints
    observer38_panel0_kernel_check s hs
def observer38Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer38Panel0Endpoints
theorem observer38_panel0_recurrence_field_kernel_check :
    observer38Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer38_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer38Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer38Panel0Endpoints
    observer38_panel0_recurrence_field_kernel_check

def observer38Panel1Data : MainPanelData :=
  {
    observer := 38, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((579515386881713605936 : ℚ) / 106446687849837599095944698708300728725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer38Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115183644698814041140222646, ellLower := 351854271741077630569308698143,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376117233148690908966650862, offsetUpper := 6390638223104178749727635798,
    supportELower := 40091520308354086303665319552, supportEUpper := 41498105492731009560054893741,
    supportLambdaLower := 351854271741077630569308698143,
    supportLambdaUpper := 361420185568959077415830089934,
    supportJLower := 43610063025764862609358406533, supportJUpper := 45112307348420600334213194641,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer38Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer38Panel1Data observer38Panel1Endpoints
theorem observer38_panel1_kernel_check : observer38Panel1Check = true := by
  decide +kernel
theorem observer38_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer38Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer38Panel1Data) s observer38Panel1Data.anchor ≤
        (observer38Panel1Endpoints.energyUpper : ℝ) ∧
      (observer38Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer38Panel1Data) s observer38Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer38Panel1Data) s observer38Panel1Data.anchor ≤
        (observer38Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer38Panel1Data) s observer38Panel1Data.anchor ≤
        (observer38Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer38Panel1Data) s observer38Panel1Data.anchor ≤
        (observer38Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer38Panel1Data observer38Panel1Endpoints
    observer38_panel1_kernel_check s hs
def observer38Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer38Panel1Endpoints
theorem observer38_panel1_recurrence_field_kernel_check :
    observer38Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer38_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer38Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer38Panel1Endpoints
    observer38_panel1_recurrence_field_kernel_check

def observer38Panel2Data : MainPanelData :=
  {
    observer := 38, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((579515386881713605936 : ℚ) / 106446687849837599095944698708300728725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer38Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817739985373355407153923911, ellLower := 351674063432533118011098283386,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591870559962564603238800472, offsetUpper := 6606882907240536963783613500,
    supportELower := 41498051571298965154848543811, supportEUpper := 42885082025169253248701359691,
    supportLambdaLower := 351674063432533118011098283386,
    supportLambdaUpper := 360893616422139484312325483586,
    supportJLower := 45014792205624296334959526644, supportJUpper := 46494018189390648091824614527,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer38Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer38Panel2Data observer38Panel2Endpoints
theorem observer38_panel2_kernel_check : observer38Panel2Check = true := by
  decide +kernel
theorem observer38_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer38Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer38Panel2Data) s observer38Panel2Data.anchor ≤
        (observer38Panel2Endpoints.energyUpper : ℝ) ∧
      (observer38Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer38Panel2Data) s observer38Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer38Panel2Data) s observer38Panel2Data.anchor ≤
        (observer38Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer38Panel2Data) s observer38Panel2Data.anchor ≤
        (observer38Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer38Panel2Data) s observer38Panel2Data.anchor ≤
        (observer38Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer38Panel2Data observer38Panel2Endpoints
    observer38_panel2_kernel_check s hs
def observer38Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer38Panel2Endpoints
theorem observer38_panel2_recurrence_field_kernel_check :
    observer38Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer38_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer38Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer38Panel2Endpoints
    observer38_panel2_recurrence_field_kernel_check

def observer38Panel3Data : MainPanelData :=
  {
    observer := 38, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((579515386881713605936 : ℚ) / 106446687849837599095944698708300728725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer38Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510207080763774773196475705, ellLower := 351497803142167025911294339125,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806508840830480191535262386, offsetUpper := 6822010006021702720430905052,
    supportELower := 42885023299062299515283586530, supportEUpper := 44261753138964483357036240260,
    supportLambdaLower := 351497803142167025911294339125,
    supportLambdaUpper := 360396377596192712539347562757,
    supportJLower := 46400001330483969774396529921, supportJUpper := 47865716914926410482429715888,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer38Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer38Panel3Data observer38Panel3Endpoints
theorem observer38_panel3_kernel_check : observer38Panel3Check = true := by
  decide +kernel
theorem observer38_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer38Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer38Panel3Data) s observer38Panel3Data.anchor ≤
        (observer38Panel3Endpoints.energyUpper : ℝ) ∧
      (observer38Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer38Panel3Data) s observer38Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer38Panel3Data) s observer38Panel3Data.anchor ≤
        (observer38Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer38Panel3Data) s observer38Panel3Data.anchor ≤
        (observer38Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer38Panel3Data) s observer38Panel3Data.anchor ≤
        (observer38Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer38Panel3Data observer38Panel3Endpoints
    observer38_panel3_kernel_check s hs
def observer38Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer38Panel3Endpoints
theorem observer38_panel3_recurrence_field_kernel_check :
    observer38Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer38_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer38Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer38Panel3Endpoints
    observer38_panel3_recurrence_field_kernel_check

def observer38Panel4Data : MainPanelData :=
  {
    observer := 38, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((579515386881713605936 : ℚ) / 106446687849837599095944698708300728725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer38Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196113749670745296795906338, ellLower := 351326769066601275711425730342,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020438467679458343888126323, offsetUpper := 7036426836892982266192819601,
    supportELower := 44261689627418726449324689554, supportEUpper := 45631668856948824673223526382,
    supportLambdaLower := 351326769066601275711425730342,
    supportLambdaUpper := 359926344323659315733236430301,
    supportJLower := 47774957318084739206438946857, supportJUpper := 49230932300185417830555890686,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer38Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer38Panel4Data observer38Panel4Endpoints
theorem observer38_panel4_kernel_check : observer38Panel4Check = true := by
  decide +kernel
theorem observer38_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer38Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer38Panel4Data) s observer38Panel4Data.anchor ≤
        (observer38Panel4Endpoints.energyUpper : ℝ) ∧
      (observer38Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer38Panel4Data) s observer38Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer38Panel4Data) s observer38Panel4Data.anchor ≤
        (observer38Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer38Panel4Data) s observer38Panel4Data.anchor ≤
        (observer38Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer38Panel4Data) s observer38Panel4Data.anchor ≤
        (observer38Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer38Panel4Data observer38Panel4Endpoints
    observer38_panel4_kernel_check s hs
def observer38Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer38Panel4Endpoints
theorem observer38_panel4_recurrence_field_kernel_check :
    observer38Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer38_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer38Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer38Panel4Endpoints
    observer38_panel4_recurrence_field_kernel_check

def observer38Panel5Data : MainPanelData :=
  {
    observer := 38, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((579515386881713605936 : ℚ) / 106446687849837599095944698708300728725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer38Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877490656319794334671373832, ellLower := 351161218123449882740655135340,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217422848887170363755182926, offsetUpper := 7233897366560111530640256957,
    supportELower := 45631600573110201816152228272, supportEUpper := 46996640692722289965084831492,
    supportLambdaLower := 351161218123449882740655135340,
    supportLambdaUpper := 359481391871564638281078533837,
    supportJLower := 49143212754344700643558779625, supportJUpper := 50591454611437936347895616831,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer38Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer38Panel5Data observer38Panel5Endpoints
theorem observer38_panel5_kernel_check : observer38Panel5Check = true := by
  decide +kernel
theorem observer38_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer38Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer38Panel5Data) s observer38Panel5Data.anchor ≤
        (observer38Panel5Endpoints.energyUpper : ℝ) ∧
      (observer38Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer38Panel5Data) s observer38Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer38Panel5Data) s observer38Panel5Data.anchor ≤
        (observer38Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer38Panel5Data) s observer38Panel5Data.anchor ≤
        (observer38Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer38Panel5Data) s observer38Panel5Data.anchor ≤
        (observer38Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer38Panel5Data observer38Panel5Endpoints
    observer38_panel5_kernel_check s hs
def observer38Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer38Panel5Endpoints
theorem observer38_panel5_recurrence_field_kernel_check :
    observer38Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer38_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer38Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer38Panel5Endpoints
    observer38_panel5_recurrence_field_kernel_check

def observer38Panel6Data : MainPanelData :=
  {
    observer := 38, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((579515386881713605936 : ℚ) / 106446687849837599095944698708300728725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer38Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554912209051320527771756297, ellLower := 351001111701940688872310126835,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429987793706320403412872648, offsetUpper := 7446947512955141359293896172,
    supportELower := 46996567646669033074651598124, supportEUpper := 48357743665640241928236817123,
    supportLambdaLower := 351001111701940688872310126835,
    supportLambdaUpper := 359059539246604510467355119913,
    supportJLower := 50506578763688439963374699392, supportJUpper := 51948339058106287032910368323,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer38Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer38Panel6Data observer38Panel6Endpoints
theorem observer38_panel6_kernel_check : observer38Panel6Check = true := by
  decide +kernel
theorem observer38_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer38Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer38Panel6Data) s observer38Panel6Data.anchor ≤
        (observer38Panel6Endpoints.energyUpper : ℝ) ∧
      (observer38Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer38Panel6Data) s observer38Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer38Panel6Data) s observer38Panel6Data.anchor ≤
        (observer38Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer38Panel6Data) s observer38Panel6Data.anchor ≤
        (observer38Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer38Panel6Data) s observer38Panel6Data.anchor ≤
        (observer38Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer38Panel6Data observer38Panel6Endpoints
    observer38_panel6_kernel_check s hs
def observer38Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer38Panel6Endpoints
theorem observer38_panel6_recurrence_field_kernel_check :
    observer38Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer38_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer38Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer38Panel6Endpoints
    observer38_panel6_recurrence_field_kernel_check

def observer38Panel7Data : MainPanelData :=
  {
    observer := 38, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((579515386881713605936 : ℚ) / 106446687849837599095944698708300728725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer38Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229303099511691518749229953, ellLower := 350846299536053653070331054606,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642253149948826468295566330, offsetUpper := 7659697386931468368934052872,
    supportELower := 48357665865629046459326530138, supportEUpper := 49715680009579551458205860422,
    supportLambdaLower := 350846299536053653070331054606,
    supportLambdaUpper := 358658978827235526278131244554,
    supportJLower := 51866128860989582990029840684, supportJUpper := 53302269797851906720987172868,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer38Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer38Panel7Data observer38Panel7Endpoints
theorem observer38_panel7_kernel_check : observer38Panel7Check = true := by
  decide +kernel
theorem observer38_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer38Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer38Panel7Data) s observer38Panel7Data.anchor ≤
        (observer38Panel7Endpoints.energyUpper : ℝ) ∧
      (observer38Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer38Panel7Data) s observer38Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer38Panel7Data) s observer38Panel7Data.anchor ≤
        (observer38Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer38Panel7Data) s observer38Panel7Data.anchor ≤
        (observer38Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer38Panel7Data) s observer38Panel7Data.anchor ≤
        (observer38Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer38Panel7Data observer38Panel7Endpoints
    observer38_panel7_kernel_check s hs
def observer38Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer38Panel7Endpoints
theorem observer38_panel7_recurrence_field_kernel_check :
    observer38Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer38_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer38Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer38Panel7Endpoints
    observer38_panel7_recurrence_field_kernel_check

def observer38InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 38, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer38Panel0Endpoints, observer38Panel1Endpoints, observer38Panel2Endpoints, observer38Panel3Endpoints, observer38Panel4Endpoints, observer38Panel5Endpoints, observer38Panel6Endpoints, observer38Panel7Endpoints]
  }
def observer38FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer38InsertionEndpoints.frameLower
    observer38InsertionEndpoints.frameUpper
theorem observer38_frame_recurrence_field_kernel_check :
    observer38FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer38_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer38InsertionEndpoints.frameLower
      observer38InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer38InsertionEndpoints.frameLower
    observer38InsertionEndpoints.frameUpper
    observer38_frame_recurrence_field_kernel_check
def observer38RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer38Panel0Endpoints ∧
  panelRecurrenceFields observer38Panel1Endpoints ∧
  panelRecurrenceFields observer38Panel2Endpoints ∧
  panelRecurrenceFields observer38Panel3Endpoints ∧
  panelRecurrenceFields observer38Panel4Endpoints ∧
  panelRecurrenceFields observer38Panel5Endpoints ∧
  panelRecurrenceFields observer38Panel6Endpoints ∧
  panelRecurrenceFields observer38Panel7Endpoints ∧ insertionFrameRecurrenceFields observer38InsertionEndpoints.frameLower
      observer38InsertionEndpoints.frameUpper
theorem observer38_all_recurrence_fields :
    observer38RecurrenceFieldBounds := by
  exact ⟨observer38_panel0_recurrence_fields_sound,
    observer38_panel1_recurrence_fields_sound,
    observer38_panel2_recurrence_fields_sound,
    observer38_panel3_recurrence_fields_sound,
    observer38_panel4_recurrence_fields_sound,
    observer38_panel5_recurrence_fields_sound,
    observer38_panel6_recurrence_fields_sound,
    observer38_panel7_recurrence_fields_sound,
    observer38_frame_recurrence_fields_sound⟩
def observer38PanelFormulaBounds : Prop :=
  panelFormulaBounds observer38Panel0Data observer38Panel0Endpoints ∧
  panelFormulaBounds observer38Panel1Data observer38Panel1Endpoints ∧
  panelFormulaBounds observer38Panel2Data observer38Panel2Endpoints ∧
  panelFormulaBounds observer38Panel3Data observer38Panel3Endpoints ∧
  panelFormulaBounds observer38Panel4Data observer38Panel4Endpoints ∧
  panelFormulaBounds observer38Panel5Data observer38Panel5Endpoints ∧
  panelFormulaBounds observer38Panel6Data observer38Panel6Endpoints ∧
  panelFormulaBounds observer38Panel7Data observer38Panel7Endpoints
theorem observer38_all_panel_formula_bounds : observer38PanelFormulaBounds := by
  exact ⟨observer38_panel0_formula_sound,
    observer38_panel1_formula_sound,
    observer38_panel2_formula_sound,
    observer38_panel3_formula_sound,
    observer38_panel4_formula_sound,
    observer38_panel5_formula_sound,
    observer38_panel6_formula_sound,
    observer38_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
