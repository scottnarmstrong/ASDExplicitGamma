module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer19Panel0Data : MainPanelData :=
  {
    observer := 19, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((498610169098 : ℚ) / 78799683530924538525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer19Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49407563472149688355137352589, ellLower := 352059238473238840786090295287,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6173547971993459350343861339, offsetUpper := 6187575669277426647906815586,
    supportELower := 38579571292867629068057911394, supportEUpper := 40105444930549204541959467605,
    supportLambdaLower := 352059238473238840786090295287,
    supportLambdaUpper := 362016384246175956915328213134,
    supportJLower := 42100163677600017475918814346, supportJUpper := 43725608773010964111112749737,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer19Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer19Panel0Data observer19Panel0Endpoints
theorem observer19_panel0_kernel_check : observer19Panel0Check = true := by
  decide +kernel
theorem observer19_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer19Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer19Panel0Data) s observer19Panel0Data.anchor ≤
        (observer19Panel0Endpoints.energyUpper : ℝ) ∧
      (observer19Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer19Panel0Data) s observer19Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer19Panel0Data) s observer19Panel0Data.anchor ≤
        (observer19Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer19Panel0Data) s observer19Panel0Data.anchor ≤
        (observer19Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer19Panel0Data) s observer19Panel0Data.anchor ≤
        (observer19Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer19Panel0Data observer19Panel0Endpoints
    observer19_panel0_kernel_check s hs
def observer19Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer19Panel0Endpoints
theorem observer19_panel0_recurrence_field_kernel_check :
    observer19Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer19_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer19Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer19Panel0Endpoints
    observer19_panel0_recurrence_field_kernel_check

def observer19Panel1Data : MainPanelData :=
  {
    observer := 19, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((498610169098 : ℚ) / 78799683530924538525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer19Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51129597373641976969018706800, ellLower := 351892230605630097843720962207,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6377227214060796587893566212, offsetUpper := 6391750731890394345278731508,
    supportELower := 40105395835167764973212636816, supportEUpper := 41512133212500294128034352103,
    supportLambdaLower := 351892230605630097843720962207,
    supportLambdaUpper := 361458678878077651175809879825,
    supportJLower := 43624318141224065951649846438, supportJUpper := 45126720001281070639792450902,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer19Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer19Panel1Data observer19Panel1Endpoints
theorem observer19_panel1_kernel_check : observer19Panel1Check = true := by
  decide +kernel
theorem observer19_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer19Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer19Panel1Data) s observer19Panel1Data.anchor ≤
        (observer19Panel1Endpoints.energyUpper : ℝ) ∧
      (observer19Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer19Panel1Data) s observer19Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer19Panel1Data) s observer19Panel1Data.anchor ≤
        (observer19Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer19Panel1Data) s observer19Panel1Data.anchor ≤
        (observer19Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer19Panel1Data) s observer19Panel1Data.anchor ≤
        (observer19Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer19Panel1Data observer19Panel1Endpoints
    observer19_panel1_kernel_check s hs
def observer19Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer19Panel1Endpoints
theorem observer19_panel1_recurrence_field_kernel_check :
    observer19Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer19_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer19Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer19Panel1Endpoints
    observer19_panel1_recurrence_field_kernel_check

def observer19Panel2Data : MainPanelData :=
  {
    observer := 19, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((498610169098 : ℚ) / 78799683530924538525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer19Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52832301178528580250247366940, ellLower := 351711676319366944703263276516,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6592982711854584539316794075, offsetUpper := 6607997591950863476578593870,
    supportELower := 41512079276406905677903780450, supportEUpper := 42899260846523197951507192500,
    supportLambdaLower := 351711676319366944703263276516,
    supportLambdaUpper := 360931745993998236111163716221,
    supportJLower := 45029196039600575124936413215, supportJUpper := 46508578306463180312618829663,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer19Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer19Panel2Data observer19Panel2Endpoints
theorem observer19_panel2_kernel_check : observer19Panel2Check = true := by
  decide +kernel
theorem observer19_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer19Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer19Panel2Data) s observer19Panel2Data.anchor ≤
        (observer19Panel2Endpoints.energyUpper : ℝ) ∧
      (observer19Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer19Panel2Data) s observer19Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer19Panel2Data) s observer19Panel2Data.anchor ≤
        (observer19Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer19Panel2Data) s observer19Panel2Data.anchor ≤
        (observer19Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer19Panel2Data) s observer19Panel2Data.anchor ≤
        (observer19Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer19Panel2Data observer19Panel2Endpoints
    observer19_panel2_kernel_check s hs
def observer19Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer19Panel2Endpoints
theorem observer19_panel2_recurrence_field_kernel_check :
    observer19Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer19_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer19Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer19Panel2Endpoints
    observer19_panel2_recurrence_field_kernel_check

def observer19Panel3Data : MainPanelData :=
  {
    observer := 19, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((498610169098 : ℚ) / 78799683530924538525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer19Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54524914830674091311066287076, ellLower := 351535082337552248347163144157,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6807623345083120800375194423, offsetUpper := 6823127048449923571987519140,
    supportELower := 42899202105293549368453498550, supportEUpper := 44276082020402576448142833355,
    supportLambdaLower := 351535082337552248347163144157,
    supportLambdaUpper := 360434156835145794985746601053,
    supportJLower := 46414552928669071851925129991, supportJUpper := 47880423588754034398000299366,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer19Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer19Panel3Data observer19Panel3Endpoints
theorem observer19_panel3_kernel_check : observer19Panel3Check = true := by
  decide +kernel
theorem observer19_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer19Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer19Panel3Data) s observer19Panel3Data.anchor ≤
        (observer19Panel3Endpoints.energyUpper : ℝ) ∧
      (observer19Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer19Panel3Data) s observer19Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer19Panel3Data) s observer19Panel3Data.anchor ≤
        (observer19Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer19Panel3Data) s observer19Panel3Data.anchor ≤
        (observer19Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer19Panel3Data) s observer19Panel3Data.anchor ≤
        (observer19Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer19Panel3Data observer19Panel3Endpoints
    observer19_panel3_kernel_check s hs
def observer19Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer19Panel3Endpoints
theorem observer19_panel3_recurrence_field_kernel_check :
    observer19Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer19_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer19Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer19Panel3Endpoints
    observer19_panel3_recurrence_field_kernel_check

def observer19Panel4Data : MainPanelData :=
  {
    observer := 19, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((498610169098 : ℚ) / 78799683530924538525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer19Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56210967173453405379822593454, ellLower := 351363726075167711364411392442,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7021555452054767931895143747, offsetUpper := 7037546365092111463876781085,
    supportELower := 44276018493277916803284048169, supportEUpper := 45646146790421112869800739951,
    supportLambdaLower := 351363726075167711364411392442,
    supportLambdaUpper := 359963785746427242148260995784,
    supportJLower := 47789655754029593916928162093, supportJUpper := 49245784647885385291283349909,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer19Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer19Panel4Data observer19Panel4Endpoints
theorem observer19_panel4_kernel_check : observer19Panel4Check = true := by
  decide +kernel
theorem observer19_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer19Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer19Panel4Data) s observer19Panel4Data.anchor ≤
        (observer19Panel4Endpoints.energyUpper : ℝ) ∧
      (observer19Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer19Panel4Data) s observer19Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer19Panel4Data) s observer19Panel4Data.anchor ≤
        (observer19Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer19Panel4Data) s observer19Panel4Data.anchor ≤
        (observer19Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer19Panel4Data) s observer19Panel4Data.anchor ≤
        (observer19Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer19Panel4Data observer19Panel4Endpoints
    observer19_panel4_kernel_check s hs
def observer19Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer19Panel4Endpoints
theorem observer19_panel4_recurrence_field_kernel_check :
    observer19Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer19_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer19Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer19Panel4Endpoints
    observer19_panel4_recurrence_field_kernel_check

def observer19Panel5Data : MainPanelData :=
  {
    observer := 19, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((498610169098 : ℚ) / 78799683530924538525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer19Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57892488894527565227065969057, ellLower := 351197863742034925160609163386,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7218539860418319197459417906, offsetUpper := 7235016927786157848133962676,
    supportELower := 45646078490552302178376889341, supportEUpper := 47011266701617743533986558272,
    supportLambdaLower := 351197863742034925160609163386,
    supportLambdaUpper := 359518507194527108400442589055,
    supportJLower := 49158057127972651429982980974, supportJUpper := 50606451773563014617990984163,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer19Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer19Panel5Data observer19Panel5Endpoints
theorem observer19_panel5_kernel_check : observer19Panel5Check = true := by
  decide +kernel
theorem observer19_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer19Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer19Panel5Data) s observer19Panel5Data.anchor ≤
        (observer19Panel5Endpoints.energyUpper : ℝ) ∧
      (observer19Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer19Panel5Data) s observer19Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer19Panel5Data) s observer19Panel5Data.anchor ≤
        (observer19Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer19Panel5Data) s observer19Panel5Data.anchor ≤
        (observer19Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer19Panel5Data) s observer19Panel5Data.anchor ≤
        (observer19Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer19Panel5Data observer19Panel5Endpoints
    observer19_panel5_kernel_check s hs
def observer19Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer19Panel5Endpoints
theorem observer19_panel5_recurrence_field_kernel_check :
    observer19Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer19_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer19Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer19Panel5Endpoints
    observer19_panel5_recurrence_field_kernel_check

def observer19Panel6Data : MainPanelData :=
  {
    observer := 19, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((498610169098 : ℚ) / 78799683530924538525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer19Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59570054424605623739899541086, ellLower := 351037456084149573792747659612,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7431107461970570166224201536, offsetUpper := 7448069736978557991232546941,
    supportELower := 47011193639087732496802409308, supportEUpper := 48372516802960995598712374997,
    supportLambdaLower := 351037456084149573792747659612,
    supportLambdaUpper := 359096339461690202402655022101,
    supportJLower := 50521568199929228234729885904, supportJUpper := 51963480197577897622738925219,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer19Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer19Panel6Data observer19Panel6Endpoints
theorem observer19_panel6_kernel_check : observer19Panel6Check = true := by
  decide +kernel
theorem observer19_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer19Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer19Panel6Data) s observer19Panel6Data.anchor ≤
        (observer19Panel6Endpoints.energyUpper : ℝ) ∧
      (observer19Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer19Panel6Data) s observer19Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer19Panel6Data) s observer19Panel6Data.anchor ≤
        (observer19Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer19Panel6Data) s observer19Panel6Data.anchor ≤
        (observer19Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer19Panel6Data) s observer19Panel6Data.anchor ≤
        (observer19Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer19Panel6Data observer19Panel6Endpoints
    observer19_panel6_kernel_check s hs
def observer19Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer19Panel6Endpoints
theorem observer19_panel6_recurrence_field_kernel_check :
    observer19Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer19_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer19Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer19Panel6Endpoints
    observer19_panel6_recurrence_field_kernel_check

def observer19Panel7Data : MainPanelData :=
  {
    observer := 19, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((498610169098 : ℚ) / 78799683530924538525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer19Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61244588476702678612158559009, ellLower := 350882352248976817285413895816,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7643375545989974967246699905, offsetUpper := 7660822344958217973576345443,
    supportELower := 48372438986031008837194695723, supportEUpper := 49730599356277741739349495016,
    supportLambdaLower := 350882352248976817285413895816,
    supportLambdaUpper := 358695474268245945274777901404,
    supportJLower := 51881262508520777010048834681, supportJUpper := 53317554098960201192097274031,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer19Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer19Panel7Data observer19Panel7Endpoints
theorem observer19_panel7_kernel_check : observer19Panel7Check = true := by
  decide +kernel
theorem observer19_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer19Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer19Panel7Data) s observer19Panel7Data.anchor ≤
        (observer19Panel7Endpoints.energyUpper : ℝ) ∧
      (observer19Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer19Panel7Data) s observer19Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer19Panel7Data) s observer19Panel7Data.anchor ≤
        (observer19Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer19Panel7Data) s observer19Panel7Data.anchor ≤
        (observer19Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer19Panel7Data) s observer19Panel7Data.anchor ≤
        (observer19Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer19Panel7Data observer19Panel7Endpoints
    observer19_panel7_kernel_check s hs
def observer19Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer19Panel7Endpoints
theorem observer19_panel7_recurrence_field_kernel_check :
    observer19Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer19_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer19Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer19Panel7Endpoints
    observer19_panel7_recurrence_field_kernel_check

def observer19InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 19, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer19Panel0Endpoints, observer19Panel1Endpoints, observer19Panel2Endpoints, observer19Panel3Endpoints, observer19Panel4Endpoints, observer19Panel5Endpoints, observer19Panel6Endpoints, observer19Panel7Endpoints]
  }
def observer19FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer19InsertionEndpoints.frameLower
    observer19InsertionEndpoints.frameUpper
theorem observer19_frame_recurrence_field_kernel_check :
    observer19FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer19_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer19InsertionEndpoints.frameLower
      observer19InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer19InsertionEndpoints.frameLower
    observer19InsertionEndpoints.frameUpper
    observer19_frame_recurrence_field_kernel_check
def observer19RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer19Panel0Endpoints ∧
  panelRecurrenceFields observer19Panel1Endpoints ∧
  panelRecurrenceFields observer19Panel2Endpoints ∧
  panelRecurrenceFields observer19Panel3Endpoints ∧
  panelRecurrenceFields observer19Panel4Endpoints ∧
  panelRecurrenceFields observer19Panel5Endpoints ∧
  panelRecurrenceFields observer19Panel6Endpoints ∧
  panelRecurrenceFields observer19Panel7Endpoints ∧ insertionFrameRecurrenceFields observer19InsertionEndpoints.frameLower
      observer19InsertionEndpoints.frameUpper
theorem observer19_all_recurrence_fields :
    observer19RecurrenceFieldBounds := by
  exact ⟨observer19_panel0_recurrence_fields_sound,
    observer19_panel1_recurrence_fields_sound,
    observer19_panel2_recurrence_fields_sound,
    observer19_panel3_recurrence_fields_sound,
    observer19_panel4_recurrence_fields_sound,
    observer19_panel5_recurrence_fields_sound,
    observer19_panel6_recurrence_fields_sound,
    observer19_panel7_recurrence_fields_sound,
    observer19_frame_recurrence_fields_sound⟩
def observer19PanelFormulaBounds : Prop :=
  panelFormulaBounds observer19Panel0Data observer19Panel0Endpoints ∧
  panelFormulaBounds observer19Panel1Data observer19Panel1Endpoints ∧
  panelFormulaBounds observer19Panel2Data observer19Panel2Endpoints ∧
  panelFormulaBounds observer19Panel3Data observer19Panel3Endpoints ∧
  panelFormulaBounds observer19Panel4Data observer19Panel4Endpoints ∧
  panelFormulaBounds observer19Panel5Data observer19Panel5Endpoints ∧
  panelFormulaBounds observer19Panel6Data observer19Panel6Endpoints ∧
  panelFormulaBounds observer19Panel7Data observer19Panel7Endpoints
theorem observer19_all_panel_formula_bounds : observer19PanelFormulaBounds := by
  exact ⟨observer19_panel0_formula_sound,
    observer19_panel1_formula_sound,
    observer19_panel2_formula_sound,
    observer19_panel3_formula_sound,
    observer19_panel4_formula_sound,
    observer19_panel5_formula_sound,
    observer19_panel6_formula_sound,
    observer19_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
