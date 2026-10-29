module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer36Panel0Data : MainPanelData :=
  {
    observer := 36, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((64390598542412622664 : ℚ) / 1314156640121451840690675292695070725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer36Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49393298970998543759704117634, ellLower := 352020922689064770121799611914,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6172437368521770447074393012, offsetUpper := 6186462542263461236741207862,
    supportELower := 38565849858748463980036168874, supportEUpper := 40091570197450596706902686853,
    supportLambdaLower := 352020922689064770121799611914,
    supportLambdaUpper := 361977515049190802425599248839,
    supportJLower := 42086059085639111681254164993, supportJUpper := 43711345347942504731158679342,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer36Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer36Panel0Data observer36Panel0Endpoints
theorem observer36_panel0_kernel_check : observer36Panel0Check = true := by
  decide +kernel
theorem observer36_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer36Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer36Panel0Data) s observer36Panel0Data.anchor ≤
        (observer36Panel0Endpoints.energyUpper : ℝ) ∧
      (observer36Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer36Panel0Data) s observer36Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer36Panel0Data) s observer36Panel0Data.anchor ≤
        (observer36Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer36Panel0Data) s observer36Panel0Data.anchor ≤
        (observer36Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer36Panel0Data) s observer36Panel0Data.anchor ≤
        (observer36Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer36Panel0Data observer36Panel0Endpoints
    observer36_panel0_kernel_check s hs
def observer36Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer36Panel0Endpoints
theorem observer36_panel0_recurrence_field_kernel_check :
    observer36Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer36_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer36Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer36Panel0Endpoints
    observer36_panel0_recurrence_field_kernel_check

def observer36Panel1Data : MainPanelData :=
  {
    observer := 36, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((64390598542412622664 : ℚ) / 1314156640121451840690675292695070725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer36Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51115184483576918039772215753, ellLower := 351854273931298276865309466907,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376117298100475107426358290, offsetUpper := 6390638288203884351048860098,
    supportELower := 40091521116262942927263004926, supportEUpper := 41498106309403265965284650803,
    supportLambdaLower := 351854273931298276865309466907,
    supportLambdaUpper := 361420187789543096074047361176,
    supportJLower := 43610063855575925695916099595, supportJUpper := 45112308187298696926025124415,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer36Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer36Panel1Data observer36Panel1Endpoints
theorem observer36_panel1_kernel_check : observer36Panel1Check = true := by
  decide +kernel
theorem observer36_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer36Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer36Panel1Data) s observer36Panel1Data.anchor ≤
        (observer36Panel1Endpoints.energyUpper : ℝ) ∧
      (observer36Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer36Panel1Data) s observer36Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer36Panel1Data) s observer36Panel1Data.anchor ≤
        (observer36Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer36Panel1Data) s observer36Panel1Data.anchor ≤
        (observer36Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer36Panel1Data) s observer36Panel1Data.anchor ≤
        (observer36Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer36Panel1Data observer36Panel1Endpoints
    observer36_panel1_kernel_check s hs
def observer36Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer36Panel1Endpoints
theorem observer36_panel1_recurrence_field_kernel_check :
    observer36Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer36_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer36Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer36Panel1Endpoints
    observer36_panel1_recurrence_field_kernel_check

def observer36Panel2Data : MainPanelData :=
  {
    observer := 36, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((64390598542412622664 : ℚ) / 1314156640121451840690675292695070725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer36Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52817740832741872542437494500, ellLower := 351674065602800123656385883451,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6591870625037578282633120266, offsetUpper := 6606882972463752689256856485,
    supportELower := 41498052387970368415745197804, supportEUpper := 42885082850541492490510903411,
    supportLambdaLower := 351674065602800123656385883451,
    supportLambdaUpper := 360893618621766532977721837144,
    supportJLower := 45014793043998369652309056638, supportJUpper := 46494019036759157820288121783,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer36Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer36Panel2Data observer36Panel2Endpoints
theorem observer36_panel2_kernel_check : observer36Panel2Check = true := by
  decide +kernel
theorem observer36_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer36Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer36Panel2Data) s observer36Panel2Data.anchor ≤
        (observer36Panel2Endpoints.energyUpper : ℝ) ∧
      (observer36Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer36Panel2Data) s observer36Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer36Panel2Data) s observer36Panel2Data.anchor ≤
        (observer36Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer36Panel2Data) s observer36Panel2Data.anchor ≤
        (observer36Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer36Panel2Data) s observer36Panel2Data.anchor ≤
        (observer36Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer36Panel2Data observer36Panel2Endpoints
    observer36_panel2_kernel_check s hs
def observer36Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer36Panel2Endpoints
theorem observer36_panel2_recurrence_field_kernel_check :
    observer36Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer36_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer36Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer36Panel2Endpoints
    observer36_panel2_recurrence_field_kernel_check

def observer36Panel3Data : MainPanelData :=
  {
    observer := 36, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((64390598542412622664 : ℚ) / 1314156640121451840690675292695070725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer36Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54510207936569795774514926443, ellLower := 351497805293181037077661253267,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6806508906039260189736502117, offsetUpper := 6822010071378989404557035327,
    supportELower := 42885024124433659031490890818, supportEUpper := 44261753972976162654052851147,
    supportLambdaLower := 351497805293181037077661253267,
    supportLambdaUpper := 360396379775626142287525214598,
    supportJLower := 46400002177365469402267503350, supportJUpper := 47865717770732424076928103293,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer36Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer36Panel3Data observer36Panel3Endpoints
theorem observer36_panel3_kernel_check : observer36Panel3Check = true := by
  decide +kernel
theorem observer36_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer36Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer36Panel3Data) s observer36Panel3Data.anchor ≤
        (observer36Panel3Endpoints.energyUpper : ℝ) ∧
      (observer36Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer36Panel3Data) s observer36Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer36Panel3Data) s observer36Panel3Data.anchor ≤
        (observer36Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer36Panel3Data) s observer36Panel3Data.anchor ≤
        (observer36Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer36Panel3Data) s observer36Panel3Data.anchor ≤
        (observer36Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer36Panel3Data observer36Panel3Endpoints
    observer36_panel3_kernel_check s hs
def observer36Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer36Panel3Endpoints
theorem observer36_panel3_recurrence_field_kernel_check :
    observer36Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer36_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer36Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer36Panel3Endpoints
    observer36_panel3_recurrence_field_kernel_check

def observer36Panel4Data : MainPanelData :=
  {
    observer := 36, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((64390598542412622664 : ℚ) / 1314156640121451840690675292695070725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer36Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56196114613862782700718023552, ellLower := 351326771199018839120287052348,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7020438533029439767522764974, offsetUpper := 7036426902391791948334132762,
    supportELower := 44261690461429499739058027346, supportEUpper := 45631669699541323118376897929,
    supportLambdaLower := 351326771199018839120287052348,
    supportLambdaUpper := 359926346483612470928104663715,
    supportJLower := 47774958173419688130260897869, supportJUpper := 49230933164377447827657944567,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer36Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer36Panel4Data observer36Panel4Endpoints
theorem observer36_panel4_kernel_check : observer36Panel4Check = true := by
  decide +kernel
theorem observer36_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer36Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer36Panel4Data) s observer36Panel4Data.anchor ≤
        (observer36Panel4Endpoints.energyUpper : ℝ) ∧
      (observer36Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer36Panel4Data) s observer36Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer36Panel4Data) s observer36Panel4Data.anchor ≤
        (observer36Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer36Panel4Data) s observer36Panel4Data.anchor ≤
        (observer36Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer36Panel4Data) s observer36Panel4Data.anchor ≤
        (observer36Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer36Panel4Data observer36Panel4Endpoints
    observer36_panel4_kernel_check s hs
def observer36Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer36Panel4Endpoints
theorem observer36_panel4_recurrence_field_kernel_check :
    observer36Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer36_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer36Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer36Panel4Endpoints
    observer36_panel4_recurrence_field_kernel_check

def observer36Panel5Data : MainPanelData :=
  {
    observer := 36, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((64390598542412622664 : ℚ) / 1314156640121451840690675292695070725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer36Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57877491528847717182002282747, ellLower := 351161220237887576497090651790,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7217422914234829883698419100, offsetUpper := 7233897432056933874237734216,
    supportELower := 45631601415701768259238719212, supportEUpper := 46996641543838794454379871118,
    supportLambdaLower := 351161220237887576497090651790,
    supportLambdaUpper := 359481394012705733402659129495,
    supportJLower := 49143213618080644024209625729, supportJUpper := 50591455483965851788406462413,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer36Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer36Panel5Data observer36Panel5Endpoints
theorem observer36_panel5_kernel_check : observer36Panel5Check = true := by
  decide +kernel
theorem observer36_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer36Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer36Panel5Data) s observer36Panel5Data.anchor ≤
        (observer36Panel5Endpoints.energyUpper : ℝ) ∧
      (observer36Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer36Panel5Data) s observer36Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer36Panel5Data) s observer36Panel5Data.anchor ≤
        (observer36Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer36Panel5Data) s observer36Panel5Data.anchor ≤
        (observer36Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer36Panel5Data) s observer36Panel5Data.anchor ≤
        (observer36Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer36Panel5Data observer36Panel5Endpoints
    observer36_panel5_kernel_check s hs
def observer36Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer36Panel5Endpoints
theorem observer36_panel5_recurrence_field_kernel_check :
    observer36Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer36_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer36Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer36Panel5Endpoints
    observer36_panel5_recurrence_field_kernel_check

def observer36Panel6Data : MainPanelData :=
  {
    observer := 36, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((64390598542412622664 : ℚ) / 1314156640121451840690675292695070725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer36Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59554913089866293150624182672, ellLower := 351001113798978736867621315471,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7429987859205488575672604585, offsetUpper := 7446947578603818189451262065,
    supportELower := 46996568497784579842220552380, supportEUpper := 48357744525225643514309221931,
    supportLambdaLower := 351001113798978736867621315471,
    supportLambdaUpper := 359059541369560873463350943346,
    supportJLower := 50506579635774367210896765534, supportJUpper := 51948339938921252248942731365,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer36Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer36Panel6Data observer36Panel6Endpoints
theorem observer36_panel6_kernel_check : observer36Panel6Check = true := by
  decide +kernel
theorem observer36_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer36Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer36Panel6Data) s observer36Panel6Data.anchor ≤
        (observer36Panel6Endpoints.energyUpper : ℝ) ∧
      (observer36Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer36Panel6Data) s observer36Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer36Panel6Data) s observer36Panel6Data.anchor ≤
        (observer36Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer36Panel6Data) s observer36Panel6Data.anchor ≤
        (observer36Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer36Panel6Data) s observer36Panel6Data.anchor ≤
        (observer36Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer36Panel6Data observer36Panel6Endpoints
    observer36_panel6_kernel_check s hs
def observer36Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer36Panel6Endpoints
theorem observer36_panel6_recurrence_field_kernel_check :
    observer36Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer36_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer36Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer36Panel6Endpoints
    observer36_panel6_recurrence_field_kernel_check

def observer36Panel7Data : MainPanelData :=
  {
    observer := 36, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((64390598542412622664 : ℚ) / 1314156640121451840690675292695070725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer36Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61229303988566116138813333820, ellLower := 350846301616239102979700850775,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642253215603653503083653431, offsetUpper := 7659697452736159369149257174,
    supportELower := 48357666725213464868185110160, supportEUpper := 49715680877580350832802368417,
    supportLambdaLower := 350846301616239102979700850775,
    supportLambdaUpper := 358658980932597310142884498480,
    supportJLower := 51866129741375855897982118667, supportJUpper := 53302270686906323934231213402,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer36Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer36Panel7Data observer36Panel7Endpoints
theorem observer36_panel7_kernel_check : observer36Panel7Check = true := by
  decide +kernel
theorem observer36_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer36Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer36Panel7Data) s observer36Panel7Data.anchor ≤
        (observer36Panel7Endpoints.energyUpper : ℝ) ∧
      (observer36Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer36Panel7Data) s observer36Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer36Panel7Data) s observer36Panel7Data.anchor ≤
        (observer36Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer36Panel7Data) s observer36Panel7Data.anchor ≤
        (observer36Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer36Panel7Data) s observer36Panel7Data.anchor ≤
        (observer36Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer36Panel7Data observer36Panel7Endpoints
    observer36_panel7_kernel_check s hs
def observer36Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer36Panel7Endpoints
theorem observer36_panel7_recurrence_field_kernel_check :
    observer36Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer36_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer36Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer36Panel7Endpoints
    observer36_panel7_recurrence_field_kernel_check

def observer36InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 36, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer36Panel0Endpoints, observer36Panel1Endpoints, observer36Panel2Endpoints, observer36Panel3Endpoints, observer36Panel4Endpoints, observer36Panel5Endpoints, observer36Panel6Endpoints, observer36Panel7Endpoints]
  }
def observer36FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer36InsertionEndpoints.frameLower
    observer36InsertionEndpoints.frameUpper
theorem observer36_frame_recurrence_field_kernel_check :
    observer36FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer36_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer36InsertionEndpoints.frameLower
      observer36InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer36InsertionEndpoints.frameLower
    observer36InsertionEndpoints.frameUpper
    observer36_frame_recurrence_field_kernel_check
def observer36RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer36Panel0Endpoints ∧
  panelRecurrenceFields observer36Panel1Endpoints ∧
  panelRecurrenceFields observer36Panel2Endpoints ∧
  panelRecurrenceFields observer36Panel3Endpoints ∧
  panelRecurrenceFields observer36Panel4Endpoints ∧
  panelRecurrenceFields observer36Panel5Endpoints ∧
  panelRecurrenceFields observer36Panel6Endpoints ∧
  panelRecurrenceFields observer36Panel7Endpoints ∧ insertionFrameRecurrenceFields observer36InsertionEndpoints.frameLower
      observer36InsertionEndpoints.frameUpper
theorem observer36_all_recurrence_fields :
    observer36RecurrenceFieldBounds := by
  exact ⟨observer36_panel0_recurrence_fields_sound,
    observer36_panel1_recurrence_fields_sound,
    observer36_panel2_recurrence_fields_sound,
    observer36_panel3_recurrence_fields_sound,
    observer36_panel4_recurrence_fields_sound,
    observer36_panel5_recurrence_fields_sound,
    observer36_panel6_recurrence_fields_sound,
    observer36_panel7_recurrence_fields_sound,
    observer36_frame_recurrence_fields_sound⟩
def observer36PanelFormulaBounds : Prop :=
  panelFormulaBounds observer36Panel0Data observer36Panel0Endpoints ∧
  panelFormulaBounds observer36Panel1Data observer36Panel1Endpoints ∧
  panelFormulaBounds observer36Panel2Data observer36Panel2Endpoints ∧
  panelFormulaBounds observer36Panel3Data observer36Panel3Endpoints ∧
  panelFormulaBounds observer36Panel4Data observer36Panel4Endpoints ∧
  panelFormulaBounds observer36Panel5Data observer36Panel5Endpoints ∧
  panelFormulaBounds observer36Panel6Data observer36Panel6Endpoints ∧
  panelFormulaBounds observer36Panel7Data observer36Panel7Endpoints
theorem observer36_all_panel_formula_bounds : observer36PanelFormulaBounds := by
  exact ⟨observer36_panel0_formula_sound,
    observer36_panel1_formula_sound,
    observer36_panel2_formula_sound,
    observer36_panel3_formula_sound,
    observer36_panel4_formula_sound,
    observer36_panel5_formula_sound,
    observer36_panel6_formula_sound,
    observer36_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
