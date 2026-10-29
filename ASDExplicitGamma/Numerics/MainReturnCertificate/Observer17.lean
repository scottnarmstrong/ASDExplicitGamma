module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer17Panel0Data : MainPanelData :=
  {
    observer := 17, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((55401129682 : ℚ) / 972835599147216525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer17Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49436157073430526898200179296, ellLower := 352136193861798782944304768799,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6175770844681792902574839671, offsetUpper := 6189803592835262502385673541,
    supportELower := 38607067529753352890170741711, supportEUpper := 40133249211721388814315127297,
    supportLambdaLower := 352136193861798782944304768799,
    supportLambdaUpper := 362094455390890352466576931139,
    supportJLower := 42128429468371340719613789398, supportJUpper := 43754193765630292338980896609,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer17Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer17Panel0Data observer17Panel0Endpoints
theorem observer17_panel0_kernel_check : observer17Panel0Check = true := by
  decide +kernel
theorem observer17_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer17Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer17Panel0Data) s observer17Panel0Data.anchor ≤
        (observer17Panel0Endpoints.energyUpper : ℝ) ∧
      (observer17Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer17Panel0Data) s observer17Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer17Panel0Data) s observer17Panel0Data.anchor ≤
        (observer17Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer17Panel0Data) s observer17Panel0Data.anchor ≤
        (observer17Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer17Panel0Data) s observer17Panel0Data.anchor ≤
        (observer17Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer17Panel0Data observer17Panel0Endpoints
    observer17_panel0_kernel_check s hs
def observer17Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer17Panel0Endpoints
theorem observer17_panel0_recurrence_field_kernel_check :
    observer17Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer17_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer17Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer17Panel0Endpoints
    observer17_panel0_recurrence_field_kernel_check

def observer17Panel1Data : MainPanelData :=
  {
    observer := 17, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((55401129682 : ℚ) / 972835599147216525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer17Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51158489157694210018313728540, ellLower := 351968464581523313762705540597,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6379448747098365233750654737, offsetUpper := 6393977324254469192848662113,
    supportELower := 40133200087894749370491153041, supportEUpper := 41540243274153455364615392695,
    supportLambdaLower := 351968464581523313762705540597,
    supportLambdaUpper := 361535990251833800927740011140,
    supportJLower := 43652884733709982508118208446, supportJUpper := 45155603176671793373892792807,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer17Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer17Panel1Data observer17Panel1Endpoints
theorem observer17_panel1_kernel_check : observer17Panel1Check = true := by
  decide +kernel
theorem observer17_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer17Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer17Panel1Data) s observer17Panel1Data.anchor ≤
        (observer17Panel1Endpoints.energyUpper : ℝ) ∧
      (observer17Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer17Panel1Data) s observer17Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer17Panel1Data) s observer17Panel1Data.anchor ≤
        (observer17Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer17Panel1Data) s observer17Panel1Data.anchor ≤
        (observer17Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer17Panel1Data) s observer17Panel1Data.anchor ≤
        (observer17Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer17Panel1Data observer17Panel1Endpoints
    observer17_panel1_kernel_check s hs
def observer17Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer17Panel1Endpoints
theorem observer17_panel1_recurrence_field_kernel_check :
    observer17Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer17_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer17Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer17Panel1Endpoints
    observer17_panel1_recurrence_field_kernel_check

def observer17Panel2Data : MainPanelData :=
  {
    observer := 17, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((55401129682 : ℚ) / 972835599147216525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer17Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52861489275811818666917708299, ellLower := 351787215378475587391780300560,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6595208627149166071523290908, offsetUpper := 6610228576552117468367123480,
    supportELower := 41540189308677221128753285029, supportEUpper := 42927674529076327890342756536,
    supportLambdaLower := 351787215378475587391780300560,
    supportLambdaUpper := 361008326600858052375173465089,
    supportJLower := 45058061462461977002671088034, supportJUpper := 46537757795084908414094491187,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer17Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer17Panel2Data observer17Panel2Endpoints
theorem observer17_panel2_kernel_check : observer17Panel2Check = true := by
  decide +kernel
theorem observer17_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer17Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer17Panel2Data) s observer17Panel2Data.anchor ≤
        (observer17Panel2Endpoints.energyUpper : ℝ) ∧
      (observer17Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer17Panel2Data) s observer17Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer17Panel2Data) s observer17Panel2Data.anchor ≤
        (observer17Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer17Panel2Data) s observer17Panel2Data.anchor ≤
        (observer17Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer17Panel2Data) s observer17Panel2Data.anchor ≤
        (observer17Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer17Panel2Data observer17Panel2Endpoints
    observer17_panel2_kernel_check s hs
def observer17Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer17Panel2Endpoints
theorem observer17_panel2_recurrence_field_kernel_check :
    observer17Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer17_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer17Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer17Panel2Endpoints
    observer17_panel2_recurrence_field_kernel_check

def observer17Panel3Data : MainPanelData :=
  {
    observer := 17, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((55401129682 : ℚ) / 972835599147216525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer17Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54554397423412951042045856989, ellLower := 351609951225543157239457641050,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6809854006003339921252454215, offsetUpper := 6825362789484518288403825550,
    supportELower := 42927615757536970700005752854, supportEUpper := 44304797236014041795629517962,
    supportLambdaLower := 351609951225543157239457641050,
    supportLambdaUpper := 360510033681734201815567148180,
    supportJLower := 46443715269792402272400329264, supportJUpper := 47909897572831383813785189444,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer17Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer17Panel3Data observer17Panel3Endpoints
theorem observer17_panel3_kernel_check : observer17Panel3Check = true := by
  decide +kernel
theorem observer17_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer17Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer17Panel3Data) s observer17Panel3Data.anchor ≤
        (observer17Panel3Endpoints.energyUpper : ℝ) ∧
      (observer17Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer17Panel3Data) s observer17Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer17Panel3Data) s observer17Panel3Data.anchor ≤
        (observer17Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer17Panel3Data) s observer17Panel3Data.anchor ≤
        (observer17Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer17Panel3Data) s observer17Panel3Data.anchor ≤
        (observer17Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer17Panel3Data observer17Panel3Endpoints
    observer17_panel3_kernel_check s hs
def observer17Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer17Panel3Endpoints
theorem observer17_panel3_recurrence_field_kernel_check :
    observer17Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer17_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer17Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer17Panel3Endpoints
    observer17_panel3_recurrence_field_kernel_check

def observer17Panel4Data : MainPanelData :=
  {
    observer := 17, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((55401129682 : ℚ) / 972835599147216525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer17Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56240742493192500962833112521, ellLower := 351437947959348791398633387272,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7023791114398820778521507669, offsetUpper := 7039787118940798679061126549,
    supportELower := 44304733677663115036393162074, supportEUpper := 45675161518499412850396801255,
    supportLambdaLower := 351437947959348791398633387272,
    supportLambdaUpper := 360038984046355770870238788563,
    supportJLower := 47819113157256602950379495946, supportJUpper := 49275551358962970559099189141,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer17Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer17Panel4Data observer17Panel4Endpoints
theorem observer17_panel4_kernel_check : observer17Panel4Check = true := by
  decide +kernel
theorem observer17_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer17Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer17Panel4Data) s observer17Panel4Data.anchor ≤
        (observer17Panel4Endpoints.energyUpper : ℝ) ∧
      (observer17Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer17Panel4Data) s observer17Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer17Panel4Data) s observer17Panel4Data.anchor ≤
        (observer17Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer17Panel4Data) s observer17Panel4Data.anchor ≤
        (observer17Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer17Panel4Data) s observer17Panel4Data.anchor ≤
        (observer17Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer17Panel4Data observer17Panel4Endpoints
    observer17_panel4_kernel_check s hs
def observer17Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer17Panel4Endpoints
theorem observer17_panel4_recurrence_field_kernel_check :
    observer17Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer17_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer17Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer17Panel4Endpoints
    observer17_panel4_recurrence_field_kernel_check

def observer17Panel5Data : MainPanelData :=
  {
    observer := 17, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((55401129682 : ℚ) / 972835599147216525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer17Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57922555219841184243443455252, ellLower := 351271460360779903632945945373,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7237257785098587293984995137, offsetUpper := 7253739939325038923224089394,
    supportELower := 45675093186497638676571386974, supportEUpper := 47040578984764367452102818165,
    supportLambdaLower := 351271460360779903632945945373,
    supportLambdaUpper := 359593050545075586707097235780,
    supportJLower := 49187807790105437712900846427, supportJUpper := 50636509490215123319173790523,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer17Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer17Panel5Data observer17Panel5Endpoints
theorem observer17_panel5_kernel_check : observer17Panel5Check = true := by
  decide +kernel
theorem observer17_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer17Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer17Panel5Data) s observer17Panel5Data.anchor ≤
        (observer17Panel5Endpoints.energyUpper : ℝ) ∧
      (observer17Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer17Panel5Data) s observer17Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer17Panel5Data) s observer17Panel5Data.anchor ≤
        (observer17Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer17Panel5Data) s observer17Panel5Data.anchor ≤
        (observer17Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer17Panel5Data) s observer17Panel5Data.anchor ≤
        (observer17Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer17Panel5Data observer17Panel5Endpoints
    observer17_panel5_kernel_check s hs
def observer17Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer17Panel5Endpoints
theorem observer17_panel5_recurrence_field_kernel_check :
    observer17Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer17_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer17Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer17Panel5Endpoints
    observer17_panel5_recurrence_field_kernel_check

def observer17Panel6Data : MainPanelData :=
  {
    observer := 17, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((55401129682 : ℚ) / 972835599147216525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer17Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59600410078952165355779965166, ellLower := 351110447877503819491176364217,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7433348570629903879680658961, offsetUpper := 7450315961201298228320622345,
    supportELower := 47040505889204149012354376844, supportEUpper := 48402124743289149750112469369,
    supportLambdaLower := 351110447877503819491176364217,
    supportLambdaUpper := 359170249997377917331220009454,
    supportJLower := 50551610367979187207266140486, supportJUpper := 51993827243262928923424669464,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer17Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer17Panel6Data observer17Panel6Endpoints
theorem observer17_panel6_kernel_check : observer17Panel6Check = true := by
  decide +kernel
theorem observer17_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer17Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer17Panel6Data) s observer17Panel6Data.anchor ≤
        (observer17Panel6Endpoints.energyUpper : ℝ) ∧
      (observer17Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer17Panel6Data) s observer17Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer17Panel6Data) s observer17Panel6Data.anchor ≤
        (observer17Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer17Panel6Data) s observer17Panel6Data.anchor ≤
        (observer17Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer17Panel6Data) s observer17Panel6Data.anchor ≤
        (observer17Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer17Panel6Data observer17Panel6Endpoints
    observer17_panel6_kernel_check s hs
def observer17Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer17Panel6Endpoints
theorem observer17_panel6_recurrence_field_kernel_check :
    observer17Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer17_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer17Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer17Panel6Endpoints
    observer17_panel6_recurrence_field_kernel_check

def observer17Panel7Data : MainPanelData :=
  {
    observer := 17, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((55401129682 : ℚ) / 972835599147216525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer17Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61275231826413960637604209501, ellLower := 350954758473373977989859432597,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7645622151397521458803789901, offsetUpper := 7663074078476069995670704620,
    supportELower := 48402046892440783402625980720, supportEUpper := 49760501112059787599073866390,
    supportLambdaLower := 350954758473373977989859432597,
    supportLambdaUpper := 358768772795018530327437829715,
    supportJLower := 51911594477174523182524575045, supportJUpper := 53348188840009972902348244688,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer17Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer17Panel7Data observer17Panel7Endpoints
theorem observer17_panel7_kernel_check : observer17Panel7Check = true := by
  decide +kernel
theorem observer17_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer17Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer17Panel7Data) s observer17Panel7Data.anchor ≤
        (observer17Panel7Endpoints.energyUpper : ℝ) ∧
      (observer17Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer17Panel7Data) s observer17Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer17Panel7Data) s observer17Panel7Data.anchor ≤
        (observer17Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer17Panel7Data) s observer17Panel7Data.anchor ≤
        (observer17Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer17Panel7Data) s observer17Panel7Data.anchor ≤
        (observer17Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer17Panel7Data observer17Panel7Endpoints
    observer17_panel7_kernel_check s hs
def observer17Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer17Panel7Endpoints
theorem observer17_panel7_recurrence_field_kernel_check :
    observer17Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer17_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer17Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer17Panel7Endpoints
    observer17_panel7_recurrence_field_kernel_check

def observer17InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 17, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer17Panel0Endpoints, observer17Panel1Endpoints, observer17Panel2Endpoints, observer17Panel3Endpoints, observer17Panel4Endpoints, observer17Panel5Endpoints, observer17Panel6Endpoints, observer17Panel7Endpoints]
  }
def observer17FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer17InsertionEndpoints.frameLower
    observer17InsertionEndpoints.frameUpper
theorem observer17_frame_recurrence_field_kernel_check :
    observer17FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer17_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer17InsertionEndpoints.frameLower
      observer17InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer17InsertionEndpoints.frameLower
    observer17InsertionEndpoints.frameUpper
    observer17_frame_recurrence_field_kernel_check
def observer17RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer17Panel0Endpoints ∧
  panelRecurrenceFields observer17Panel1Endpoints ∧
  panelRecurrenceFields observer17Panel2Endpoints ∧
  panelRecurrenceFields observer17Panel3Endpoints ∧
  panelRecurrenceFields observer17Panel4Endpoints ∧
  panelRecurrenceFields observer17Panel5Endpoints ∧
  panelRecurrenceFields observer17Panel6Endpoints ∧
  panelRecurrenceFields observer17Panel7Endpoints ∧ insertionFrameRecurrenceFields observer17InsertionEndpoints.frameLower
      observer17InsertionEndpoints.frameUpper
theorem observer17_all_recurrence_fields :
    observer17RecurrenceFieldBounds := by
  exact ⟨observer17_panel0_recurrence_fields_sound,
    observer17_panel1_recurrence_fields_sound,
    observer17_panel2_recurrence_fields_sound,
    observer17_panel3_recurrence_fields_sound,
    observer17_panel4_recurrence_fields_sound,
    observer17_panel5_recurrence_fields_sound,
    observer17_panel6_recurrence_fields_sound,
    observer17_panel7_recurrence_fields_sound,
    observer17_frame_recurrence_fields_sound⟩
def observer17PanelFormulaBounds : Prop :=
  panelFormulaBounds observer17Panel0Data observer17Panel0Endpoints ∧
  panelFormulaBounds observer17Panel1Data observer17Panel1Endpoints ∧
  panelFormulaBounds observer17Panel2Data observer17Panel2Endpoints ∧
  panelFormulaBounds observer17Panel3Data observer17Panel3Endpoints ∧
  panelFormulaBounds observer17Panel4Data observer17Panel4Endpoints ∧
  panelFormulaBounds observer17Panel5Data observer17Panel5Endpoints ∧
  panelFormulaBounds observer17Panel6Data observer17Panel6Endpoints ∧
  panelFormulaBounds observer17Panel7Data observer17Panel7Endpoints
theorem observer17_all_panel_formula_bounds : observer17PanelFormulaBounds := by
  exact ⟨observer17_panel0_formula_sound,
    observer17_panel1_formula_sound,
    observer17_panel2_formula_sound,
    observer17_panel3_formula_sound,
    observer17_panel4_formula_sound,
    observer17_panel5_formula_sound,
    observer17_panel6_formula_sound,
    observer17_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
