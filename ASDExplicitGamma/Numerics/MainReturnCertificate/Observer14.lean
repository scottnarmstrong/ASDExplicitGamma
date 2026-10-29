module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer14Panel0Data : MainPanelData :=
  {
    observer := 14, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2051893456 : ℚ) / 1334479559872725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer14Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49616357957354872253041049345, ellLower := 352620730456453691907720789602,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6189765222786236443817849267, offsetUpper := 6203829769331913746078800614,
    supportELower := 38780161343233098244033918770, supportEUpper := 40308282653062073448213404687,
    supportLambdaLower := 352620730456453691907720789602,
    supportLambdaUpper := 362586019317332959627000315030,
    supportJLower := 42306368647797635163111126666, supportJUpper := 43934142846235403044483407838,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer14Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer14Panel0Data observer14Panel0Endpoints
theorem observer14_panel0_kernel_check : observer14Panel0Check = true := by
  decide +kernel
theorem observer14_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer14Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer14Panel0Data) s observer14Panel0Data.anchor ≤
        (observer14Panel0Endpoints.energyUpper : ℝ) ∧
      (observer14Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer14Panel0Data) s observer14Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer14Panel0Data) s observer14Panel0Data.anchor ≤
        (observer14Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer14Panel0Data) s observer14Panel0Data.anchor ≤
        (observer14Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer14Panel0Data) s observer14Panel0Data.anchor ≤
        (observer14Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer14Panel0Data observer14Panel0Endpoints
    observer14_panel0_kernel_check s hs
def observer14Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer14Panel0Endpoints
theorem observer14_panel0_recurrence_field_kernel_check :
    observer14Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer14_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer14Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer14Panel0Endpoints
    observer14_panel0_recurrence_field_kernel_check

def observer14Panel1Data : MainPanelData :=
  {
    observer := 14, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2051893456 : ℚ) / 1334479559872725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer14Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51340567578163547124675567865, ellLower := 352448458842966401775294855676,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6407995305302804482900524122, offsetUpper := 6422555719953773129937447956,
    supportELower := 40308233350166491706597150853, supportEUpper := 41717202091555311572692130544,
    supportLambdaLower := 352448458842966401775294855676,
    supportLambdaUpper := 362022770226658425822414276712,
    supportJLower := 43832717938596155724350099409, supportJUpper := 45337429793821895830916273312,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer14Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer14Panel1Data observer14Panel1Endpoints
theorem observer14_panel1_kernel_check : observer14Panel1Check = true := by
  decide +kernel
theorem observer14_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer14Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer14Panel1Data) s observer14Panel1Data.anchor ≤
        (observer14Panel1Endpoints.energyUpper : ℝ) ∧
      (observer14Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer14Panel1Data) s observer14Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer14Panel1Data) s observer14Panel1Data.anchor ≤
        (observer14Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer14Panel1Data) s observer14Panel1Data.anchor ≤
        (observer14Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer14Panel1Data) s observer14Panel1Data.anchor ≤
        (observer14Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer14Panel1Data observer14Panel1Endpoints
    observer14_panel1_kernel_check s hs
def observer14Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer14Panel1Endpoints
theorem observer14_panel1_recurrence_field_kernel_check :
    observer14Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer14_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer14Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer14Panel1Endpoints
    observer14_panel1_recurrence_field_kernel_check

def observer14Panel2Data : MainPanelData :=
  {
    observer := 14, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2051893456 : ℚ) / 1334479559872725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer14Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 53045433463975337076356401326, ellLower := 352262834174501199873273557761,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6624274381341990737595962311, offsetUpper := 6639326230970268582409977319,
    supportELower := 41717147941106250248911620358, supportEUpper := 43106545126998063643073289288,
    supportLambdaLower := 352262834174501199873273557761,
    supportLambdaUpper := 361490505293112853112153610534,
    supportJLower := 45239776282851262247644355935, supportJUpper := 46721450179929192174194825394,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer14Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer14Panel2Data observer14Panel2Endpoints
theorem observer14_panel2_kernel_check : observer14Panel2Check = true := by
  decide +kernel
theorem observer14_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer14Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer14Panel2Data) s observer14Panel2Data.anchor ≤
        (observer14Panel2Endpoints.energyUpper : ℝ) ∧
      (observer14Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer14Panel2Data) s observer14Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer14Panel2Data) s observer14Panel2Data.anchor ≤
        (observer14Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer14Panel2Data) s observer14Panel2Data.anchor ≤
        (observer14Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer14Panel2Data) s observer14Panel2Data.anchor ≤
        (observer14Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer14Panel2Data observer14Panel2Endpoints
    observer14_panel2_kernel_check s hs
def observer14Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer14Panel2Endpoints
theorem observer14_panel2_recurrence_field_kernel_check :
    observer14Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer14_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer14Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer14Panel2Endpoints
    observer14_panel2_recurrence_field_kernel_check

def observer14Panel3Data : MainPanelData :=
  {
    observer := 14, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2051893456 : ℚ) / 1334479559872725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer14Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54740195936334774579969823111, ellLower := 352081350398991173110658289703,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6839438700973861505418068484, offsetUpper := 6854979452600763013440039532,
    supportELower := 43106486164649876244964373535, supportEUpper := 44485566470655371361095397465,
    supportLambdaLower := 352081350398991173110658289703,
    supportLambdaUpper := 360987781177860134127539928076,
    supportJLower := 46627299668639787976070956432, supportJUpper := 48095444282433972702370796746,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer14Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer14Panel3Data observer14Panel3Endpoints
theorem observer14_panel3_kernel_check : observer14Panel3Check = true := by
  decide +kernel
theorem observer14_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer14Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer14Panel3Data) s observer14Panel3Data.anchor ≤
        (observer14Panel3Endpoints.energyUpper : ℝ) ∧
      (observer14Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer14Panel3Data) s observer14Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer14Panel3Data) s observer14Panel3Data.anchor ≤
        (observer14Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer14Panel3Data) s observer14Panel3Data.anchor ≤
        (observer14Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer14Panel3Data) s observer14Panel3Data.anchor ≤
        (observer14Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer14Panel3Data observer14Panel3Endpoints
    observer14_panel3_kernel_check s hs
def observer14Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer14Panel3Endpoints
theorem observer14_panel3_recurrence_field_kernel_check :
    observer14Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer14_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer14Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer14Panel3Endpoints
    observer14_panel3_recurrence_field_kernel_check

def observer14Panel4Data : MainPanelData :=
  {
    observer := 14, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2051893456 : ℚ) / 1334479559872725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer14Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56428384198455112502235140389, ellLower := 351905273410837742258334924655,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7037866682516980993838429618, offsetUpper := 7053894742803197564178210525,
    supportELower := 44485502715724478307247961382, supportEUpper := 45857816669525043593007924157,
    supportLambdaLower := 351905273410837742258334924655,
    supportLambdaUpper := 360512459138130385615493403173,
    supportJLower := 48004555449832855729831310628, supportJUpper := 49462941260906347449162858189,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer14Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer14Panel4Data observer14Panel4Endpoints
theorem observer14_panel4_kernel_check : observer14Panel4Check = true := by
  decide +kernel
theorem observer14_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer14Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer14Panel4Data) s observer14Panel4Data.anchor ≤
        (observer14Panel4Endpoints.energyUpper : ℝ) ∧
      (observer14Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer14Panel4Data) s observer14Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer14Panel4Data) s observer14Panel4Data.anchor ≤
        (observer14Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer14Panel4Data) s observer14Panel4Data.anchor ≤
        (observer14Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer14Panel4Data) s observer14Panel4Data.anchor ≤
        (observer14Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer14Panel4Data observer14Panel4Endpoints
    observer14_panel4_kernel_check s hs
def observer14Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer14Panel4Endpoints
theorem observer14_panel4_recurrence_field_kernel_check :
    observer14Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer14_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer14Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer14Panel4Endpoints
    observer14_panel4_recurrence_field_kernel_check

def observer14Panel5Data : MainPanelData :=
  {
    observer := 14, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2051893456 : ℚ) / 1334479559872725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer14Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 58112029281123030736231323517, ellLower := 351734848990100546408691835565,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7251366204622724078204366038, offsetUpper := 7267880489409312323624090079,
    supportELower := 45857748135234249942399299135, supportEUpper := 47225107729750187779035055139,
    supportLambdaLower := 351734848990100546408691835565,
    supportLambdaUpper := 360062401842754738358824482832,
    supportJLower := 49375096625135255406486217490, supportJUpper := 50825731748177735162623299968,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer14Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer14Panel5Data observer14Panel5Endpoints
theorem observer14_panel5_kernel_check : observer14Panel5Check = true := by
  decide +kernel
theorem observer14_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer14Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer14Panel5Data) s observer14Panel5Data.anchor ≤
        (observer14Panel5Endpoints.energyUpper : ℝ) ∧
      (observer14Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer14Panel5Data) s observer14Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer14Panel5Data) s observer14Panel5Data.anchor ≤
        (observer14Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer14Panel5Data) s observer14Panel5Data.anchor ≤
        (observer14Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer14Panel5Data) s observer14Panel5Data.anchor ≤
        (observer14Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer14Panel5Data observer14Panel5Endpoints
    observer14_panel5_kernel_check s hs
def observer14Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer14Panel5Endpoints
theorem observer14_panel5_recurrence_field_kernel_check :
    observer14Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer14_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer14Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer14Panel5Endpoints
    observer14_panel5_recurrence_field_kernel_check

def observer14Panel6Data : MainPanelData :=
  {
    observer := 14, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2051893456 : ℚ) / 1334479559872725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer14Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59791705942516986946752623940, ellLower := 351570028406437864797498541849,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7464458307794560438767426693, offsetUpper := 7481457889224325987455755391,
    supportELower := 47225034426251400042245686395, supportEUpper := 48588515134536320404231521203,
    supportLambdaLower := 351570028406437864797498541849,
    supportLambdaUpper := 359635616897219546082744821496,
    supportJLower := 50740734710315778690220671813, supportJUpper := 52184871303508515865058969418,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer14Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer14Panel6Data observer14Panel6Endpoints
theorem observer14_panel6_kernel_check : observer14Panel6Check = true := by
  decide +kernel
theorem observer14_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer14Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer14Panel6Data) s observer14Panel6Data.anchor ≤
        (observer14Panel6Endpoints.energyUpper : ℝ) ∧
      (observer14Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer14Panel6Data) s observer14Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer14Panel6Data) s observer14Panel6Data.anchor ≤
        (observer14Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer14Panel6Data) s observer14Panel6Data.anchor ≤
        (observer14Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer14Panel6Data) s observer14Panel6Data.anchor ≤
        (observer14Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer14Panel6Data observer14Panel6Endpoints
    observer14_panel6_kernel_check s hs
def observer14Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer14Panel6Endpoints
theorem observer14_panel6_recurrence_field_kernel_check :
    observer14Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer14_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer14Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer14Panel6Endpoints
    observer14_panel6_recurrence_field_kernel_check

def observer14Panel7Data : MainPanelData :=
  {
    observer := 14, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2051893456 : ℚ) / 1334479559872725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer14Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61468339208449518924012204716, ellLower := 351410652168399155045281650295,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7677251242325852456094693753, offsetUpper := 7694735439071168244320490500,
    supportELower := 48588437070156941270578315549, supportEUpper := 49948741555479607546528417336,
    supportLambdaLower := 351410652168399155045281650295,
    supportLambdaUpper := 359230286324668899288946374617,
    supportJLower := 52102543591840932821031132051, supportJUpper := 53541044418726296539417881083,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer14Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer14Panel7Data observer14Panel7Endpoints
theorem observer14_panel7_kernel_check : observer14Panel7Check = true := by
  decide +kernel
theorem observer14_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer14Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer14Panel7Data) s observer14Panel7Data.anchor ≤
        (observer14Panel7Endpoints.energyUpper : ℝ) ∧
      (observer14Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer14Panel7Data) s observer14Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer14Panel7Data) s observer14Panel7Data.anchor ≤
        (observer14Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer14Panel7Data) s observer14Panel7Data.anchor ≤
        (observer14Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer14Panel7Data) s observer14Panel7Data.anchor ≤
        (observer14Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer14Panel7Data observer14Panel7Endpoints
    observer14_panel7_kernel_check s hs
def observer14Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer14Panel7Endpoints
theorem observer14_panel7_recurrence_field_kernel_check :
    observer14Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer14_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer14Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer14Panel7Endpoints
    observer14_panel7_recurrence_field_kernel_check

def observer14InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 14, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer14Panel0Endpoints, observer14Panel1Endpoints, observer14Panel2Endpoints, observer14Panel3Endpoints, observer14Panel4Endpoints, observer14Panel5Endpoints, observer14Panel6Endpoints, observer14Panel7Endpoints]
  }
def observer14FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer14InsertionEndpoints.frameLower
    observer14InsertionEndpoints.frameUpper
theorem observer14_frame_recurrence_field_kernel_check :
    observer14FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer14_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer14InsertionEndpoints.frameLower
      observer14InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer14InsertionEndpoints.frameLower
    observer14InsertionEndpoints.frameUpper
    observer14_frame_recurrence_field_kernel_check
def observer14RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer14Panel0Endpoints ∧
  panelRecurrenceFields observer14Panel1Endpoints ∧
  panelRecurrenceFields observer14Panel2Endpoints ∧
  panelRecurrenceFields observer14Panel3Endpoints ∧
  panelRecurrenceFields observer14Panel4Endpoints ∧
  panelRecurrenceFields observer14Panel5Endpoints ∧
  panelRecurrenceFields observer14Panel6Endpoints ∧
  panelRecurrenceFields observer14Panel7Endpoints ∧ insertionFrameRecurrenceFields observer14InsertionEndpoints.frameLower
      observer14InsertionEndpoints.frameUpper
theorem observer14_all_recurrence_fields :
    observer14RecurrenceFieldBounds := by
  exact ⟨observer14_panel0_recurrence_fields_sound,
    observer14_panel1_recurrence_fields_sound,
    observer14_panel2_recurrence_fields_sound,
    observer14_panel3_recurrence_fields_sound,
    observer14_panel4_recurrence_fields_sound,
    observer14_panel5_recurrence_fields_sound,
    observer14_panel6_recurrence_fields_sound,
    observer14_panel7_recurrence_fields_sound,
    observer14_frame_recurrence_fields_sound⟩
def observer14PanelFormulaBounds : Prop :=
  panelFormulaBounds observer14Panel0Data observer14Panel0Endpoints ∧
  panelFormulaBounds observer14Panel1Data observer14Panel1Endpoints ∧
  panelFormulaBounds observer14Panel2Data observer14Panel2Endpoints ∧
  panelFormulaBounds observer14Panel3Data observer14Panel3Endpoints ∧
  panelFormulaBounds observer14Panel4Data observer14Panel4Endpoints ∧
  panelFormulaBounds observer14Panel5Data observer14Panel5Endpoints ∧
  panelFormulaBounds observer14Panel6Data observer14Panel6Endpoints ∧
  panelFormulaBounds observer14Panel7Data observer14Panel7Endpoints
theorem observer14_all_panel_formula_bounds : observer14PanelFormulaBounds := by
  exact ⟨observer14_panel0_formula_sound,
    observer14_panel1_formula_sound,
    observer14_panel2_formula_sound,
    observer14_panel3_formula_sound,
    observer14_panel4_formula_sound,
    observer14_panel5_formula_sound,
    observer14_panel6_formula_sound,
    observer14_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
