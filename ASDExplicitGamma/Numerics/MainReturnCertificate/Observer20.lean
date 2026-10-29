module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer20Panel0Data : MainPanelData :=
  {
    observer := 20, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1495830507784 : ℚ) / 709197151778320846725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer20Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 49401525036602179688552719562, ellLower := 352042992988705941693649349188,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 6173078312191085494284510827, offsetUpper := 6187104942301757300147933711,
    supportELower := 38573763403510150995613505858, supportEUpper := 40099572020341224477521343918,
    supportLambdaLower := 352042992988705941693649349188,
    supportLambdaUpper := 361999903451069321494120405171,
    supportJLower := 42094193333397210412549999349, supportJUpper := 43719571054851917692462547970,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer20Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer20Panel0Data observer20Panel0Endpoints
theorem observer20_panel0_kernel_check : observer20Panel0Check = true := by
  decide +kernel
theorem observer20_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer20Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer20Panel0Data) s observer20Panel0Data.anchor ≤
        (observer20Panel0Endpoints.energyUpper : ℝ) ∧
      (observer20Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer20Panel0Data) s observer20Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer20Panel0Data) s observer20Panel0Data.anchor ≤
        (observer20Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer20Panel0Data) s observer20Panel0Data.anchor ≤
        (observer20Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer20Panel0Data) s observer20Panel0Data.anchor ≤
        (observer20Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer20Panel0Data observer20Panel0Endpoints
    observer20_panel0_kernel_check s hs
def observer20Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer20Panel0Endpoints
theorem observer20_panel0_recurrence_field_kernel_check :
    observer20Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer20_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer20Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer20Panel0Endpoints
    observer20_panel0_recurrence_field_kernel_check

def observer20Panel1Data : MainPanelData :=
  {
    observer := 20, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1495830507784 : ℚ) / 709197151778320846725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer20Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51123495999041694816289105579, ellLower := 351876137404716698494484934727,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6376757839914552959318505420, offsetUpper := 6391280288789955907521185539,
    supportELower := 40099522930967988440272838180, supportEUpper := 41506195759535692293172002638,
    supportLambdaLower := 351876137404716698494484934727,
    supportLambdaUpper := 361442358453355844182527830293,
    supportJLower := 43618284305015155425217687527, supportJUpper := 45120619344069250734997280941,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer20Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer20Panel1Data observer20Panel1Endpoints
theorem observer20_panel1_kernel_check : observer20Panel1Check = true := by
  decide +kernel
theorem observer20_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer20Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer20Panel1Data) s observer20Panel1Data.anchor ≤
        (observer20Panel1Endpoints.energyUpper : ℝ) ∧
      (observer20Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer20Panel1Data) s observer20Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer20Panel1Data) s observer20Panel1Data.anchor ≤
        (observer20Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer20Panel1Data) s observer20Panel1Data.anchor ≤
        (observer20Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer20Panel1Data) s observer20Panel1Data.anchor ≤
        (observer20Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer20Panel1Data observer20Panel1Endpoints
    observer20_panel1_kernel_check s hs
def observer20Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer20Panel1Endpoints
theorem observer20_panel1_recurrence_field_kernel_check :
    observer20Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer20_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer20Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer20Panel1Endpoints
    observer20_panel1_recurrence_field_kernel_check

def observer20Panel2Data : MainPanelData :=
  {
    observer := 20, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1495830507784 : ℚ) / 709197151778320846725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer20Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 52826137259794493923082532003, ellLower := 351695729813050951128958632308,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6592512414404797463148335074, offsetUpper := 6607526223444147122895427149,
    supportELower := 41506141829648431204891231992, supportEUpper := 42893259306896566138440399098,
    supportLambdaLower := 351695729813050951128958632308,
    supportLambdaUpper := 360915579822099009494802688712,
    supportJLower := 45023099127778940716180818315, supportJUpper := 46502415105117556233388425986,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer20Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer20Panel2Data observer20Panel2Endpoints
theorem observer20_panel2_kernel_check : observer20Panel2Check = true := by
  decide +kernel
theorem observer20_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer20Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer20Panel2Data) s observer20Panel2Data.anchor ≤
        (observer20Panel2Endpoints.energyUpper : ℝ) ∧
      (observer20Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer20Panel2Data) s observer20Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer20Panel2Data) s observer20Panel2Data.anchor ≤
        (observer20Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer20Panel2Data) s observer20Panel2Data.anchor ≤
        (observer20Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer20Panel2Data) s observer20Panel2Data.anchor ≤
        (observer20Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer20Panel2Data observer20Panel2Endpoints
    observer20_panel2_kernel_check s hs
def observer20Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer20Panel2Endpoints
theorem observer20_panel2_recurrence_field_kernel_check :
    observer20Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer20_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer20Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer20Panel2Endpoints
    observer20_panel2_recurrence_field_kernel_check

def observer20Panel3Data : MainPanelData :=
  {
    observer := 20, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1495830507784 : ℚ) / 709197151778320846725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer20Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 54518688751795866085452645109, ellLower := 351519277305756088316490636217,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 6807152047535602325411369430, offsetUpper := 6822654677567850019806344231,
    supportELower := 42893200572068691111444607021, supportEUpper := 44270016835068989508016889928,
    supportLambdaLower := 351519277305756088316490636217,
    supportLambdaUpper := 360418139219528191230419873077,
    supportJLower := 46408393345126251994609513383, supportJUpper := 47874198227264271420321088659,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer20Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer20Panel3Data observer20Panel3Endpoints
theorem observer20_panel3_kernel_check : observer20Panel3Check = true := by
  decide +kernel
theorem observer20_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer20Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer20Panel3Data) s observer20Panel3Data.anchor ≤
        (observer20Panel3Endpoints.energyUpper : ℝ) ∧
      (observer20Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer20Panel3Data) s observer20Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer20Panel3Data) s observer20Panel3Data.anchor ≤
        (observer20Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer20Panel3Data) s observer20Panel3Data.anchor ≤
        (observer20Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer20Panel3Data) s observer20Panel3Data.anchor ≤
        (observer20Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer20Panel3Data observer20Panel3Endpoints
    observer20_panel3_kernel_check s hs
def observer20Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer20Panel3Endpoints
theorem observer20_panel3_recurrence_field_kernel_check :
    observer20Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer20_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer20Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer20Panel3Endpoints
    observer20_panel3_recurrence_field_kernel_check

def observer20Panel4Data : MainPanelData :=
  {
    observer := 20, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1495830507784 : ℚ) / 709197151778320846725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer20Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56204679308007338857044490933, ellLower := 351348057630549653584989169874,
    rhoLower := 99956009678580422823591322424690, rhoUpper := 99956109634640079425512775338690,
    offsetLower := 7021083100335655118805812570, offsetUpper := 7037072937637669783972566617,
    supportELower := 44269953314539573036036328706, supportEUpper := 45640018386142736508016733435,
    supportLambdaLower := 351348057630549653584989169874,
    supportLambdaUpper := 359947911368504450842294521277,
    supportJLower := 47783433890845069571886220404, supportJUpper := 49239497499827781016439678648,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer20Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer20Panel4Data observer20Panel4Endpoints
theorem observer20_panel4_kernel_check : observer20Panel4Check = true := by
  decide +kernel
theorem observer20_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer20Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer20Panel4Data) s observer20Panel4Data.anchor ≤
        (observer20Panel4Endpoints.energyUpper : ℝ) ∧
      (observer20Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer20Panel4Data) s observer20Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer20Panel4Data) s observer20Panel4Data.anchor ≤
        (observer20Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer20Panel4Data) s observer20Panel4Data.anchor ≤
        (observer20Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer20Panel4Data) s observer20Panel4Data.anchor ≤
        (observer20Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer20Panel4Data observer20Panel4Endpoints
    observer20_panel4_kernel_check s hs
def observer20Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer20Panel4Endpoints
theorem observer20_panel4_recurrence_field_kernel_check :
    observer20Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer20_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer20Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer20Panel4Endpoints
    observer20_panel4_recurrence_field_kernel_check

def observer20Panel5Data : MainPanelData :=
  {
    observer := 20, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1495830507784 : ℚ) / 709197151778320846725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer20Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 57886139606159897335008443055, ellLower := 351182327298504925894506583366,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7218067491833838893006621082, offsetUpper := 7234543480971295855172360175,
    supportELower := 45639950093060555368623920850, supportEUpper := 47005075491819389107755080785,
    supportLambdaLower := 351182327298504925894506583366,
    supportLambdaUpper := 359502771076441986611280863543,
    supportJLower := 49151773366045604627568986683, supportJUpper := 50600103202583808973867889421,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer20Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer20Panel5Data observer20Panel5Endpoints
theorem observer20_panel5_kernel_check : observer20Panel5Check = true := by
  decide +kernel
theorem observer20_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer20Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer20Panel5Data) s observer20Panel5Data.anchor ≤
        (observer20Panel5Endpoints.energyUpper : ℝ) ∧
      (observer20Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer20Panel5Data) s observer20Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer20Panel5Data) s observer20Panel5Data.anchor ≤
        (observer20Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer20Panel5Data) s observer20Panel5Data.anchor ≤
        (observer20Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer20Panel5Data) s observer20Panel5Data.anchor ≤
        (observer20Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer20Panel5Data observer20Panel5Endpoints
    observer20_panel5_kernel_check s hs
def observer20Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer20Panel5Endpoints
theorem observer20_panel5_recurrence_field_kernel_check :
    observer20Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer20_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer20Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer20Panel5Endpoints
    observer20_panel5_recurrence_field_kernel_check

def observer20Panel6Data : MainPanelData :=
  {
    observer := 20, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1495830507784 : ℚ) / 709197151778320846725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer20Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 59563644067485312125881528169, ellLower := 351022047329348910883452951904,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7430633964508219244840484322, offsetUpper := 7447595158709044330893695162,
    supportELower := 47005002436265397252059306023, supportEUpper := 48366263188506465839228724508,
    supportLambdaLower := 351022047329348910883452951904,
    supportLambdaUpper := 359080736933958241742661905374,
    supportJLower := 50515222909558886360893835542, supportJUpper := 51957070557846048256655343562,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer20Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer20Panel6Data observer20Panel6Endpoints
theorem observer20_panel6_kernel_check : observer20Panel6Check = true := by
  decide +kernel
theorem observer20_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer20Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer20Panel6Data) s observer20Panel6Data.anchor ≤
        (observer20Panel6Endpoints.energyUpper : ℝ) ∧
      (observer20Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer20Panel6Data) s observer20Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer20Panel6Data) s observer20Panel6Data.anchor ≤
        (observer20Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer20Panel6Data) s observer20Panel6Data.anchor ≤
        (observer20Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer20Panel6Data) s observer20Panel6Data.anchor ≤
        (observer20Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer20Panel6Data observer20Panel6Endpoints
    observer20_panel6_kernel_check s hs
def observer20Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer20Panel6Endpoints
theorem observer20_panel6_recurrence_field_kernel_check :
    observer20Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer20_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer20Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer20Panel6Endpoints
    observer20_panel6_recurrence_field_kernel_check

def observer20Panel7Data : MainPanelData :=
  {
    observer := 20, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((1495830507784 : ℚ) / 709197151778320846725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer20Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61238117395945726387592894137, ellLower := 350867067120104561410002699960,
    rhoLower := 99956109634640079425512775338688, rhoUpper := 99956209590799692137068876661790,
    offsetLower := 7642900889603889402865863438, offsetUpper := 7660346605119605812847583101,
    supportELower := 48366185378739971513760312371, supportEUpper := 49724283726176900831571295034,
    supportLambdaLower := 350867067120104561410002699960,
    supportLambdaUpper := 358680000941481038389474538466,
    supportJLower := 51874856049941017127860339370, supportJUpper := 53311083735591711215466040419,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer20Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer20Panel7Data observer20Panel7Endpoints
theorem observer20_panel7_kernel_check : observer20Panel7Check = true := by
  decide +kernel
theorem observer20_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer20Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer20Panel7Data) s observer20Panel7Data.anchor ≤
        (observer20Panel7Endpoints.energyUpper : ℝ) ∧
      (observer20Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer20Panel7Data) s observer20Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer20Panel7Data) s observer20Panel7Data.anchor ≤
        (observer20Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer20Panel7Data) s observer20Panel7Data.anchor ≤
        (observer20Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer20Panel7Data) s observer20Panel7Data.anchor ≤
        (observer20Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer20Panel7Data observer20Panel7Endpoints
    observer20_panel7_kernel_check s hs
def observer20Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer20Panel7Endpoints
theorem observer20_panel7_recurrence_field_kernel_check :
    observer20Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer20_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer20Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer20Panel7Endpoints
    observer20_panel7_recurrence_field_kernel_check

def observer20InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 20, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer20Panel0Endpoints, observer20Panel1Endpoints, observer20Panel2Endpoints, observer20Panel3Endpoints, observer20Panel4Endpoints, observer20Panel5Endpoints, observer20Panel6Endpoints, observer20Panel7Endpoints]
  }
def observer20FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer20InsertionEndpoints.frameLower
    observer20InsertionEndpoints.frameUpper
theorem observer20_frame_recurrence_field_kernel_check :
    observer20FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer20_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer20InsertionEndpoints.frameLower
      observer20InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer20InsertionEndpoints.frameLower
    observer20InsertionEndpoints.frameUpper
    observer20_frame_recurrence_field_kernel_check
def observer20RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer20Panel0Endpoints ∧
  panelRecurrenceFields observer20Panel1Endpoints ∧
  panelRecurrenceFields observer20Panel2Endpoints ∧
  panelRecurrenceFields observer20Panel3Endpoints ∧
  panelRecurrenceFields observer20Panel4Endpoints ∧
  panelRecurrenceFields observer20Panel5Endpoints ∧
  panelRecurrenceFields observer20Panel6Endpoints ∧
  panelRecurrenceFields observer20Panel7Endpoints ∧ insertionFrameRecurrenceFields observer20InsertionEndpoints.frameLower
      observer20InsertionEndpoints.frameUpper
theorem observer20_all_recurrence_fields :
    observer20RecurrenceFieldBounds := by
  exact ⟨observer20_panel0_recurrence_fields_sound,
    observer20_panel1_recurrence_fields_sound,
    observer20_panel2_recurrence_fields_sound,
    observer20_panel3_recurrence_fields_sound,
    observer20_panel4_recurrence_fields_sound,
    observer20_panel5_recurrence_fields_sound,
    observer20_panel6_recurrence_fields_sound,
    observer20_panel7_recurrence_fields_sound,
    observer20_frame_recurrence_fields_sound⟩
def observer20PanelFormulaBounds : Prop :=
  panelFormulaBounds observer20Panel0Data observer20Panel0Endpoints ∧
  panelFormulaBounds observer20Panel1Data observer20Panel1Endpoints ∧
  panelFormulaBounds observer20Panel2Data observer20Panel2Endpoints ∧
  panelFormulaBounds observer20Panel3Data observer20Panel3Endpoints ∧
  panelFormulaBounds observer20Panel4Data observer20Panel4Endpoints ∧
  panelFormulaBounds observer20Panel5Data observer20Panel5Endpoints ∧
  panelFormulaBounds observer20Panel6Data observer20Panel6Endpoints ∧
  panelFormulaBounds observer20Panel7Data observer20Panel7Endpoints
theorem observer20_all_panel_formula_bounds : observer20PanelFormulaBounds := by
  exact ⟨observer20_panel0_formula_sound,
    observer20_panel1_formula_sound,
    observer20_panel2_formula_sound,
    observer20_panel3_formula_sound,
    observer20_panel4_formula_sound,
    observer20_panel5_formula_sound,
    observer20_panel6_formula_sound,
    observer20_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
