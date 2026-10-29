module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer4Panel0Data : MainPanelData :=
  {
    observer := 4, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((144329642328994216417 : ℚ) / 2500000000000000000000),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer4Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 102405032670710898925945088549, ellLower := 468308362678154850496228452885,
    rhoLower := 99941417166446657012474360039547, rhoUpper := 99941517107913794184371502867716,
    offsetLower := 12788459382864939469277784515, offsetUpper := 12810313592661262366033627485,
    supportELower := 80114167002309468685755958232, supportEUpper := 82105527278473858992974470484,
    supportLambdaLower := 468308362678154850496228452885,
    supportLambdaUpper := 479951814431960134596079675608,
    supportJLower := 84797250629091017190718242760, supportJUpper := 86905045422793460338935267241,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer4Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer4Panel0Data observer4Panel0Endpoints
theorem observer4_panel0_kernel_check : observer4Panel0Check = true := by
  decide +kernel
theorem observer4_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer4Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer4Panel0Data) s observer4Panel0Data.anchor ≤
        (observer4Panel0Endpoints.energyUpper : ℝ) ∧
      (observer4Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer4Panel0Data) s observer4Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer4Panel0Data) s observer4Panel0Data.anchor ≤
        (observer4Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer4Panel0Data) s observer4Panel0Data.anchor ≤
        (observer4Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer4Panel0Data) s observer4Panel0Data.anchor ≤
        (observer4Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer4Panel0Data observer4Panel0Endpoints
    observer4_panel0_kernel_check s hs
def observer4Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer4Panel0Endpoints
theorem observer4_panel0_recurrence_field_kernel_check :
    observer4Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer4_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer4Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer4Panel0Endpoints
    observer4_panel0_recurrence_field_kernel_check

def observer4Panel1Data : MainPanelData :=
  {
    observer := 4, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((144329642328994216417 : ℚ) / 2500000000000000000000),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer4Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 104577655851548697467927714850, ellLower := 467051554677164526484300669512,
    rhoLower := 99941617049480872873376567818525, rhoUpper := 99941716991147893179431121970680,
    offsetLower := 13050166262569128973261641429, offsetUpper := 13072544231669572377614190336,
    supportELower := 82105435214546600334829227116, supportEUpper := 83974282679088969679593733215,
    supportLambdaLower := 467051554677164526484300669512,
    supportLambdaUpper := 478246325132010711612250728040,
    supportJLower := 86775950761318245599672233811, supportJUpper := 88756745930409076795716240496,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer4Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer4Panel1Data observer4Panel1Endpoints
theorem observer4_panel1_kernel_check : observer4Panel1Check = true := by
  decide +kernel
theorem observer4_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer4Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer4Panel1Data) s observer4Panel1Data.anchor ≤
        (observer4Panel1Endpoints.energyUpper : ℝ) ∧
      (observer4Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer4Panel1Data) s observer4Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer4Panel1Data) s observer4Panel1Data.anchor ≤
        (observer4Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer4Panel1Data) s observer4Panel1Data.anchor ≤
        (observer4Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer4Panel1Data) s observer4Panel1Data.anchor ≤
        (observer4Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer4Panel1Data observer4Panel1Endpoints
    observer4_panel1_kernel_check s hs
def observer4Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer4Panel1Endpoints
theorem observer4_panel1_recurrence_field_kernel_check :
    observer4Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer4_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer4Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer4Panel1Endpoints
    observer4_panel1_recurrence_field_kernel_check

def observer4Panel2Data : MainPanelData :=
  {
    observer := 4, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((144329642328994216417 : ℚ) / 2500000000000000000000),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer4Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 106728125222389808331945845181, ellLower := 465821240961137424673188542168,
    rhoLower := 99941716991147893179431121970678, rhoUpper := 99941816932914855202476832344489,
    offsetLower := 13330799722385587691052228277, offsetUpper := 13353698200345203942426803999,
    supportELower := 83974184357593338802849754504, supportEUpper := 85820215387999782280929089657,
    supportLambdaLower := 465821240961137424673188542168,
    supportLambdaUpper := 476615441354591177040299979093,
    supportJLower := 88632396767204713049581639925, supportJUpper := 90586369801545694051332089448,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer4Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer4Panel2Data observer4Panel2Endpoints
theorem observer4_panel2_kernel_check : observer4Panel2Check = true := by
  decide +kernel
theorem observer4_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer4Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer4Panel2Data) s observer4Panel2Data.anchor ≤
        (observer4Panel2Endpoints.energyUpper : ℝ) ∧
      (observer4Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer4Panel2Data) s observer4Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer4Panel2Data) s observer4Panel2Data.anchor ≤
        (observer4Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer4Panel2Data) s observer4Panel2Data.anchor ≤
        (observer4Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer4Panel2Data) s observer4Panel2Data.anchor ≤
        (observer4Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer4Panel2Data observer4Panel2Endpoints
    observer4_panel2_kernel_check s hs
def observer4Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer4Panel2Endpoints
theorem observer4_panel2_recurrence_field_kernel_check :
    observer4Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer4_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer4Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer4Panel2Endpoints
    observer4_panel2_recurrence_field_kernel_check

def observer4Panel3Data : MainPanelData :=
  {
    observer := 4, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((144329642328994216417 : ℚ) / 2500000000000000000000),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer4Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 108865758930115881425556160969, ellLower := 464632282419897657061987711938,
    rhoLower := 99941916874781759042455465901983, rhoUpper := 99942016816748604799308889547016,
    offsetLower := 13585761232454557188128405860, offsetUpper := 13609178154784975651591217397,
    supportELower := 85820110860798337242567571219, supportEUpper := 87652687993013860104171593870,
    supportLambdaLower := 464632282419897657061987711938,
    supportLambdaUpper := 475054714640325006533336093284,
    supportJLower := 90466433684997313813187448338, supportJUpper := 92403235139417110169504954803,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer4Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer4Panel3Data observer4Panel3Endpoints
theorem observer4_panel3_kernel_check : observer4Panel3Check = true := by
  decide +kernel
theorem observer4_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer4Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer4Panel3Data) s observer4Panel3Data.anchor ≤
        (observer4Panel3Endpoints.energyUpper : ℝ) ∧
      (observer4Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer4Panel3Data) s observer4Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer4Panel3Data) s observer4Panel3Data.anchor ≤
        (observer4Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer4Panel3Data) s observer4Panel3Data.anchor ≤
        (observer4Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer4Panel3Data) s observer4Panel3Data.anchor ≤
        (observer4Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer4Panel3Data observer4Panel3Endpoints
    observer4_panel3_kernel_check s hs
def observer4Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer4Panel3Endpoints
theorem observer4_panel3_recurrence_field_kernel_check :
    observer4Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer4_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer4Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer4Panel3Endpoints
    observer4_panel3_recurrence_field_kernel_check

def observer4Panel4Data : MainPanelData :=
  {
    observer := 4, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((144329642328994216417 : ℚ) / 2500000000000000000000),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer4Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 110994160326415568443296475747, ellLower := 463483570501901726850030330450,
    rhoLower := 99942016816748604799308889547014, rhoUpper := 99942116758815392572979070125348,
    offsetLower := 13861768056416006379371105954, offsetUpper := 13885701991706059918661279169,
    supportELower := 87652577294911347245866731445, supportEUpper := 89475352164495214914492852748,
    supportLambdaLower := 463483570501901726850030330450,
    supportLambdaUpper := 473559308757361909727916099779,
    supportJLower := 92287412999930364514367034749, supportJUpper := 94210945252068834011772013746,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer4Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer4Panel4Data observer4Panel4Endpoints
theorem observer4_panel4_kernel_check : observer4Panel4Check = true := by
  decide +kernel
theorem observer4_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer4Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer4Panel4Data) s observer4Panel4Data.anchor ≤
        (observer4Panel4Endpoints.energyUpper : ℝ) ∧
      (observer4Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer4Panel4Data) s observer4Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer4Panel4Data) s observer4Panel4Data.anchor ≤
        (observer4Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer4Panel4Data) s observer4Panel4Data.anchor ≤
        (observer4Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer4Panel4Data) s observer4Panel4Data.anchor ≤
        (observer4Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer4Panel4Data observer4Panel4Endpoints
    observer4_panel4_kernel_check s hs
def observer4Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer4Panel4Endpoints
theorem observer4_panel4_recurrence_field_kernel_check :
    observer4Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer4_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer4Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer4Panel4Endpoints
    observer4_panel4_recurrence_field_kernel_check

def observer4Panel5Data : MainPanelData :=
  {
    observer := 4, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((144329642328994216417 : ℚ) / 2500000000000000000000),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer4Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 113115431146348858068449570064, ellLower := 462373201392012507532765792542,
    rhoLower := 99942216700982122463408074424761, rhoUpper := 99942316643248794570538069175160,
    offsetLower := 14111712679795400685499045478, offsetUpper := 14136162653432116873151377800,
    supportELower := 89475235323537937353886842803, supportEUpper := 91290114928986119410247934213,
    supportLambdaLower := 462373201392012507532765792542,
    supportLambdaUpper := 472124654761947370614143250086,
    supportJLower := 94098967337458062429214500728, supportJUpper := 96011361476605593116389366714,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer4Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer4Panel5Data observer4Panel5Endpoints
theorem observer4_panel5_kernel_check : observer4Panel5Check = true := by
  decide +kernel
theorem observer4_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer4Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer4Panel5Data) s observer4Panel5Data.anchor ≤
        (observer4Panel5Endpoints.energyUpper : ℝ) ∧
      (observer4Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer4Panel5Data) s observer4Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer4Panel5Data) s observer4Panel5Data.anchor ≤
        (observer4Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer4Panel5Data) s observer4Panel5Data.anchor ≤
        (observer4Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer4Panel5Data) s observer4Panel5Data.anchor ≤
        (observer4Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer4Panel5Data observer4Panel5Endpoints
    observer4_panel5_kernel_check s hs
def observer4Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer4Panel5Endpoints
theorem observer4_panel5_recurrence_field_kernel_check :
    observer4Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer4_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer4Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer4Panel5Endpoints
    observer4_panel5_recurrence_field_kernel_check

def observer4Panel6Data : MainPanelData :=
  {
    observer := 4, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((144329642328994216417 : ℚ) / 2500000000000000000000),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer4Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 115230213625908786168332981934, ellLower := 461299173291995531989117160346,
    rhoLower := 99942316643248794570538069175158, rhoUpper := 99942416585615408994311321048653,
    offsetLower := 14384047327666839222101641927, offsetUpper := 14409012428239367774663483204,
    supportELower := 91289991969533512884490417035, supportEUpper := 93098141252702389792659913572,
    supportLambdaLower := 461299173291995531989117160346,
    supportLambdaUpper := 470746559739995591552723403819,
    supportJLower := 95902983702453468204381588638, supportJUpper := 97805606850102345708187147611,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer4Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer4Panel6Data observer4Panel6Endpoints
theorem observer4_panel6_kernel_check : observer4Panel6Check = true := by
  decide +kernel
theorem observer4_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer4Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer4Panel6Data) s observer4Panel6Data.anchor ≤
        (observer4Panel6Endpoints.energyUpper : ℝ) ∧
      (observer4Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer4Panel6Data) s observer4Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer4Panel6Data) s observer4Panel6Data.anchor ≤
        (observer4Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer4Panel6Data) s observer4Panel6Data.anchor ≤
        (observer4Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer4Panel6Data) s observer4Panel6Data.anchor ≤
        (observer4Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer4Panel6Data observer4Panel6Endpoints
    observer4_panel6_kernel_check s hs
def observer4Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer4Panel6Endpoints
theorem observer4_panel6_recurrence_field_kernel_check :
    observer4Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer4_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer4Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer4Panel6Endpoints
    observer4_panel6_recurrence_field_kernel_check

def observer4Panel7Data : MainPanelData :=
  {
    observer := 4, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((144329642328994216417 : ℚ) / 2500000000000000000000),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer4Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 117339497245121898377785461688, ellLower := 460259546256300551675852048840,
    rhoLower := 99942416585615408994311321048651, rhoUpper := 99942516528081965834670196659675,
    offsetLower := 14654952297306919065890616620, offsetUpper := 14680431831353751498385320582,
    supportELower := 93098012196717004247839174750, supportEUpper := 94900218247465189996633169568,
    supportLambdaLower := 460259546256300551675852048840,
    supportLambdaUpper := 469421207113551661810578868587,
    supportJLower := 97700607659280009764597695238, supportJUpper := 99594430318600706614738958254,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer4Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer4Panel7Data observer4Panel7Endpoints
theorem observer4_panel7_kernel_check : observer4Panel7Check = true := by
  decide +kernel
theorem observer4_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer4Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer4Panel7Data) s observer4Panel7Data.anchor ≤
        (observer4Panel7Endpoints.energyUpper : ℝ) ∧
      (observer4Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer4Panel7Data) s observer4Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer4Panel7Data) s observer4Panel7Data.anchor ≤
        (observer4Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer4Panel7Data) s observer4Panel7Data.anchor ≤
        (observer4Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer4Panel7Data) s observer4Panel7Data.anchor ≤
        (observer4Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer4Panel7Data observer4Panel7Endpoints
    observer4_panel7_kernel_check s hs
def observer4Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer4Panel7Endpoints
theorem observer4_panel7_recurrence_field_kernel_check :
    observer4Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer4_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer4Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer4Panel7Endpoints
    observer4_panel7_recurrence_field_kernel_check

def observer4InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 4, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer4Panel0Endpoints, observer4Panel1Endpoints, observer4Panel2Endpoints, observer4Panel3Endpoints, observer4Panel4Endpoints, observer4Panel5Endpoints, observer4Panel6Endpoints, observer4Panel7Endpoints]
  }
def observer4FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer4InsertionEndpoints.frameLower
    observer4InsertionEndpoints.frameUpper
theorem observer4_frame_recurrence_field_kernel_check :
    observer4FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer4_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer4InsertionEndpoints.frameLower
      observer4InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer4InsertionEndpoints.frameLower
    observer4InsertionEndpoints.frameUpper
    observer4_frame_recurrence_field_kernel_check
def observer4RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer4Panel0Endpoints ∧
  panelRecurrenceFields observer4Panel1Endpoints ∧
  panelRecurrenceFields observer4Panel2Endpoints ∧
  panelRecurrenceFields observer4Panel3Endpoints ∧
  panelRecurrenceFields observer4Panel4Endpoints ∧
  panelRecurrenceFields observer4Panel5Endpoints ∧
  panelRecurrenceFields observer4Panel6Endpoints ∧
  panelRecurrenceFields observer4Panel7Endpoints ∧ insertionFrameRecurrenceFields observer4InsertionEndpoints.frameLower
      observer4InsertionEndpoints.frameUpper
theorem observer4_all_recurrence_fields :
    observer4RecurrenceFieldBounds := by
  exact ⟨observer4_panel0_recurrence_fields_sound,
    observer4_panel1_recurrence_fields_sound,
    observer4_panel2_recurrence_fields_sound,
    observer4_panel3_recurrence_fields_sound,
    observer4_panel4_recurrence_fields_sound,
    observer4_panel5_recurrence_fields_sound,
    observer4_panel6_recurrence_fields_sound,
    observer4_panel7_recurrence_fields_sound,
    observer4_frame_recurrence_fields_sound⟩
def observer4PanelFormulaBounds : Prop :=
  panelFormulaBounds observer4Panel0Data observer4Panel0Endpoints ∧
  panelFormulaBounds observer4Panel1Data observer4Panel1Endpoints ∧
  panelFormulaBounds observer4Panel2Data observer4Panel2Endpoints ∧
  panelFormulaBounds observer4Panel3Data observer4Panel3Endpoints ∧
  panelFormulaBounds observer4Panel4Data observer4Panel4Endpoints ∧
  panelFormulaBounds observer4Panel5Data observer4Panel5Endpoints ∧
  panelFormulaBounds observer4Panel6Data observer4Panel6Endpoints ∧
  panelFormulaBounds observer4Panel7Data observer4Panel7Endpoints
theorem observer4_all_panel_formula_bounds : observer4PanelFormulaBounds := by
  exact ⟨observer4_panel0_formula_sound,
    observer4_panel1_formula_sound,
    observer4_panel2_formula_sound,
    observer4_panel3_formula_sound,
    observer4_panel4_formula_sound,
    observer4_panel5_formula_sound,
    observer4_panel6_formula_sound,
    observer4_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
