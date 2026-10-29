module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer3Panel0Data : MainPanelData :=
  {
    observer := 3, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((423198987121844722901 : ℚ) / 2500000000000000000000),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer3Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 152162161101426505379505253409, ellLower := 551171903328246011818853984657,
    rhoLower := 99931123730599559387403312154692, rhoUpper := 99931223661773255565483190789931,
    offsetLower := 18987100383801031332599200073, offsetUpper := 19014688407173036971928411885,
    supportELower := 109728568295251981884870669160, supportEUpper := 112051890856723338593005945320,
    supportLambdaLower := 551171903328246011818853984657,
    supportLambdaUpper := 564017706471239356739675703388,
    supportJLower := 115240287328534442003059209006, supportJUpper := 117692067921435732160402702354,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer3Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer3Panel0Data observer3Panel0Endpoints
theorem observer3_panel0_kernel_check : observer3Panel0Check = true := by
  decide +kernel
theorem observer3_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer3Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer3Panel0Data) s observer3Panel0Data.anchor ≤
        (observer3Panel0Endpoints.energyUpper : ℝ) ∧
      (observer3Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer3Panel0Data) s observer3Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer3Panel0Data) s observer3Panel0Data.anchor ≤
        (observer3Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer3Panel0Data) s observer3Panel0Data.anchor ≤
        (observer3Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer3Panel0Data) s observer3Panel0Data.anchor ≤
        (observer3Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer3Panel0Data observer3Panel0Endpoints
    observer3_panel0_kernel_check s hs
def observer3Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer3Panel0Endpoints
theorem observer3_panel0_recurrence_field_kernel_check :
    observer3Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer3_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer3Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer3Panel0Endpoints
    observer3_panel0_recurrence_field_kernel_check

def observer3Panel1Data : MainPanelData :=
  {
    observer := 3, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((423198987121844722901 : ℚ) / 2500000000000000000000),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer3Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 154656126955417842302683222792, ellLower := 549138262404138378774647195589,
    rhoLower := 99931323593046882967224851008333, rhoUpper := 99931423524420441692559566437317,
    offsetLower := 19313482303992070987707797353, offsetUpper := 19341626398574490382684035768,
    supportELower := 112051768155777575332627056158, supportEUpper := 114250170732247942239625067907,
    supportLambdaLower := 549138262404138378774647195589,
    supportLambdaUpper := 561494036995694475875395078354,
    supportJLower := 117543150779818959120373528113, supportJUpper := 119865111102204886998379018691,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer3Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer3Panel1Data observer3Panel1Endpoints
theorem observer3_panel1_kernel_check : observer3Panel1Check = true := by
  decide +kernel
theorem observer3_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer3Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer3Panel1Data) s observer3Panel1Data.anchor ≤
        (observer3Panel1Endpoints.energyUpper : ℝ) ∧
      (observer3Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer3Panel1Data) s observer3Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer3Panel1Data) s observer3Panel1Data.anchor ≤
        (observer3Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer3Panel1Data) s observer3Panel1Data.anchor ≤
        (observer3Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer3Panel1Data) s observer3Panel1Data.anchor ≤
        (observer3Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer3Panel1Data observer3Panel1Endpoints
    observer3_panel1_kernel_check s hs
def observer3Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer3Panel1Endpoints
theorem observer3_panel1_recurrence_field_kernel_check :
    observer3Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer3_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer3Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer3Panel1Endpoints
    observer3_panel1_recurrence_field_kernel_check

def observer3Panel2Data : MainPanelData :=
  {
    observer := 3, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((423198987121844722901 : ℚ) / 2500000000000000000000),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer3Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 157125925995620910090832423649, ellLower := 547159663536955877014105386384,
    rhoLower := 99931623387467353513733757093369, rhoUpper := 99931723319140706809436279232282,
    offsetLower := 19606775533444166180534922899, offsetUpper := 19635472562407208480445240738,
    supportELower := 114250040763302534555577341787, supportEUpper := 116423302388560627373553778526,
    supportLambdaLower := 547159663536955877014105386384,
    supportLambdaUpper := 559076225414283380457215964242,
    supportJLower := 119721637398672093325718395650, supportJUpper := 122014064642703461178125938169,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer3Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer3Panel2Data observer3Panel2Endpoints
theorem observer3_panel2_kernel_check : observer3Panel2Check = true := by
  decide +kernel
theorem observer3_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer3Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer3Panel2Data) s observer3Panel2Data.anchor ≤
        (observer3Panel2Endpoints.energyUpper : ℝ) ∧
      (observer3Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer3Panel2Data) s observer3Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer3Panel2Data) s observer3Panel2Data.anchor ≤
        (observer3Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer3Panel2Data) s observer3Panel2Data.anchor ≤
        (observer3Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer3Panel2Data) s observer3Panel2Data.anchor ≤
        (observer3Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer3Panel2Data observer3Panel2Endpoints
    observer3_panel2_kernel_check s hs
def observer3Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer3Panel2Endpoints
theorem observer3_panel2_recurrence_field_kernel_check :
    observer3Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer3_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer3Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer3Panel2Endpoints
    observer3_panel2_recurrence_field_kernel_check

def observer3Panel3Data : MainPanelData :=
  {
    observer := 3, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((423198987121844722901 : ℚ) / 2500000000000000000000),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer3Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 159580932125137509480528812287, ellLower := 545249080860818632514851560001,
    rhoLower := 99931823250913991828457950405643, rhoUpper := 99931923182787208670730543898488,
    offsetLower := 19924402127883552618388402346, offsetUpper := 19953649717722269784862534721,
    supportELower := 116423165215088819290408104341, supportEUpper := 118580725703860329826987481099,
    supportLambdaLower := 545249080860818632514851560001,
    supportLambdaUpper := 556757669850507376539739527447,
    supportJLower := 121875656023697005615556619941, supportJUpper := 124148302402365403592384876374,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer3Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer3Panel3Data observer3Panel3Endpoints
theorem observer3_panel3_kernel_check : observer3Panel3Check = true := by
  decide +kernel
theorem observer3_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer3Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer3Panel3Data) s observer3Panel3Data.anchor ≤
        (observer3Panel3Endpoints.energyUpper : ℝ) ∧
      (observer3Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer3Panel3Data) s observer3Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer3Panel3Data) s observer3Panel3Data.anchor ≤
        (observer3Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer3Panel3Data) s observer3Panel3Data.anchor ≤
        (observer3Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer3Panel3Data) s observer3Panel3Data.anchor ≤
        (observer3Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer3Panel3Data observer3Panel3Endpoints
    observer3_panel3_kernel_check s hs
def observer3Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer3Panel3Endpoints
theorem observer3_panel3_recurrence_field_kernel_check :
    observer3Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer3_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer3Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer3Panel3Endpoints
    observer3_panel3_recurrence_field_kernel_check

def observer3Panel4Data : MainPanelData :=
  {
    observer := 3, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((423198987121844722901 : ℚ) / 2500000000000000000000),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer3Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 162024801817364748061148059938, ellLower := 543403704407877946512704388803,
    rhoLower := 99932023114760357436185932927661, rhoUpper := 99932123046833438224756090641943,
    offsetLower := 20238636202825416953028615226, offsetUpper := 20268432603189960445624361140,
    supportELower := 118580581371761803501246844914, supportEUpper := 120726164799644128358923664819,
    supportLambdaLower := 543403704407877946512704388803,
    supportLambdaUpper := 554531601130055063860720337076,
    supportJLower := 124014618415840582966373888802, supportJUpper := 126271480810944678997530868190,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer3Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer3Panel4Data observer3Panel4Endpoints
theorem observer3_panel4_kernel_check : observer3Panel4Check = true := by
  decide +kernel
theorem observer3_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer3Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer3Panel4Data) s observer3Panel4Data.anchor ≤
        (observer3Panel4Endpoints.energyUpper : ℝ) ∧
      (observer3Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer3Panel4Data) s observer3Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer3Panel4Data) s observer3Panel4Data.anchor ≤
        (observer3Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer3Panel4Data) s observer3Panel4Data.anchor ≤
        (observer3Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer3Panel4Data) s observer3Panel4Data.anchor ≤
        (observer3Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer3Panel4Data observer3Panel4Endpoints
    observer3_panel4_kernel_check s hs
def observer3Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer3Panel4Endpoints
theorem observer3_panel4_recurrence_field_kernel_check :
    observer3Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer3_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer3Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer3Panel4Endpoints
    observer3_panel4_recurrence_field_kernel_check

def observer3Panel5Data : MainPanelData :=
  {
    observer := 3, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((423198987121844722901 : ℚ) / 2500000000000000000000),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer3Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 164459687461277802715524999295, ellLower := 541620090087945137109393500478,
    rhoLower := 99932222979006451136373090122123, rhoUpper := 99932322911279396270969104381127,
    offsetLower := 20549741530954674650593609142, offsetUpper := 20580085365455317620525342120,
    supportELower := 120726013347583819589111176013, supportEUpper := 122861594780326412813440472087,
    supportLambdaLower := 541620090087945137109393500478,
    supportLambdaUpper := 552391707913479031793159411021,
    supportJLower := 126142214248463270960205111017, supportJUpper := 128385511859461203131372066198,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer3Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer3Panel5Data observer3Panel5Endpoints
theorem observer3_panel5_kernel_check : observer3Panel5Check = true := by
  decide +kernel
theorem observer3_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer3Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer3Panel5Data) s observer3Panel5Data.anchor ≤
        (observer3Panel5Endpoints.energyUpper : ℝ) ∧
      (observer3Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer3Panel5Data) s observer3Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer3Panel5Data) s observer3Panel5Data.anchor ≤
        (observer3Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer3Panel5Data) s observer3Panel5Data.anchor ≤
        (observer3Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer3Panel5Data) s observer3Panel5Data.anchor ≤
        (observer3Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer3Panel5Data observer3Panel5Endpoints
    observer3_panel5_kernel_check s hs
def observer3Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer3Panel5Endpoints
theorem observer3_panel5_recurrence_field_kernel_check :
    observer3Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer3_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer3Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer3Panel5Endpoints
    observer3_panel5_recurrence_field_kernel_check

def observer3Panel6Data : MainPanelData :=
  {
    observer := 3, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((423198987121844722901 : ℚ) / 2500000000000000000000),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer3Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 166886279635021277859932659665, ellLower := 539894836668686772848450889671,
    rhoLower := 99932522776125083608827368948490, rhoUpper := 99932622708697826011954464944210,
    offsetLower := 20826917972925769064518607667, offsetUpper := 20857808016961456098914240040,
    supportELower := 122861436242841096527054772583, supportEUpper := 124988244722071848598362552267,
    supportLambdaLower := 539894836668686772848450889671,
    supportLambdaUpper := 550332220506965416933154332784,
    supportJLower := 128260384609527964255539281479, supportJUpper := 130491566927141502767694095595,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer3Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer3Panel6Data observer3Panel6Endpoints
theorem observer3_panel6_kernel_check : observer3Panel6Check = true := by
  decide +kernel
theorem observer3_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer3Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer3Panel6Data) s observer3Panel6Data.anchor ≤
        (observer3Panel6Endpoints.energyUpper : ℝ) ∧
      (observer3Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer3Panel6Data) s observer3Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer3Panel6Data) s observer3Panel6Data.anchor ≤
        (observer3Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer3Panel6Data) s observer3Panel6Data.anchor ≤
        (observer3Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer3Panel6Data) s observer3Panel6Data.anchor ≤
        (observer3Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer3Panel6Data observer3Panel6Endpoints
    observer3_panel6_kernel_check s hs
def observer3Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer3Panel6Endpoints
theorem observer3_panel6_recurrence_field_kernel_check :
    observer3Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer3_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer3Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer3Panel6Endpoints
    observer3_panel6_recurrence_field_kernel_check

def observer3Panel7Data : MainPanelData :=
  {
    observer := 3, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((423198987121844722901 : ℚ) / 2500000000000000000000),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer3Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 169305613994372539211958435827, ellLower := 538224728472043192310050189635,
    rhoLower := 99932722641370501037790267093655, rhoUpper := 99932822574143108786267448071869,
    offsetLower := 21131536195950117955175116448, offsetUpper := 21162971354034634868999287221,
    supportELower := 124988079130891351790489664376, supportEUpper := 127106962233194068395630656608,
    supportLambdaLower := 538224728472043192310050189635,
    supportLambdaUpper := 548347890258394442118854603743,
    supportJLower := 130370326415611783713590166272, supportJUpper := 132590441135778012816819202646,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer3Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer3Panel7Data observer3Panel7Endpoints
theorem observer3_panel7_kernel_check : observer3Panel7Check = true := by
  decide +kernel
theorem observer3_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer3Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer3Panel7Data) s observer3Panel7Data.anchor ≤
        (observer3Panel7Endpoints.energyUpper : ℝ) ∧
      (observer3Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer3Panel7Data) s observer3Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer3Panel7Data) s observer3Panel7Data.anchor ≤
        (observer3Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer3Panel7Data) s observer3Panel7Data.anchor ≤
        (observer3Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer3Panel7Data) s observer3Panel7Data.anchor ≤
        (observer3Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer3Panel7Data observer3Panel7Endpoints
    observer3_panel7_kernel_check s hs
def observer3Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer3Panel7Endpoints
theorem observer3_panel7_recurrence_field_kernel_check :
    observer3Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer3_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer3Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer3Panel7Endpoints
    observer3_panel7_recurrence_field_kernel_check

def observer3InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 3, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer3Panel0Endpoints, observer3Panel1Endpoints, observer3Panel2Endpoints, observer3Panel3Endpoints, observer3Panel4Endpoints, observer3Panel5Endpoints, observer3Panel6Endpoints, observer3Panel7Endpoints]
  }
def observer3FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer3InsertionEndpoints.frameLower
    observer3InsertionEndpoints.frameUpper
theorem observer3_frame_recurrence_field_kernel_check :
    observer3FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer3_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer3InsertionEndpoints.frameLower
      observer3InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer3InsertionEndpoints.frameLower
    observer3InsertionEndpoints.frameUpper
    observer3_frame_recurrence_field_kernel_check
def observer3RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer3Panel0Endpoints ∧
  panelRecurrenceFields observer3Panel1Endpoints ∧
  panelRecurrenceFields observer3Panel2Endpoints ∧
  panelRecurrenceFields observer3Panel3Endpoints ∧
  panelRecurrenceFields observer3Panel4Endpoints ∧
  panelRecurrenceFields observer3Panel5Endpoints ∧
  panelRecurrenceFields observer3Panel6Endpoints ∧
  panelRecurrenceFields observer3Panel7Endpoints ∧ insertionFrameRecurrenceFields observer3InsertionEndpoints.frameLower
      observer3InsertionEndpoints.frameUpper
theorem observer3_all_recurrence_fields :
    observer3RecurrenceFieldBounds := by
  exact ⟨observer3_panel0_recurrence_fields_sound,
    observer3_panel1_recurrence_fields_sound,
    observer3_panel2_recurrence_fields_sound,
    observer3_panel3_recurrence_fields_sound,
    observer3_panel4_recurrence_fields_sound,
    observer3_panel5_recurrence_fields_sound,
    observer3_panel6_recurrence_fields_sound,
    observer3_panel7_recurrence_fields_sound,
    observer3_frame_recurrence_fields_sound⟩
def observer3PanelFormulaBounds : Prop :=
  panelFormulaBounds observer3Panel0Data observer3Panel0Endpoints ∧
  panelFormulaBounds observer3Panel1Data observer3Panel1Endpoints ∧
  panelFormulaBounds observer3Panel2Data observer3Panel2Endpoints ∧
  panelFormulaBounds observer3Panel3Data observer3Panel3Endpoints ∧
  panelFormulaBounds observer3Panel4Data observer3Panel4Endpoints ∧
  panelFormulaBounds observer3Panel5Data observer3Panel5Endpoints ∧
  panelFormulaBounds observer3Panel6Data observer3Panel6Endpoints ∧
  panelFormulaBounds observer3Panel7Data observer3Panel7Endpoints
theorem observer3_all_panel_formula_bounds : observer3PanelFormulaBounds := by
  exact ⟨observer3_panel0_formula_sound,
    observer3_panel1_formula_sound,
    observer3_panel2_formula_sound,
    observer3_panel3_formula_sound,
    observer3_panel4_formula_sound,
    observer3_panel5_formula_sound,
    observer3_panel6_formula_sound,
    observer3_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
