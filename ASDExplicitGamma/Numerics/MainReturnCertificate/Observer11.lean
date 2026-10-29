module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer11Panel0Data : MainPanelData :=
  {
    observer := 11, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((75995818 : ℚ) / 1830561810525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer11Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 50558218174823219987570716627, ellLower := 355138532555480999347478778129,
    rhoLower := 99955609855341355513132301067048, rhoUpper := 99955709811001188676074757351148,
    offsetLower := 6305238190553814924533697346, offsetUpper := 6319468074372079499379307389,
    supportELower := 39679600684514523718449735769, supportEUpper := 41217801009096443337426450655,
    supportLambdaLower := 355138532555480999347478778129,
    supportLambdaUpper := 365140338687587261208102857897,
    supportJLower := 43230986010069333711924523550, supportJUpper := 44869204395972315949507479234,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer11Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer11Panel0Data observer11Panel0Endpoints
theorem observer11_panel0_kernel_check : observer11Panel0Check = true := by
  decide +kernel
theorem observer11_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer11Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer11Panel0Data) s observer11Panel0Data.anchor ≤
        (observer11Panel0Endpoints.energyUpper : ℝ) ∧
      (observer11Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer11Panel0Data) s observer11Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer11Panel0Data) s observer11Panel0Data.anchor ≤
        (observer11Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer11Panel0Data) s observer11Panel0Data.anchor ≤
        (observer11Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer11Panel0Data) s observer11Panel0Data.anchor ≤
        (observer11Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer11Panel0Data observer11Panel0Endpoints
    observer11_panel0_kernel_check s hs
def observer11Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer11Panel0Endpoints
theorem observer11_panel0_recurrence_field_kernel_check :
    observer11Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer11_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer11Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer11Panel0Endpoints
    observer11_panel0_recurrence_field_kernel_check

def observer11Panel1Data : MainPanelData :=
  {
    observer := 11, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((75995818 : ℚ) / 1830561810525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer11Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 52292184164417442240626196016, ellLower := 354942657532735251564053565802,
    rhoLower := 99955609855341355513132301067048, rhoUpper := 99955709811001188676074757351148,
    offsetLower := 6525084180926032682847170344, offsetUpper := 6539810220925295265683470104,
    supportELower := 41217750775712614122090652315, supportEUpper := 42636725406217288363281053772,
    supportLambdaLower := 354942657532735251564053565802,
    supportLambdaUpper := 364552230612706775408025180455,
    supportJLower := 44767177351039966637731187973, supportJUpper := 46282247712344356117361305577,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer11Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer11Panel1Data observer11Panel1Endpoints
theorem observer11_panel1_kernel_check : observer11Panel1Check = true := by
  decide +kernel
theorem observer11_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer11Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer11Panel1Data) s observer11Panel1Data.anchor ≤
        (observer11Panel1Endpoints.energyUpper : ℝ) ∧
      (observer11Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer11Panel1Data) s observer11Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer11Panel1Data) s observer11Panel1Data.anchor ≤
        (observer11Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer11Panel1Data) s observer11Panel1Data.anchor ≤
        (observer11Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer11Panel1Data) s observer11Panel1Data.anchor ≤
        (observer11Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer11Panel1Data observer11Panel1Endpoints
    observer11_panel1_kernel_check s hs
def observer11Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer11Panel1Endpoints
theorem observer11_panel1_recurrence_field_kernel_check :
    observer11Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer11_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer11Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer11Panel1Endpoints
    observer11_panel1_recurrence_field_kernel_check

def observer11Panel2Data : MainPanelData :=
  {
    observer := 11, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((75995818 : ℚ) / 1830561810525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer11Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 54006745265336513170586386902, ellLower := 354734296572180393594277394201,
    rhoLower := 99955609855341355513132301067048, rhoUpper := 99955709811001188676074757351148,
    offsetLower := 6742987577254744787909926475, offsetUpper := 6758205389320288419843322905,
    supportELower := 42636670294601274901713119729, supportEUpper := 44036002754311041542670658163,
    supportLambdaLower := 354734296572180393594277394201,
    supportLambdaUpper := 363996055924789189624855692007,
    supportJLower := 46184013260323078837655893671, supportJUpper := 47675963313558933438919215084,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer11Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer11Panel2Data observer11Panel2Endpoints
theorem observer11_panel2_kernel_check : observer11Panel2Check = true := by
  decide +kernel
theorem observer11_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer11Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer11Panel2Data) s observer11Panel2Data.anchor ≤
        (observer11Panel2Endpoints.energyUpper : ℝ) ∧
      (observer11Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer11Panel2Data) s observer11Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer11Panel2Data) s observer11Panel2Data.anchor ≤
        (observer11Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer11Panel2Data) s observer11Panel2Data.anchor ≤
        (observer11Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer11Panel2Data) s observer11Panel2Data.anchor ≤
        (observer11Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer11Panel2Data observer11Panel2Endpoints
    observer11_panel2_kernel_check s hs
def observer11Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer11Panel2Endpoints
theorem observer11_panel2_recurrence_field_kernel_check :
    observer11Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer11_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer11Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer11Panel2Endpoints
    observer11_panel2_recurrence_field_kernel_check

def observer11Panel3Data : MainPanelData :=
  {
    observer := 11, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((75995818 : ℚ) / 1830561810525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer11Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 55711143492679355934941299820, ellLower := 354530886330165325738902767931,
    rhoLower := 99955609855341355513132301067048, rhoUpper := 99955709811001188676074757351148,
    offsetLower := 6959780289305423621399180622, offsetUpper := 6975487366805816223523031649,
    supportELower := 44035942800469926873450287675, supportEUpper := 45424890112058748008232295951,
    supportLambdaLower := 354530886330165325738902767931,
    supportLambdaUpper := 363470305898837121960438161783,
    supportJLower := 47581251663771580130839315354, supportJUpper := 49059593171047119227836677569,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer11Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer11Panel3Data observer11Panel3Endpoints
theorem observer11_panel3_kernel_check : observer11Panel3Check = true := by
  decide +kernel
theorem observer11_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer11Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer11Panel3Data) s observer11Panel3Data.anchor ≤
        (observer11Panel3Endpoints.energyUpper : ℝ) ∧
      (observer11Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer11Panel3Data) s observer11Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer11Panel3Data) s observer11Panel3Data.anchor ≤
        (observer11Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer11Panel3Data) s observer11Panel3Data.anchor ≤
        (observer11Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer11Panel3Data) s observer11Panel3Data.anchor ≤
        (observer11Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer11Panel3Data observer11Panel3Endpoints
    observer11_panel3_kernel_check s hs
def observer11Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer11Panel3Endpoints
theorem observer11_panel3_recurrence_field_kernel_check :
    observer11Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer11_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer11Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer11Panel3Endpoints
    observer11_panel3_recurrence_field_kernel_check

def observer11Panel4Data : MainPanelData :=
  {
    observer := 11, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((75995818 : ℚ) / 1830561810525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer11Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 57408909663206970178162005969, ellLower := 354333641036057757235619162764,
    rhoLower := 99955709811001188676074757351146, rhoUpper := 99955809766760977548828223153566,
    offsetLower := 7159673297170572874169023561, offsetUpper := 7175868065376204991096036973,
    supportELower := 45424825335646016986092592883, supportEUpper := 46806940226937906259056748067,
    supportLambdaLower := 354333641036057757235619162764,
    supportLambdaUpper := 362972783098886403652737981572,
    supportJLower := 48968161746006594558448784510, supportJUpper := 50436668057926770295584127883,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer11Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer11Panel4Data observer11Panel4Endpoints
theorem observer11_panel4_kernel_check : observer11Panel4Check = true := by
  decide +kernel
theorem observer11_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer11Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer11Panel4Data) s observer11Panel4Data.anchor ≤
        (observer11Panel4Endpoints.energyUpper : ℝ) ∧
      (observer11Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer11Panel4Data) s observer11Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer11Panel4Data) s observer11Panel4Data.anchor ≤
        (observer11Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer11Panel4Data) s observer11Panel4Data.anchor ≤
        (observer11Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer11Panel4Data) s observer11Panel4Data.anchor ≤
        (observer11Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer11Panel4Data observer11Panel4Endpoints
    observer11_panel4_kernel_check s hs
def observer11Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer11Panel4Endpoints
theorem observer11_panel4_recurrence_field_kernel_check :
    observer11Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer11_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer11Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer11Panel4Endpoints
    observer11_panel4_recurrence_field_kernel_check

def observer11Panel5Data : MainPanelData :=
  {
    observer := 11, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((75995818 : ℚ) / 1830561810525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer11Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 59102076346309424484086489553, ellLower := 354142759696938771510893649690,
    rhoLower := 99955709811001188676074757351146, rhoUpper := 99955809766760977548828223153566,
    offsetLower := 7374807100077221443983903865, offsetUpper := 7391488488541440803309192985,
    supportELower := 46806870641498961116592038367, supportEUpper := 48183967172781191973282404185,
    supportLambdaLower := 354142759696938771510893649690,
    supportLambdaUpper := 362501297285150210769046593299,
    supportJLower := 50348298238468348831700974863, supportJUpper := 51808980145632694080972870118,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer11Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer11Panel5Data observer11Panel5Endpoints
theorem observer11_panel5_kernel_check : observer11Panel5Check = true := by
  decide +kernel
theorem observer11_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer11Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer11Panel5Data) s observer11Panel5Data.anchor ≤
        (observer11Panel5Endpoints.energyUpper : ℝ) ∧
      (observer11Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer11Panel5Data) s observer11Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer11Panel5Data) s observer11Panel5Data.anchor ≤
        (observer11Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer11Panel5Data) s observer11Panel5Data.anchor ≤
        (observer11Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer11Panel5Data) s observer11Panel5Data.anchor ≤
        (observer11Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer11Panel5Data observer11Panel5Endpoints
    observer11_panel5_kernel_check s hs
def observer11Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer11Panel5Endpoints
theorem observer11_panel5_recurrence_field_kernel_check :
    observer11Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer11_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer11Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer11Panel5Endpoints
    observer11_panel5_recurrence_field_kernel_check

def observer11Panel6Data : MainPanelData :=
  {
    observer := 11, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((75995818 : ℚ) / 1830561810525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer11Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 60791219768561942131054103018, ellLower := 353958151085349385633869638619,
    rhoLower := 99955709811001188676074757351146, rhoUpper := 99955809766760977548828223153566,
    offsetLower := 7589536142112072479247228809, offsetUpper := 7606703235289123653677770704,
    supportELower := 48183892788777132251793634034, supportEUpper := 49557048379998593412666970022,
    supportLambdaLower := 353958151085349385633869638619,
    supportLambdaUpper := 362053808182344280718788258726,
    supportJLower := 51723474299630626108132330420, supportJUpper := 53177586461822036219854852610,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer11Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer11Panel6Data observer11Panel6Endpoints
theorem observer11_panel6_kernel_check : observer11Panel6Check = true := by
  decide +kernel
theorem observer11_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer11Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer11Panel6Data) s observer11Panel6Data.anchor ≤
        (observer11Panel6Endpoints.energyUpper : ℝ) ∧
      (observer11Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer11Panel6Data) s observer11Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer11Panel6Data) s observer11Panel6Data.anchor ≤
        (observer11Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer11Panel6Data) s observer11Panel6Data.anchor ≤
        (observer11Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer11Panel6Data) s observer11Panel6Data.anchor ≤
        (observer11Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer11Panel6Data observer11Panel6Endpoints
    observer11_panel6_kernel_check s hs
def observer11Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer11Panel6Endpoints
theorem observer11_panel6_recurrence_field_kernel_check :
    observer11Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer11_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer11Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer11Panel6Endpoints
    observer11_panel6_recurrence_field_kernel_check

def observer11Panel7Data : MainPanelData :=
  {
    observer := 11, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((75995818 : ℚ) / 1830561810525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer11Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 62477266358381068280619068240, ellLower := 353779616968326465774947205905,
    rhoLower := 99955709811001188676074757351146, rhoUpper := 99955809766760977548828223153566,
    offsetLower := 7803968459722114289308934449, offsetUpper := 7821620586438456073556124758,
    supportELower := 49556969206053559101976507275, supportEUpper := 50926888357666600095784049892,
    supportLambdaLower := 353779616968326465774947205905,
    supportLambdaUpper := 361628454325981097073509882865,
    supportJLower := 53094765375736823759725979334, supportJUpper := 54543172900926411066519148721,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer11Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer11Panel7Data observer11Panel7Endpoints
theorem observer11_panel7_kernel_check : observer11Panel7Check = true := by
  decide +kernel
theorem observer11_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer11Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer11Panel7Data) s observer11Panel7Data.anchor ≤
        (observer11Panel7Endpoints.energyUpper : ℝ) ∧
      (observer11Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer11Panel7Data) s observer11Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer11Panel7Data) s observer11Panel7Data.anchor ≤
        (observer11Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer11Panel7Data) s observer11Panel7Data.anchor ≤
        (observer11Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer11Panel7Data) s observer11Panel7Data.anchor ≤
        (observer11Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer11Panel7Data observer11Panel7Endpoints
    observer11_panel7_kernel_check s hs
def observer11Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer11Panel7Endpoints
theorem observer11_panel7_recurrence_field_kernel_check :
    observer11Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer11_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer11Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer11Panel7Endpoints
    observer11_panel7_recurrence_field_kernel_check

def observer11InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 11, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer11Panel0Endpoints, observer11Panel1Endpoints, observer11Panel2Endpoints, observer11Panel3Endpoints, observer11Panel4Endpoints, observer11Panel5Endpoints, observer11Panel6Endpoints, observer11Panel7Endpoints]
  }
def observer11FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer11InsertionEndpoints.frameLower
    observer11InsertionEndpoints.frameUpper
theorem observer11_frame_recurrence_field_kernel_check :
    observer11FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer11_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer11InsertionEndpoints.frameLower
      observer11InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer11InsertionEndpoints.frameLower
    observer11InsertionEndpoints.frameUpper
    observer11_frame_recurrence_field_kernel_check
def observer11RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer11Panel0Endpoints ∧
  panelRecurrenceFields observer11Panel1Endpoints ∧
  panelRecurrenceFields observer11Panel2Endpoints ∧
  panelRecurrenceFields observer11Panel3Endpoints ∧
  panelRecurrenceFields observer11Panel4Endpoints ∧
  panelRecurrenceFields observer11Panel5Endpoints ∧
  panelRecurrenceFields observer11Panel6Endpoints ∧
  panelRecurrenceFields observer11Panel7Endpoints ∧ insertionFrameRecurrenceFields observer11InsertionEndpoints.frameLower
      observer11InsertionEndpoints.frameUpper
theorem observer11_all_recurrence_fields :
    observer11RecurrenceFieldBounds := by
  exact ⟨observer11_panel0_recurrence_fields_sound,
    observer11_panel1_recurrence_fields_sound,
    observer11_panel2_recurrence_fields_sound,
    observer11_panel3_recurrence_fields_sound,
    observer11_panel4_recurrence_fields_sound,
    observer11_panel5_recurrence_fields_sound,
    observer11_panel6_recurrence_fields_sound,
    observer11_panel7_recurrence_fields_sound,
    observer11_frame_recurrence_fields_sound⟩
def observer11PanelFormulaBounds : Prop :=
  panelFormulaBounds observer11Panel0Data observer11Panel0Endpoints ∧
  panelFormulaBounds observer11Panel1Data observer11Panel1Endpoints ∧
  panelFormulaBounds observer11Panel2Data observer11Panel2Endpoints ∧
  panelFormulaBounds observer11Panel3Data observer11Panel3Endpoints ∧
  panelFormulaBounds observer11Panel4Data observer11Panel4Endpoints ∧
  panelFormulaBounds observer11Panel5Data observer11Panel5Endpoints ∧
  panelFormulaBounds observer11Panel6Data observer11Panel6Endpoints ∧
  panelFormulaBounds observer11Panel7Data observer11Panel7Endpoints
theorem observer11_all_panel_formula_bounds : observer11PanelFormulaBounds := by
  exact ⟨observer11_panel0_formula_sound,
    observer11_panel1_formula_sound,
    observer11_panel2_formula_sound,
    observer11_panel3_formula_sound,
    observer11_panel4_formula_sound,
    observer11_panel5_formula_sound,
    observer11_panel6_formula_sound,
    observer11_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
