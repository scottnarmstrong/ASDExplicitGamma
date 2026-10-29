module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer6Panel0Data : MainPanelData :=
  {
    observer := 6, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((32510441860151370407 : ℚ) / 5000000000000000000000),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer6Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 64991430657960062142461786163, ellLower := 391041887755609890205705450946,
    rhoLower := 99951111954101402071920853897312, rhoUpper := 99951211905263331745958499342851,
    offsetLower := 8108614895992488649252380799, offsetUpper := 8125226847839945831616457088,
    supportELower := 52506131189428350253268604904, supportEUpper := 54188070017801225494239533495,
    supportLambdaLower := 391041887755609890205705450946,
    supportLambdaUpper := 401564452025379042177669313070,
    supportJLower := 56416550066984449155325659413, supportJUpper := 58203714538055015916016226626,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer6Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer6Panel0Data observer6Panel0Endpoints
theorem observer6_panel0_kernel_check : observer6Panel0Check = true := by
  decide +kernel
theorem observer6_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer6Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer6Panel0Data) s observer6Panel0Data.anchor ≤
        (observer6Panel0Endpoints.energyUpper : ℝ) ∧
      (observer6Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer6Panel0Data) s observer6Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer6Panel0Data) s observer6Panel0Data.anchor ≤
        (observer6Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer6Panel0Data) s observer6Panel0Data.anchor ≤
        (observer6Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer6Panel0Data) s observer6Panel0Data.anchor ≤
        (observer6Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer6Panel0Data observer6Panel0Endpoints
    observer6_panel0_kernel_check s hs
def observer6Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer6Panel0Endpoints
theorem observer6_panel0_recurrence_field_kernel_check :
    observer6Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer6_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer6Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer6Panel0Endpoints
    observer6_panel0_recurrence_field_kernel_check

def observer6Panel1Data : MainPanelData :=
  {
    observer := 6, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((32510441860151370407 : ℚ) / 5000000000000000000000),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer6Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 66864534229887415727619961480, ellLower := 390509431747132286658727649175,
    rhoLower := 99951111954101402071920853897312, rhoUpper := 99951211905263331745958499342851,
    offsetLower := 8353686147696740012426274185, offsetUpper := 8370800171955419873952400757,
    supportELower := 54188006515093788680259841579, supportEUpper := 55749676863330510035051410155,
    supportLambdaLower := 390509431747132286658727649175,
    supportLambdaUpper := 400621857342967738092133874124,
    supportJLower := 58093100832565111546847118070, supportJUpper := 59755895436760187415972748897,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer6Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer6Panel1Data observer6Panel1Endpoints
theorem observer6_panel1_kernel_check : observer6Panel1Check = true := by
  decide +kernel
theorem observer6_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer6Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer6Panel1Data) s observer6Panel1Data.anchor ≤
        (observer6Panel1Endpoints.energyUpper : ℝ) ∧
      (observer6Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer6Panel1Data) s observer6Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer6Panel1Data) s observer6Panel1Data.anchor ≤
        (observer6Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer6Panel1Data) s observer6Panel1Data.anchor ≤
        (observer6Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer6Panel1Data) s observer6Panel1Data.anchor ≤
        (observer6Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer6Panel1Data observer6Panel1Endpoints
    observer6_panel1_kernel_check s hs
def observer6Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer6Panel1Endpoints
theorem observer6_panel1_recurrence_field_kernel_check :
    observer6Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer6_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer6Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer6Panel1Endpoints
    observer6_panel1_recurrence_field_kernel_check

def observer6Panel2Data : MainPanelData :=
  {
    observer := 6, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((32510441860151370407 : ℚ) / 5000000000000000000000),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer6Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 68717360853613680557792363410, ellLower := 389976855270572472301069245494,
    rhoLower := 99951211905263331745958499342849, rhoUpper := 99951311856525212631901416449402,
    offsetLower := 8579280229664303502878478891, offsetUpper := 8596892523413576082468567258,
    supportELower := 55749608044876907210382195395, supportEUpper := 57290629235304427297322638063,
    supportLambdaLower := 389976855270572472301069245494,
    supportLambdaUpper := 399724732547753134042023138485,
    supportJLower := 59649376597582631933392887849, supportJUpper := 61287876560781958637742869448,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer6Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer6Panel2Data observer6Panel2Endpoints
theorem observer6_panel2_kernel_check : observer6Panel2Check = true := by
  decide +kernel
theorem observer6_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer6Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer6Panel2Data) s observer6Panel2Data.anchor ≤
        (observer6Panel2Endpoints.energyUpper : ℝ) ∧
      (observer6Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer6Panel2Data) s observer6Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer6Panel2Data) s observer6Panel2Data.anchor ≤
        (observer6Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer6Panel2Data) s observer6Panel2Data.anchor ≤
        (observer6Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer6Panel2Data) s observer6Panel2Data.anchor ≤
        (observer6Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer6Panel2Data observer6Panel2Endpoints
    observer6_panel2_kernel_check s hs
def observer6Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer6Panel2Endpoints
theorem observer6_panel2_recurrence_field_kernel_check :
    observer6Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer6_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer6Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer6Panel2Endpoints
    observer6_panel2_recurrence_field_kernel_check

def observer6Panel3Data : MainPanelData :=
  {
    observer := 6, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((32510441860151370407 : ℚ) / 5000000000000000000000),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer6Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 70559176695057686529985762358, ellLower := 389460777948062445629502138453,
    rhoLower := 99951311856525212631901416449400, rhoUpper := 99951411807887044829700867097861,
    offsetLower := 8802793571805086143230341241, offsetUpper := 8820901905685552514337769807,
    supportELower := 57290555142141702510341379775, supportEUpper := 58820217667979957999351129318,
    supportLambdaLower := 389460777948062445629502138453,
    supportLambdaUpper := 398870636439134963514768864494,
    supportJLower := 61185162921622326966636401159, supportJUpper := 62808924032371307634498817963,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer6Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer6Panel3Data observer6Panel3Endpoints
theorem observer6_panel3_kernel_check : observer6Panel3Check = true := by
  decide +kernel
theorem observer6_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer6Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer6Panel3Data) s observer6Panel3Data.anchor ≤
        (observer6Panel3Endpoints.energyUpper : ℝ) ∧
      (observer6Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer6Panel3Data) s observer6Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer6Panel3Data) s observer6Panel3Data.anchor ≤
        (observer6Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer6Panel3Data) s observer6Panel3Data.anchor ≤
        (observer6Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer6Panel3Data) s observer6Panel3Data.anchor ≤
        (observer6Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer6Panel3Data observer6Panel3Endpoints
    observer6_panel3_kernel_check s hs
def observer6Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer6Panel3Endpoints
theorem observer6_panel3_recurrence_field_kernel_check :
    observer6Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer6_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer6Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer6Panel3Endpoints
    observer6_panel3_recurrence_field_kernel_check

def observer6Panel4Data : MainPanelData :=
  {
    observer := 6, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((32510441860151370407 : ℚ) / 5000000000000000000000),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer6Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 72393535580844190924668940550, ellLower := 388961677217250635409793538468,
    rhoLower := 99951311856525212631901416449400, rhoUpper := 99951411807887044829700867097861,
    offsetLower := 9043232844179312629985381801, offsetUpper := 9061835788615690977658433202,
    supportELower := 58820138324568165269908619876, supportEUpper := 60342026288939421017464863787,
    supportLambdaLower := 388961677217250635409793538468,
    supportLambdaUpper := 398056534557042783624387653291,
    supportJLower := 62709755096740671624006555260, supportJUpper := 64322591634509848853708740320,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer6Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer6Panel4Data observer6Panel4Endpoints
theorem observer6_panel4_kernel_check : observer6Panel4Check = true := by
  decide +kernel
theorem observer6_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer6Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer6Panel4Data) s observer6Panel4Data.anchor ≤
        (observer6Panel4Endpoints.energyUpper : ℝ) ∧
      (observer6Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer6Panel4Data) s observer6Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer6Panel4Data) s observer6Panel4Data.anchor ≤
        (observer6Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer6Panel4Data) s observer6Panel4Data.anchor ≤
        (observer6Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer6Panel4Data) s observer6Panel4Data.anchor ≤
        (observer6Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer6Panel4Data observer6Panel4Endpoints
    observer6_panel4_kernel_check s hs
def observer6Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer6Panel4Endpoints
theorem observer6_panel4_recurrence_field_kernel_check :
    observer6Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer6_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer6Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer6Panel4Endpoints
    observer6_panel4_recurrence_field_kernel_check

def observer6Panel5Data : MainPanelData :=
  {
    observer := 6, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((32510441860151370407 : ℚ) / 5000000000000000000000),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer6Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 74222492021464282202082497244, ellLower := 388479085060856400454176890726,
    rhoLower := 99951411807887044829700867097859, rhoUpper := 99951511759348828439308213120434,
    offsetLower := 9264123071909109473350465593, offsetUpper := 9283219715358023854966504544,
    supportELower := 60341941713424222125139975010, supportEUpper := 61857898658394808763677074620,
    supportLambdaLower := 388479085060856400454176890726,
    supportLambdaUpper := 397279482133860084690948104408,
    supportJLower := 64226732564032786129681743917, supportJUpper := 65830693479733409610586555665,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer6Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer6Panel5Data observer6Panel5Endpoints
theorem observer6_panel5_kernel_check : observer6Panel5Check = true := by
  decide +kernel
theorem observer6_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer6Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer6Panel5Data) s observer6Panel5Data.anchor ≤
        (observer6Panel5Endpoints.energyUpper : ℝ) ∧
      (observer6Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer6Panel5Data) s observer6Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer6Panel5Data) s observer6Panel5Data.anchor ≤
        (observer6Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer6Panel5Data) s observer6Panel5Data.anchor ≤
        (observer6Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer6Panel5Data) s observer6Panel5Data.anchor ≤
        (observer6Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer6Panel5Data observer6Panel5Endpoints
    observer6_panel5_kernel_check s hs
def observer6Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer6Panel5Endpoints
theorem observer6_panel5_recurrence_field_kernel_check :
    observer6Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer6_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer6Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer6Panel5Endpoints
    observer6_panel5_recurrence_field_kernel_check

def observer6Panel6Data : MainPanelData :=
  {
    observer := 6, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((32510441860151370407 : ℚ) / 5000000000000000000000),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer6Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 76046643183396436730731304967, ellLower := 388012304206474928107695501677,
    rhoLower := 99951411807887044829700867097859, rhoUpper := 99951511759348828439308213120434,
    offsetLower := 9503224241641894490964104403, offsetUpper := 9522813757405993304540125256,
    supportELower := 61857808865646414220931530050, supportEUpper := 63368939974897280673335026321,
    supportLambdaLower := 388012304206474928107695501677,
    supportLambdaUpper := 396536756070510795781470609387,
    supportJLower := 65737931907711163502008485066, supportJUpper := 67334307535602388631149732415,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer6Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer6Panel6Data observer6Panel6Endpoints
theorem observer6_panel6_kernel_check : observer6Panel6Check = true := by
  decide +kernel
theorem observer6_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer6Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer6Panel6Data) s observer6Panel6Data.anchor ≤
        (observer6Panel6Endpoints.energyUpper : ℝ) ∧
      (observer6Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer6Panel6Data) s observer6Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer6Panel6Data) s observer6Panel6Data.anchor ≤
        (observer6Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer6Panel6Data) s observer6Panel6Data.anchor ≤
        (observer6Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer6Panel6Data) s observer6Panel6Data.anchor ≤
        (observer6Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer6Panel6Data observer6Panel6Endpoints
    observer6_panel6_kernel_check s hs
def observer6Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer6Panel6Endpoints
theorem observer6_panel6_recurrence_field_kernel_check :
    observer6Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer6_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer6Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer6Panel6Endpoints
    observer6_panel6_recurrence_field_kernel_check

def observer6Panel7Data : MainPanelData :=
  {
    observer := 6, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((32510441860151370407 : ℚ) / 5000000000000000000000),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer6Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 77866935496708900345060697104, ellLower := 387560583935912387531412992072,
    rhoLower := 99951511759348828439308213120432, rhoUpper := 99951611710910563560674916300738,
    offsetLower := 9721958169890432816507366577, offsetUpper := 9742039989696213191946134747,
    supportELower := 63368844977771318035167457281, supportEUpper := 64875880950892532733620530156,
    supportLambdaLower := 387560583935912387531412992072,
    supportLambdaUpper := 395825874730756820895792528443,
    supportJLower := 67244450817130441910481587201, supportJUpper := 68834139698200100942578455441,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer6Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer6Panel7Data observer6Panel7Endpoints
theorem observer6_panel7_kernel_check : observer6Panel7Check = true := by
  decide +kernel
theorem observer6_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer6Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer6Panel7Data) s observer6Panel7Data.anchor ≤
        (observer6Panel7Endpoints.energyUpper : ℝ) ∧
      (observer6Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer6Panel7Data) s observer6Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer6Panel7Data) s observer6Panel7Data.anchor ≤
        (observer6Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer6Panel7Data) s observer6Panel7Data.anchor ≤
        (observer6Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer6Panel7Data) s observer6Panel7Data.anchor ≤
        (observer6Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer6Panel7Data observer6Panel7Endpoints
    observer6_panel7_kernel_check s hs
def observer6Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer6Panel7Endpoints
theorem observer6_panel7_recurrence_field_kernel_check :
    observer6Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer6_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer6Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer6Panel7Endpoints
    observer6_panel7_recurrence_field_kernel_check

def observer6InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 6, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer6Panel0Endpoints, observer6Panel1Endpoints, observer6Panel2Endpoints, observer6Panel3Endpoints, observer6Panel4Endpoints, observer6Panel5Endpoints, observer6Panel6Endpoints, observer6Panel7Endpoints]
  }
def observer6FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer6InsertionEndpoints.frameLower
    observer6InsertionEndpoints.frameUpper
theorem observer6_frame_recurrence_field_kernel_check :
    observer6FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer6_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer6InsertionEndpoints.frameLower
      observer6InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer6InsertionEndpoints.frameLower
    observer6InsertionEndpoints.frameUpper
    observer6_frame_recurrence_field_kernel_check
def observer6RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer6Panel0Endpoints ∧
  panelRecurrenceFields observer6Panel1Endpoints ∧
  panelRecurrenceFields observer6Panel2Endpoints ∧
  panelRecurrenceFields observer6Panel3Endpoints ∧
  panelRecurrenceFields observer6Panel4Endpoints ∧
  panelRecurrenceFields observer6Panel5Endpoints ∧
  panelRecurrenceFields observer6Panel6Endpoints ∧
  panelRecurrenceFields observer6Panel7Endpoints ∧ insertionFrameRecurrenceFields observer6InsertionEndpoints.frameLower
      observer6InsertionEndpoints.frameUpper
theorem observer6_all_recurrence_fields :
    observer6RecurrenceFieldBounds := by
  exact ⟨observer6_panel0_recurrence_fields_sound,
    observer6_panel1_recurrence_fields_sound,
    observer6_panel2_recurrence_fields_sound,
    observer6_panel3_recurrence_fields_sound,
    observer6_panel4_recurrence_fields_sound,
    observer6_panel5_recurrence_fields_sound,
    observer6_panel6_recurrence_fields_sound,
    observer6_panel7_recurrence_fields_sound,
    observer6_frame_recurrence_fields_sound⟩
def observer6PanelFormulaBounds : Prop :=
  panelFormulaBounds observer6Panel0Data observer6Panel0Endpoints ∧
  panelFormulaBounds observer6Panel1Data observer6Panel1Endpoints ∧
  panelFormulaBounds observer6Panel2Data observer6Panel2Endpoints ∧
  panelFormulaBounds observer6Panel3Data observer6Panel3Endpoints ∧
  panelFormulaBounds observer6Panel4Data observer6Panel4Endpoints ∧
  panelFormulaBounds observer6Panel5Data observer6Panel5Endpoints ∧
  panelFormulaBounds observer6Panel6Data observer6Panel6Endpoints ∧
  panelFormulaBounds observer6Panel7Data observer6Panel7Endpoints
theorem observer6_all_panel_formula_bounds : observer6PanelFormulaBounds := by
  exact ⟨observer6_panel0_formula_sound,
    observer6_panel1_formula_sound,
    observer6_panel2_formula_sound,
    observer6_panel3_formula_sound,
    observer6_panel4_formula_sound,
    observer6_panel5_formula_sound,
    observer6_panel6_formula_sound,
    observer6_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
