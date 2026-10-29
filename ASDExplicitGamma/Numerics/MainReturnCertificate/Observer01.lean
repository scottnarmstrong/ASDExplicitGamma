module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer1Panel0Data : MainPanelData :=
  {
    observer := 1, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 430004960586916748083722713660, ellLower := 864232279614533487755097153990,
    rhoLower := 99891958407002114481813654444098, rhoUpper := 99892058299010467479780301211662,
    offsetLower := 53707166434920711398789859053, offsetUpper := 53756868419130254346821170792,
    supportELower := 221660849413118773689651916210, supportEUpper := 225239337285335010719250416934,
    supportLambdaLower := 864232279614533487755097153990,
    supportLambdaUpper := 881622861713653513124276531247,
    supportJLower := 230303172209264108567202887749, supportJUpper := 234055565902471545850493182247,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer1Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel0Data observer1Panel0Endpoints
theorem observer1_panel0_kernel_check : observer1Panel0Check = true := by
  decide +kernel
theorem observer1_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel0Data) s observer1Panel0Data.anchor ≤
        (observer1Panel0Endpoints.energyUpper : ℝ) ∧
      (observer1Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel0Data) s observer1Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel0Data) s observer1Panel0Data.anchor ≤
        (observer1Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel0Data) s observer1Panel0Data.anchor ≤
        (observer1Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel0Data) s observer1Panel0Data.anchor ≤
        (observer1Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel0Data observer1Panel0Endpoints
    observer1_panel0_kernel_check s hs
def observer1Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel0Endpoints
theorem observer1_panel0_recurrence_field_kernel_check :
    observer1Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel0Endpoints
    observer1_panel0_recurrence_field_kernel_check

def observer1Panel1Data : MainPanelData :=
  {
    observer := 1, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 433713966741085795074422059311, ellLower := 859263661668854018417196929551,
    rhoLower := 99892557760550615341942480211000, rhoUpper := 99892657653158322188086861250103,
    offsetLower := 54181128709180080983145617293, offsetUpper := 54231549576568447357306766829,
    supportELower := 225239098785587185872281561789, supportEUpper := 228683570408973467615498215460,
    supportLambdaLower := 859263661668854018417196929551,
    supportLambdaUpper := 876007897444494314049265939133,
    supportJLower := 233831735402275726056453531084, supportJUpper := 237443649383418410755990874852,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer1Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel1Data observer1Panel1Endpoints
theorem observer1_panel1_kernel_check : observer1Panel1Check = true := by
  decide +kernel
theorem observer1_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel1Data) s observer1Panel1Data.anchor ≤
        (observer1Panel1Endpoints.energyUpper : ℝ) ∧
      (observer1Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel1Data) s observer1Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel1Data) s observer1Panel1Data.anchor ≤
        (observer1Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel1Data) s observer1Panel1Data.anchor ≤
        (observer1Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel1Data) s observer1Panel1Data.anchor ≤
        (observer1Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel1Data observer1Panel1Endpoints
    observer1_panel1_kernel_check s hs
def observer1Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel1Endpoints
theorem observer1_panel1_recurrence_field_kernel_check :
    observer1Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel1Endpoints
    observer1_panel1_recurrence_field_kernel_check

def observer1Panel2Data : MainPanelData :=
  {
    observer := 1, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 437391199674962302778471196218, ellLower := 854457982879149045885326483618,
    rhoLower := 99893157117695248281461916526451, rhoUpper := 99893257010902312571917909294341,
    offsetLower := 54641006338321428934038461292, offsetUpper := 54692140988067464594768079355,
    supportELower := 228683320820751365319141347462, supportEUpper := 232093867661898182447005377247,
    supportLambdaLower := 854457982879149045885326483618,
    supportLambdaUpper := 870616915569224240463235313242,
    supportJLower := 237227900649542855777994612298, supportJUpper := 240800036817590424851637730380,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer1Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel2Data observer1Panel2Endpoints
theorem observer1_panel2_kernel_check : observer1Panel2Check = true := by
  decide +kernel
theorem observer1_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel2Data) s observer1Panel2Data.anchor ≤
        (observer1Panel2Endpoints.energyUpper : ℝ) ∧
      (observer1Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel2Data) s observer1Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel2Data) s observer1Panel2Data.anchor ≤
        (observer1Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel2Data) s observer1Panel2Data.anchor ≤
        (observer1Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel2Data) s observer1Panel2Data.anchor ≤
        (observer1Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel2Data observer1Panel2Endpoints
    observer1_panel2_kernel_check s hs
def observer1Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel2Endpoints
theorem observer1_panel2_recurrence_field_kernel_check :
    observer1Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel2Endpoints
    observer1_panel2_recurrence_field_kernel_check

def observer1Panel3Data : MainPanelData :=
  {
    observer := 1, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 441046244015007075951334728749, ellLower := 849821083907557843401235503173,
    rhoLower := 99893756478436034877229170241002, rhoUpper := 99893856372242460208152229062926,
    offsetLower := 55087181566893615954932161854, offsetUpper := 55139025171339945411513532565,
    supportELower := 232093607092547114216566102668, supportEUpper := 235479961066069832608244684928,
    supportLambdaLower := 849821083907557843401235503173,
    supportLambdaUpper := 865435172171070844081912754947,
    supportJLower := 240591817931622692650578457699, supportJUpper := 244134312787780541049063812478,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer1Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel3Data observer1Panel3Endpoints
theorem observer1_panel3_kernel_check : observer1Panel3Check = true := by
  decide +kernel
theorem observer1_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel3Data) s observer1Panel3Data.anchor ≤
        (observer1Panel3Endpoints.energyUpper : ℝ) ∧
      (observer1Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel3Data) s observer1Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel3Data) s observer1Panel3Data.anchor ≤
        (observer1Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel3Data) s observer1Panel3Data.anchor ≤
        (observer1Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel3Data) s observer1Panel3Data.anchor ≤
        (observer1Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel3Data observer1Panel3Endpoints
    observer1_panel3_kernel_check s hs
def observer1Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel3Endpoints
theorem observer1_panel3_recurrence_field_kernel_check :
    observer1Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel3Endpoints
    observer1_panel3_recurrence_field_kernel_check

def observer1Panel4Data : MainPanelData :=
  {
    observer := 1, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 444682956999041025134872830638, ellLower := 845343722231981492501458176340,
    rhoLower := 99894355842772996706230909736835, rhoUpper := 99894455737178786673798065935494,
    offsetLower := 55520297426117761441235419899, offsetUpper := 55572845683809979423100320107,
    supportELower := 235479689603412258299323867664, supportEUpper := 238845848589572655014762078158,
    supportLambdaLower := 845343722231981492501458176340,
    supportLambdaUpper := 860448589859387204236658037395,
    supportJLower := 243933126825732073224338449427, supportJUpper := 247450334488166527057128658532,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer1Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel4Data observer1Panel4Endpoints
theorem observer1_panel4_kernel_check : observer1Panel4Check = true := by
  decide +kernel
theorem observer1_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel4Data) s observer1Panel4Data.anchor ≤
        (observer1Panel4Endpoints.energyUpper : ℝ) ∧
      (observer1Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel4Data) s observer1Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel4Data) s observer1Panel4Data.anchor ≤
        (observer1Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel4Data) s observer1Panel4Data.anchor ≤
        (observer1Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel4Data) s observer1Panel4Data.anchor ≤
        (observer1Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel4Data observer1Panel4Endpoints
    observer1_panel4_kernel_check s hs
def observer1Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel4Endpoints
theorem observer1_panel4_recurrence_field_kernel_check :
    observer1Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel4Endpoints
    observer1_panel4_recurrence_field_kernel_check

def observer1Panel5Data : MainPanelData :=
  {
    observer := 1, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 448303682451860340418474281948, ellLower := 841016630596908068509358311665,
    rhoLower := 99894855315800892100384118159433, rhoUpper := 99894955210706155345583265704524,
    offsetLower := 55994095894854047216662025679, offsetUpper := 56047344846490006923040031613,
    supportELower := 238845566312396134419993122608, supportEUpper := 242193762648610940295354234878,
    supportLambdaLower := 841016630596908068509358311665,
    supportLambdaUpper := 855644269697837152484013361440,
    supportJLower := 247255732618365215105086705724, supportJUpper := 250750205345589311820194368493,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer1Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel5Data observer1Panel5Endpoints
theorem observer1_panel5_kernel_check : observer1Panel5Check = true := by
  decide +kernel
theorem observer1_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel5Data) s observer1Panel5Data.anchor ≤
        (observer1Panel5Endpoints.energyUpper : ℝ) ∧
      (observer1Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel5Data) s observer1Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel5Data) s observer1Panel5Data.anchor ≤
        (observer1Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel5Data) s observer1Panel5Data.anchor ≤
        (observer1Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel5Data) s observer1Panel5Data.anchor ≤
        (observer1Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel5Data observer1Panel5Endpoints
    observer1_panel5_kernel_check s hs
def observer1Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel5Endpoints
theorem observer1_panel5_recurrence_field_kernel_check :
    observer1Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel5Endpoints
    observer1_panel5_recurrence_field_kernel_check

def observer1Panel6Data : MainPanelData :=
  {
    observer := 1, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 451909293648747110854492335594, ellLower := 836831117209877349162695916789,
    rhoLower := 99895354791326158877437551741590, rhoUpper := 99895454686730897897641322219444,
    offsetLower := 56457029025460902124850601799, offsetUpper := 56510974990024077288149612186,
    supportELower := 242193469629907073943771307419, supportEUpper := 245525174629268903839154019283,
    supportLambdaLower := 836831117209877349162695916789,
    supportLambdaUpper := 851010480714400290897277188289,
    supportJLower := 250561780802005847435398266586, supportJUpper := 254035279436412906748126791166,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer1Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel6Data observer1Panel6Endpoints
theorem observer1_panel6_kernel_check : observer1Panel6Check = true := by
  decide +kernel
theorem observer1_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel6Data) s observer1Panel6Data.anchor ≤
        (observer1Panel6Endpoints.energyUpper : ℝ) ∧
      (observer1Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel6Data) s observer1Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel6Data) s observer1Panel6Data.anchor ≤
        (observer1Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel6Data) s observer1Panel6Data.anchor ≤
        (observer1Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel6Data) s observer1Panel6Data.anchor ≤
        (observer1Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel6Data observer1Panel6Endpoints
    observer1_panel6_kernel_check s hs
def observer1Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel6Endpoints
theorem observer1_panel6_recurrence_field_kernel_check :
    observer1Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel6Endpoints
    observer1_panel6_recurrence_field_kernel_check

def observer1Panel7Data : MainPanelData :=
  {
    observer := 1, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((559403904376645107821 : ℚ) / 500000000000000000000),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer1Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 455501000753520080386505549000, ellLower := 832779143611440630188972787360,
    rhoLower := 99895954165253026816872854070067, rhoUpper := 99896054061257140063631627312873,
    offsetLower := 56854784950916416567188052270, offsetUpper := 56909424563584349075332907871,
    supportELower := 245524870937672613389223686377, supportEUpper := 248841160788416830550204998458,
    supportLambdaLower := 832779143611440630188972787360,
    supportLambdaUpper := 846536560205429442703433700296,
    supportJLower := 253852662373787019691113414250, supportJUpper := 257306526390471124977239335461,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer1Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer1Panel7Data observer1Panel7Endpoints
theorem observer1_panel7_kernel_check : observer1Panel7Check = true := by
  decide +kernel
theorem observer1_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer1Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer1Panel7Data) s observer1Panel7Data.anchor ≤
        (observer1Panel7Endpoints.energyUpper : ℝ) ∧
      (observer1Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer1Panel7Data) s observer1Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer1Panel7Data) s observer1Panel7Data.anchor ≤
        (observer1Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer1Panel7Data) s observer1Panel7Data.anchor ≤
        (observer1Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer1Panel7Data) s observer1Panel7Data.anchor ≤
        (observer1Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer1Panel7Data observer1Panel7Endpoints
    observer1_panel7_kernel_check s hs
def observer1Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer1Panel7Endpoints
theorem observer1_panel7_recurrence_field_kernel_check :
    observer1Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer1Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer1Panel7Endpoints
    observer1_panel7_recurrence_field_kernel_check

def observer1InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 1, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer1Panel0Endpoints, observer1Panel1Endpoints, observer1Panel2Endpoints, observer1Panel3Endpoints, observer1Panel4Endpoints, observer1Panel5Endpoints, observer1Panel6Endpoints, observer1Panel7Endpoints]
  }
def observer1FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer1InsertionEndpoints.frameLower
    observer1InsertionEndpoints.frameUpper
theorem observer1_frame_recurrence_field_kernel_check :
    observer1FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer1_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer1InsertionEndpoints.frameLower
      observer1InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer1InsertionEndpoints.frameLower
    observer1InsertionEndpoints.frameUpper
    observer1_frame_recurrence_field_kernel_check
def observer1RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer1Panel0Endpoints ∧
  panelRecurrenceFields observer1Panel1Endpoints ∧
  panelRecurrenceFields observer1Panel2Endpoints ∧
  panelRecurrenceFields observer1Panel3Endpoints ∧
  panelRecurrenceFields observer1Panel4Endpoints ∧
  panelRecurrenceFields observer1Panel5Endpoints ∧
  panelRecurrenceFields observer1Panel6Endpoints ∧
  panelRecurrenceFields observer1Panel7Endpoints ∧ insertionFrameRecurrenceFields observer1InsertionEndpoints.frameLower
      observer1InsertionEndpoints.frameUpper
theorem observer1_all_recurrence_fields :
    observer1RecurrenceFieldBounds := by
  exact ⟨observer1_panel0_recurrence_fields_sound,
    observer1_panel1_recurrence_fields_sound,
    observer1_panel2_recurrence_fields_sound,
    observer1_panel3_recurrence_fields_sound,
    observer1_panel4_recurrence_fields_sound,
    observer1_panel5_recurrence_fields_sound,
    observer1_panel6_recurrence_fields_sound,
    observer1_panel7_recurrence_fields_sound,
    observer1_frame_recurrence_fields_sound⟩
def observer1PanelFormulaBounds : Prop :=
  panelFormulaBounds observer1Panel0Data observer1Panel0Endpoints ∧
  panelFormulaBounds observer1Panel1Data observer1Panel1Endpoints ∧
  panelFormulaBounds observer1Panel2Data observer1Panel2Endpoints ∧
  panelFormulaBounds observer1Panel3Data observer1Panel3Endpoints ∧
  panelFormulaBounds observer1Panel4Data observer1Panel4Endpoints ∧
  panelFormulaBounds observer1Panel5Data observer1Panel5Endpoints ∧
  panelFormulaBounds observer1Panel6Data observer1Panel6Endpoints ∧
  panelFormulaBounds observer1Panel7Data observer1Panel7Endpoints
theorem observer1_all_panel_formula_bounds : observer1PanelFormulaBounds := by
  exact ⟨observer1_panel0_formula_sound,
    observer1_panel1_formula_sound,
    observer1_panel2_formula_sound,
    observer1_panel3_formula_sound,
    observer1_panel4_formula_sound,
    observer1_panel5_formula_sound,
    observer1_panel6_formula_sound,
    observer1_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
