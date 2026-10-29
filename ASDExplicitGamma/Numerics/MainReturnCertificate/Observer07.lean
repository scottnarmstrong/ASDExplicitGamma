module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer7Panel0Data : MainPanelData :=
  {
    observer := 7, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((937978 : ℚ) / 279006525),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer7Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 60385498757960986560925839210, ellLower := 380078642161234951793502304416,
    rhoLower := 99952411327002710949153797500735, rhoUpper := 99952511279464014174186987395861,
    offsetLower := 7544833507709800788349337905, offsetUpper := 7560713587667886449177669051,
    supportELower := 48589353227327451684996981940, supportEUpper := 50227398156557192019444423177,
    supportLambdaLower := 380078642161234951793502304416,
    supportLambdaUpper := 390442185001759590636512638463,
    supportJLower := 52390139648939801202932004984, supportJUpper := 54131820006574787925809549562,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer7Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer7Panel0Data observer7Panel0Endpoints
theorem observer7_panel0_kernel_check : observer7Panel0Check = true := by
  decide +kernel
theorem observer7_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer7Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer7Panel0Data) s observer7Panel0Data.anchor ≤
        (observer7Panel0Endpoints.energyUpper : ℝ) ∧
      (observer7Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer7Panel0Data) s observer7Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer7Panel0Data) s observer7Panel0Data.anchor ≤
        (observer7Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer7Panel0Data) s observer7Panel0Data.anchor ≤
        (observer7Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer7Panel0Data) s observer7Panel0Data.anchor ≤
        (observer7Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer7Panel0Data observer7Panel0Endpoints
    observer7_panel0_kernel_check s hs
def observer7Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer7Panel0Endpoints
theorem observer7_panel0_recurrence_field_kernel_check :
    observer7Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer7_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer7Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer7Panel0Endpoints
    observer7_panel0_recurrence_field_kernel_check

def observer7Panel1Data : MainPanelData :=
  {
    observer := 7, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((937978 : ℚ) / 279006525),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer7Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 62216113352884707531840656994, ellLower := 379648962830551600321296919288,
    rhoLower := 99952511279464014174186987395859, rhoUpper := 99952611232025269910499649634535,
    offsetLower := 7765976595819892246129326247, offsetUpper := 7782356621817154385008177135,
    supportELower := 50227338705844806262423415765, supportEUpper := 51745433580038380202355488941,
    supportLambdaLower := 379648962830551600321296919288,
    supportLambdaUpper := 389607834823794660916722535834,
    supportJLower := 54023828334150322265636384957, supportJUpper := 55641511928276326811522714300,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer7Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer7Panel1Data observer7Panel1Endpoints
theorem observer7_panel1_kernel_check : observer7Panel1Check = true := by
  decide +kernel
theorem observer7_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer7Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer7Panel1Data) s observer7Panel1Data.anchor ≤
        (observer7Panel1Endpoints.energyUpper : ℝ) ∧
      (observer7Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer7Panel1Data) s observer7Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer7Panel1Data) s observer7Panel1Data.anchor ≤
        (observer7Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer7Panel1Data) s observer7Panel1Data.anchor ≤
        (observer7Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer7Panel1Data) s observer7Panel1Data.anchor ≤
        (observer7Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer7Panel1Data observer7Panel1Endpoints
    observer7_panel1_kernel_check s hs
def observer7Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer7Panel1Endpoints
theorem observer7_panel1_recurrence_field_kernel_check :
    observer7Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer7_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer7Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer7Panel1Endpoints
    observer7_panel1_recurrence_field_kernel_check

def observer7Panel2Data : MainPanelData :=
  {
    observer := 7, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((937978 : ℚ) / 279006525),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer7Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 64026717290904016840275058296, ellLower := 379215387074476787463647529795,
    rhoLower := 99952511279464014174186987395859, rhoUpper := 99952611232025269910499649634535,
    offsetLower := 8001118502310118409347047339, offsetUpper := 8017994490469232653561116417,
    supportELower := 51745368947184890332032258178, supportEUpper := 53243122156860510693323317352,
    supportLambdaLower := 379215387074476787463647529795,
    supportLambdaUpper := 388814820973063181823151687051,
    supportJLower := 55537522817929658206668733475, supportJUpper := 57131270366591142511554834223,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer7Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer7Panel2Data observer7Panel2Endpoints
theorem observer7_panel2_kernel_check : observer7Panel2Check = true := by
  decide +kernel
theorem observer7_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer7Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer7Panel2Data) s observer7Panel2Data.anchor ≤
        (observer7Panel2Endpoints.energyUpper : ℝ) ∧
      (observer7Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer7Panel2Data) s observer7Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer7Panel2Data) s observer7Panel2Data.anchor ≤
        (observer7Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer7Panel2Data) s observer7Panel2Data.anchor ≤
        (observer7Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer7Panel2Data) s observer7Panel2Data.anchor ≤
        (observer7Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer7Panel2Data observer7Panel2Endpoints
    observer7_panel2_kernel_check s hs
def observer7Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer7Panel2Endpoints
theorem observer7_panel2_recurrence_field_kernel_check :
    observer7Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer7_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer7Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer7Panel2Endpoints
    observer7_panel2_recurrence_field_kernel_check

def observer7Panel3Data : MainPanelData :=
  {
    observer := 7, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((937978 : ℚ) / 279006525),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer7Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 65826569363166856942667388143, ellLower := 378794784013253564382198901619,
    rhoLower := 99952611232025269910499649634533, rhoUpper := 99952711184686478258044345472504,
    offsetLower := 8217801861887862848030590103, offsetUpper := 8235171532917530977747241055,
    supportELower := 53243052381367018270266669872, supportEUpper := 54729744198995397936496377410,
    supportLambdaLower := 378794784013253564382198901619,
    supportLambdaUpper := 388060987000392770201333622682,
    supportJLower := 57031000221499553914088658888, supportJUpper := 58610354068999325638509713637,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer7Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer7Panel3Data observer7Panel3Endpoints
theorem observer7_panel3_kernel_check : observer7Panel3Check = true := by
  decide +kernel
theorem observer7_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer7Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer7Panel3Data) s observer7Panel3Data.anchor ≤
        (observer7Panel3Endpoints.energyUpper : ℝ) ∧
      (observer7Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer7Panel3Data) s observer7Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer7Panel3Data) s observer7Panel3Data.anchor ≤
        (observer7Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer7Panel3Data) s observer7Panel3Data.anchor ≤
        (observer7Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer7Panel3Data) s observer7Panel3Data.anchor ≤
        (observer7Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer7Panel3Data observer7Panel3Endpoints
    observer7_panel3_kernel_check s hs
def observer7Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer7Panel3Endpoints
theorem observer7_panel3_recurrence_field_kernel_check :
    observer7Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer7_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer7Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer7Panel3Endpoints
    observer7_panel3_recurrence_field_kernel_check

def observer7Panel4Data : MainPanelData :=
  {
    observer := 7, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((937978 : ℚ) / 279006525),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer7Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 67619216369938244953126191616, ellLower := 378387856078493225417117047950,
    rhoLower := 99952711184686478258044345472502, rhoUpper := 99952811137447639316773736118123,
    offsetLower := 8432812670704301559500923100, offsetUpper := 8450674574238331339867387613,
    supportELower := 54729669303854230281580474387, supportEUpper := 56208874251638271956633256372,
    supportLambdaLower := 378387856078493225417117047950,
    supportLambdaUpper := 387343554048447851686200490233,
    supportJLower := 58513547864639162535751644866, supportJUpper := 60082309792122750473495261275,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer7Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer7Panel4Data observer7Panel4Endpoints
theorem observer7_panel4_kernel_check : observer7Panel4Check = true := by
  decide +kernel
theorem observer7_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer7Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer7Panel4Data) s observer7Panel4Data.anchor ≤
        (observer7Panel4Endpoints.energyUpper : ℝ) ∧
      (observer7Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer7Panel4Data) s observer7Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer7Panel4Data) s observer7Panel4Data.anchor ≤
        (observer7Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer7Panel4Data) s observer7Panel4Data.anchor ≤
        (observer7Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer7Panel4Data) s observer7Panel4Data.anchor ≤
        (observer7Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer7Panel4Data observer7Panel4Endpoints
    observer7_panel4_kernel_check s hs
def observer7Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer7Panel4Endpoints
theorem observer7_panel4_recurrence_field_kernel_check :
    observer7Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer7_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer7Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer7Panel4Endpoints
    observer7_panel4_recurrence_field_kernel_check

def observer7Panel5Data : MainPanelData :=
  {
    observer := 7, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((937978 : ℚ) / 279006525),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer7Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 69406706121714883788086918015, ellLower := 377994338941628450662179592035,
    rhoLower := 99952711184686478258044345472502, rhoUpper := 99952811137447639316773736118123,
    offsetLower := 8664742240744163360346278589, offsetUpper := 8683095404284612211300295647,
    supportELower := 56208794253590363537049471930, supportEUpper := 57682346870903588597567566002,
    supportLambdaLower := 377994338941628450662179592035,
    supportLambdaUpper := 386659807759927019035268032259,
    supportJLower := 59988737643006648043671267850, supportJUpper := 61548944948502858787920246325,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer7Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer7Panel5Data observer7Panel5Endpoints
theorem observer7_panel5_kernel_check : observer7Panel5Check = true := by
  decide +kernel
theorem observer7_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer7Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer7Panel5Data) s observer7Panel5Data.anchor ≤
        (observer7Panel5Endpoints.energyUpper : ℝ) ∧
      (observer7Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer7Panel5Data) s observer7Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer7Panel5Data) s observer7Panel5Data.anchor ≤
        (observer7Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer7Panel5Data) s observer7Panel5Data.anchor ≤
        (observer7Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer7Panel5Data) s observer7Panel5Data.anchor ≤
        (observer7Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer7Panel5Data observer7Panel5Endpoints
    observer7_panel5_kernel_check s hs
def observer7Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer7Panel5Endpoints
theorem observer7_panel5_recurrence_field_kernel_check :
    observer7Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer7_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer7Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer7Panel5Endpoints
    observer7_panel5_recurrence_field_kernel_check

def observer7Panel6Data : MainPanelData :=
  {
    observer := 7, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((937978 : ℚ) / 279006525),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer7Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 71189629390713821160824512714, ellLower := 377613720397376167273430994159,
    rhoLower := 99952711184686478258044345472502, rhoUpper := 99952811137447639316773736118123,
    offsetLower := 8896280656689913191675954528, offsetUpper := 8915124251716455950429645609,
    supportELower := 57682261783472792280974038494, supportEUpper := 59151258775944765337844124642,
    supportLambdaLower := 377613720397376167273430994159,
    supportLambdaUpper := 386007233549385531472808540844,
    supportJLower := 61458398987446553953708348435, supportJUpper := 63011331111438620652572210051,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer7Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer7Panel6Data observer7Panel6Endpoints
theorem observer7_panel6_kernel_check : observer7Panel6Check = true := by
  decide +kernel
theorem observer7_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer7Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer7Panel6Data) s observer7Panel6Data.anchor ≤
        (observer7Panel6Endpoints.energyUpper : ℝ) ∧
      (observer7Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer7Panel6Data) s observer7Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer7Panel6Data) s observer7Panel6Data.anchor ≤
        (observer7Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer7Panel6Data) s observer7Panel6Data.anchor ≤
        (observer7Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer7Panel6Data) s observer7Panel6Data.anchor ≤
        (observer7Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer7Panel6Data observer7Panel6Endpoints
    observer7_panel6_kernel_check s hs
def observer7Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer7Panel6Endpoints
theorem observer7_panel6_recurrence_field_kernel_check :
    observer7Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer7_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer7Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer7Panel6Endpoints
    observer7_panel6_recurrence_field_kernel_check

def observer7Panel7Data : MainPanelData :=
  {
    observer := 7, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((937978 : ℚ) / 279006525),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer7Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 72968926499252875560774354439, ellLower := 377245418438894427923404881107,
    rhoLower := 99952811137447639316773736118121, rhoUpper := 99952911090308753186640582732460,
    offsetLower := 9108201245781615741074821758, offsetUpper := 9127534689263022480394384039,
    supportELower := 59151168610694590537783922190, supportEUpper := 60616332677644629779787795214,
    supportLambdaLower := 377245418438894427923404881107,
    supportLambdaUpper := 385383539161829396983358745094,
    supportJLower := 62923622795083534817017971001, supportJUpper := 64470168069262923749621382665,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer7Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer7Panel7Data observer7Panel7Endpoints
theorem observer7_panel7_kernel_check : observer7Panel7Check = true := by
  decide +kernel
theorem observer7_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer7Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer7Panel7Data) s observer7Panel7Data.anchor ≤
        (observer7Panel7Endpoints.energyUpper : ℝ) ∧
      (observer7Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer7Panel7Data) s observer7Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer7Panel7Data) s observer7Panel7Data.anchor ≤
        (observer7Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer7Panel7Data) s observer7Panel7Data.anchor ≤
        (observer7Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer7Panel7Data) s observer7Panel7Data.anchor ≤
        (observer7Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer7Panel7Data observer7Panel7Endpoints
    observer7_panel7_kernel_check s hs
def observer7Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer7Panel7Endpoints
theorem observer7_panel7_recurrence_field_kernel_check :
    observer7Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer7_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer7Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer7Panel7Endpoints
    observer7_panel7_recurrence_field_kernel_check

def observer7InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 7, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer7Panel0Endpoints, observer7Panel1Endpoints, observer7Panel2Endpoints, observer7Panel3Endpoints, observer7Panel4Endpoints, observer7Panel5Endpoints, observer7Panel6Endpoints, observer7Panel7Endpoints]
  }
def observer7FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer7InsertionEndpoints.frameLower
    observer7InsertionEndpoints.frameUpper
theorem observer7_frame_recurrence_field_kernel_check :
    observer7FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer7_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer7InsertionEndpoints.frameLower
      observer7InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer7InsertionEndpoints.frameLower
    observer7InsertionEndpoints.frameUpper
    observer7_frame_recurrence_field_kernel_check
def observer7RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer7Panel0Endpoints ∧
  panelRecurrenceFields observer7Panel1Endpoints ∧
  panelRecurrenceFields observer7Panel2Endpoints ∧
  panelRecurrenceFields observer7Panel3Endpoints ∧
  panelRecurrenceFields observer7Panel4Endpoints ∧
  panelRecurrenceFields observer7Panel5Endpoints ∧
  panelRecurrenceFields observer7Panel6Endpoints ∧
  panelRecurrenceFields observer7Panel7Endpoints ∧ insertionFrameRecurrenceFields observer7InsertionEndpoints.frameLower
      observer7InsertionEndpoints.frameUpper
theorem observer7_all_recurrence_fields :
    observer7RecurrenceFieldBounds := by
  exact ⟨observer7_panel0_recurrence_fields_sound,
    observer7_panel1_recurrence_fields_sound,
    observer7_panel2_recurrence_fields_sound,
    observer7_panel3_recurrence_fields_sound,
    observer7_panel4_recurrence_fields_sound,
    observer7_panel5_recurrence_fields_sound,
    observer7_panel6_recurrence_fields_sound,
    observer7_panel7_recurrence_fields_sound,
    observer7_frame_recurrence_fields_sound⟩
def observer7PanelFormulaBounds : Prop :=
  panelFormulaBounds observer7Panel0Data observer7Panel0Endpoints ∧
  panelFormulaBounds observer7Panel1Data observer7Panel1Endpoints ∧
  panelFormulaBounds observer7Panel2Data observer7Panel2Endpoints ∧
  panelFormulaBounds observer7Panel3Data observer7Panel3Endpoints ∧
  panelFormulaBounds observer7Panel4Data observer7Panel4Endpoints ∧
  panelFormulaBounds observer7Panel5Data observer7Panel5Endpoints ∧
  panelFormulaBounds observer7Panel6Data observer7Panel6Endpoints ∧
  panelFormulaBounds observer7Panel7Data observer7Panel7Endpoints
theorem observer7_all_panel_formula_bounds : observer7PanelFormulaBounds := by
  exact ⟨observer7_panel0_formula_sound,
    observer7_panel1_formula_sound,
    observer7_panel2_formula_sound,
    observer7_panel3_formula_sound,
    observer7_panel4_formula_sound,
    observer7_panel5_formula_sound,
    observer7_panel6_formula_sound,
    observer7_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
