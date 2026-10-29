module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer2Panel0Data : MainPanelData :=
  {
    observer := 2, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2348204711708936647311 : ℚ) / 5000000000000000000000),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer2Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 252531216462249090968879156679, ellLower := 683799140215751208676207983865,
    rhoLower := 99914536540835120025756934104473, rhoUpper := 99914636455421618145799804341334,
    offsetLower := 31525280577431817840997903628, offsetUpper := 31562179647036865668430041088,
    supportELower := 157140277074320553927882998762, supportEUpper := 159995171971261122388163537585,
    supportLambdaLower := 683799140215751208676207983865,
    supportLambdaUpper := 698569915854264043400039575627,
    supportJLower := 163978268476478066014645078600, supportJUpper := 166980871129803762822163933342,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer2Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer2Panel0Data observer2Panel0Endpoints
theorem observer2_panel0_kernel_check : observer2Panel0Check = true := by
  decide +kernel
theorem observer2_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer2Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer2Panel0Data) s observer2Panel0Data.anchor ≤
        (observer2Panel0Endpoints.energyUpper : ℝ) ∧
      (observer2Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer2Panel0Data) s observer2Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer2Panel0Data) s observer2Panel0Data.anchor ≤
        (observer2Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer2Panel0Data) s observer2Panel0Data.anchor ≤
        (observer2Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer2Panel0Data) s observer2Panel0Data.anchor ≤
        (observer2Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer2Panel0Data observer2Panel0Endpoints
    observer2_panel0_kernel_check s hs
def observer2Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer2Panel0Endpoints
theorem observer2_panel0_recurrence_field_kernel_check :
    observer2Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer2_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer2Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer2Panel0Endpoints
    observer2_panel0_recurrence_field_kernel_check

def observer2Panel1Data : MainPanelData :=
  {
    observer := 2, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2348204711708936647311 : ℚ) / 5000000000000000000000),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer2Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 255539756458758730045827452597, ellLower := 680522118988994581293750522869,
    rhoLower := 99914936199780600724319840283900, rhoUpper := 99915036114766757989672948433857,
    offsetLower := 31904400951064034096920070763, offsetUpper := 31941919571718333132646410764,
    supportELower := 159995000221096299525891774018, supportEUpper := 162721121834579225652489936999,
    supportLambdaLower := 680522118988994581293750522869,
    supportLambdaUpper := 694736661851199416142063921432,
    supportJLower := 166800221410986245338829279246, supportJUpper := 169668488453091219813910576214,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer2Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer2Panel1Data observer2Panel1Endpoints
theorem observer2_panel1_kernel_check : observer2Panel1Check = true := by
  decide +kernel
theorem observer2_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer2Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer2Panel1Data) s observer2Panel1Data.anchor ≤
        (observer2Panel1Endpoints.energyUpper : ℝ) ∧
      (observer2Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer2Panel1Data) s observer2Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer2Panel1Data) s observer2Panel1Data.anchor ≤
        (observer2Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer2Panel1Data) s observer2Panel1Data.anchor ≤
        (observer2Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer2Panel1Data) s observer2Panel1Data.anchor ≤
        (observer2Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer2Panel1Data observer2Panel1Endpoints
    observer2_panel1_kernel_check s hs
def observer2Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer2Panel1Endpoints
theorem observer2_panel1_recurrence_field_kernel_check :
    observer2Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer2_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer2Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer2Panel1Endpoints
    observer2_panel1_recurrence_field_kernel_check

def observer2Panel2Data : MainPanelData :=
  {
    observer := 2, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2348204711708936647311 : ℚ) / 5000000000000000000000),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer2Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 258520907395542771032646363852, ellLower := 677345842354911900908831619759,
    rhoLower := 99915335860324720402081367593554, rhoUpper := 99915435775710538411384492174985,
    offsetLower := 32275417710553950937138167984, offsetUpper := 32313552168004290076844039804,
    supportELower := 162720941198410697168896342702, supportEUpper := 165418200896257956196843269105,
    supportLambdaLower := 677345842354911900908831619759,
    supportLambdaUpper := 691059299391281099548393698459,
    supportJLower := 169494399621959816177984658899, supportJUpper := 172328793890170767192327206090,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer2Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer2Panel2Data observer2Panel2Endpoints
theorem observer2_panel2_kernel_check : observer2Panel2Check = true := by
  decide +kernel
theorem observer2_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer2Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer2Panel2Data) s observer2Panel2Data.anchor ≤
        (observer2Panel2Endpoints.energyUpper : ℝ) ∧
      (observer2Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer2Panel2Data) s observer2Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer2Panel2Data) s observer2Panel2Data.anchor ≤
        (observer2Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer2Panel2Data) s observer2Panel2Data.anchor ≤
        (observer2Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer2Panel2Data) s observer2Panel2Data.anchor ≤
        (observer2Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer2Panel2Data observer2Panel2Endpoints
    observer2_panel2_kernel_check s hs
def observer2Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer2Panel2Endpoints
theorem observer2_panel2_recurrence_field_kernel_check :
    observer2Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer2_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer2Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer2Panel2Endpoints
    observer2_panel2_recurrence_field_kernel_check

def observer2Panel3Data : MainPanelData :=
  {
    observer := 2, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2348204711708936647311 : ℚ) / 5000000000000000000000),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer2Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 261484132435331026097749149828, ellLower := 674280263326025849072816309475,
    rhoLower := 99915735522467485453610221956806, rhoUpper := 99915835438252965805509536059991,
    offsetLower := 32638798148511122989784597201, offsetUpper := 32677545230257295813232395619,
    supportELower := 165418011456144233506003924187, supportEUpper := 168095972776089796866444382838,
    supportLambdaLower := 674280263326025849072816309475,
    supportLambdaUpper := 687527778401456841554815879451,
    supportJLower := 172160814089404491996732087281, supportJUpper := 174971250560104365281992541633,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer2Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer2Panel3Data observer2Panel3Endpoints
theorem observer2_panel3_kernel_check : observer2Panel3Check = true := by
  decide +kernel
theorem observer2_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer2Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer2Panel3Data) s observer2Panel3Data.anchor ≤
        (observer2Panel3Endpoints.energyUpper : ℝ) ∧
      (observer2Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer2Panel3Data) s observer2Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer2Panel3Data) s observer2Panel3Data.anchor ≤
        (observer2Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer2Panel3Data) s observer2Panel3Data.anchor ≤
        (observer2Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer2Panel3Data) s observer2Panel3Data.anchor ≤
        (observer2Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer2Panel3Data observer2Panel3Endpoints
    observer2_panel3_kernel_check s hs
def observer2Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer2Panel3Endpoints
theorem observer2_panel3_recurrence_field_kernel_check :
    observer2Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer2_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer2Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer2Panel3Endpoints
    observer2_panel3_recurrence_field_kernel_check

def observer2Panel4Data : MainPanelData :=
  {
    observer := 2, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2348204711708936647311 : ℚ) / 5000000000000000000000),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer2Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 264433173093070434467510178611, ellLower := 671319847627631213131169126157,
    rhoLower := 99916035270123674115538833538926, rhoUpper := 99916135186208902273500687623010,
    offsetLower := 33034385770075488340892369798, offsetUpper := 33073742758481668737763915947,
    supportELower := 168095774595690152228171838252, supportEUpper := 170758277588184374464236708238,
    supportLambdaLower := 671319847627631213131169126157,
    supportLambdaUpper := 684132234601143601204360634235,
    supportJLower := 174808973071966464359483529513, supportJUpper := 177599599934195810476280314581,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer2Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer2Panel4Data observer2Panel4Endpoints
theorem observer2_panel4_kernel_check : observer2Panel4Check = true := by
  decide +kernel
theorem observer2_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer2Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer2Panel4Data) s observer2Panel4Data.anchor ≤
        (observer2Panel4Endpoints.energyUpper : ℝ) ∧
      (observer2Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer2Panel4Data) s observer2Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer2Panel4Data) s observer2Panel4Data.anchor ≤
        (observer2Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer2Panel4Data) s observer2Panel4Data.anchor ≤
        (observer2Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer2Panel4Data) s observer2Panel4Data.anchor ≤
        (observer2Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer2Panel4Data observer2Panel4Endpoints
    observer2_panel4_kernel_check s hs
def observer2Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer2Panel4Endpoints
theorem observer2_panel4_recurrence_field_kernel_check :
    observer2Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer2_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer2Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer2Panel4Endpoints
    observer2_panel4_recurrence_field_kernel_check

def observer2Panel5Data : MainPanelData :=
  {
    observer := 2, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2348204711708936647311 : ℚ) / 5000000000000000000000),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer2Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 267370262848163717766543082189, ellLower := 668458684921018818265662480962,
    rhoLower := 99916434935064083958168393740399, rhoUpper := 99916534851548977256372627269804,
    offsetLower := 33384409812324745072683397624, offsetUpper := 33424374431577081023796704126,
    supportELower := 170758070723160818987105200568, supportEUpper := 173407199426884214686426108046,
    supportLambdaLower := 668458684921018818265662480962,
    supportLambdaUpper := 680863566700834856835136876337,
    supportJLower := 177442657572371007169761825377, supportJUpper := 180215835093892563254777476810,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer2Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer2Panel5Data observer2Panel5Endpoints
theorem observer2_panel5_kernel_check : observer2Panel5Check = true := by
  decide +kernel
theorem observer2_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer2Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer2Panel5Data) s observer2Panel5Data.anchor ≤
        (observer2Panel5Endpoints.energyUpper : ℝ) ∧
      (observer2Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer2Panel5Data) s observer2Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer2Panel5Data) s observer2Panel5Data.anchor ≤
        (observer2Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer2Panel5Data) s observer2Panel5Data.anchor ≤
        (observer2Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer2Panel5Data) s observer2Panel5Data.anchor ≤
        (observer2Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer2Panel5Data observer2Panel5Endpoints
    observer2_panel5_kernel_check s hs
def observer2Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer2Panel5Endpoints
theorem observer2_panel5_recurrence_field_kernel_check :
    observer2Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer2_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer2Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer2Panel5Endpoints
    observer2_panel5_recurrence_field_kernel_check

def observer2Panel6Data : MainPanelData :=
  {
    observer := 2, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2348204711708936647311 : ℚ) / 5000000000000000000000),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer2Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 270296169667901148861174117230, ellLower := 665691133270542910176193024531,
    rhoLower := 99916734684818513557252351049351, rhoUpper := 99916834601603156759761110835818,
    offsetLower := 33768346177499630325058514098, offsetUpper := 33808916229923047936081487853,
    supportELower := 173406983928064140107671388840, supportEUpper := 176044070004738318193495303699,
    supportLambdaLower := 665691133270542910176193024531,
    supportLambdaUpper := 677713480282850064782757717866,
    supportJLower := 180063895260769569209433319085, supportJUpper := 182821204807566818841322880878,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer2Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer2Panel6Data observer2Panel6Endpoints
theorem observer2_panel6_kernel_check : observer2Panel6Check = true := by
  decide +kernel
theorem observer2_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer2Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer2Panel6Data) s observer2Panel6Data.anchor ≤
        (observer2Panel6Endpoints.energyUpper : ℝ) ∧
      (observer2Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer2Panel6Data) s observer2Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer2Panel6Data) s observer2Panel6Data.anchor ≤
        (observer2Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer2Panel6Data) s observer2Panel6Data.anchor ≤
        (observer2Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer2Panel6Data) s observer2Panel6Data.anchor ≤
        (observer2Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer2Panel6Data observer2Panel6Endpoints
    observer2_panel6_kernel_check s hs
def observer2Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer2Panel6Endpoints
theorem observer2_panel6_recurrence_field_kernel_check :
    observer2Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer2_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer2Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer2Panel6Endpoints
    observer2_panel6_recurrence_field_kernel_check

def observer2Panel7Data : MainPanelData :=
  {
    observer := 2, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((2348204711708936647311 : ℚ) / 5000000000000000000000),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer2Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 273212003128683600943346575526, ellLower := 663011934389825192689016140920,
    rhoLower := 99917134352556587774564697251300, rhoUpper := 99917234269740898914981609998527,
    offsetLower := 34105858102400289396905512552, offsetUpper := 34147031681119875541389912372,
    supportELower := 176043845919485715504856869698, supportEUpper := 178669833780564796955111410858,
    supportLambdaLower := 663011934389825192689016140920,
    supportLambdaUpper := 674674433706972266548325920434,
    supportJLower := 182673965263383967431747031107, supportJUpper := 185416578117634519620594670063,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer2Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer2Panel7Data observer2Panel7Endpoints
theorem observer2_panel7_kernel_check : observer2Panel7Check = true := by
  decide +kernel
theorem observer2_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer2Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer2Panel7Data) s observer2Panel7Data.anchor ≤
        (observer2Panel7Endpoints.energyUpper : ℝ) ∧
      (observer2Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer2Panel7Data) s observer2Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer2Panel7Data) s observer2Panel7Data.anchor ≤
        (observer2Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer2Panel7Data) s observer2Panel7Data.anchor ≤
        (observer2Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer2Panel7Data) s observer2Panel7Data.anchor ≤
        (observer2Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer2Panel7Data observer2Panel7Endpoints
    observer2_panel7_kernel_check s hs
def observer2Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer2Panel7Endpoints
theorem observer2_panel7_recurrence_field_kernel_check :
    observer2Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer2_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer2Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer2Panel7Endpoints
    observer2_panel7_recurrence_field_kernel_check

def observer2InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 2, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer2Panel0Endpoints, observer2Panel1Endpoints, observer2Panel2Endpoints, observer2Panel3Endpoints, observer2Panel4Endpoints, observer2Panel5Endpoints, observer2Panel6Endpoints, observer2Panel7Endpoints]
  }
def observer2FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer2InsertionEndpoints.frameLower
    observer2InsertionEndpoints.frameUpper
theorem observer2_frame_recurrence_field_kernel_check :
    observer2FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer2_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer2InsertionEndpoints.frameLower
      observer2InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer2InsertionEndpoints.frameLower
    observer2InsertionEndpoints.frameUpper
    observer2_frame_recurrence_field_kernel_check
def observer2RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer2Panel0Endpoints ∧
  panelRecurrenceFields observer2Panel1Endpoints ∧
  panelRecurrenceFields observer2Panel2Endpoints ∧
  panelRecurrenceFields observer2Panel3Endpoints ∧
  panelRecurrenceFields observer2Panel4Endpoints ∧
  panelRecurrenceFields observer2Panel5Endpoints ∧
  panelRecurrenceFields observer2Panel6Endpoints ∧
  panelRecurrenceFields observer2Panel7Endpoints ∧ insertionFrameRecurrenceFields observer2InsertionEndpoints.frameLower
      observer2InsertionEndpoints.frameUpper
theorem observer2_all_recurrence_fields :
    observer2RecurrenceFieldBounds := by
  exact ⟨observer2_panel0_recurrence_fields_sound,
    observer2_panel1_recurrence_fields_sound,
    observer2_panel2_recurrence_fields_sound,
    observer2_panel3_recurrence_fields_sound,
    observer2_panel4_recurrence_fields_sound,
    observer2_panel5_recurrence_fields_sound,
    observer2_panel6_recurrence_fields_sound,
    observer2_panel7_recurrence_fields_sound,
    observer2_frame_recurrence_fields_sound⟩
def observer2PanelFormulaBounds : Prop :=
  panelFormulaBounds observer2Panel0Data observer2Panel0Endpoints ∧
  panelFormulaBounds observer2Panel1Data observer2Panel1Endpoints ∧
  panelFormulaBounds observer2Panel2Data observer2Panel2Endpoints ∧
  panelFormulaBounds observer2Panel3Data observer2Panel3Endpoints ∧
  panelFormulaBounds observer2Panel4Data observer2Panel4Endpoints ∧
  panelFormulaBounds observer2Panel5Data observer2Panel5Endpoints ∧
  panelFormulaBounds observer2Panel6Data observer2Panel6Endpoints ∧
  panelFormulaBounds observer2Panel7Data observer2Panel7Endpoints
theorem observer2_all_panel_formula_bounds : observer2PanelFormulaBounds := by
  exact ⟨observer2_panel0_formula_sound,
    observer2_panel1_formula_sound,
    observer2_panel2_formula_sound,
    observer2_panel3_formula_sound,
    observer2_panel4_formula_sound,
    observer2_panel5_formula_sound,
    observer2_panel6_formula_sound,
    observer2_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
