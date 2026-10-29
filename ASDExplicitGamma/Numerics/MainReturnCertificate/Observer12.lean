module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
import Mathlib.Tactic.NormNum

/- Generated data (exact rationals), checked by kernel reduction. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics

def observer12Panel0Data : MainPanelData :=
  {
    observer := 12, panel := 0, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((227987944 : ℚ) / 16475056294725),
    time := ⟨((0 : ℚ) / 1), ((1 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer12Panel0Endpoints : PanelEndpoints :=
  {
    aUpper := 50064124158261048552294292317, ellLower := 353820781182972037912676035895,
    rhoLower := 99955709811001188676074757351146, rhoUpper := 99955809766760977548828223153566,
    offsetLower := 6252728616064130458831817627, offsetUpper := 6266871927691198548287883256,
    supportELower := 39208857176778763009901490493, supportEUpper := 40741782393982459327033048965,
    supportLambdaLower := 353820781182972037912676035895,
    supportLambdaUpper := 363803475089960847935858973835,
    supportJLower := 42747064988608483389028250851, supportJUpper := 44379817144882067806391638704,
    inverseAbsoluteUpper := 136705950999044221999686347
  }
def observer12Panel0Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer12Panel0Data observer12Panel0Endpoints
theorem observer12_panel0_kernel_check : observer12Panel0Check = true := by
  decide +kernel
theorem observer12_panel0_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer12Panel0Data.time s) :
    panelEnergyReal (mainPanelRealData observer12Panel0Data) s observer12Panel0Data.anchor ≤
        (observer12Panel0Endpoints.energyUpper : ℝ) ∧
      (observer12Panel0Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer12Panel0Data) s observer12Panel0Data.anchor ∧
      panelSupportReal (mainPanelRealData observer12Panel0Data) s observer12Panel0Data.anchor ≤
        (observer12Panel0Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer12Panel0Data) s observer12Panel0Data.anchor ≤
        (observer12Panel0Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer12Panel0Data) s observer12Panel0Data.anchor ≤
        (observer12Panel0Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer12Panel0Data observer12Panel0Endpoints
    observer12_panel0_kernel_check s hs
def observer12Panel0RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer12Panel0Endpoints
theorem observer12_panel0_recurrence_field_kernel_check :
    observer12Panel0RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer12_panel0_recurrence_fields_sound :
    panelRecurrenceFields observer12Panel0Endpoints := by
  exact panelRecurrenceFields_sound observer12Panel0Endpoints
    observer12_panel0_recurrence_field_kernel_check

def observer12Panel1Data : MainPanelData :=
  {
    observer := 12, panel := 1, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((227987944 : ℚ) / 16475056294725),
    time := ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer12Panel1Endpoints : PanelEndpoints :=
  {
    aUpper := 51792983904949286161812949190, ellLower := 353637259565315817050616147701,
    rhoLower := 99955709811001188676074757351146, rhoUpper := 99955809766760977548828223153566,
    offsetLower := 6472010448553767634680306252, offsetUpper := 6486649763043184111993502204,
    supportELower := 40741732647592367295584049898, supportEUpper := 42155470442775741459386251443,
    supportLambdaLower := 353637259565315817050616147701,
    supportLambdaUpper := 363228377557238187132239108713,
    supportJLower := 44278105243245525466090211375, supportJUpper := 45787754218348123330708642531,
    inverseAbsoluteUpper := 273093512578960441121838910
  }
def observer12Panel1Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer12Panel1Data observer12Panel1Endpoints
theorem observer12_panel1_kernel_check : observer12Panel1Check = true := by
  decide +kernel
theorem observer12_panel1_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer12Panel1Data.time s) :
    panelEnergyReal (mainPanelRealData observer12Panel1Data) s observer12Panel1Data.anchor ≤
        (observer12Panel1Endpoints.energyUpper : ℝ) ∧
      (observer12Panel1Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer12Panel1Data) s observer12Panel1Data.anchor ∧
      panelSupportReal (mainPanelRealData observer12Panel1Data) s observer12Panel1Data.anchor ≤
        (observer12Panel1Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer12Panel1Data) s observer12Panel1Data.anchor ≤
        (observer12Panel1Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer12Panel1Data) s observer12Panel1Data.anchor ≤
        (observer12Panel1Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer12Panel1Data observer12Panel1Endpoints
    observer12_panel1_kernel_check s hs
def observer12Panel1RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer12Panel1Endpoints
theorem observer12_panel1_recurrence_field_kernel_check :
    observer12Panel1RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer12_panel1_recurrence_fields_sound :
    panelRecurrenceFields observer12Panel1Endpoints := by
  exact panelRecurrenceFields_sound observer12Panel1Endpoints
    observer12_panel1_recurrence_field_kernel_check

def observer12Panel2Data : MainPanelData :=
  {
    observer := 12, panel := 2, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((227987944 : ℚ) / 16475056294725),
    time := ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer12Panel2Endpoints : PanelEndpoints :=
  {
    aUpper := 53502470769197678426792101017, ellLower := 353440798182664582846314978647,
    rhoLower := 99955809766760977548828223153564, rhoUpper := 99955909722620722231348458263183,
    offsetLower := 6674211887308731998892366618, offsetUpper := 6689342810200763313684199287,
    supportELower := 42155415834209940822697375455, supportEUpper := 43549548416807087128461279822,
    supportLambdaLower := 353440798182664582846314978647,
    supportLambdaUpper := 362684716608493485882423315680,
    supportJLower := 45689823816036586651160525241, supportJUpper := 47176395582892021987285512979,
    inverseAbsoluteUpper := 409403900641188183444619805
  }
def observer12Panel2Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer12Panel2Data observer12Panel2Endpoints
theorem observer12_panel2_kernel_check : observer12Panel2Check = true := by
  decide +kernel
theorem observer12_panel2_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer12Panel2Data.time s) :
    panelEnergyReal (mainPanelRealData observer12Panel2Data) s observer12Panel2Data.anchor ≤
        (observer12Panel2Endpoints.energyUpper : ℝ) ∧
      (observer12Panel2Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer12Panel2Data) s observer12Panel2Data.anchor ∧
      panelSupportReal (mainPanelRealData observer12Panel2Data) s observer12Panel2Data.anchor ≤
        (observer12Panel2Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer12Panel2Data) s observer12Panel2Data.anchor ≤
        (observer12Panel2Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer12Panel2Data) s observer12Panel2Data.anchor ≤
        (observer12Panel2Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer12Panel2Data observer12Panel2Endpoints
    observer12_panel2_kernel_check s hs
def observer12Panel2RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer12Panel2Endpoints
theorem observer12_panel2_recurrence_field_kernel_check :
    observer12Panel2RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer12_panel2_recurrence_fields_sound :
    panelRecurrenceFields observer12Panel2Endpoints := by
  exact panelRecurrenceFields_sound observer12Panel2Endpoints
    observer12_panel2_recurrence_field_kernel_check

def observer12Panel3Data : MainPanelData :=
  {
    observer := 12, panel := 3, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((227987944 : ℚ) / 16475056294725),
    time := ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer12Panel3Endpoints : PanelEndpoints :=
  {
    aUpper := 55201825879742196859973585634, ellLower := 353248863676382192640991840803,
    rhoLower := 99955809766760977548828223153564, rhoUpper := 99955909722620722231348458263183,
    offsetLower := 6889940959895443795620244065, offsetUpper := 6905560956256821494988632513,
    supportELower := 43549488981888051517406152450, supportEUpper := 44933272146179326478943618323,
    supportLambdaLower := 353248863676382192640991840803,
    supportLambdaUpper := 362171017740255696608592883966,
    supportJLower := 47081977618651873443816070858, supportJUpper := 48554982323581883445029547163,
    inverseAbsoluteUpper := 545637158853579292802569754
  }
def observer12Panel3Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer12Panel3Data observer12Panel3Endpoints
theorem observer12_panel3_kernel_check : observer12Panel3Check = true := by
  decide +kernel
theorem observer12_panel3_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer12Panel3Data.time s) :
    panelEnergyReal (mainPanelRealData observer12Panel3Data) s observer12Panel3Data.anchor ≤
        (observer12Panel3Endpoints.energyUpper : ℝ) ∧
      (observer12Panel3Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer12Panel3Data) s observer12Panel3Data.anchor ∧
      panelSupportReal (mainPanelRealData observer12Panel3Data) s observer12Panel3Data.anchor ≤
        (observer12Panel3Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer12Panel3Data) s observer12Panel3Data.anchor ≤
        (observer12Panel3Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer12Panel3Data) s observer12Panel3Data.anchor ≤
        (observer12Panel3Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer12Panel3Data observer12Panel3Endpoints
    observer12_panel3_kernel_check s hs
def observer12Panel3RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer12Panel3Endpoints
theorem observer12_panel3_recurrence_field_kernel_check :
    observer12Panel3RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer12_panel3_recurrence_fields_sound :
    panelRecurrenceFields observer12Panel3Endpoints := by
  exact panelRecurrenceFields_sound observer12Panel3Endpoints
    observer12_panel3_recurrence_field_kernel_check

def observer12Panel4Data : MainPanelData :=
  {
    observer := 12, panel := 4, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((227987944 : ℚ) / 16475056294725),
    time := ⟨((1 : ℚ) / 2), ((5 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer12Panel4Endpoints : PanelEndpoints :=
  {
    aUpper := 56894579208854362363355314819, ellLower := 353062697316048558816901457502,
    rhoLower := 99955809766760977548828223153564, rhoUpper := 99955909722620722231348458263183,
    offsetLower := 7104964069455814204478289509, offsetUpper := 7121071538817105109563821424,
    supportELower := 44933207904384130051861300669, supportEUpper := 46310193226694620377037696335,
    supportLambdaLower := 353062697316048558816901457502,
    supportLambdaUpper := 361685114235146539590032417795,
    supportJLower := 48463834877544615640030315244, supportJUpper := 49927044369046085772938020513,
    inverseAbsoluteUpper := 681793330859276602196325106
  }
def observer12Panel4Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer12Panel4Data observer12Panel4Endpoints
theorem observer12_panel4_kernel_check : observer12Panel4Check = true := by
  decide +kernel
theorem observer12_panel4_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer12Panel4Data.time s) :
    panelEnergyReal (mainPanelRealData observer12Panel4Data) s observer12Panel4Data.anchor ≤
        (observer12Panel4Endpoints.energyUpper : ℝ) ∧
      (observer12Panel4Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer12Panel4Data) s observer12Panel4Data.anchor ∧
      panelSupportReal (mainPanelRealData observer12Panel4Data) s observer12Panel4Data.anchor ≤
        (observer12Panel4Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer12Panel4Data) s observer12Panel4Data.anchor ≤
        (observer12Panel4Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer12Panel4Data) s observer12Panel4Data.anchor ≤
        (observer12Panel4Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer12Panel4Data observer12Panel4Endpoints
    observer12_panel4_kernel_check s hs
def observer12Panel4RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer12Panel4Endpoints
theorem observer12_panel4_recurrence_field_kernel_check :
    observer12Panel4RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer12_panel4_recurrence_fields_sound :
    panelRecurrenceFields observer12Panel4Endpoints := by
  exact panelRecurrenceFields_sound observer12Panel4Endpoints
    observer12_panel4_recurrence_field_kernel_check

def observer12Panel5Data : MainPanelData :=
  {
    observer := 12, panel := 5, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((227987944 : ℚ) / 16475056294725),
    time := ⟨((5 : ℚ) / 8), ((3 : ℚ) / 4), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer12Panel5Endpoints : PanelEndpoints :=
  {
    aUpper := 58582762520658761816813257839, ellLower := 352882522588571930476824748136,
    rhoLower := 99955809766760977548828223153564, rhoUpper := 99955909722620722231348458263183,
    offsetLower := 7319518774217271055879958087, offsetUpper := 7336112654670790141664733010,
    supportELower := 46310124191399826465666053905, supportEUpper := 47682124650009402927970627587,
    supportLambdaLower := 352882522588571930476824748136,
    supportLambdaUpper := 361224843544455177788959459668,
    supportJLower := 49838949417285545770434301386, supportJUpper := 51294373085453954705860222184,
    inverseAbsoluteUpper := 818112814613541256652565971
  }
def observer12Panel5Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer12Panel5Data observer12Panel5Endpoints
theorem observer12_panel5_kernel_check : observer12Panel5Check = true := by
  decide +kernel
theorem observer12_panel5_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer12Panel5Data.time s) :
    panelEnergyReal (mainPanelRealData observer12Panel5Data) s observer12Panel5Data.anchor ≤
        (observer12Panel5Endpoints.energyUpper : ℝ) ∧
      (observer12Panel5Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer12Panel5Data) s observer12Panel5Data.anchor ∧
      panelSupportReal (mainPanelRealData observer12Panel5Data) s observer12Panel5Data.anchor ≤
        (observer12Panel5Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer12Panel5Data) s observer12Panel5Data.anchor ≤
        (observer12Panel5Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer12Panel5Data) s observer12Panel5Data.anchor ≤
        (observer12Panel5Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer12Panel5Data observer12Panel5Endpoints
    observer12_panel5_kernel_check s hs
def observer12Panel5RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer12Panel5Endpoints
theorem observer12_panel5_recurrence_field_kernel_check :
    observer12Panel5RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer12_panel5_recurrence_fields_sound :
    panelRecurrenceFields observer12Panel5Endpoints := by
  exact panelRecurrenceFields_sound observer12Panel5Endpoints
    observer12_panel5_recurrence_field_kernel_check

def observer12Panel6Data : MainPanelData :=
  {
    observer := 12, panel := 6, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((227987944 : ℚ) / 16475056294725),
    time := ⟨((3 : ℚ) / 4), ((7 : ℚ) / 8), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer12Panel6Endpoints : PanelEndpoints :=
  {
    aUpper := 60266951273209519891890830315, ellLower := 352708270508436914091523206834,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 7516587443965439771978952725, offsetUpper := 7533666830689370845246147042,
    supportELower := 47682050831514287557788218019, supportEUpper := 49050142827416359772955568158,
    supportLambdaLower := 352708270508436914091523206834,
    supportLambdaUpper := 360788190452517749989659552821,
    supportJLower := 51209133536598656698703450087, supportJUpper := 52658024731941537272852163687,
    inverseAbsoluteUpper := 954114809034450898658696460
  }
def observer12Panel6Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer12Panel6Data observer12Panel6Endpoints
theorem observer12_panel6_kernel_check : observer12Panel6Check = true := by
  decide +kernel
theorem observer12_panel6_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer12Panel6Data.time s) :
    panelEnergyReal (mainPanelRealData observer12Panel6Data) s observer12Panel6Data.anchor ≤
        (observer12Panel6Endpoints.energyUpper : ℝ) ∧
      (observer12Panel6Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer12Panel6Data) s observer12Panel6Data.anchor ∧
      panelSupportReal (mainPanelRealData observer12Panel6Data) s observer12Panel6Data.anchor ≤
        (observer12Panel6Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer12Panel6Data) s observer12Panel6Data.anchor ≤
        (observer12Panel6Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer12Panel6Data) s observer12Panel6Data.anchor ≤
        (observer12Panel6Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer12Panel6Data observer12Panel6Endpoints
    observer12_panel6_kernel_check s hs
def observer12Panel6RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer12Panel6Endpoints
theorem observer12_panel6_recurrence_field_kernel_check :
    observer12Panel6RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer12_panel6_recurrence_fields_sound :
    panelRecurrenceFields observer12Panel6Endpoints := by
  exact panelRecurrenceFields_sound observer12Panel6Endpoints
    observer12_panel6_recurrence_field_kernel_check

def observer12Panel7Data : MainPanelData :=
  {
    observer := 12, panel := 7, panelCount := 8,
    initialMean := ((4441091003104432097305984305313 : ℚ) / 50000000000000000000000000000000),
    initialInverseMean := ((9240579435271425137263891132441267185379583782928353095239921303296091633731282783113124901177485456563246097474115925217548933589624222538138015412077983011426407537713730259634961888092342636026172657180496146012153707097777057 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    covarianceCap := ((227987944 : ℚ) / 16475056294725),
    time := ⟨((7 : ℚ) / 8), ((1 : ℚ) / 1), by norm_num⟩,
    anchor := ((1 : ℚ) / 100)
  }
def observer12Panel7Endpoints : PanelEndpoints :=
  {
    aUpper := 61948071160836358036193286616, ellLower := 352539763119030514213989013268,
    rhoLower := 99955909722620722231348458263181, rhoUpper := 99956009678580422823591322424692,
    offsetLower := 7729952325315231462213040111, offsetUpper := 7747516525307024455414983231,
    supportELower := 49050064234189758427355295061, supportEUpper := 50414951306301593427512114753,
    supportLambdaLower := 352539763119030514213989013268,
    supportLambdaUpper := 360373316255203068674183612400,
    supportJLower := 52575461865380063569495185193, supportJUpper := 54018684468853624114253950877,
    inverseAbsoluteUpper := 1090039848106936335479865088
  }
def observer12Panel7Check : Bool := mainPanelCheck mainReturnGridDigits
  mainReturnTaylorDegree mainReturnTaylorDegree_ge observer12Panel7Data observer12Panel7Endpoints
theorem observer12_panel7_kernel_check : observer12Panel7Check = true := by
  decide +kernel
theorem observer12_panel7_formula_sound (s : ℝ)
    (hs : QInterval.Contains observer12Panel7Data.time s) :
    panelEnergyReal (mainPanelRealData observer12Panel7Data) s observer12Panel7Data.anchor ≤
        (observer12Panel7Endpoints.energyUpper : ℝ) ∧
      (observer12Panel7Endpoints.lambdaLower : ℝ) ≤
        panelLambdaReal (mainPanelRealData observer12Panel7Data) s observer12Panel7Data.anchor ∧
      panelSupportReal (mainPanelRealData observer12Panel7Data) s observer12Panel7Data.anchor ≤
        (observer12Panel7Endpoints.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData observer12Panel7Data) s observer12Panel7Data.anchor ≤
        (observer12Panel7Endpoints.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData observer12Panel7Data) s observer12Panel7Data.anchor ≤
        (observer12Panel7Endpoints.generatorUpper : ℝ) := by
  exact mainPanel_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge observer12Panel7Data observer12Panel7Endpoints
    observer12_panel7_kernel_check s hs
def observer12Panel7RecurrenceFieldCheck : Bool :=
  panelRecurrenceFieldGridCheck observer12Panel7Endpoints
theorem observer12_panel7_recurrence_field_kernel_check :
    observer12Panel7RecurrenceFieldCheck = true := by
  decide +kernel
theorem observer12_panel7_recurrence_fields_sound :
    panelRecurrenceFields observer12Panel7Endpoints := by
  exact panelRecurrenceFields_sound observer12Panel7Endpoints
    observer12_panel7_recurrence_field_kernel_check

def observer12InsertionEndpoints : MainInsertionEndpoints :=
  {
    observer := 12, frameLower := 100074727907398509635704814393512, frameUpper := 100074827982176454414847274840827,
    panels := [observer12Panel0Endpoints, observer12Panel1Endpoints, observer12Panel2Endpoints, observer12Panel3Endpoints, observer12Panel4Endpoints, observer12Panel5Endpoints, observer12Panel6Endpoints, observer12Panel7Endpoints]
  }
def observer12FrameRecurrenceFieldCheck : Bool :=
  insertionFrameRecurrenceFieldGridCheck
    observer12InsertionEndpoints.frameLower
    observer12InsertionEndpoints.frameUpper
theorem observer12_frame_recurrence_field_kernel_check :
    observer12FrameRecurrenceFieldCheck = true := by
  decide +kernel
theorem observer12_frame_recurrence_fields_sound :
    insertionFrameRecurrenceFields
      observer12InsertionEndpoints.frameLower
      observer12InsertionEndpoints.frameUpper := by
  exact insertionFrameRecurrenceFields_sound
    observer12InsertionEndpoints.frameLower
    observer12InsertionEndpoints.frameUpper
    observer12_frame_recurrence_field_kernel_check
def observer12RecurrenceFieldBounds : Prop :=
  panelRecurrenceFields observer12Panel0Endpoints ∧
  panelRecurrenceFields observer12Panel1Endpoints ∧
  panelRecurrenceFields observer12Panel2Endpoints ∧
  panelRecurrenceFields observer12Panel3Endpoints ∧
  panelRecurrenceFields observer12Panel4Endpoints ∧
  panelRecurrenceFields observer12Panel5Endpoints ∧
  panelRecurrenceFields observer12Panel6Endpoints ∧
  panelRecurrenceFields observer12Panel7Endpoints ∧ insertionFrameRecurrenceFields observer12InsertionEndpoints.frameLower
      observer12InsertionEndpoints.frameUpper
theorem observer12_all_recurrence_fields :
    observer12RecurrenceFieldBounds := by
  exact ⟨observer12_panel0_recurrence_fields_sound,
    observer12_panel1_recurrence_fields_sound,
    observer12_panel2_recurrence_fields_sound,
    observer12_panel3_recurrence_fields_sound,
    observer12_panel4_recurrence_fields_sound,
    observer12_panel5_recurrence_fields_sound,
    observer12_panel6_recurrence_fields_sound,
    observer12_panel7_recurrence_fields_sound,
    observer12_frame_recurrence_fields_sound⟩
def observer12PanelFormulaBounds : Prop :=
  panelFormulaBounds observer12Panel0Data observer12Panel0Endpoints ∧
  panelFormulaBounds observer12Panel1Data observer12Panel1Endpoints ∧
  panelFormulaBounds observer12Panel2Data observer12Panel2Endpoints ∧
  panelFormulaBounds observer12Panel3Data observer12Panel3Endpoints ∧
  panelFormulaBounds observer12Panel4Data observer12Panel4Endpoints ∧
  panelFormulaBounds observer12Panel5Data observer12Panel5Endpoints ∧
  panelFormulaBounds observer12Panel6Data observer12Panel6Endpoints ∧
  panelFormulaBounds observer12Panel7Data observer12Panel7Endpoints
theorem observer12_all_panel_formula_bounds : observer12PanelFormulaBounds := by
  exact ⟨observer12_panel0_formula_sound,
    observer12_panel1_formula_sound,
    observer12_panel2_formula_sound,
    observer12_panel3_formula_sound,
    observer12_panel4_formula_sound,
    observer12_panel5_formula_sound,
    observer12_panel6_formula_sound,
    observer12_panel7_formula_sound⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
