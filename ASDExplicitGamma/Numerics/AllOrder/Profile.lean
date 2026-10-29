module
public import ASDExplicitGamma.Numerics.Scalar.Factors
/-! Positive all-order profile formulas, independently transcribed.
Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.AllOrder
open Mirror Scalar
local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.divPos
local prefix:max "√ₑ " => Expr.sqrt

def aoM2Expr : Expr := sc (745121/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

def aoM4Expr : Expr := sc (410669803453/78125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

def aoM8Expr : Expr := sc (24951866313321747046169/1525878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

def aoLayer2Expr : Expr := (((((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) /ₑ (sc (3/1) -ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))) -ₑ sc (1/2)) *ₑ sc (4/1)) +ₑ sc (1/1))

def aoLayer4Expr : Expr := (((((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/62500))) /ₑ (sc (3/1) -ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/62500))))) -ₑ sc (1/2)) *ₑ sc (4/1)) +ₑ sc (1/1))

def aoLayerFExpr : Expr := ((((((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/62500))) *ₑ sc (3/1)) /ₑ ((sc (3/1) -ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/62500)))) *ₑ (sc (3/1) -ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/62500)))))) -ₑ sc (3/4)) *ₑ sc (8/1)) +ₑ sc (332/91))

def aoLayerRootExpr : Expr := (√ₑ (sc (1/3)))

def aoL0Expr : Expr := (((((aoLayerRootExpr *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))) +ₑ ((aoLayerRootExpr *ₑ aoLayerRootExpr) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))))) +ₑ ((aoLayerRootExpr *ₑ (aoLayerRootExpr *ₑ aoLayerRootExpr)) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000)))))))) *ₑ sc (2/1)) /ₑ (sc (1/1) -ₑ ((aoLayerRootExpr *ₑ (aoLayerRootExpr *ₑ aoLayerRootExpr)) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000)))))))))

def aoL1Expr : Expr := (((((((aoLayerRootExpr *ₑ sc (2/1)) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))) +ₑ (((aoLayerRootExpr *ₑ sc (3/1)) *ₑ aoLayerRootExpr) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))))) +ₑ (((aoLayerRootExpr *ₑ (aoLayerRootExpr *ₑ aoLayerRootExpr)) *ₑ sc (4/1)) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000)))))))) /ₑ (sc (1/1) -ₑ ((aoLayerRootExpr *ₑ (aoLayerRootExpr *ₑ aoLayerRootExpr)) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))))))) +ₑ (((((aoLayerRootExpr *ₑ (aoLayerRootExpr *ₑ aoLayerRootExpr)) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))))) *ₑ sc (4/1)) *ₑ (((aoLayerRootExpr *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))) +ₑ ((aoLayerRootExpr *ₑ aoLayerRootExpr) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))))) +ₑ ((aoLayerRootExpr *ₑ (aoLayerRootExpr *ₑ aoLayerRootExpr)) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))))))) /ₑ ((sc (1/1) -ₑ ((aoLayerRootExpr *ₑ (aoLayerRootExpr *ₑ aoLayerRootExpr)) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000)))))))) *ₑ (sc (1/1) -ₑ ((aoLayerRootExpr *ₑ (aoLayerRootExpr *ₑ aoLayerRootExpr)) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))) *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))))))))) *ₑ sc (2/1))

def aoSelectedJExpr : Expr := ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (1309/5000))) +ₑ sc (1/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))

def aoSelectedWExpr : Expr := ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (1309/2500))) *ₑ sc (5408/1))

def aoSelectedW0Expr : Expr := (aoSelectedWExpr +ₑ sc (1/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))

def aoSelectedW1Expr : Expr := ((aoSelectedWExpr *ₑ sc (350/1)) +ₑ sc (351/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))

def aoMatrixTailExpr : Expr := sc (5000/67125992532455863755629045325581276555227009699224616404106338356890144017629760561667011043586030096312919426721924316850251754956410091202388857096062798535890307)

def aoDensityTailExpr : Expr := sc (10000/26772935819801760271150833780932880665223648984015226879590194295065041791748710249)

def aoVarianceTailExpr : Expr := ((√ₑ ((aoM8Expr *ₑ sc (254016/1)))) *ₑ sc (4/1))

def aoFourthTailExpr : Expr := ((((((√ₑ (aoVarianceTailExpr)) *ₑ sc (1/77355401014542844188348446843727534965514746256921793516785161121)) /ₑ sc (49/400)) +ₑ (((√ₑ (sc (21069103104/1))) *ₑ sc (1/15926791088519786003064148590679881418931379526481396121112548658575277686941529)) /ₑ sc (1681/10000))) +ₑ sc (2500/22375330844151954585209681775193758851742336566408205468035446118963381339209920187222337014528676698770973142240641438950083918318803363734129619032020932845296769)) *ₑ sc (3591754554768605936580822008015114131704309/1))

def aoSensitivityExpr : Expr := (sc (1/1) /ₑ (sc (1/1) -ₑ sc (4361/18500)))

def aoMatrixErrorExpr : Expr := ((((aoSensitivityExpr *ₑ sc (80/1)) *ₑ sc (66/1)) *ₑ sc (6808576000000001183744/289)) *ₑ aoMatrixTailExpr)

def aoDensityErrorExpr : Expr := ((((aoSensitivityExpr *ₑ sc (40/1)) *ₑ sc (130/1)) *ₑ sc (19947000000000000578/289)) *ₑ aoFourthTailExpr)

def aoInverseRootExpr : Expr := (aoSensitivityExpr *ₑ ((((((aoM2Expr *ₑ sc (23881576034656461564337263083377237642940324085245322708363534/289)) +ₑ sc (29/25)) *ₑ aoLayer2Expr) *ₑ aoSelectedJExpr) +ₑ (aoMatrixTailExpr *ₑ sc (6808576000000001183744/289))) +ₑ (aoDensityTailExpr *ₑ sc (71644728103969384693011789250131712928820972255735968125090602/289))))

def aoTraceRootExpr : Expr := (aoSensitivityExpr *ₑ ((((((aoM2Expr *ₑ sc (90335637869348442439556340083511929899924289432629361466649578512094225387138291459179816834667579726/1093185780802562880124157800500033044331961)) +ₑ sc (29/25)) *ₑ aoLayer2Expr) *ₑ aoSelectedJExpr) +ₑ (aoMatrixTailExpr *ₑ sc (13617152000000002367488/289))) +ₑ (aoDensityTailExpr *ₑ sc (271006913608045327318669020250535789699772868297888084399948735536282676161414874377539450504002739178/1093185780802562880124157800500033044331961))))

def aoWaveSlopeExpr : Expr := (((aoSensitivityExpr *ₑ (((aoSelectedW0Expr *ₑ sc (29/100)) *ₑ aoLayer4Expr) +ₑ ((((√ₑ (aoM4Expr)) *ₑ sc (23881576034656461564337263083377237642940324085245322708363534/289)) *ₑ aoSelectedW0Expr) *ₑ aoL0Expr))) +ₑ aoMatrixErrorExpr) +ₑ aoDensityErrorExpr)

def aoWaveOffsetExpr : Expr := ((aoSensitivityExpr *ₑ ((((aoSelectedW0Expr *ₑ aoLayerFExpr) +ₑ (aoSelectedW1Expr *ₑ aoLayer4Expr)) *ₑ sc (29/100)) +ₑ (((√ₑ (aoM4Expr)) *ₑ sc (23881576034656461564337263083377237642940324085245322708363534/289)) *ₑ ((aoSelectedW0Expr *ₑ aoL1Expr) +ₑ (aoSelectedW1Expr *ₑ aoL0Expr))))) +ₑ ((aoMatrixErrorExpr +ₑ aoDensityErrorExpr) *ₑ sc (350/1)))

def aoActiveDensityExpr : Expr := ((√ₑ (aoM4Expr)) *ₑ sc (23881576034656461564337263083377237642940324085245322708363534/289))

def aoAlphaExpr : Expr := (√ₑ ((√ₑ (sc (1/3)))))

def aoHistoryRootExpr : Expr := (√ₑ ((√ₑ ((√ₑ ((√ₑ ((√ₑ (sc (1/2187)))))))))))

def aoInverseHistoryExpr : Expr := (((sc (1/1) -ₑ aoAlphaExpr) +ₑ sc (1/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) /ₑ (sc (1/1) -ₑ (aoHistoryRootExpr *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/250000))))))

def aoTraceHistoryExpr : Expr := (((sc (1/1) -ₑ aoAlphaExpr) +ₑ sc (1/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) /ₑ (sc (1/1) -ₑ (aoHistoryRootExpr *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))))

def aoGapHistoryExpr : Expr := ((((sc (1/1) -ₑ aoAlphaExpr) +ₑ sc (1/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) *ₑ (aoHistoryRootExpr *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))) /ₑ ((sc (1/1) -ₑ (aoHistoryRootExpr *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000))))) *ₑ (sc (1/1) -ₑ (aoHistoryRootExpr *ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (187/125000)))))))

def aoSmallSelectedJExpr : Expr := ((sc (1/1) /ₑ (sc (1/1) -ₑ sc (77/32768))) +ₑ sc (1/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))

def aoSmallInverseRootExpr : Expr := (aoSensitivityExpr *ₑ ((((((aoM2Expr *ₑ sc (23881576034656461564337263083377237642940324085245322708363534/289)) +ₑ sc (29/25)) *ₑ (((((sc (1/1) /ₑ (sc (1/1) -ₑ sc (11/819200))) /ₑ (sc (3/1) -ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (11/819200))))) -ₑ sc (1/2)) *ₑ sc (4/1)) +ₑ sc (1/1))) *ₑ aoSmallSelectedJExpr) +ₑ (aoMatrixTailExpr *ₑ sc (6808576000000001183744/289))) +ₑ (aoDensityTailExpr *ₑ sc (71644728103969384693011789250131712928820972255735968125090602/289))))

def aoSmallTraceRootExpr : Expr := (aoSensitivityExpr *ₑ ((((((aoM2Expr *ₑ sc (90335637869348442439556340083511929899924289432629361466649578512094225387138291459179816834667579726/1093185780802562880124157800500033044331961)) +ₑ sc (29/25)) *ₑ (((((sc (1/1) /ₑ (sc (1/1) -ₑ sc (11/819200))) /ₑ (sc (3/1) -ₑ (sc (1/1) /ₑ (sc (1/1) -ₑ sc (11/819200))))) -ₑ sc (1/2)) *ₑ sc (4/1)) +ₑ sc (1/1))) *ₑ aoSmallSelectedJExpr) +ₑ (aoMatrixTailExpr *ₑ sc (13617152000000002367488/289))) +ₑ (aoDensityTailExpr *ₑ sc (271006913608045327318669020250535789699772868297888084399948735536282676161414874377539450504002739178/1093185780802562880124157800500033044331961))))

def aoEffectiveWaveExpr : Expr := (aoLayer4Expr *ₑ sc (29/100))


def profileUpperCheck (e : Expr) (u : ℚ) : Bool :=
  match evalGrid 200 25 (by decide) scalarGridEnv e with
  | none => false
  | some I => decide (I.hi < u)

theorem profile_upper_sound (e : Expr) (u : ℚ) (hc : profileUpperCheck e u = true) :
    evalReal scalarRealEnv e < (u : ℝ) := by
  unfold profileUpperCheck at hc
  cases he : evalGrid 200 25 (by decide) scalarGridEnv e with
  | none => simp only [he, Bool.false_eq_true] at hc
  | some I =>
    rw [he] at hc
    exact (evalGrid_sound 200 25 (by decide) scalarGridEnv scalarRealEnv scalar_env_sound e I he).2.trans_lt
      (by exact_mod_cast of_decide_eq_true hc)

theorem aoInverseRoot_kernel_check : profileUpperCheck aoInverseRootExpr (207/100) = true := by
  decide +kernel

theorem aoInverseRoot_bound : evalReal scalarRealEnv aoInverseRootExpr < ((207/100) : ℝ) := by
  simpa using profile_upper_sound _ _ aoInverseRoot_kernel_check

theorem aoTraceRoot_kernel_check : profileUpperCheck aoTraceRootExpr (207/100) = true := by
  decide +kernel

theorem aoTraceRoot_bound : evalReal scalarRealEnv aoTraceRootExpr < ((207/100) : ℝ) := by
  simpa using profile_upper_sound _ _ aoTraceRoot_kernel_check

theorem aoSmallInverseRoot_kernel_check : profileUpperCheck aoSmallInverseRootExpr (153/100) = true := by
  decide +kernel

theorem aoSmallInverseRoot_bound : evalReal scalarRealEnv aoSmallInverseRootExpr < ((153/100) : ℝ) := by
  simpa using profile_upper_sound _ _ aoSmallInverseRoot_kernel_check

theorem aoSmallTraceRoot_kernel_check : profileUpperCheck aoSmallTraceRootExpr (153/100) = true := by
  decide +kernel

theorem aoSmallTraceRoot_bound : evalReal scalarRealEnv aoSmallTraceRootExpr < ((153/100) : ℝ) := by
  simpa using profile_upper_sound _ _ aoSmallTraceRoot_kernel_check

theorem aoWaveSlope_kernel_check : profileUpperCheck aoWaveSlopeExpr (12100/1) = true := by
  decide +kernel

theorem aoWaveSlope_bound : evalReal scalarRealEnv aoWaveSlopeExpr < ((12100/1) : ℝ) := by
  simpa using profile_upper_sound _ _ aoWaveSlope_kernel_check

theorem aoWaveOffset_kernel_check : profileUpperCheck aoWaveOffsetExpr (4271000/1) = true := by
  decide +kernel

theorem aoWaveOffset_bound : evalReal scalarRealEnv aoWaveOffsetExpr < ((4271000/1) : ℝ) := by
  simpa using profile_upper_sound _ _ aoWaveOffset_kernel_check

theorem aoInverseHistory_kernel_check : profileUpperCheck aoInverseHistoryExpr (5637/5000) = true := by
  decide +kernel

theorem aoInverseHistory_bound : evalReal scalarRealEnv aoInverseHistoryExpr < ((5637/5000) : ℝ) := by
  simpa using profile_upper_sound _ _ aoInverseHistory_kernel_check

theorem aoTraceHistory_kernel_check : profileUpperCheck aoTraceHistoryExpr (2261/2000) = true := by
  decide +kernel

theorem aoTraceHistory_bound : evalReal scalarRealEnv aoTraceHistoryExpr < ((2261/2000) : ℝ) := by
  simpa using profile_upper_sound _ _ aoTraceHistory_kernel_check

theorem aoGapHistory_kernel_check : profileUpperCheck aoGapHistoryExpr (4191/1000) = true := by
  decide +kernel

theorem aoGapHistory_bound : evalReal scalarRealEnv aoGapHistoryExpr < ((4191/1000) : ℝ) := by
  simpa using profile_upper_sound _ _ aoGapHistory_kernel_check

theorem aoActiveDensity_kernel_check : profileUpperCheck aoActiveDensityExpr (19/100) = true := by
  decide +kernel

theorem aoActiveDensity_bound : evalReal scalarRealEnv aoActiveDensityExpr < ((19/100) : ℝ) := by
  simpa using profile_upper_sound _ _ aoActiveDensity_kernel_check

theorem aoSensitivity_kernel_check : profileUpperCheck aoSensitivityExpr (1309/1000) = true := by
  decide +kernel

theorem aoSensitivity_bound : evalReal scalarRealEnv aoSensitivityExpr < ((1309/1000) : ℝ) := by
  simpa using profile_upper_sound _ _ aoSensitivity_kernel_check

theorem aoEffectiveWave_kernel_check : profileUpperCheck aoEffectiveWaveExpr (293/1000) = true := by
  decide +kernel

theorem aoEffectiveWave_bound : evalReal scalarRealEnv aoEffectiveWaveExpr < ((293/1000) : ℝ) := by
  simpa using profile_upper_sound _ _ aoEffectiveWave_kernel_check

theorem aoLayer2_kernel_check : profileUpperCheck aoLayer2Expr (2009/2000) = true := by
  decide +kernel

theorem aoLayer2_bound : evalReal scalarRealEnv aoLayer2Expr < ((2009/2000) : ℝ) := by
  simpa using profile_upper_sound _ _ aoLayer2_kernel_check

theorem aoLayer4_kernel_check : profileUpperCheck aoLayer4Expr (10091/10000) = true := by
  decide +kernel

theorem aoLayer4_bound : evalReal scalarRealEnv aoLayer4Expr < ((10091/10000) : ℝ) := by
  simpa using profile_upper_sound _ _ aoLayer4_kernel_check

theorem aoLayerF_kernel_check : profileUpperCheck aoLayerFExpr (737/200) = true := by
  decide +kernel

theorem aoLayerF_bound : evalReal scalarRealEnv aoLayerFExpr < ((737/200) : ℝ) := by
  simpa using profile_upper_sound _ _ aoLayerF_kernel_check

theorem aoL0_kernel_check : profileUpperCheck aoL0Expr (3/1) = true := by
  decide +kernel

theorem aoL0_bound : evalReal scalarRealEnv aoL0Expr < ((3/1) : ℝ) := by
  simpa using profile_upper_sound _ _ aoL0_kernel_check

theorem aoL1_kernel_check : profileUpperCheck aoL1Expr (15/1) = true := by
  decide +kernel

theorem aoL1_bound : evalReal scalarRealEnv aoL1Expr < ((15/1) : ℝ) := by
  simpa using profile_upper_sound _ _ aoL1_kernel_check

theorem aoMatrixError_kernel_check : profileUpperCheck aoMatrixErrorExpr (1/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = true := by
  decide +kernel

theorem aoMatrixError_bound : evalReal scalarRealEnv aoMatrixErrorExpr < ((1/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) := by
  simpa using profile_upper_sound _ _ aoMatrixError_kernel_check

theorem aoDensityError_kernel_check : profileUpperCheck aoDensityErrorExpr (1/10000000) = true := by
  decide +kernel

theorem aoDensityError_bound : evalReal scalarRealEnv aoDensityErrorExpr < ((1/10000000) : ℝ) := by
  simpa using profile_upper_sound _ _ aoDensityError_kernel_check


/-- The spatial coefficient used by every all-order transfer allocation. -/
theorem allorder_spatial_coefficient :
    (4440*(1309/1000)*((293/1000)+(190/1000))+1 : ℚ) = 280817668/100000 ∧
    (280817668/100000 : ℚ) < 2810 ∧ (26/25 : ℚ)^64 > 12 := by
  decide +kernel

end ASDExplicitGamma.Numerics.AllOrder
