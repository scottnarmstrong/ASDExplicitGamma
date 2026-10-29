module

public import ASDExplicitGamma.Cold.ColdHistoryDepthCaps

/-! # The exact alpha, beta and finite-union factors in the cold history -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold

/-- Source depth weight. -/
def coldHistoryAlpha : ℝ := (3:ℝ)^(-(1/4:ℝ))
/-- Source L20 strong-sum weight. -/
def coldHistoryBeta : ℝ := (3:ℝ)^(-(3/20:ℝ))
/-- Source finite-union factor per depth in dimension two. -/
def coldHistoryUnionFactor : ℝ := (9:ℝ)^((1:ℝ)/20)

theorem coldHistoryAlpha_pos : 0 < coldHistoryAlpha := Real.rpow_pos_of_pos (by norm_num) _
theorem coldHistoryAlpha_le_one : coldHistoryAlpha ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
theorem coldHistoryBeta_pos : 0 < coldHistoryBeta := Real.rpow_pos_of_pos (by norm_num) _

theorem coldHistoryAlpha_lt_one : coldHistoryAlpha < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- The alpha weight is included once: alpha times the union factor is beta. -/
theorem cold_history_weight_relation : coldHistoryAlpha*coldHistoryUnionFactor = coldHistoryBeta := by
  have he : coldHistoryUnionFactor = (3:ℝ)^((1:ℝ)/10) := by
    dsimp [coldHistoryUnionFactor]
    rw [show (9:ℝ)=3^2 by norm_num,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    norm_num
  rw [he]
  dsimp [coldHistoryAlpha,coldHistoryBeta]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  norm_num

theorem coldHistoryAlpha_ge_threeQuarters : (3/4:ℝ) ≤ coldHistoryAlpha := by
  have hp : coldHistoryAlpha^4 = (1/3:ℝ) := by
    dsimp [coldHistoryAlpha]
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  apply (pow_le_pow_iff_left₀ (by norm_num : (0:ℝ) ≤ 3/4) coldHistoryAlpha_pos.le (by norm_num : (4:ℕ) ≠ 0)).mp
  rw [hp]
  norm_num

theorem coldHistoryBeta_le_nineTenths : coldHistoryBeta ≤ (9/10:ℝ) := by
  have hp : coldHistoryBeta^20 = (1/27:ℝ) := by
    dsimp [coldHistoryBeta]
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  apply (pow_le_pow_iff_left₀ coldHistoryBeta_pos.le (by norm_num : (0:ℝ) ≤ 9/10) (by norm_num : (20:ℕ) ≠ 0)).mp
  rw [hp]
  norm_num

/-- The genuine source root and strong constants satisfy the global history branch. -/
theorem cold_history_native_constants {θ : ℝ} (hθ : 0 ≤ θ) :
    (1-coldHistoryAlpha)*((2013/10000:ℝ)*θ) ≤
      (1-coldHistoryBeta)*((2379/2500:ℝ)*θ) := by
  have ha := coldHistoryAlpha_ge_threeQuarters
  have hb := coldHistoryBeta_le_nineTenths
  have hbase : (1-coldHistoryAlpha)*(2013/10000:ℝ) ≤
      (1-coldHistoryBeta)*(2379/2500:ℝ) := by linarith only [ha,hb]
  have h := mul_le_mul_of_nonneg_right hbase hθ
  convert h using 1 <;> ring

/-- The literal depth union factor has the displayed source form. -/
theorem coldHistoryUnionFactor_pow (r : ℕ) :
    coldHistoryUnionFactor^r = (9:ℝ)^((r:ℝ)/20) := by
  dsimp [coldHistoryUnionFactor]
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 9)]
  congr 1
  ring

end ASDExplicitGamma.Cold
