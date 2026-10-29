module
public import ASDExplicitGamma.Numerics.Cold.HistoryRowsA
public import ASDExplicitGamma.Numerics.Cold.HistoryRowsB
public import ASDExplicitGamma.Numerics.Cold.HistoryRowsC
public import ASDExplicitGamma.Numerics.Cold.HistoryRowsD
import Mathlib.Tactic.FinCases

/-! Finite assembly of the checked depth-history rows. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Cold

theorem cold_history_indexed_check :
    ∀ i : Fin 63, coldHistoryAt (4 + 2*i.val) = coldHistoryExpected (4 + 2*i.val) := by
  intro i
  fin_cases i <;> simp only [Nat.reduceAdd, Nat.reduceMul, cold_history_row_4, cold_history_row_6, cold_history_row_8, cold_history_row_10, cold_history_row_12, cold_history_row_14, cold_history_row_16, cold_history_row_18, cold_history_row_20, cold_history_row_22, cold_history_row_24, cold_history_row_26, cold_history_row_28, cold_history_row_30, cold_history_row_32, cold_history_row_34, cold_history_row_36, cold_history_row_38, cold_history_row_40, cold_history_row_42, cold_history_row_44, cold_history_row_46, cold_history_row_48, cold_history_row_50, cold_history_row_52, cold_history_row_54, cold_history_row_56, cold_history_row_58, cold_history_row_60, cold_history_row_62, cold_history_row_64, cold_history_row_66, cold_history_row_68, cold_history_row_70, cold_history_row_72, cold_history_row_74, cold_history_row_76, cold_history_row_78, cold_history_row_80, cold_history_row_82, cold_history_row_84, cold_history_row_86, cold_history_row_88, cold_history_row_90, cold_history_row_92, cold_history_row_94, cold_history_row_96, cold_history_row_98, cold_history_row_100, cold_history_row_102, cold_history_row_104, cold_history_row_106, cold_history_row_108, cold_history_row_110, cold_history_row_112, cold_history_row_114, cold_history_row_116, cold_history_row_118, cold_history_row_120, cold_history_row_122, cold_history_row_124, cold_history_row_126, cold_history_row_128]

theorem cold_history_table_check :
    ∀ j ∈ coldUpdatedLags, coldHistoryAt j = coldHistoryExpected j := by
  intro j hj
  change j ∈ (List.range 63).map (fun i => 4 + 2*i) at hj
  rcases List.mem_map.mp hj with ⟨i, hi, heq⟩
  have hlt : i < 63 := List.mem_range.mp hi
  subst j
  exact cold_history_indexed_check ⟨i, hlt⟩

end ASDExplicitGamma.Numerics.Cold
