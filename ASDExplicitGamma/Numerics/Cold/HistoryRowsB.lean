module
public import ASDExplicitGamma.Numerics.Cold.History

/-! Rowwise kernel checks of the outward depth-history formula.
The finite rows here keep each exact rational normalization within
Lean's default heartbeat budget. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Cold

theorem cold_history_row_36 : coldHistoryAt 36 = coldHistoryExpected 36 := by
  decide +kernel

theorem cold_history_row_38 : coldHistoryAt 38 = coldHistoryExpected 38 := by
  decide +kernel

theorem cold_history_row_40 : coldHistoryAt 40 = coldHistoryExpected 40 := by
  decide +kernel

theorem cold_history_row_42 : coldHistoryAt 42 = coldHistoryExpected 42 := by
  decide +kernel

theorem cold_history_row_44 : coldHistoryAt 44 = coldHistoryExpected 44 := by
  decide +kernel

theorem cold_history_row_46 : coldHistoryAt 46 = coldHistoryExpected 46 := by
  decide +kernel

theorem cold_history_row_48 : coldHistoryAt 48 = coldHistoryExpected 48 := by
  decide +kernel

theorem cold_history_row_50 : coldHistoryAt 50 = coldHistoryExpected 50 := by
  decide +kernel

theorem cold_history_row_52 : coldHistoryAt 52 = coldHistoryExpected 52 := by
  decide +kernel

theorem cold_history_row_54 : coldHistoryAt 54 = coldHistoryExpected 54 := by
  decide +kernel

theorem cold_history_row_56 : coldHistoryAt 56 = coldHistoryExpected 56 := by
  decide +kernel

theorem cold_history_row_58 : coldHistoryAt 58 = coldHistoryExpected 58 := by
  decide +kernel

theorem cold_history_row_60 : coldHistoryAt 60 = coldHistoryExpected 60 := by
  decide +kernel

theorem cold_history_row_62 : coldHistoryAt 62 = coldHistoryExpected 62 := by
  decide +kernel

theorem cold_history_row_64 : coldHistoryAt 64 = coldHistoryExpected 64 := by
  decide +kernel

theorem cold_history_row_66 : coldHistoryAt 66 = coldHistoryExpected 66 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Cold
