module
public import ASDExplicitGamma.Numerics.Cold.History

/-! Rowwise kernel checks of the outward depth-history formula.
The finite rows here keep each exact rational normalization within
Lean's default heartbeat budget. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Cold

theorem cold_history_row_4 : coldHistoryAt 4 = coldHistoryExpected 4 := by
  decide +kernel

theorem cold_history_row_6 : coldHistoryAt 6 = coldHistoryExpected 6 := by
  decide +kernel

theorem cold_history_row_8 : coldHistoryAt 8 = coldHistoryExpected 8 := by
  decide +kernel

theorem cold_history_row_10 : coldHistoryAt 10 = coldHistoryExpected 10 := by
  decide +kernel

theorem cold_history_row_12 : coldHistoryAt 12 = coldHistoryExpected 12 := by
  decide +kernel

theorem cold_history_row_14 : coldHistoryAt 14 = coldHistoryExpected 14 := by
  decide +kernel

theorem cold_history_row_16 : coldHistoryAt 16 = coldHistoryExpected 16 := by
  decide +kernel

theorem cold_history_row_18 : coldHistoryAt 18 = coldHistoryExpected 18 := by
  decide +kernel

theorem cold_history_row_20 : coldHistoryAt 20 = coldHistoryExpected 20 := by
  decide +kernel

theorem cold_history_row_22 : coldHistoryAt 22 = coldHistoryExpected 22 := by
  decide +kernel

theorem cold_history_row_24 : coldHistoryAt 24 = coldHistoryExpected 24 := by
  decide +kernel

theorem cold_history_row_26 : coldHistoryAt 26 = coldHistoryExpected 26 := by
  decide +kernel

theorem cold_history_row_28 : coldHistoryAt 28 = coldHistoryExpected 28 := by
  decide +kernel

theorem cold_history_row_30 : coldHistoryAt 30 = coldHistoryExpected 30 := by
  decide +kernel

theorem cold_history_row_32 : coldHistoryAt 32 = coldHistoryExpected 32 := by
  decide +kernel

theorem cold_history_row_34 : coldHistoryAt 34 = coldHistoryExpected 34 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Cold
