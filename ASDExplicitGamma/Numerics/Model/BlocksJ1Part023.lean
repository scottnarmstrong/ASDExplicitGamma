module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B23 : ModeBlockData :=
  ⟨⟨23, 24, (3727499977574193303/5000000000000000000000 : ℚ), (7224204483203897987/10000000000000000000000 : ℚ)⟩, [
    (23, modeDataJ1M24)], (1490999991029677321/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b23 : entryChecks 1 bflatBlockJ1B23.entries = true := by
  simp only [entryChecks,bflatBlockJ1B23,List.all_cons,List.all_nil,
    mode_checked_j1_m24,Bool.and_self]
theorem block_mass_checked_j1_b23 : blockMassCheck bflatBlockJ1B23 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
