module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B30 : ModeBlockData :=
  ⟨⟨30, 31, (4353150773760008731/10000000000000000000000 : ℚ), (2141314089400880809/5000000000000000000000 : ℚ)⟩, [
    (30, modeDataJ1M31)], (435315077376000873/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b30 : entryChecks 1 bflatBlockJ1B30.entries = true := by
  simp only [entryChecks,bflatBlockJ1B30,List.all_cons,List.all_nil,
    mode_checked_j1_m31,Bool.and_self]
theorem block_mass_checked_j1_b30 : blockMassCheck bflatBlockJ1B30 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
