module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B19 : ModeBlockData :=
  ⟨⟨19, 20, (688494342242325677/625000000000000000000 : ℚ), (10535743522257381177/10000000000000000000000 : ℚ)⟩, [
    (19, modeDataJ1M20)], (11015909475877210831/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b19 : entryChecks 1 bflatBlockJ1B19.entries = true := by
  simp only [entryChecks,bflatBlockJ1B19,List.all_cons,List.all_nil,
    mode_checked_j1_m20,Bool.and_self]
theorem block_mass_checked_j1_b19 : blockMassCheck bflatBlockJ1B19 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
