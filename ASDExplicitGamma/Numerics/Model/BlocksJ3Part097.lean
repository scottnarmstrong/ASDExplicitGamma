module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part009

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B97 : ModeBlockData :=
  ⟨⟨145, 148, (114289658762977879/1250000000000000000000 : ℚ), (11968508167408857/200000000000000000000 : ℚ)⟩, [
    (145, modeDataJ3M146),
    (146, modeDataJ3M147),
    (147, modeDataJ3M148)], (914317270103823029/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b97 : entryChecks 3 bflatBlockJ3B97.entries = true := by
  simp only [entryChecks,bflatBlockJ3B97,List.all_cons,List.all_nil,
    mode_checked_j3_m146,
    mode_checked_j3_m147,
    mode_checked_j3_m148,Bool.and_self]
theorem block_mass_checked_j3_b97 : blockMassCheck bflatBlockJ3B97 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
