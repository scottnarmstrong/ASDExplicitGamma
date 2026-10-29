module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B50 : ModeBlockData :=
  ⟨⟨50, 51, (20577887713815230033/2500000000000000000000 : ℚ), (879280979918264637/5000000000000000000000 : ℚ)⟩, [
    (50, modeDataJ3M51)], (82311550855260920131/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b50 : entryChecks 3 bflatBlockJ3B50.entries = true := by
  simp only [entryChecks,bflatBlockJ3B50,List.all_cons,List.all_nil,
    mode_checked_j3_m51,Bool.and_self]
theorem block_mass_checked_j3_b50 : blockMassCheck bflatBlockJ3B50 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
