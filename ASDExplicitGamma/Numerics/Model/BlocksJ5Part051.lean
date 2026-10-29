module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B51 : ModeBlockData :=
  ⟨⟨51, 52, (24905947134286733391/10000000000000000000000 : ℚ), (39201415828251647/10000000000000000000000 : ℚ)⟩, [
    (51, modeDataJ5M52)], (2490594713428673339/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b51 : entryChecks 5 bflatBlockJ5B51.entries = true := by
  simp only [entryChecks,bflatBlockJ5B51,List.all_cons,List.all_nil,
    mode_checked_j5_m52,Bool.and_self]
theorem block_mass_checked_j5_b51 : blockMassCheck bflatBlockJ5B51 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
