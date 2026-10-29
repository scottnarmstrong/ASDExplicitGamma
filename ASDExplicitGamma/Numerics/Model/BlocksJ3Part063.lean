module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B63 : ModeBlockData :=
  ⟨⟨63, 64, (43813423299691389667/10000000000000000000000 : ℚ), (1280526598413997917/10000000000000000000000 : ℚ)⟩, [
    (63, modeDataJ3M64)], (21906711649845694833/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b63 : entryChecks 3 bflatBlockJ3B63.entries = true := by
  simp only [entryChecks,bflatBlockJ3B63,List.all_cons,List.all_nil,
    mode_checked_j3_m64,Bool.and_self]
theorem block_mass_checked_j3_b63 : blockMassCheck bflatBlockJ3B63 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
