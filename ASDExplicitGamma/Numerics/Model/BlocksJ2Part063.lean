module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B63 : ModeBlockData :=
  ⟨⟨63, 64, (537468620790680733/5000000000000000000000 : ℚ), (204690126115254787/2000000000000000000000 : ℚ)⟩, [
    (63, modeDataJ2M64)], (214987448316272293/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b63 : entryChecks 2 bflatBlockJ2B63.entries = true := by
  simp only [entryChecks,bflatBlockJ2B63,List.all_cons,List.all_nil,
    mode_checked_j2_m64,Bool.and_self]
theorem block_mass_checked_j2_b63 : blockMassCheck bflatBlockJ2B63 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
