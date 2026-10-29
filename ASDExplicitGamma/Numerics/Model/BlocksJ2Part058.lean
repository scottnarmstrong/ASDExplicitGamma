module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B58 : ModeBlockData :=
  ⟨⟨58, 59, (1271378507924216931/10000000000000000000000 : ℚ), (606279555485835031/5000000000000000000000 : ℚ)⟩, [
    (58, modeDataJ2M59)], (127137850792421693/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b58 : entryChecks 2 bflatBlockJ2B58.entries = true := by
  simp only [entryChecks,bflatBlockJ2B58,List.all_cons,List.all_nil,
    mode_checked_j2_m59,Bool.and_self]
theorem block_mass_checked_j2_b58 : blockMassCheck bflatBlockJ2B58 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
