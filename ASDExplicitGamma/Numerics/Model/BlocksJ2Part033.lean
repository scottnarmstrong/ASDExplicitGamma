module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B33 : ModeBlockData :=
  ⟨⟨33, 34, (175347254302619723/200000000000000000000 : ℚ), (4147009043167701797/10000000000000000000000 : ℚ)⟩, [
    (33, modeDataJ2M34)], (8767362715130986149/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b33 : entryChecks 2 bflatBlockJ2B33.entries = true := by
  simp only [entryChecks,bflatBlockJ2B33,List.all_cons,List.all_nil,
    mode_checked_j2_m34,Bool.and_self]
theorem block_mass_checked_j2_b33 : blockMassCheck bflatBlockJ2B33 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
