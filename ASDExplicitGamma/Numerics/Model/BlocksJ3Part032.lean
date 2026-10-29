module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B32 : ModeBlockData :=
  ⟨⟨32, 33, (150138173173078675367/10000000000000000000000 : ℚ), (49522118635827043/200000000000000000000 : ℚ)⟩, [
    (32, modeDataJ3M33)], (75069086586539337683/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b32 : entryChecks 3 bflatBlockJ3B32.entries = true := by
  simp only [entryChecks,bflatBlockJ3B32,List.all_cons,List.all_nil,
    mode_checked_j3_m33,Bool.and_self]
theorem block_mass_checked_j3_b32 : blockMassCheck bflatBlockJ3B32 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
