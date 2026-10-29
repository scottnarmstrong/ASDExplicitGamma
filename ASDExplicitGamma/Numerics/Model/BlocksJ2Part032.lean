module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B32 : ModeBlockData :=
  ⟨⟨32, 33, (2806697491181176847/2500000000000000000000 : ℚ), (4466714966255312819/10000000000000000000000 : ℚ)⟩, [
    (32, modeDataJ2M33)], (11226789964724707387/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b32 : entryChecks 2 bflatBlockJ2B32.entries = true := by
  simp only [entryChecks,bflatBlockJ2B32,List.all_cons,List.all_nil,
    mode_checked_j2_m33,Bool.and_self]
theorem block_mass_checked_j2_b32 : blockMassCheck bflatBlockJ2B32 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
