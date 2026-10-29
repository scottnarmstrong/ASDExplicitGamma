module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B9 : ModeBlockData :=
  ⟨⟨9, 10, (6302190798593681469/2500000000000000000000 : ℚ), (1580142058299149/400000000000000000000 : ℚ)⟩, [
    (9, modeDataJ5M10)], (201670105554997807/80000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b9 : entryChecks 5 bflatBlockJ5B9.entries = true := by
  simp only [entryChecks,bflatBlockJ5B9,List.all_cons,List.all_nil,
    mode_checked_j5_m10,Bool.and_self]
theorem block_mass_checked_j5_b9 : blockMassCheck bflatBlockJ5B9 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
