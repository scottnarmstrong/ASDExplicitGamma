module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B16 : ModeBlockData :=
  ⟨⟨16, 17, (101851095403204228669/5000000000000000000000 : ℚ), (1493936414704614209/5000000000000000000000 : ℚ)⟩, [
    (16, modeDataJ3M17)], (203702190806408457337/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b16 : entryChecks 3 bflatBlockJ3B16.entries = true := by
  simp only [entryChecks,bflatBlockJ3B16,List.all_cons,List.all_nil,
    mode_checked_j3_m17,Bool.and_self]
theorem block_mass_checked_j3_b16 : blockMassCheck bflatBlockJ3B16 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
