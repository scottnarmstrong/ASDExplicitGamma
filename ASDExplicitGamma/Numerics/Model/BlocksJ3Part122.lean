module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part015

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B122 : ModeBlockData :=
  ⟨⟨255, 256, (32537804648064911/5000000000000000000000 : ℚ), (62987273672434399/10000000000000000000000 : ℚ)⟩, [
    (255, modeDataJ3M256)], (65075609296129821/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b122 : entryChecks 3 bflatBlockJ3B122.entries = true := by
  simp only [entryChecks,bflatBlockJ3B122,List.all_cons,List.all_nil,
    mode_checked_j3_m256,Bool.and_self]
theorem block_mass_checked_j3_b122 : blockMassCheck bflatBlockJ3B122 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
