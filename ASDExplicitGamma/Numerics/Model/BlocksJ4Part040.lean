module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B40 : ModeBlockData :=
  ⟨⟨40, 41, (17632083592338121621/2500000000000000000000 : ℚ), (34014796802218489/1000000000000000000000 : ℚ)⟩, [
    (40, modeDataJ4M41)], (70528334369352486483/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b40 : entryChecks 4 bflatBlockJ4B40.entries = true := by
  simp only [entryChecks,bflatBlockJ4B40,List.all_cons,List.all_nil,
    mode_checked_j4_m41,Bool.and_self]
theorem block_mass_checked_j4_b40 : blockMassCheck bflatBlockJ4B40 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
