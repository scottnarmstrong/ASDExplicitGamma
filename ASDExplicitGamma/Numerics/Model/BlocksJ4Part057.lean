module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B57 : ModeBlockData :=
  ⟨⟨57, 58, (65708477604654679077/10000000000000000000000 : ℚ), (325380277230767021/10000000000000000000000 : ℚ)⟩, [
    (57, modeDataJ4M58)], (16427119401163669769/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b57 : entryChecks 4 bflatBlockJ4B57.entries = true := by
  simp only [entryChecks,bflatBlockJ4B57,List.all_cons,List.all_nil,
    mode_checked_j4_m58,Bool.and_self]
theorem block_mass_checked_j4_b57 : blockMassCheck bflatBlockJ4B57 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
