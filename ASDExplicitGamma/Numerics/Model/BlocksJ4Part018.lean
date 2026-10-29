module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B18 : ModeBlockData :=
  ⟨⟨18, 19, (37265609059235574669/5000000000000000000000 : ℚ), (17612325623125189/500000000000000000000 : ℚ)⟩, [
    (18, modeDataJ4M19)], (74531218118471149337/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b18 : entryChecks 4 bflatBlockJ4B18.entries = true := by
  simp only [entryChecks,bflatBlockJ4B18,List.all_cons,List.all_nil,
    mode_checked_j4_m19,Bool.and_self]
theorem block_mass_checked_j4_b18 : blockMassCheck bflatBlockJ4B18 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
