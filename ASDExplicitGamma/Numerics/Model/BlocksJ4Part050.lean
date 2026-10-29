module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B50 : ModeBlockData :=
  ⟨⟨50, 51, (8481899147469365971/1250000000000000000000 : ℚ), (165992934967179357/5000000000000000000000 : ℚ)⟩, [
    (50, modeDataJ4M51)], (67855193179754927767/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b50 : entryChecks 4 bflatBlockJ4B50.entries = true := by
  simp only [entryChecks,bflatBlockJ4B50,List.all_cons,List.all_nil,
    mode_checked_j4_m51,Bool.and_self]
theorem block_mass_checked_j4_b50 : blockMassCheck bflatBlockJ4B50 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
