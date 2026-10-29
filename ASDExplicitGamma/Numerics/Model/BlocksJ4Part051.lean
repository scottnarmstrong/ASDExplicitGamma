module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B51 : ModeBlockData :=
  ⟨⟨51, 52, (8445215754443549587/1250000000000000000000 : ℚ), (66217116095089487/2000000000000000000000 : ℚ)⟩, [
    (51, modeDataJ4M52)], (13512345207109679339/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b51 : entryChecks 4 bflatBlockJ4B51.entries = true := by
  simp only [entryChecks,bflatBlockJ4B51,List.all_cons,List.all_nil,
    mode_checked_j4_m52,Bool.and_self]
theorem block_mass_checked_j4_b51 : blockMassCheck bflatBlockJ4B51 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
