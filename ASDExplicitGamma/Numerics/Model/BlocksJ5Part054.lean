module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B54 : ModeBlockData :=
  ⟨⟨54, 55, (12434424183608250463/5000000000000000000000 : ℚ), (19582173204817939/5000000000000000000000 : ℚ)⟩, [
    (54, modeDataJ5M55)], (994753934688660037/400000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b54 : entryChecks 5 bflatBlockJ5B54.entries = true := by
  simp only [entryChecks,bflatBlockJ5B54,List.all_cons,List.all_nil,
    mode_checked_j5_m55,Bool.and_self]
theorem block_mass_checked_j5_b54 : blockMassCheck bflatBlockJ5B54 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
