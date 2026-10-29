module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B48 : ModeBlockData :=
  ⟨⟨48, 49, (13685668977891167989/2000000000000000000000 : ℚ), (166870860893145733/5000000000000000000000 : ℚ)⟩, [
    (48, modeDataJ4M49)], (8553543111181979993/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b48 : entryChecks 4 bflatBlockJ4B48.entries = true := by
  simp only [entryChecks,bflatBlockJ4B48,List.all_cons,List.all_nil,
    mode_checked_j4_m49,Bool.and_self]
theorem block_mass_checked_j4_b48 : blockMassCheck bflatBlockJ4B48 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
