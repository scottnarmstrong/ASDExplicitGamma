module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B53 : ModeBlockData :=
  ⟨⟨53, 54, (66961325159704191253/10000000000000000000000 : ℚ), (82310254955084703/2500000000000000000000 : ℚ)⟩, [
    (53, modeDataJ4M54)], (16740331289926047813/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b53 : entryChecks 4 bflatBlockJ4B53.entries = true := by
  simp only [entryChecks,bflatBlockJ4B53,List.all_cons,List.all_nil,
    mode_checked_j4_m54,Bool.and_self]
theorem block_mass_checked_j4_b53 : blockMassCheck bflatBlockJ4B53 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
