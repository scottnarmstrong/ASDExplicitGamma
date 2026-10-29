module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B6 : ModeBlockData :=
  ⟨⟨6, 7, (578857431730281526459/10000000000000000000000 : ℚ), (6484976117474802373/2500000000000000000000 : ℚ)⟩, [
    (6, modeDataJ2M7)], (289428715865140763229/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b6 : entryChecks 2 bflatBlockJ2B6.entries = true := by
  simp only [entryChecks,bflatBlockJ2B6,List.all_cons,List.all_nil,
    mode_checked_j2_m7,Bool.and_self]
theorem block_mass_checked_j2_b6 : blockMassCheck bflatBlockJ2B6 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
