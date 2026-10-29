module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B24 : ModeBlockData :=
  ⟨⟨24, 25, (17971695292209572943/2500000000000000000000 : ℚ), (8558678430702515087/10000000000000000000000 : ℚ)⟩, [
    (24, modeDataJ2M25)], (71886781168838291771/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b24 : entryChecks 2 bflatBlockJ2B24.entries = true := by
  simp only [entryChecks,bflatBlockJ2B24,List.all_cons,List.all_nil,
    mode_checked_j2_m25,Bool.and_self]
theorem block_mass_checked_j2_b24 : blockMassCheck bflatBlockJ2B24 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
