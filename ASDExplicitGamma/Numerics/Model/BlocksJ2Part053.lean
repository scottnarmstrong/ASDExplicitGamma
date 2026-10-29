module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B53 : ModeBlockData :=
  ⟨⟨53, 54, (406741393266671589/2500000000000000000000 : ℚ), (730545381353544459/5000000000000000000000 : ℚ)⟩, [
    (53, modeDataJ2M54)], (325393114613337271/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b53 : entryChecks 2 bflatBlockJ2B53.entries = true := by
  simp only [entryChecks,bflatBlockJ2B53,List.all_cons,List.all_nil,
    mode_checked_j2_m54,Bool.and_self]
theorem block_mass_checked_j2_b53 : blockMassCheck bflatBlockJ2B53 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
