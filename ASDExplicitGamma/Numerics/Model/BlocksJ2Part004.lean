module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B4 : ModeBlockData :=
  ⟨⟨4, 5, (313479035319284499993/5000000000000000000000 : ℚ), (27302709031280087607/10000000000000000000000 : ℚ)⟩, [
    (4, modeDataJ2M5)], (125391614127713799997/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b4 : entryChecks 2 bflatBlockJ2B4.entries = true := by
  simp only [entryChecks,bflatBlockJ2B4,List.all_cons,List.all_nil,
    mode_checked_j2_m5,Bool.and_self]
theorem block_mass_checked_j2_b4 : blockMassCheck bflatBlockJ2B4 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
