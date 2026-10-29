module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B52 : ModeBlockData :=
  ⟨⟨52, 53, (15114397242712296911/2000000000000000000000 : ℚ), (42007908297083627/250000000000000000000 : ℚ)⟩, [
    (52, modeDataJ3M53)], (37785993106780742277/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b52 : entryChecks 3 bflatBlockJ3B52.entries = true := by
  simp only [entryChecks,bflatBlockJ3B52,List.all_cons,List.all_nil,
    mode_checked_j3_m53,Bool.and_self]
theorem block_mass_checked_j3_b52 : blockMassCheck bflatBlockJ3B52 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
