module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B9 : ModeBlockData :=
  ⟨⟨9, 10, (487708411829566830183/10000000000000000000000 : ℚ), (23287642651061313913/10000000000000000000000 : ℚ)⟩, [
    (9, modeDataJ2M10)], (243854205914783415091/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b9 : entryChecks 2 bflatBlockJ2B9.entries = true := by
  simp only [entryChecks,bflatBlockJ2B9,List.all_cons,List.all_nil,
    mode_checked_j2_m10,Bool.and_self]
theorem block_mass_checked_j2_b9 : blockMassCheck bflatBlockJ2B9 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
