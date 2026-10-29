module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B2 : ModeBlockData :=
  ⟨⟨2, 3, (40656799071494813927/400000000000000000000 : ℚ), (586650277814987382037/10000000000000000000000 : ℚ)⟩, [
    (2, modeDataJ0M3)], (508209988393685174087/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b2 : entryChecks 0 bflatBlockJ0B2.entries = true := by
  simp only [entryChecks,bflatBlockJ0B2,List.all_cons,List.all_nil,
    mode_checked_j0_m3,Bool.and_self]
theorem block_mass_checked_j0_b2 : blockMassCheck bflatBlockJ0B2 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
