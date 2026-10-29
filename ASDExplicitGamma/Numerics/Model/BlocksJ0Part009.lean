module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B9 : ModeBlockData :=
  ⟨⟨9, 10, (2095856705198771567/500000000000000000000 : ℚ), (2060032289341353189/500000000000000000000 : ℚ)⟩, [
    (9, modeDataJ0M10)], (41917134103975431339/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b9 : entryChecks 0 bflatBlockJ0B9.entries = true := by
  simp only [entryChecks,bflatBlockJ0B9,List.all_cons,List.all_nil,
    mode_checked_j0_m10,Bool.and_self]
theorem block_mass_checked_j0_b9 : blockMassCheck bflatBlockJ0B9 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
