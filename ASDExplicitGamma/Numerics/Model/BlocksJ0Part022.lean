module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B22 : ModeBlockData :=
  ⟨⟨22, 23, (7707723305439129259/10000000000000000000000 : ℚ), (3842212374202698853/5000000000000000000000 : ℚ)⟩, [
    (22, modeDataJ0M23)], (3853861652719564629/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b22 : entryChecks 0 bflatBlockJ0B22.entries = true := by
  simp only [entryChecks,bflatBlockJ0B22,List.all_cons,List.all_nil,
    mode_checked_j0_m23,Bool.and_self]
theorem block_mass_checked_j0_b22 : blockMassCheck bflatBlockJ0B22 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
