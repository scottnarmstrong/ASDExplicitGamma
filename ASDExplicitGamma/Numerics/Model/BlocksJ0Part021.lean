module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B21 : ModeBlockData :=
  ⟨⟨21, 22, (526820985180014309/625000000000000000000 : ℚ), (1680250874255969891/2000000000000000000000 : ℚ)⟩, [
    (21, modeDataJ0M22)], (8429135762880228943/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b21 : entryChecks 0 bflatBlockJ0B21.entries = true := by
  simp only [entryChecks,bflatBlockJ0B21,List.all_cons,List.all_nil,
    mode_checked_j0_m22,Bool.and_self]
theorem block_mass_checked_j0_b21 : blockMassCheck bflatBlockJ0B21 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
