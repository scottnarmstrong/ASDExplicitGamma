module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B7 : ModeBlockData :=
  ⟨⟨7, 8, (158064972725798835239/5000000000000000000000 : ℚ), (10459346483246693823/1250000000000000000000 : ℚ)⟩, [
    (7, modeDataJ1M8)], (316129945451597670477/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b7 : entryChecks 1 bflatBlockJ1B7.entries = true := by
  simp only [entryChecks,bflatBlockJ1B7,List.all_cons,List.all_nil,
    mode_checked_j1_m8,Bool.and_self]
theorem block_mass_checked_j1_b7 : blockMassCheck bflatBlockJ1B7 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
