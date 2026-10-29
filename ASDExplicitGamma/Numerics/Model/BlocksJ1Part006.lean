module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B6 : ModeBlockData :=
  ⟨⟨6, 7, (493844723368865552937/10000000000000000000000 : ℚ), (1330688907592347293/125000000000000000000 : ℚ)⟩, [
    (6, modeDataJ1M7)], (61730590421108194117/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b6 : entryChecks 1 bflatBlockJ1B6.entries = true := by
  simp only [entryChecks,bflatBlockJ1B6,List.all_cons,List.all_nil,
    mode_checked_j1_m7,Bool.and_self]
theorem block_mass_checked_j1_b6 : blockMassCheck bflatBlockJ1B6 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
