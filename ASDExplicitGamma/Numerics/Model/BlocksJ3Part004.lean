module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B4 : ModeBlockData :=
  ⟨⟨4, 5, (44975632663444295217/2000000000000000000000 : ℚ), (3181676278726557207/10000000000000000000000 : ℚ)⟩, [
    (4, modeDataJ3M5)], (56219540829305369021/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b4 : entryChecks 3 bflatBlockJ3B4.entries = true := by
  simp only [entryChecks,bflatBlockJ3B4,List.all_cons,List.all_nil,
    mode_checked_j3_m5,Bool.and_self]
theorem block_mass_checked_j3_b4 : blockMassCheck bflatBlockJ3B4 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
