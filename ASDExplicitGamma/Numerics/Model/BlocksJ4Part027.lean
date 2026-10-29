module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B27 : ModeBlockData :=
  ⟨⟨27, 28, (14645304857787541283/2000000000000000000000 : ℚ), (348318861163949779/10000000000000000000000 : ℚ)⟩, [
    (27, modeDataJ4M28)], (36613262144468853207/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b27 : entryChecks 4 bflatBlockJ4B27.entries = true := by
  simp only [entryChecks,bflatBlockJ4B27,List.all_cons,List.all_nil,
    mode_checked_j4_m28,Bool.and_self]
theorem block_mass_checked_j4_b27 : blockMassCheck bflatBlockJ4B27 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
