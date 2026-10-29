module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B22 : ModeBlockData :=
  ⟨⟨22, 23, (12579323026255652307/5000000000000000000000 : ℚ), (246585005490403/62500000000000000000 : ℚ)⟩, [
    (22, modeDataJ5M23)], (25158646052511304613/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b22 : entryChecks 5 bflatBlockJ5B22.entries = true := by
  simp only [entryChecks,bflatBlockJ5B22,List.all_cons,List.all_nil,
    mode_checked_j5_m23,Bool.and_self]
theorem block_mass_checked_j5_b22 : blockMassCheck bflatBlockJ5B22 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
