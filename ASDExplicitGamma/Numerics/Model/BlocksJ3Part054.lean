module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B54 : ModeBlockData :=
  ⟨⟨54, 55, (34552206718584558497/5000000000000000000000 : ℚ), (1603459803522673153/10000000000000000000000 : ℚ)⟩, [
    (54, modeDataJ3M55)], (69104413437169116993/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b54 : entryChecks 3 bflatBlockJ3B54.entries = true := by
  simp only [entryChecks,bflatBlockJ3B54,List.all_cons,List.all_nil,
    mode_checked_j3_m55,Bool.and_self]
theorem block_mass_checked_j3_b54 : blockMassCheck bflatBlockJ3B54 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
