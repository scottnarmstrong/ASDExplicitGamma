module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B43 : ModeBlockData :=
  ⟨⟨43, 44, (13530105010605431/50000000000000000000 : ℚ), (565703133618931113/2500000000000000000000 : ℚ)⟩, [
    (43, modeDataJ2M44)], (2706021002121086199/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b43 : entryChecks 2 bflatBlockJ2B43.entries = true := by
  simp only [entryChecks,bflatBlockJ2B43,List.all_cons,List.all_nil,
    mode_checked_j2_m44,Bool.and_self]
theorem block_mass_checked_j2_b43 : blockMassCheck bflatBlockJ2B43 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
