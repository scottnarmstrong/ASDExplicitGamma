module
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part000
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part001
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part002
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part003
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part004
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part005
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part006
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part007
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part008
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part009
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part010
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part011
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part012
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part013
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part014
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part015
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part016
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part017
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part018
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part019
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part020
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part021
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part022
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part023
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part024
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part025
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part026
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part027
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part028
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part029
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part030
public import ASDExplicitGamma.Numerics.Model.BlocksJ0Part031

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlocksJ0 : List ModeBlockData := [
  bflatBlockJ0B0,
  bflatBlockJ0B1,
  bflatBlockJ0B2,
  bflatBlockJ0B3,
  bflatBlockJ0B4,
  bflatBlockJ0B5,
  bflatBlockJ0B6,
  bflatBlockJ0B7,
  bflatBlockJ0B8,
  bflatBlockJ0B9,
  bflatBlockJ0B10,
  bflatBlockJ0B11,
  bflatBlockJ0B12,
  bflatBlockJ0B13,
  bflatBlockJ0B14,
  bflatBlockJ0B15,
  bflatBlockJ0B16,
  bflatBlockJ0B17,
  bflatBlockJ0B18,
  bflatBlockJ0B19,
  bflatBlockJ0B20,
  bflatBlockJ0B21,
  bflatBlockJ0B22,
  bflatBlockJ0B23,
  bflatBlockJ0B24,
  bflatBlockJ0B25,
  bflatBlockJ0B26,
  bflatBlockJ0B27,
  bflatBlockJ0B28,
  bflatBlockJ0B29,
  bflatBlockJ0B30,
  bflatBlockJ0B31]
theorem block_cover_j0 : (bflatBlocksJ0.map ModeBlockData.bound).flatMap blockModes = List.range 32 := by
  decide +kernel
theorem all_blocks_entries_j0 : bflatBlocksJ0.all (fun b => entryChecks 0 b.entries) = true := by
  simp only [bflatBlocksJ0,List.all_cons,List.all_nil,
    block_entries_checked_j0_b0,
    block_entries_checked_j0_b1,
    block_entries_checked_j0_b2,
    block_entries_checked_j0_b3,
    block_entries_checked_j0_b4,
    block_entries_checked_j0_b5,
    block_entries_checked_j0_b6,
    block_entries_checked_j0_b7,
    block_entries_checked_j0_b8,
    block_entries_checked_j0_b9,
    block_entries_checked_j0_b10,
    block_entries_checked_j0_b11,
    block_entries_checked_j0_b12,
    block_entries_checked_j0_b13,
    block_entries_checked_j0_b14,
    block_entries_checked_j0_b15,
    block_entries_checked_j0_b16,
    block_entries_checked_j0_b17,
    block_entries_checked_j0_b18,
    block_entries_checked_j0_b19,
    block_entries_checked_j0_b20,
    block_entries_checked_j0_b21,
    block_entries_checked_j0_b22,
    block_entries_checked_j0_b23,
    block_entries_checked_j0_b24,
    block_entries_checked_j0_b25,
    block_entries_checked_j0_b26,
    block_entries_checked_j0_b27,
    block_entries_checked_j0_b28,
    block_entries_checked_j0_b29,
    block_entries_checked_j0_b30,
    block_entries_checked_j0_b31,Bool.and_self]
theorem all_blocks_mass_j0 : bflatBlocksJ0.all (blockMassCheck) = true := by
  simp only [bflatBlocksJ0,List.all_cons,List.all_nil,
    block_mass_checked_j0_b0,
    block_mass_checked_j0_b1,
    block_mass_checked_j0_b2,
    block_mass_checked_j0_b3,
    block_mass_checked_j0_b4,
    block_mass_checked_j0_b5,
    block_mass_checked_j0_b6,
    block_mass_checked_j0_b7,
    block_mass_checked_j0_b8,
    block_mass_checked_j0_b9,
    block_mass_checked_j0_b10,
    block_mass_checked_j0_b11,
    block_mass_checked_j0_b12,
    block_mass_checked_j0_b13,
    block_mass_checked_j0_b14,
    block_mass_checked_j0_b15,
    block_mass_checked_j0_b16,
    block_mass_checked_j0_b17,
    block_mass_checked_j0_b18,
    block_mass_checked_j0_b19,
    block_mass_checked_j0_b20,
    block_mass_checked_j0_b21,
    block_mass_checked_j0_b22,
    block_mass_checked_j0_b23,
    block_mass_checked_j0_b24,
    block_mass_checked_j0_b25,
    block_mass_checked_j0_b26,
    block_mass_checked_j0_b27,
    block_mass_checked_j0_b28,
    block_mass_checked_j0_b29,
    block_mass_checked_j0_b30,
    block_mass_checked_j0_b31,Bool.and_self]
end ASDExplicitGamma.Numerics.Model
