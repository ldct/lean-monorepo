import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Playground.Geometry.SmallGroups.AlternatingGroup
import Playground.Geometry.Cpq
import Playground.Geometry.Dicyclic
import Playground.Geometry.Dihedralization
import Playground.Geometry.FrobeniusGroup

set_option linter.style.longLine false

/-
inv1: ab = ba (commutativity)
inv3: a² = b² (same square)
inv5: a³ = b³ (same cube)
inv6: a⁴ = b⁴ (same fourth power)
inv13: (ab)² = e (product is an involution or identity)
invA: ab = ba AND a² = e (commuting pairs where a is an involution or identity)
invB: (ab)⁵ = e (product has order dividing 5)
invC: a⁷ = b⁷ (same seventh power)
-/

def inv1 (G) [Group G] [Fintype G] [DecidableEq G] : ℕ :=
Finset.card { (a, b) : G × G | a * b = b * a }
def inv3 (G) [Group G] [Fintype G] [DecidableEq G] : ℕ :=
Finset.card { (a, b) : G × G | a^2 = b^2 }
def inv5 (G) [Group G] [Fintype G] [DecidableEq G] : ℕ :=
Finset.card { (a, b) : G × G | a^3 = b^3 }
def inv6 (G) [Group G] [Fintype G] [DecidableEq G] : ℕ :=
Finset.card { (a, b) : G × G | a^4 = b^4 }
def inv13 (G) [Group G] [Fintype G] [DecidableEq G] : ℕ :=
Finset.card { (a, b) : G × G | (a * b)^2 = 1 }
def invA (G) [Group G] [Fintype G] [DecidableEq G] : ℕ :=
Finset.card { (a, b) : G × G | a * b = b * a ∧ a^2 = 1 }
def invB (G) [Group G] [Fintype G] [DecidableEq G] : ℕ :=
Finset.card { (a, b) : G × G | (a * b)^5 = 1 }
def invC (G) [Group G] [Fintype G] [DecidableEq G] : ℕ :=
Finset.card { (a, b) : G × G | a^7 = b^7 }

def Group.signature (G) [Group G] [Fintype G] [DecidableEq G] := ((inv1 G, inv3 G, inv5 G), (inv6 G, inv13 G, invA G), (invB G, invC G))

/-
# Groups of order 1
-/
abbrev Gap_1_1 := Multiplicative (ZMod 1)

/-
# Groups of order 2
-/
abbrev Gap_2_1 := Multiplicative (ZMod 2)

/-
# Groups of order 3
-/
abbrev Gap_3_1 := Multiplicative (ZMod 3)

/-
# Groups of order 4
-/
abbrev Gap_4_1 := Multiplicative (ZMod 4)
abbrev Gap_4_2 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

def sigs := [Group.signature Gap_4_1]


#eval [Group.signature Gap_4_1, Group.signature Gap_4_2].Nodup

/-
# Groups of order 5
-/
abbrev Gap_5_1 := Multiplicative (ZMod 5)

/-
# Groups of order 6
-/
abbrev Gap_6_2 := Multiplicative (ZMod 6)
abbrev Gap_6_1 := Equiv.Perm (Fin 3)

#eval Group.signature Gap_6_2
#eval Group.signature Gap_6_1

/-
# Groups of order 7
-/
abbrev Gap_7_1 := Multiplicative (ZMod 7)

/-
# Groups of order 8
-/
abbrev Gap_8_1 := Multiplicative (ZMod 8)
abbrev Gap_8_3 := DihedralGroup 4
abbrev Gap_8_4 := QuaternionGroup 2
abbrev Gap_8_5 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
abbrev Gap_8_2 := Multiplicative (ZMod 2) × Multiplicative (ZMod 4)

#eval Group.signature Gap_8_1
#eval Group.signature Gap_8_3
#eval Group.signature Gap_8_4
#eval Group.signature Gap_8_5
#eval Group.signature Gap_8_2

/-
# Groups of order 9
-/

abbrev Gap_9_1 := Multiplicative (ZMod 9)
abbrev Gap_9_2 := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

#eval Group.signature Gap_9_1
#eval Group.signature Gap_9_2

/-
# Groups of order 10
-/
abbrev Gap_10_2 := Multiplicative (ZMod 10)
abbrev Gap_10_1 := DihedralGroup 5

#eval Group.signature Gap_10_2
#eval Group.signature Gap_10_1

/-
# Groups of order 11
-/
abbrev Gap_11_1 := Multiplicative (ZMod 11)

/-
# Groups of order 12
-/
abbrev Gap_12_2 := Multiplicative (ZMod 12)
abbrev Gap_12_3 := AlternatingGroup 4
abbrev Gap_12_4 := DihedralGroup 6
abbrev Gap_12_1 := DicyclicGroup 3
abbrev Gap_12_5 := Multiplicative (ZMod 2) × Multiplicative (ZMod 6)

#eval Group.signature Gap_12_1
#eval Group.signature Gap_12_2
#eval Group.signature Gap_12_3
#eval Group.signature Gap_12_4
#eval Group.signature Gap_12_5

/-
# Groups of order 13
-/
abbrev Gap_13_1 := Multiplicative (ZMod 13)

/-
# Groups of order 14
-/
abbrev Gap_14_2 := Multiplicative (ZMod 14)
abbrev Gap_14_1 := DihedralGroup 7



abbrev Gap_15_1 := Multiplicative (ZMod 15)
abbrev Gap_16_1 := Multiplicative (ZMod 16)
abbrev Gap_16_7 := DihedralGroup 8
abbrev Gap_16_9 := QuaternionGroup 4
instance : Fact ((3 : ZMod (8:PNat)) ^ (2:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_16_8 := Cpqr 8 2 3
instance : Fact ((5 : ZMod (8:PNat)) ^ (2:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_16_6 := Cpqr 8 2 5
instance : Fact ((3 : ZMod (4:PNat)) ^ (4:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_16_4 := Cpqr 4 4 3
abbrev Gap_16_2 := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)
abbrev Gap_16_14 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
abbrev Gap_16_5 := Multiplicative (ZMod 2) × Multiplicative (ZMod 8)
abbrev Gap_16_10 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 4)
abbrev Gap_16_11 := Multiplicative (ZMod 2) × DihedralGroup 4
abbrev Gap_16_12 := Multiplicative (ZMod 2) × QuaternionGroup 2
abbrev Gap_17_1 := Multiplicative (ZMod 17)
abbrev Gap_18_2 := Multiplicative (ZMod 18)
abbrev Gap_18_1 := DihedralGroup 9
abbrev Gap_18_4 := Dihedralization (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
abbrev Gap_18_5 := Multiplicative (ZMod 3) × Multiplicative (ZMod 6)
abbrev Gap_18_3 := Multiplicative (ZMod 3) × Equiv.Perm (Fin 3)
abbrev Gap_19_1 := Multiplicative (ZMod 19)
abbrev Gap_20_2 := Multiplicative (ZMod 20)
abbrev Gap_20_4 := DihedralGroup 10
abbrev Gap_20_3 := @FrobeniusGroup 5 (Fact.mk (by decide : Nat.Prime 5))
abbrev Gap_20_1 := DicyclicGroup 5
abbrev Gap_20_5 := Multiplicative (ZMod 2) × Multiplicative (ZMod 10)
abbrev Gap_21_2 := Multiplicative (ZMod 21)
instance : Fact ((2 : ZMod (7:PNat)) ^ (3:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_21_1 := Cpqr 7 3 2
abbrev Gap_22_2 := Multiplicative (ZMod 22)
abbrev Gap_22_1 := DihedralGroup 11
abbrev Gap_23_1 := Multiplicative (ZMod 23)
abbrev Gap_24_2 := Multiplicative (ZMod 24)
abbrev Gap_24_12 := Equiv.Perm (Fin 4)
abbrev Gap_24_6 := DihedralGroup 12
abbrev Gap_24_4 := DicyclicGroup 6
instance : Fact ((2 : ZMod (3:PNat)) ^ (8:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_24_1 := Cpqr 3 8 2
abbrev Gap_24_9 := Multiplicative (ZMod 2) × Multiplicative (ZMod 12)
abbrev Gap_24_15 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 6)
abbrev Gap_24_13 := Multiplicative (ZMod 2) × AlternatingGroup 4
abbrev Gap_24_5 := Multiplicative (ZMod 4) × Equiv.Perm (Fin 3)
abbrev Gap_24_10 := Multiplicative (ZMod 3) × DihedralGroup 4
abbrev Gap_24_14 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)
abbrev Gap_24_11 := Multiplicative (ZMod 3) × QuaternionGroup 2
abbrev Gap_24_7 := Multiplicative (ZMod 2) × DicyclicGroup 3
abbrev Gap_25_1 := Multiplicative (ZMod 25)
abbrev Gap_25_2 := Multiplicative (ZMod 5) × Multiplicative (ZMod 5)
abbrev Gap_26_2 := Multiplicative (ZMod 26)
abbrev Gap_26_1 := DihedralGroup 13
abbrev Gap_27_1 := Multiplicative (ZMod 27)
abbrev Gap_27_5 := Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3)
abbrev Gap_27_2 := Multiplicative (ZMod 3) × Multiplicative (ZMod 9)
abbrev Gap_28_2 := Multiplicative (ZMod 28)
abbrev Gap_28_3 := DihedralGroup 14
abbrev Gap_28_1 := DicyclicGroup 7
abbrev Gap_28_4 := Multiplicative (ZMod 2) × Multiplicative (ZMod 14)
abbrev Gap_29_1 := Multiplicative (ZMod 29)
abbrev Gap_30_4 := Multiplicative (ZMod 30)
abbrev Gap_30_3 := DihedralGroup 15
abbrev Gap_30_1 := Multiplicative (ZMod 5) × Equiv.Perm (Fin 3)
abbrev Gap_30_2 := Multiplicative (ZMod 3) × DihedralGroup 5
abbrev Gap_31_1 := Multiplicative (ZMod 31)
abbrev Gap_32_1 := Multiplicative (ZMod 32)
abbrev Gap_32_18 := DihedralGroup 16
abbrev Gap_32_20 := QuaternionGroup 8
instance : Fact ((3 : ZMod (4:PNat)) ^ (8:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_32_12 := Cpqr 4 8 3
instance : Fact ((3 : ZMod (8:PNat)) ^ (4:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_32_4 := Cpqr 8 4 3
abbrev Gap_32_51 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
abbrev Gap_32_3 := Multiplicative (ZMod 4) × Multiplicative (ZMod 8)
abbrev Gap_32_16 := Multiplicative (ZMod 2) × Multiplicative (ZMod 16)
abbrev Gap_32_21 := Multiplicative (ZMod 2) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4)
abbrev Gap_32_36 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 8)
abbrev Gap_32_45 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 4)
abbrev Gap_32_25 := Multiplicative (ZMod 4) × DihedralGroup 4
abbrev Gap_32_39 := Multiplicative (ZMod 2) × DihedralGroup 8
abbrev Gap_32_40 := Multiplicative (ZMod 2) × Cpqr 8 2 3
abbrev Gap_32_46 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × DihedralGroup 4
abbrev Gap_32_37 := Multiplicative (ZMod 2) × Cpqr 8 2 5
abbrev Gap_32_26 := Multiplicative (ZMod 4) × QuaternionGroup 2
abbrev Gap_32_41 := Multiplicative (ZMod 2) × QuaternionGroup 4
abbrev Gap_32_47 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × QuaternionGroup 2
abbrev Gap_32_23 := Multiplicative (ZMod 2) × Cpqr 4 4 3
abbrev Gap_33_1 := Multiplicative (ZMod 33)
abbrev Gap_34_2 := Multiplicative (ZMod 34)
abbrev Gap_34_1 := DihedralGroup 17
abbrev Gap_35_1 := Multiplicative (ZMod 35)
abbrev Gap_36_2 := Multiplicative (ZMod 36)
abbrev Gap_36_4 := DihedralGroup 18
abbrev Gap_36_1 := DicyclicGroup 9
abbrev Gap_36_14 := Multiplicative (ZMod 6) × Multiplicative (ZMod 6)
abbrev Gap_36_5 := Multiplicative (ZMod 2) × Multiplicative (ZMod 18)
abbrev Gap_36_8 := Multiplicative (ZMod 3) × Multiplicative (ZMod 12)
abbrev Gap_36_12 := Equiv.Perm (Fin 3) × Multiplicative (ZMod 6)
abbrev Gap_36_11 := Multiplicative (ZMod 3) × AlternatingGroup 4
abbrev Gap_36_6 := Multiplicative (ZMod 3) × DicyclicGroup 3
abbrev Gap_36_13 := Multiplicative (ZMod 2) × Dihedralization (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
abbrev Gap_37_1 := Multiplicative (ZMod 37)
abbrev Gap_38_2 := Multiplicative (ZMod 38)
abbrev Gap_38_1 := DihedralGroup 19
abbrev Gap_39_2 := Multiplicative (ZMod 39)
instance : Fact ((3 : ZMod (13:PNat)) ^ (3:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_39_1 := Cpqr 13 3 3
abbrev Gap_40_2 := Multiplicative (ZMod 40)
abbrev Gap_40_6 := DihedralGroup 20
abbrev Gap_40_4 := DicyclicGroup 10
instance : Fact ((4 : ZMod (5:PNat)) ^ (8:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_40_3 := Cpqr 5 8 4
abbrev Gap_40_9 := Multiplicative (ZMod 2) × Multiplicative (ZMod 20)
abbrev Gap_40_14 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 10)
abbrev Gap_40_12 := Multiplicative (ZMod 2) × @FrobeniusGroup 5 (Fact.mk (by decide : Nat.Prime 5))
abbrev Gap_40_5 := Multiplicative (ZMod 4) × DihedralGroup 5
abbrev Gap_40_10 := Multiplicative (ZMod 5) × DihedralGroup 4
abbrev Gap_40_13 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × DihedralGroup 5
abbrev Gap_40_11 := Multiplicative (ZMod 5) × QuaternionGroup 2
abbrev Gap_40_7 := Multiplicative (ZMod 2) × DicyclicGroup 5
abbrev Gap_41_1 := Multiplicative (ZMod 41)
abbrev Gap_42_6 := Multiplicative (ZMod 42)
abbrev Gap_42_5 := DihedralGroup 21
abbrev Gap_42_1 := @FrobeniusGroup 7 (Fact.mk (by decide : Nat.Prime 7))
abbrev Gap_42_3 := Equiv.Perm (Fin 3) × Multiplicative (ZMod 7)
abbrev Gap_42_4 := Multiplicative (ZMod 3) × DihedralGroup 7
abbrev Gap_42_2 := Multiplicative (ZMod 2) × Cpqr 7 3 2
abbrev Gap_43_1 := Multiplicative (ZMod 43)
abbrev Gap_44_2 := Multiplicative (ZMod 44)
abbrev Gap_44_3 := DihedralGroup 22
abbrev Gap_44_1 := DicyclicGroup 11
abbrev Gap_44_4 := Multiplicative (ZMod 2) × Multiplicative (ZMod 22)
abbrev Gap_45_1 := Multiplicative (ZMod 45)
abbrev Gap_45_2 := Multiplicative (ZMod 3) × Multiplicative (ZMod 15)
abbrev Gap_46_2 := Multiplicative (ZMod 46)
abbrev Gap_46_1 := DihedralGroup 23
abbrev Gap_47_1 := Multiplicative (ZMod 47)
abbrev Gap_48_2 := Multiplicative (ZMod 48)
abbrev Gap_48_7 := DihedralGroup 24
abbrev Gap_48_8 := DicyclicGroup 12
instance : Fact ((23 : ZMod (24:PNat)) ^ (2:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_48_6 := Cpqr 24 2 23
instance : Fact ((2 : ZMod (3:PNat)) ^ (16:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_48_1 := Cpqr 3 16 2
abbrev Gap_48_20 := Multiplicative (ZMod 4) × Multiplicative (ZMod 12)
abbrev Gap_48_23 := Multiplicative (ZMod 2) × Multiplicative (ZMod 24)
abbrev Gap_48_52 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 6)
abbrev Gap_48_44 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 12)
abbrev Gap_48_48 := Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)
abbrev Gap_48_31 := Multiplicative (ZMod 4) × AlternatingGroup 4
abbrev Gap_48_38 := Equiv.Perm (Fin 3) × DihedralGroup 4
abbrev Gap_48_49 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × AlternatingGroup 4
abbrev Gap_48_4 := Equiv.Perm (Fin 3) × Multiplicative (ZMod 8)
abbrev Gap_48_25 := Multiplicative (ZMod 3) × DihedralGroup 8
abbrev Gap_48_45 := Multiplicative (ZMod 6) × DihedralGroup 4
abbrev Gap_48_40 := Equiv.Perm (Fin 3) × QuaternionGroup 2
abbrev Gap_48_36 := Multiplicative (ZMod 2) × DihedralGroup 12
abbrev Gap_48_51 := Equiv.Perm (Fin 3) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
abbrev Gap_48_26 := Multiplicative (ZMod 3) × Cpqr 8 2 3
abbrev Gap_48_24 := Multiplicative (ZMod 3) × Cpqr 8 2 5
abbrev Gap_48_46 := Multiplicative (ZMod 6) × QuaternionGroup 2
abbrev Gap_48_27 := Multiplicative (ZMod 3) × QuaternionGroup 4
abbrev Gap_48_11 := Multiplicative (ZMod 4) × DicyclicGroup 3
abbrev Gap_48_34 := Multiplicative (ZMod 2) × DicyclicGroup 6
abbrev Gap_48_42 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × DicyclicGroup 3
abbrev Gap_48_35 := Equiv.Perm (Fin 3) × Multiplicative (ZMod 2) × Multiplicative (ZMod 4)
abbrev Gap_48_9 := Multiplicative (ZMod 2) × Cpqr 3 8 2
abbrev Gap_48_22 := Multiplicative (ZMod 3) × Cpqr 4 4 3
abbrev Gap_49_1 := Multiplicative (ZMod 49)
abbrev Gap_49_2 := Multiplicative (ZMod 7) × Multiplicative (ZMod 7)
abbrev Gap_50_2 := Multiplicative (ZMod 50)
abbrev Gap_50_1 := DihedralGroup 25
abbrev Gap_50_4 := Dihedralization (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))
abbrev Gap_50_5 := Multiplicative (ZMod 5) × Multiplicative (ZMod 10)
abbrev Gap_50_3 := Multiplicative (ZMod 5) × DihedralGroup 5
abbrev Gap_51_1 := Multiplicative (ZMod 51)
abbrev Gap_52_2 := Multiplicative (ZMod 52)
abbrev Gap_52_4 := DihedralGroup 26
abbrev Gap_52_1 := DicyclicGroup 13
instance : Fact ((5 : ZMod (13:PNat)) ^ (4:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_52_3 := Cpqr 13 4 5
abbrev Gap_52_5 := Multiplicative (ZMod 2) × Multiplicative (ZMod 26)
abbrev Gap_53_1 := Multiplicative (ZMod 53)
abbrev Gap_54_2 := Multiplicative (ZMod 54)
abbrev Gap_54_1 := DihedralGroup 27
instance : Fact ((2 : ZMod (9:PNat)) ^ (6:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_54_6 := Cpqr 9 6 2
abbrev Gap_54_9 := Multiplicative (ZMod 3) × Multiplicative (ZMod 18)
abbrev Gap_54_15 := Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 6)
abbrev Gap_54_4 := Equiv.Perm (Fin 3) × Multiplicative (ZMod 9)
abbrev Gap_54_3 := Multiplicative (ZMod 3) × DihedralGroup 9
abbrev Gap_54_12 := Equiv.Perm (Fin 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3)
abbrev Gap_54_13 := Multiplicative (ZMod 3) × Dihedralization (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
abbrev Gap_55_2 := Multiplicative (ZMod 55)
instance : Fact ((3 : ZMod (11:PNat)) ^ (5:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_55_1 := Cpqr 11 5 3
abbrev Gap_56_2 := Multiplicative (ZMod 56)
abbrev Gap_56_5 := DihedralGroup 28
abbrev Gap_56_3 := DicyclicGroup 14
instance : Fact ((6 : ZMod (7:PNat)) ^ (8:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_56_1 := Cpqr 7 8 6
abbrev Gap_56_8 := Multiplicative (ZMod 2) × Multiplicative (ZMod 28)
abbrev Gap_56_13 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 14)
abbrev Gap_56_4 := Multiplicative (ZMod 4) × DihedralGroup 7
abbrev Gap_56_9 := Multiplicative (ZMod 7) × DihedralGroup 4
abbrev Gap_56_12 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × DihedralGroup 7
abbrev Gap_56_10 := Multiplicative (ZMod 7) × QuaternionGroup 2
abbrev Gap_56_6 := Multiplicative (ZMod 2) × DicyclicGroup 7
abbrev Gap_57_2 := Multiplicative (ZMod 57)
instance : Fact ((7 : ZMod (19:PNat)) ^ (3:PNat).val = 1) := ⟨(by decide)⟩
abbrev Gap_57_1 := Cpqr 19 3 7
abbrev Gap_58_2 := Multiplicative (ZMod 58)
abbrev Gap_58_1 := DihedralGroup 29
abbrev Gap_59_1 := Multiplicative (ZMod 59)
abbrev Gap_60_4 := Multiplicative (ZMod 60)
abbrev Gap_60_5 := AlternatingGroup 5
abbrev Gap_60_12 := DihedralGroup 30
abbrev Gap_60_3 := DicyclicGroup 15
abbrev Gap_60_13 := Multiplicative (ZMod 2) × Multiplicative (ZMod 30)
abbrev Gap_60_8 := Equiv.Perm (Fin 3) × DihedralGroup 5
abbrev Gap_60_6 := Multiplicative (ZMod 3) × @FrobeniusGroup 5 (Fact.mk (by decide : Nat.Prime 5))
abbrev Gap_60_9 := Multiplicative (ZMod 5) × AlternatingGroup 4
abbrev Gap_60_10 := Multiplicative (ZMod 6) × DihedralGroup 5
abbrev Gap_60_11 := Equiv.Perm (Fin 3) × Multiplicative (ZMod 10)
abbrev Gap_60_1 := Multiplicative (ZMod 5) × DicyclicGroup 3
abbrev Gap_60_2 := Multiplicative (ZMod 3) × DicyclicGroup 5
