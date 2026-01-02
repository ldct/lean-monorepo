#!/usr/bin/env python3
"""
Parse group labels from GroupNames website and generate Lean types.
Returns None for groups not yet implemented in Lean.
"""

import re
from typing import Optional


def parse_group_label(label: str, order: int) -> Optional[str]:
    """
    Parse a group label and return the corresponding Lean type.

    Args:
        label: Group label (e.g., "C2xC6", "D4", "S3")
        order: Order of the group (needed for some conversions)

    Returns:
        Lean type string or None if not implemented

    Examples:
        >>> parse_group_label("C2", 2)
        'Multiplicative (ZMod 2)'
        >>> parse_group_label("C2xC6", 12)
        'Multiplicative (ZMod 2) × Multiplicative (ZMod 6)'
        >>> parse_group_label("D4", 8)
        'DihedralGroup 4'
        >>> parse_group_label("C4:C4", 16)
        None
    """
    # Normalize label
    label = label.strip()

    # Cyclic groups: C<n> or Z<n>
    if match := re.match(r'^C(\d+)$', label):
        n = match.group(1)
        return f"Multiplicative (ZMod {n})"

    # Dihedral groups: D<n> or Dih<n>
    if match := re.match(r'^D(\d+)$', label):
        n = match.group(1)
        return f"DihedralGroup {n}"

    # Symmetric groups: S<n>
    if match := re.match(r'^S(\d+)$', label):
        n = match.group(1)
        if n in ['3', '4']:
            return f"Equiv.Perm (Fin {n})"
        return None  # Only S3 and S4 seem to be implemented

    # Alternating groups: A<n>
    if match := re.match(r'^A(\d+)$', label):
        n = match.group(1)
        if n in ['4', '5']:
            return f"AlternatingGroup {n}"
        return None  # Only A4 and A5 seem to be implemented

    # Quaternion groups: Q8, Q16, Q32
    # Pattern: Q<4n> maps to QuaternionGroup n
    if match := re.match(r'^Q(\d+)$', label):
        order_q = int(match.group(1))
        if order_q % 4 == 0:
            n = order_q // 4
            return f"QuaternionGroup {n}"
        return None

    # Powers of cyclic groups: C<n>^<k> (e.g., C2^3)
    if match := re.match(r'^C(\d+)\^(\d+)$', label):
        n = match.group(1)
        k = int(match.group(2))
        parts = [f"Multiplicative (ZMod {n})"] * k
        return " × ".join(parts)

    # Direct products: C<n>xC<m> or C<n>xC<m>xC<p>, etc.
    # Also handles patterns like C2xD4, C3xS3, etc.
    if 'x' in label:
        parts = label.split('x')
        lean_parts = []
        for part in parts:
            part_lean = parse_group_label(part, 0)  # Recursive call
            if part_lean is None:
                return None
            lean_parts.append(part_lean)
        return " × ".join(lean_parts)

    # Special groups with specific names (check before general patterns)
    special_groups = {
        'He3': None,  # Heisenberg group - not implemented
        'GL(2,3)': None,
        'CSU(2,3)': None,
        'SL(2,3)': None,
        'SD16': "Cpqr 8 2 3",  # Semidihedral group = Cpq(8,2,3)
        'SD32': None,
        'M4(2)': "Cpqr 8 2 5",  # Modular group M4(2) = Cpq(8,2,5)
        'M5(2)': None,
        'C4:C4': "Cpqr 4 4 3",  # C4:C4 = Cpq(4,4,3)
        'C7:C3': "Cpqr 7 3 2",  # C7:C3 = Cpq(7,3,2)
        'C13:C3': "Cpqr 13 3 3",  # C13:C3 = Cpq(13,3,3)
        'C3:S3': "Dihedralization (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))",
        'C5:D5': "Dihedralization (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))",
        'ES+(2,2)': None,  # Extraspecial - not implemented
        'ES-(2,2)': None,
        'ES-(3,1)': None,
    }

    if label in special_groups:
        return special_groups[label]

    # Semidirect products: C<n>:C<m> - not implemented yet
    if ':' in label:
        return None

    # Central products: C<n>.C<m> - not implemented yet
    if '.' in label:
        return None

    # Dicyclic groups: Dic<n>
    # Dicyclic group Dicₙ has order 4n
    if match := re.match(r'^Dic(\d+)$', label):
        n = match.group(1)
        return f"DicyclicGroup {n}"

    # Cpq groups: Cpq<p>,<q>,<r>
    # Semidirect product parameterized by p, q, r
    if match := re.match(r'^Cpq(\d+),(\d+),(\d+)$', label):
        p = match.group(1)
        q = match.group(2)
        r = match.group(3)
        return f"Cpqr {p} {q} {r}"

    # Wreath products: C<n>wrC<m> - not implemented yet
    if 'wr' in label:
        return None

    # Special notation with 'o': C4oD4 - not implemented yet
    if 'o' in label and 'o' != label[0]:
        return None

    # Frobenius groups: F<p> where p is prime
    if match := re.match(r'^F(\d+)$', label):
        p = match.group(1)
        if p in ['5', '7']:
            return f"@FrobeniusGroup {p} (Fact.mk (by decide : Nat.Prime {p}))"
        # F8 and other F groups not implemented
        return None

    # Unknown/unimplemented
    return None


def test_against_existing():
    """Test the parser against known examples from generate_direct_products.py"""
    test_cases = [
        # (label, order, gap_id, expected_lean_type)
        ("C1", 1, 1, "Multiplicative (ZMod 1)"),
        ("C2", 2, 1, "Multiplicative (ZMod 2)"),
        ("C4", 4, 1, "Multiplicative (ZMod 4)"),
        ("C2^2", 4, 2, "Multiplicative (ZMod 2) × Multiplicative (ZMod 2)"),
        ("S3", 6, 1, "Equiv.Perm (Fin 3)"),
        ("C6", 6, 2, "Multiplicative (ZMod 6)"),
        ("D4", 8, 3, "DihedralGroup 4"),
        ("Q8", 8, 4, "QuaternionGroup 2"),
        ("C2^3", 8, 5, "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)"),
        ("C2xC4", 8, 2, "Multiplicative (ZMod 2) × Multiplicative (ZMod 4)"),
        ("C3^2", 9, 2, "Multiplicative (ZMod 3) × Multiplicative (ZMod 3)"),
        ("D5", 10, 1, "DihedralGroup 5"),
        ("A4", 12, 3, "AlternatingGroup 4"),
        ("D6", 12, 4, "DihedralGroup 6"),
        ("C2xC6", 12, 5, "Multiplicative (ZMod 2) × Multiplicative (ZMod 6)"),
        ("C4^2", 16, 2, "Multiplicative (ZMod 4) × Multiplicative (ZMod 4)"),
        ("C2xC8", 16, 5, "Multiplicative (ZMod 2) × Multiplicative (ZMod 8)"),
        ("D8", 16, 7, "DihedralGroup 8"),
        ("C2^4", 16, 14, "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)"),
        ("C2xD4", 16, 11, "Multiplicative (ZMod 2) × DihedralGroup 4"),
        ("C2xQ8", 16, 12, "Multiplicative (ZMod 2) × QuaternionGroup 2"),
        ("D9", 18, 1, "DihedralGroup 9"),
        ("C3xS3", 18, 3, "Multiplicative (ZMod 3) × Equiv.Perm (Fin 3)"),
        ("C3xC6", 18, 5, "Multiplicative (ZMod 3) × Multiplicative (ZMod 6)"),
        ("D10", 20, 4, "DihedralGroup 10"),
        ("C2xC10", 20, 5, "Multiplicative (ZMod 2) × Multiplicative (ZMod 10)"),
        ("S4", 24, 12, "Equiv.Perm (Fin 4)"),
        ("C4xS3", 24, 5, "Multiplicative (ZMod 4) × Equiv.Perm (Fin 3)"),
        ("C2xA4", 24, 13, "Multiplicative (ZMod 2) × AlternatingGroup 4"),
        ("C3xD4", 24, 10, "Multiplicative (ZMod 3) × DihedralGroup 4"),
        ("C3xQ8", 24, 11, "Multiplicative (ZMod 3) × QuaternionGroup 2"),
        ("C5^2", 25, 2, "Multiplicative (ZMod 5) × Multiplicative (ZMod 5)"),
        ("C3^3", 27, 5, "Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3)"),
        ("C3xC9", 27, 2, "Multiplicative (ZMod 3) × Multiplicative (ZMod 9)"),
        ("D14", 28, 3, "DihedralGroup 14"),
        ("C2xC14", 28, 4, "Multiplicative (ZMod 2) × Multiplicative (ZMod 14)"),
        ("C5xS3", 30, 1, "Multiplicative (ZMod 5) × Equiv.Perm (Fin 3)"),
        ("C3xD5", 30, 2, "Multiplicative (ZMod 3) × DihedralGroup 5"),
        ("D15", 30, 3, "DihedralGroup 15"),
        ("C4xC8", 32, 3, "Multiplicative (ZMod 4) × Multiplicative (ZMod 8)"),
        ("C2xC16", 32, 16, "Multiplicative (ZMod 2) × Multiplicative (ZMod 16)"),
        ("D16", 32, 18, "DihedralGroup 16"),
        ("C6^2", 36, 14, "Multiplicative (ZMod 6) × Multiplicative (ZMod 6)"),
        ("C4xD5", 40, 5, "Multiplicative (ZMod 4) × DihedralGroup 5"),
        ("C5xD4", 40, 10, "Multiplicative (ZMod 5) × DihedralGroup 4"),
        ("S3xC7", 42, 3, "Equiv.Perm (Fin 3) × Multiplicative (ZMod 7)"),
        ("C3xD7", 42, 4, "Multiplicative (ZMod 3) × DihedralGroup 7"),
        ("D21", 42, 5, "DihedralGroup 21"),
        ("C3xC15", 45, 2, "Multiplicative (ZMod 3) × Multiplicative (ZMod 15)"),
        ("A5", 60, 5, "AlternatingGroup 5"),
        ("C2xC30", 60, 13, "Multiplicative (ZMod 2) × Multiplicative (ZMod 30)"),
        ("C5xA4", 60, 9, "Multiplicative (ZMod 5) × AlternatingGroup 4"),
        ("D30", 60, 12, "DihedralGroup 30"),
        # Dicyclic groups - now implemented
        ("Dic3", 12, 1, "DicyclicGroup 3"),
        # Frobenius groups - now implemented
        ("F5", 20, 3, "@FrobeniusGroup 5 (Fact.mk (by decide : Nat.Prime 5))"),
        ("F7", 42, 1, "@FrobeniusGroup 7 (Fact.mk (by decide : Nat.Prime 7))"),
        # Semidirect products - special cases
        ("C3:S3", 18, 4, "Dihedralization (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))"),
        # Not implemented - should return None
        ("C4:C4", 16, 4, None),
        ("F8", 56, 11, None),
        ("SL(2,3)", 24, 3, None),
    ]

    passed = 0
    failed = 0

    print("Testing parser against known examples from generate_direct_products.py\n")
    print("=" * 80)

    for label, order, gap_id, expected in test_cases:
        result = parse_group_label(label, order)
        if result == expected:
            passed += 1
            status = "✓ PASS"
        else:
            failed += 1
            status = "✗ FAIL"
            print(f"{status}: {label} (order {order})")
            print(f"  Expected: {expected}")
            print(f"  Got:      {result}")
            print()

    print("=" * 80)
    print(f"Results: {passed} passed, {failed} failed out of {len(test_cases)} tests")

    return failed == 0


def analyze_tsv_file(filename: str = "group_names.tsv"):
    """Analyze which groups from the TSV file can be parsed."""
    import csv

    implemented = []
    not_implemented = []

    with open(filename, 'r') as f:
        reader = csv.reader(f, delimiter='\t')
        for row in reader:
            if len(row) != 2:
                continue
            label = row[0]
            gap_id = row[1]
            order = int(gap_id.split(',')[0])

            lean_type = parse_group_label(label, order)
            if lean_type:
                implemented.append((label, gap_id, lean_type))
            else:
                not_implemented.append((label, gap_id))

    print(f"\n{'='*80}")
    print(f"Analysis of {filename}")
    print(f"{'='*80}\n")
    print(f"✓ Implemented in Lean: {len(implemented)}/{len(implemented) + len(not_implemented)}")
    print(f"✗ Not implemented: {len(not_implemented)}/{len(implemented) + len(not_implemented)}")

    if implemented:
        print(f"\n{'='*80}")
        print("Sample implemented groups (first 20):")
        print(f"{'='*80}")
        for label, gap_id, lean_type in implemented[:20]:
            print(f"{label:15} Gap({gap_id:6}) → {lean_type}")

    if not_implemented:
        print(f"\n{'='*80}")
        print("Not implemented (first 30):")
        print(f"{'='*80}")
        for label, gap_id in not_implemented[:30]:
            print(f"{label:15} Gap({gap_id})")

    return implemented, not_implemented


if __name__ == "__main__":
    import sys

    success = test_against_existing()

    if not success:
        exit(1)

    # If tests pass, analyze the TSV file if it exists
    try:
        implemented, not_implemented = analyze_tsv_file()
        print(f"\n{'='*80}")
        print(f"Summary: {len(implemented)} groups can be generated, {len(not_implemented)} cannot")
        print(f"{'='*80}")
    except FileNotFoundError:
        print("\nNote: group_names.tsv not found, skipping TSV analysis")

    exit(0)
