#!/usr/bin/env python3
"""
Generate Lean files for all groups in the SmallGroups project.
Based on GAP IDs from GroupNames webpage (https://people.maths.bris.ac.uk/~matyd/GroupNames/index.html)

Reads from group_names.tsv and uses parse_group_label to determine Lean types.
"""

from pathlib import Path
import csv
import re
from parse_group_label import parse_group_label

LEAN_FILE_HEADER = """import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Playground.Geometry.SmallGroups.AlternatingGroup
import Playground.Geometry.Cpq
import Playground.Geometry.Dicyclic
import Playground.Geometry.Dihedralization
import Playground.Geometry.FrobeniusGroup

set_option linter.style.longLine false

"""


def load_groups_from_tsv(tsv_file: str = "group_names.tsv"):
    """
    Load groups from TSV file and parse their Lean types.
    Returns: dict mapping order -> [(gap_id, label, lean_type), ...]
    If primary label fails to parse, tries alternative names.
    """
    groups_by_order = {}

    with open(tsv_file, 'r') as f:
        reader = csv.reader(f, delimiter='\t')
        for row in reader:
            if len(row) < 2:
                continue

            label = row[0]
            gap_id_and_alts = row[1]

            # Split the second column by whitespace to separate GAP ID from alternative names
            parts = gap_id_and_alts.split()
            gap_id_str = parts[0]

            # Parse gap_id as "order,id"
            order, gap_id = map(int, gap_id_str.split(','))

            # Check for alternative names in the remaining parts
            alt_labels = []
            if len(parts) > 1:
                # Additional parts after GAP ID are alternative names
                alt_labels.extend(parts[1:])

            # Also check for alternative names in column 3+
            if len(row) >= 3:
                for alt_name in row[2:]:
                    alt_name = alt_name.strip()
                    if alt_name:
                        alt_labels.append(alt_name)

            # Try to parse the Lean type from primary label
            lean_type = parse_group_label(label, order)

            # If primary label fails, try alternative labels
            if not lean_type:
                for alt_label in alt_labels:
                    lean_type = parse_group_label(alt_label, order)
                    if lean_type:
                        break

            if lean_type:  # Only include if we can generate it
                if order not in groups_by_order:
                    groups_by_order[order] = []
                groups_by_order[order].append((gap_id, label, lean_type))

    return groups_by_order


def main():
    """Generate single SmallGroups.lean file with all group definitions."""
    base_dir = Path("Playground/Geometry/SmallGroups")

    print("Loading groups from group_names.tsv...")
    groups_by_order = load_groups_from_tsv()

    total_groups = sum(len(groups) for groups in groups_by_order.values())
    print(f"Found {total_groups} implementable groups\n")

    # Check if any group uses AlternatingGroup
    uses_alternating = False
    abbrev_lines = []
    cpqr_instances_added = set()  # Track which Cpqr instances we've already added

    # Generate all group definitions
    for order, groups in sorted(groups_by_order.items()):
        for gap_id, label, lean_type in groups:
            abbrev_name = f"Gap_{order}_{gap_id}"

            # Check if this group uses AlternatingGroup
            if "AlternatingGroup" in lean_type:
                uses_alternating = True

            # Check if this is a Cpqr group and add instance declaration (only once per p,q,r)
            if "Cpqr" in lean_type:
                # Extract all p, q, r from "Cpqr p q r" (may appear multiple times in products)
                matches = re.finditer(r'Cpqr\s+(\d+)\s+(\d+)\s+(\d+)', lean_type)
                for match in matches:
                    p, q, r = match.groups()
                    param_tuple = (p, q, r)
                    if param_tuple not in cpqr_instances_added:
                        instance_line = f"instance : Fact (({r} : ZMod ({p}:PNat)) ^ ({q}:PNat).val = 1) := ⟨(by decide)⟩"
                        abbrev_lines.append(instance_line)
                        cpqr_instances_added.add(param_tuple)

            # Add the abbrev line
            abbrev_lines.append(f"abbrev {abbrev_name} := {lean_type}")
            print(f"✓ Added {abbrev_name}: {label}")

    header = LEAN_FILE_HEADER

    # Write SmallGroups.lean with header and all abbrev lines
    smallgroups_path = base_dir / "SmallGroups.lean"
    content = header + "\n".join(abbrev_lines) + "\n"
    smallgroups_path.write_text(content)

    print(f"\n{'='*60}")
    print(f"✓ Generated {smallgroups_path} with {len(abbrev_lines)} group definitions")
    print(f"\n⚠️  IMPORTANT: You need to:")
    print(f"  1. Regenerate evaluation files: python3 generate_eval_files.py")


if __name__ == "__main__":
    main()
