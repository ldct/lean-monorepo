#!/usr/bin/env python3
"""
Generate Lean files for all groups in the SmallGroups project.
Based on GAP IDs from GroupNames webpage (https://people.maths.bris.ac.uk/~matyd/GroupNames/index.html)

Reads from group_names.tsv and uses parse_group_label to determine Lean types.
"""

from pathlib import Path
import csv
from parse_group_label import parse_group_label

LEAN_FILE_HEADER = """import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Playground.Geometry.SmallGroups.AlternatingGroup

set_option linter.style.longLine false

"""


def load_groups_from_tsv(tsv_file: str = "group_names.tsv"):
    """
    Load groups from TSV file and parse their Lean types.
    Returns: dict mapping order -> [(gap_id, label, lean_type), ...]
    """
    groups_by_order = {}

    with open(tsv_file, 'r') as f:
        reader = csv.reader(f, delimiter='\t')
        for row in reader:
            if len(row) != 2:
                continue

            label = row[0]
            gap_id_str = row[1]

            # Parse gap_id as "order,id"
            order, gap_id = map(int, gap_id_str.split(','))

            # Try to parse the Lean type
            lean_type = parse_group_label(label, order)

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

    # Generate all group definitions
    for order, groups in sorted(groups_by_order.items()):
        for gap_id, label, lean_type in groups:
            abbrev_name = f"Gap_{order}_{gap_id}"

            # Check if this group uses AlternatingGroup
            if "AlternatingGroup" in lean_type:
                uses_alternating = True

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
