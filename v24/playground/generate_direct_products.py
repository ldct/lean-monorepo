#!/usr/bin/env python3
"""
Generate Lean files for all groups in the SmallGroups project.
Consolidated generator handling cyclic, dihedral, abelian, and direct product groups.
Based on GAP IDs from GroupNames webpage (https://people.maths.bris.ac.uk/~matyd/GroupNames/index.html)

Reads from group_names.tsv and uses parse_group_label to determine Lean types.
"""

from pathlib import Path
import csv
from parse_group_label import parse_group_label

LEAN_TEMPLATE = """import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion

{alternating_import}

set_option linter.style.longLine false

abbrev {abbrev_name} := {lean_type}
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
    """Generate all group files from TSV file."""
    base_dir = Path("Playground/Geometry/SmallGroups")
    created = []
    overwritten = []
    skipped = []
    all_imports = []

    print("Loading groups from group_names.tsv...")
    groups_by_order = load_groups_from_tsv()

    total_groups = sum(len(groups) for groups in groups_by_order.values())
    print(f"Found {total_groups} implementable groups\n")

    # Generate all groups
    for order, groups in sorted(groups_by_order.items()):
        for gap_id, label, lean_type in groups:
            # Create directory if needed
            gap_dir = base_dir / f"Gap_{order}"
            gap_dir.mkdir(parents=True, exist_ok=True)

            # Create file with Gap_ORDER_ID naming
            file_path = gap_dir / f"Gap_{order}_{gap_id}.lean"
            abbrev_name = f"Gap_{order}_{gap_id}"

            existed = file_path.exists()

            # Determine conditional template parts
            alternating_import = "\nimport Playground.Geometry.SmallGroups.AlternatingGroup" if "AlternatingGroup" in lean_type else ""

            content = LEAN_TEMPLATE.format(
                abbrev_name=abbrev_name,
                lean_type=lean_type,
                alternating_import=alternating_import
            )
            file_path.write_text(content)

            # Track import for SmallGroups.lean
            all_imports.append(f"import Playground.Geometry.SmallGroups.Gap_{order}.Gap_{order}_{gap_id}")

            if existed:
                overwritten.append((order, gap_id, label))
                print(f"↻ Overwrote {file_path.name}: {label} = {abbrev_name}")
            else:
                created.append((order, gap_id, label))
                print(f"✓ Created {file_path.name}: {label} = {abbrev_name}")

    # Write SmallGroups.lean
    smallgroups_path = base_dir / "SmallGroups.lean"
    smallgroups_content = "\n".join(all_imports) + "\n"
    smallgroups_path.write_text(smallgroups_content)
    print(f"\n✓ Wrote {smallgroups_path} with {len(all_imports)} imports")

    # Report results
    print(f"\n{'='*60}")
    print(f"Generated {len(created) + len(overwritten)} group files")

    if created:
        print(f"\n✓ Created {len(created)} new files")

    if overwritten:
        print(f"\n↻ Overwrote {len(overwritten)} existing files")

    print(f"\nTotal: {len(created)} created, {len(overwritten)} overwritten")

    if created:
        print(f"\n⚠️  IMPORTANT: You need to:")
        print(f"  1. Regenerate evaluation files: python3 generate_eval_files.py")


if __name__ == "__main__":
    main()
