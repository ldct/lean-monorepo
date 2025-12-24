#!/usr/bin/env python3
"""
Generate centralized evaluation files for SmallGroups project.
"""

import re
from pathlib import Path

def parse_smallgroups_imports():
    """Parse SmallGroups.lean to get list of all group import paths."""
    smallgroups_file = Path("Playground/Geometry/SmallGroups/SmallGroups.lean")
    imports = []

    with open(smallgroups_file, 'r') as f:
        for line in f:
            line = line.strip()
            # Skip commented imports
            if line.startswith('--'):
                continue
            # Match import statements
            match = re.match(r'import (Playground\.Geometry\.SmallGroups\.Gap_\d+\.Gap_\d+_\d+)', line)
            if match:
                imports.append(match.group(1))

    return imports

def import_to_filepath(import_path):
    """Convert import path to file path."""
    # Playground.Geometry.SmallGroups.Gap_1.Gap_1_1 -> Playground/Geometry/SmallGroups/Gap_1/Gap_1_1.lean
    return import_path.replace('.', '/') + '.lean'

def extract_abbrev_name(filepath):
    """Extract abbrev name from a group file."""
    with open(filepath, 'r') as f:
        for line in f:
            line = line.strip()
            # Match: abbrev GroupName := ...
            match = re.match(r'abbrev\s+(\w+)\s+:=', line)
            if match:
                return match.group(1)
    return None

def generate_eval_file(property_name, eval_expr, group_names, output_file):
    """Generate a centralized evaluation file for a property."""
    lines = [
        "import Playground.Geometry.SmallGroups.SmallGroups",
        "",
        f"-- Evaluate {property_name} for all groups",
    ]

    for group_name in group_names:
        lines.append(f"#eval {eval_expr} {group_name}")

    lines.append("")  # Empty line at end

    with open(output_file, 'w') as f:
        f.write('\n'.join(lines))

    print(f"Generated {output_file} with {len(group_names)} evaluations")

def main():
    """Main function to generate all evaluation files."""
    # Parse imports from SmallGroups.lean
    imports = parse_smallgroups_imports()
    print(f"Found {len(imports)} group imports")

    # Extract abbrev names from each group file
    group_names = []
    for import_path in imports:
        filepath = import_to_filepath(import_path)
        abbrev_name = extract_abbrev_name(filepath)
        if abbrev_name:
            group_names.append(abbrev_name)
            print(f"  {import_path} -> {abbrev_name}")
        else:
            print(f"  WARNING: Could not extract abbrev from {filepath}")

    print(f"\nTotal groups: {len(group_names)}")

    # Generate the 5 evaluation files
    base_path = Path("Playground/Geometry/SmallGroups")

    properties = [
        ("Cardinality", "Fintype.card", "EvalCardinality.lean"),
        ("IsAbelian", "Group.IsAbelian", "EvalAbelian.lean"),
        ("FracInvolutions", "Group.FracInvolutions", "EvalFracInvolutions.lean"),
        ("CommutingFraction", "Group.CommutingFraction", "EvalCommutingFraction.lean"),
        ("NumSubgroups", "Group.numSubgroups", "EvalNumSubgroups.lean"),
    ]

    for prop_name, eval_expr, filename in properties:
        output_file = base_path / filename
        generate_eval_file(prop_name, eval_expr, group_names, output_file)

    print("\n✅ Successfully generated all 5 evaluation files")

if __name__ == "__main__":
    main()
