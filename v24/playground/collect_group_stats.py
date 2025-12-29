#!/usr/bin/env python3
"""
Collect group statistics by running lake build on evaluation files.
Saves results to group_stats.json for later HTML generation.
"""

import subprocess
import re
import time
import json
from pathlib import Path
from collections import defaultdict


def get_group_order_from_smallgroups():
    """Parse SmallGroups.lean to get ordered list of (order, gap_id) tuples."""
    smallgroups_file = Path("Playground/Geometry/SmallGroups/SmallGroups.lean")
    groups = []

    with open(smallgroups_file, 'r') as f:
        for line in f:
            line = line.strip()
            # Skip commented imports
            if line.startswith('--'):
                continue
            # Match import statements: import Playground.Geometry.SmallGroups.Gap_N.Gap_N_M
            match = re.match(r'import Playground\.Geometry\.SmallGroups\.Gap_(\d+)\.Gap_\d+_(\d+)', line)
            if match:
                order = int(match.group(1))
                gap_id = int(match.group(2))
                groups.append((order, gap_id))

    return groups


def run_build():
    """Run lake build for all eval files and capture outputs."""
    eval_files = [
        ("Playground.Geometry.SmallGroups.EvalCardinality", "cardinality"),
        ("Playground.Geometry.SmallGroups.EvalAbelian", "abelian"),
        ("Playground.Geometry.SmallGroups.EvalFracInvolutions", "fracinvolutions"),
        ("Playground.Geometry.SmallGroups.EvalCommutingFraction", "commutingfraction"),
        ("Playground.Geometry.SmallGroups.EvalNumSubgroups", "numsubgroups"),
        ("Playground.Geometry.SmallGroups.EvalExponent", "exponent"),
    ]

    outputs = {}
    for eval_file, property_name in eval_files:
        print(f"Building {eval_file}...")

        # Use Popen to stream output while also capturing it
        process = subprocess.Popen(
            ["lake", "build", eval_file],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1
        )

        # Stream output line by line while collecting it
        collected_output = []
        for line in process.stdout:
            print(line, end='')  # Print to stdout in real-time
            collected_output.append(line)

        process.wait()
        outputs[property_name] = ''.join(collected_output)

    return outputs


def parse_output(outputs):
    """Parse the build outputs from all eval files to extract group information."""
    groups = defaultdict(dict)

    # Get ordered list of groups from SmallGroups.lean
    group_order = get_group_order_from_smallgroups()

    # Pattern to match info lines from eval files
    # Example: info: Playground/Geometry/SmallGroups/EvalCardinality.lean:4:0: 1
    pattern = r'info: Playground/Geometry/SmallGroups/Eval(\w+)\.lean:(\d+):0: (.+)'

    # Property name mapping to dict keys
    property_map = {
        'Cardinality': 'card',
        'Abelian': 'abelian',
        'FracInvolutions': 'frac_involutions',
        'CommutingFraction': 'commuting_fraction',
        'NumSubgroups': 'num_subgroups',
        'Exponent': 'exponent',
    }

    # Parse each property's output
    for property_name, output in outputs.items():
        for line in output.split('\n'):
            match = re.search(pattern, line)
            if match:
                eval_type = match.group(1)  # e.g., "Cardinality"
                line_num = int(match.group(2))
                value = match.group(3)

                # Map line number to group index
                # Line 1: import, Line 2: blank, Line 3: comment, Line 4+: #eval statements
                group_index = line_num - 4
                if 0 <= group_index < len(group_order):
                    key = group_order[group_index]
                    dict_key = property_map.get(eval_type, eval_type.lower())
                    groups[key][dict_key] = value

    return groups


def parse_lean_files():
    """Parse Lean files to extract group names and abbrev definitions."""
    base_dir = Path("Playground/Geometry/SmallGroups")
    group_info = {}

    for gap_file in base_dir.glob("Gap_*/Gap_*.lean"):
        try:
            # Extract order and gap_id from filename
            parts = gap_file.stem.split("_")
            if len(parts) >= 3:
                order = int(parts[1])
                gap_id = int(parts[2])

                # Read file and find abbrev line
                content = gap_file.read_text()

                # Match the full abbrev line
                abbrev_match = re.search(r'abbrev\s+(\w+)\s*:=\s*(.+?)(?=\n|$)', content, re.MULTILINE)
                if abbrev_match:
                    abbrev_name = abbrev_match.group(1)
                    abbrev_def = abbrev_match.group(2).strip()
                    group_info[(order, gap_id)] = {
                        'name': abbrev_name,
                        'definition': abbrev_def
                    }
        except (ValueError, IndexError):
            continue

    return group_info


def save_stats(groups, group_info, output_file="group_stats.json"):
    """Save collected stats to JSON file."""
    # Convert tuple keys to strings for JSON serialization
    stats = {
        'groups': {f"{order},{gap_id}": data for (order, gap_id), data in groups.items()},
        'group_info': {f"{order},{gap_id}": info for (order, gap_id), info in group_info.items()}
    }

    with open(output_file, 'w') as f:
        json.dump(stats, f, indent=2)

    return output_file


def main():
    """Main function."""
    print("Parsing Lean files for group names and definitions...")
    group_info = parse_lean_files()
    print(f"Found {len(group_info)} group definitions from Lean files")

    # Run build and capture outputs
    build_start = time.time()
    outputs = run_build()
    build_time = time.time() - build_start
    print(f"Lake build completed in {build_time:.2f}s")

    # Parse the outputs
    groups = parse_output(outputs)
    print(f"Found {len(groups)} groups from build output")

    # Save to JSON
    output_file = save_stats(groups, group_info)
    print(f"Statistics saved to {output_file}")
    print(f"\nNext step: Run 'python3 generate_groups_table.py' to generate HTML")


if __name__ == "__main__":
    main()
