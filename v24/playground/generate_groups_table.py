#!/usr/bin/env python3
"""
Generate an HTML table of small groups from Lean build output.
Includes both implemented and unimplemented groups from TSV file.
"""

import subprocess
import re
import time
import csv
from collections import defaultdict
from pathlib import Path
from parse_group_label import parse_group_label

# Expected number of groups per order (1-60)
EXPECTED_GROUPS = {
    1: 1, 2: 1, 3: 1, 4: 2, 5: 1, 6: 2, 7: 1, 8: 5, 9: 2, 10: 2,
    11: 1, 12: 5, 13: 1, 14: 2, 15: 1, 16: 14, 17: 1, 18: 5, 19: 1, 20: 5,
    21: 2, 22: 2, 23: 1, 24: 15, 25: 2, 26: 2, 27: 5, 28: 4, 29: 1, 30: 4,
    31: 1, 32: 51, 33: 1, 34: 2, 35: 1, 36: 14, 37: 1, 38: 2, 39: 2, 40: 14,
    41: 1, 42: 6, 43: 1, 44: 4, 45: 2, 46: 2, 47: 1, 48: 52, 49: 2, 50: 5,
    51: 1, 52: 5, 53: 1, 54: 15, 55: 2, 56: 13, 57: 2, 58: 2, 59: 1, 60: 13,
}

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
        result = subprocess.run(
            ["lake", "build", eval_file],
            capture_output=True,
            text=True
        )
        outputs[property_name] = result.stdout + result.stderr

    return outputs

def load_all_groups_from_tsv(tsv_file="group_names.tsv"):
    """
    Load all groups from TSV file with their labels.
    Returns dict: {(order, gap_id): {'label': label, 'implemented': bool}}
    """
    all_groups = {}

    with open(tsv_file, 'r') as f:
        reader = csv.reader(f, delimiter='\t')
        for row in reader:
            if len(row) != 2:
                continue

            label = row[0]
            gap_id_str = row[1]

            # Parse gap_id as "order,id"
            order, gap_id = map(int, gap_id_str.split(','))

            # Check if this group is implementable
            lean_type = parse_group_label(label, order)
            implemented = lean_type is not None

            all_groups[(order, gap_id)] = {
                'label': label,
                'implemented': implemented
            }

    return all_groups

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

def format_group_name_html(name):
    """Convert Lean group name to HTML with proper formatting."""
    if not name:
        return ""

    # Handle cyclic groups: Z8 -> ℤ₈
    if name.startswith('Z') and name[1:].isdigit():
        n = name[1:]
        subscript = ''.join(['₀₁₂₃₄₅₆₇₈₉'[int(d)] for d in n])
        return f"ℤ{subscript}"

    # Handle dihedral groups: Dih5 -> D₅
    if name.startswith('Dih') and name[3:].isdigit():
        n = name[3:]
        subscript = ''.join(['₀₁₂₃₄₅₆₇₈₉'[int(d)] for d in n])
        return f"D{subscript}"

    # Handle symmetric groups: S3, S4 -> S₃, S₄
    if name.startswith('S') and len(name) <= 3 and name[1:].isdigit():
        n = name[1:]
        subscript = ''.join(['₀₁₂₃₄₅₆₇₈₉'[int(d)] for d in n])
        return f"S{subscript}"

    # Handle quaternion group: Q -> Q₈
    if name == 'Q':
        return "Q₈"

    # Handle elementary abelian groups: E8 -> ℤ₂³, E9 -> ℤ₃²
    if name.startswith('E') and name[1:].isdigit():
        n = int(name[1:])
        # E8 = Z2^3, E9 = Z3^2, E27 = Z3^3, etc.
        if n == 4:
            return "ℤ₂²"
        elif n == 8:
            return "ℤ₂³"
        elif n == 9:
            return "ℤ₃²"
        elif n == 16:
            return "ℤ₂⁴"
        elif n == 25:
            return "ℤ₅²"
        elif n == 27:
            return "ℤ₃³"
        elif n == 32:
            return "ℤ₂⁵"

    # Handle direct products: C2_C6 -> ℤ₂ × ℤ₆
    if '_' in name and name.replace('_', '').replace('C', '').isdigit():
        parts = name.split('_')
        formatted_parts = []
        for part in parts:
            if part.startswith('C') and part[1:].isdigit():
                n = part[1:]
                subscript = ''.join(['₀₁₂₃₄₅₆₇₈₉'[int(d)] for d in n])
                formatted_parts.append(f"ℤ{subscript}")
        if formatted_parts:
            return ' × '.join(formatted_parts)

    # Handle names like Gap_8_2 - parse from Lean definition would be better but this is a fallback
    if name.startswith('Gap_'):
        return name  # Keep as-is, will show Gap(order, id) in final output

    # Handle alternating groups: A4 -> A₄, A5 -> A₅
    if name.startswith('A') and len(name) <= 3 and name[1:].isdigit():
        n = name[1:]
        subscript = ''.join(['₀₁₂₃₄₅₆₇₈₉'[int(d)] for d in n])
        return f"A{subscript}"

    # Handle special names
    if name == 'Trivial':
        return 'Trivial'
    if name == 'V4':
        return 'ℤ₂²'

    # Default: return as-is
    return name

def format_rational(rat_str):
    """Format rational number strings like 'mkRat 1 3' into fractions."""
    if rat_str.startswith('mkRat '):
        parts = rat_str.split()
        if len(parts) == 3:
            num, denom = parts[1], parts[2]
            if denom == '1':
                return num
            return f"{num}/{denom}"
    return rat_str

def generate_html(groups, group_info, all_groups_tsv):
    """Generate HTML page with group table sectioned by order, including unimplemented groups."""
    # Group by order - include ALL groups from TSV
    by_order = defaultdict(list)
    for (order, gap_id), tsv_data in all_groups_tsv.items():
        # Get stats if implemented
        stats = groups.get((order, gap_id), {})
        by_order[order].append((gap_id, stats, tsv_data))

    # Calculate statistics - count implemented groups
    complete_orders = []
    partial_orders = []
    implemented_count_by_order = {}

    for order in sorted(by_order.keys()):
        groups_in_order = by_order[order]
        implemented = sum(1 for _, stats, tsv_data in groups_in_order if tsv_data['implemented'])
        total_in_order = len(groups_in_order)
        implemented_count_by_order[order] = implemented

        if implemented == total_in_order:
            complete_orders.append(order)
        elif implemented > 0:
            partial_orders.append((order, implemented, total_in_order))

    total_expected = sum(len(by_order[order]) for order in by_order.keys())
    total_actual = len(groups)
    percentage = (total_actual / total_expected * 100) if total_expected > 0 else 0

    total_orders = len(by_order)

    html = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Small Groups Table</title>
    <style>
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
            max-width: 1400px;
            margin: 40px auto;
            padding: 0 20px;
            background-color: #f5f5f5;
        }
        h1 {
            color: #333;
            text-align: center;
            margin-bottom: 10px;
        }
        .summary {
            text-align: center;
            color: #666;
            margin-bottom: 30px;
            font-size: 18px;
        }
        .summary strong {
            color: #4CAF50;
        }
        .order-section {
            margin-bottom: 40px;
            background-color: white;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            overflow: hidden;
        }
        .order-header {
            padding: 15px 20px;
            font-size: 18px;
            font-weight: 600;
            display: flex;
            justify-content: space-between;
            align-items: center;
        }
        .order-header.complete {
            background-color: #4CAF50;
            color: white;
        }
        .order-header.partial {
            background-color: #FF9800;
            color: white;
        }
        .progress {
            font-size: 14px;
            font-weight: normal;
        }
        table {
            width: 100%;
            border-collapse: collapse;
        }
        th, td {
            padding: 12px 15px;
            text-align: left;
            border-bottom: 1px solid #f0f0f0;
        }
        th {
            background-color: #f9f9f9;
            color: #333;
            font-weight: 600;
        }
        tr:hover {
            background-color: #f5f5f5;
        }
        tr:last-child td {
            border-bottom: none;
        }
        .abelian-yes {
            color: #4CAF50;
            font-weight: 600;
        }
        .abelian-no {
            color: #f44336;
            font-weight: 600;
        }
        .number {
            text-align: right;
        }
        .gap-id {
            font-family: 'Courier New', monospace;
            color: #666;
            font-size: 14px;
        }
        .group-name-cell {
            padding: 8px 15px;
        }
        .group-name {
            font-weight: 500;
            font-size: 16px;
            margin-bottom: 4px;
        }
        .group-abbrev {
            font-family: 'Courier New', monospace;
            font-size: 11px;
            color: #888;
            line-height: 1.3;
        }
    </style>
</head>
<body>
    <h1>Small Groups (Orders 1-60)</h1>
    <div class="summary">
        <strong>""" + f"{total_actual}/{total_expected}</strong> groups ({percentage:.1f}%) | " + f"""
        <strong>{len(complete_orders)}/{total_orders}</strong> complete orders
    </div>
"""

    # Generate sections by order
    for order in sorted(by_order.keys()):
        groups_in_order = sorted(by_order[order], key=lambda x: x[0])
        total_in_order = len(groups_in_order)
        implemented_in_order = implemented_count_by_order.get(order, 0)
        is_complete = implemented_in_order == total_in_order

        header_class = "complete" if is_complete else "partial"
        status_icon = "✓" if is_complete else "⚠"

        html += f"""
    <div class="order-section">
        <div class="order-header {header_class}">
            <span>{status_icon} Order {order}</span>
            <span class="progress">{implemented_in_order}/{total_in_order} groups</span>
        </div>
        <table>
            <thead>
                <tr>
                    <th>GAP ID</th>
                    <th>Group Name</th>
                    <th>Abelian?</th>
                    <th class="number">Exponent</th>
                    <th class="number">Frac. Involutions</th>
                    <th class="number">Commuting Fraction</th>
                    <th class="number"># Subgroups</th>
                </tr>
            </thead>
            <tbody>
"""

        for gap_id, data, tsv_data in groups_in_order:
            label = tsv_data['label']
            implemented = tsv_data['implemented']

            if implemented and data:
                # Implemented group - show full stats
                abelian = data.get('abelian', '?')
                exponent_val = data.get('exponent', '?')
                frac_inv = format_rational(data.get('frac_involutions', '?'))
                comm_frac = format_rational(data.get('commuting_fraction', '?'))
                num_subgroups = data.get('num_subgroups', '?')

                abelian_class = 'abelian-yes' if abelian == 'true' else 'abelian-no'
                abelian_text = 'Yes' if abelian == 'true' else 'No'

                # Get formatted group name and abbrev from Lean file
                info = group_info.get((order, gap_id), {})
                lean_name = info.get('name', '')
                lean_def = info.get('definition', '')

                group_name = format_group_name_html(lean_name) or f"Gap({order}, {gap_id})"

                # Format the abbrev line
                abbrev_line = f"abbrev {lean_name} := {lean_def}" if lean_name and lean_def else ""
            else:
                # Unimplemented group - show label, blank stats
                abelian_class = ''
                abelian_text = '-'
                exponent_val = '-'
                frac_inv = '-'
                comm_frac = '-'
                num_subgroups = '-'
                group_name = label
                abbrev_line = f'<span style="color: #999; font-style: italic;">Not implemented</span>'

            html += f"""                <tr>
                    <td class="gap-id">({order}, {gap_id})</td>
                    <td class="group-name-cell">
                        <div class="group-name">{group_name}</div>
                        <div class="group-abbrev">{abbrev_line}</div>
                    </td>
                    <td class="{abelian_class}">{abelian_text}</td>
                    <td class="number">{exponent_val}</td>
                    <td class="number">{frac_inv}</td>
                    <td class="number">{comm_frac}</td>
                    <td class="number">{num_subgroups}</td>
                </tr>
"""

        html += """            </tbody>
        </table>
    </div>
"""

    html += """</body>
</html>
"""
    return html

def main():
    """Main function."""
    # Load all groups from TSV (implemented and unimplemented)
    print("Loading all groups from TSV file...")
    all_groups_tsv = load_all_groups_from_tsv()
    total_groups = len(all_groups_tsv)
    implemented_groups = sum(1 for g in all_groups_tsv.values() if g['implemented'])
    print(f"Found {total_groups} groups total, {implemented_groups} implementable")

    # Parse Lean files to get group names and definitions
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

    # Generate HTML
    html = generate_html(groups, group_info, all_groups_tsv)

    # Write to file
    output_file = Path("groups_table.html")
    output_file.write_text(html)
    print(f"HTML table written to {output_file.absolute()}")

if __name__ == "__main__":
    main()
