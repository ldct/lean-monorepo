#!/usr/bin/env python3
"""
Generate an HTML table of small groups from Lean build output.
"""

import subprocess
import re
from collections import defaultdict
from pathlib import Path

def run_build():
    """Run the lake build command and capture output."""
    print("Running lake build...")
    result = subprocess.run(
        ["lake", "build", "Playground.Geometry.SmallGroups.SmallGroups"],
        capture_output=True,
        text=True
    )
    return result.stdout + result.stderr

def parse_output(output):
    """Parse the build output to extract group information."""
    groups = defaultdict(dict)

    # Pattern to match info lines
    # Example: info: Playground/Geometry/SmallGroups/Gap_1/Gap_1_1.lean:6:0: 1
    pattern = r'info: Playground/Geometry/SmallGroups/Gap_(\d+)/Gap_\1_(\d+)\.lean:(\d+):0: (.+)'

    for line in output.split('\n'):
        match = re.search(pattern, line)
        if match:
            order = int(match.group(1))
            gap_id = int(match.group(2))
            line_num = int(match.group(3))
            value = match.group(4)

            key = (order, gap_id)

            # Line 6: card, Line 7: IsAbelian, Line 8: FracInvolutions, Line 9: CommutingFraction
            if line_num == 6:
                groups[key]['card'] = value
            elif line_num == 7:
                groups[key]['abelian'] = value
            elif line_num == 8:
                groups[key]['frac_involutions'] = value
            elif line_num == 9:
                groups[key]['commuting_fraction'] = value

    return groups

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

def get_group_name(order, gap_id):
    """Get the common name for a group based on its GAP ID."""
    names = {
        (1, 1): "Trivial",
        (2, 1): "ℤ₂",
        (3, 1): "ℤ₃",
        (4, 1): "ℤ₄",
        (4, 2): "V₄ (Klein four-group)",
        (5, 1): "ℤ₅",
        (6, 1): "ℤ₆",
        (6, 2): "S₃",
        (7, 1): "ℤ₇",
        (8, 1): "ℤ₈",
        (8, 2): "ℤ₄ × ℤ₂",
        (8, 3): "D₈",
        (8, 4): "Q₈",
        (8, 5): "ℤ₂ × ℤ₂ × ℤ₂",
        (9, 1): "ℤ₉",
        (9, 2): "ℤ₃ × ℤ₃",
        (10, 1): "D₁₀",
        (10, 2): "ℤ₁₀",
        (11, 1): "ℤ₁₁",
        (12, 1): "Dic₁₂",
        (12, 2): "ℤ₁₂",
    }
    return names.get((order, gap_id), f"Gap({order}, {gap_id})")

def generate_html(groups):
    """Generate HTML page with group table."""
    html = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Small Groups Table</title>
    <style>
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
            max-width: 1200px;
            margin: 40px auto;
            padding: 0 20px;
            background-color: #f5f5f5;
        }
        h1 {
            color: #333;
            text-align: center;
            margin-bottom: 30px;
        }
        table {
            width: 100%;
            border-collapse: collapse;
            background-color: white;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        th, td {
            padding: 12px 15px;
            text-align: left;
            border-bottom: 1px solid #ddd;
        }
        th {
            background-color: #4CAF50;
            color: white;
            font-weight: 600;
            position: sticky;
            top: 0;
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
        }
        .group-name {
            font-weight: 500;
        }
    </style>
</head>
<body>
    <h1>Small Groups (Orders 1-12)</h1>
    <table>
        <thead>
            <tr>
                <th>GAP ID</th>
                <th>Group Name</th>
                <th class="number">Order</th>
                <th>Abelian?</th>
                <th class="number">Frac. Involutions</th>
                <th class="number">Commuting Fraction</th>
            </tr>
        </thead>
        <tbody>
"""

    # Sort groups by order, then by GAP ID
    sorted_groups = sorted(groups.items(), key=lambda x: (x[0][0], x[0][1]))

    for (order, gap_id), data in sorted_groups:
        card = data.get('card', '?')
        abelian = data.get('abelian', '?')
        frac_inv = format_rational(data.get('frac_involutions', '?'))
        comm_frac = format_rational(data.get('commuting_fraction', '?'))

        abelian_class = 'abelian-yes' if abelian == 'true' else 'abelian-no'
        abelian_text = 'Yes' if abelian == 'true' else 'No'

        group_name = get_group_name(order, gap_id)

        html += f"""            <tr>
                <td class="gap-id">({order}, {gap_id})</td>
                <td class="group-name">{group_name}</td>
                <td class="number">{card}</td>
                <td class="{abelian_class}">{abelian_text}</td>
                <td class="number">{frac_inv}</td>
                <td class="number">{comm_frac}</td>
            </tr>
"""

    html += """        </tbody>
    </table>
</body>
</html>
"""
    return html

def main():
    """Main function."""
    # Run build and capture output
    output = run_build()

    # Parse the output
    groups = parse_output(output)

    print(f"Found {len(groups)} groups")

    # Generate HTML
    html = generate_html(groups)

    # Write to file
    output_file = Path("groups_table.html")
    output_file.write_text(html)

    print(f"HTML table written to {output_file.absolute()}")

if __name__ == "__main__":
    main()
