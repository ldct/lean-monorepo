#!/usr/bin/env python3
"""
Check coverage of Lean theorem/def statements from input file against output file.

Extracts:
- All `def` statements (both textbook definitions with LaTeX quotes and helper definitions)
- Only `theorem` statements that have a LaTeX quote comment block above them
  (comment starting with "/-Exact quote of the latex code")

Usage:
    python check_coverage_lean_statement.py <input_lean_file> <output_lean_file>

Example:
    python check_coverage_lean_statement.py input.lean output.lean
"""

import sys
import re
from typing import List, Tuple, Dict
from collections import defaultdict


# Statement types to track
STATEMENT_TYPES = ['theorem', 'def', 'lemma']

# Marker for LaTeX quote comment blocks
LATEX_QUOTE_MARKER = "Exact quote of the latex code"


def get_statement_type(stmt: str) -> str:
    """Extract the type (theorem/def) from a statement."""
    for stype in STATEMENT_TYPES:
        if re.match(rf'\s*{stype}\s+', stmt):
            return stype
    return 'unknown'


def get_statement_name(stmt: str) -> str:
    """Extract the name from a theorem/lemma statement."""
    pattern = '|'.join(STATEMENT_TYPES)
    match = re.search(rf'({pattern})\s+(\w+)', stmt)
    if match:
        return match.group(2)
    return None


def extract_lean_statements_simple(content: str) -> List[str]:
    """
    Extract def/theorem signatures (statement only, without proof).

    - Extracts ALL `def` statements
    - Only extracts `theorem` statements that have a LaTeX quote comment block
      (starting with "/-Exact quote of the latex code") immediately before them

    Extracts from keyword until ':=' or 'where' or '|' (pattern match).
    """
    lines = content.split('\n')
    statements = []
    current_stmt = []
    in_statement = False

    # Track LaTeX quote comment blocks
    in_latex_comment = False
    latex_comment_just_ended = False

    for line in lines:
        stripped = line.strip()

        # Check for LaTeX quote comment block start
        if LATEX_QUOTE_MARKER in line and '/-' in line:
            in_latex_comment = True
            latex_comment_just_ended = False
            continue

        # Check for comment block end
        if in_latex_comment:
            if '-/' in line:
                in_latex_comment = False
                latex_comment_just_ended = True
            continue

        # Check if line starts a new declaration
        first_word = stripped.split()[0] if stripped.split() else ''

        if first_word == 'def':
            # Always extract all def statements
            # Save previous statement if any
            if current_stmt:
                statements.append('\n'.join(current_stmt))
                current_stmt = []

            # Check if statement ends on the same line
            if ':=' in line:
                stmt = line.split(':=')[0].rstrip()
                statements.append(stmt)
                in_statement = False
            elif stripped.startswith('|'):
                stmt = line.split('|')[0].rstrip()
                statements.append(stmt)
                in_statement = False
            else:
                current_stmt = [line]
                in_statement = True

            latex_comment_just_ended = False

        elif first_word in ('theorem', 'lemma'):
            # Only extract theorem/lemma if it follows a LaTeX quote comment block
            if latex_comment_just_ended:
                # Save previous statement if any
                if current_stmt:
                    statements.append('\n'.join(current_stmt))
                    current_stmt = []

                # Check if statement ends on the same line
                if ':=' in line:
                    stmt = line.split(':=')[0].rstrip()
                    statements.append(stmt)
                    in_statement = False
                elif stripped.startswith('|'):
                    stmt = line.split('|')[0].rstrip()
                    statements.append(stmt)
                    in_statement = False
                else:
                    current_stmt = [line]
                    in_statement = True

            latex_comment_just_ended = False

        elif in_statement:
            # Check if this line contains := or where or starts with |
            if ':=' in line:
                # Add part before := to current statement
                before_assign = line.split(':=')[0].rstrip()
                if before_assign.strip():  # Only add if non-empty
                    current_stmt.append(before_assign)
                statements.append('\n'.join(current_stmt))
                current_stmt = []
                in_statement = False
            elif stripped.startswith('|'):
                # Pattern matching starts - end of signature
                statements.append('\n'.join(current_stmt))
                current_stmt = []
                in_statement = False
            elif 'where' in stripped and stripped.index('where') == 0:
                # 'where' clause starts
                statements.append('\n'.join(current_stmt))
                current_stmt = []
                in_statement = False
            else:
                # Continue building the statement
                current_stmt.append(line)
        else:
            # Reset latex comment flag if we see non-whitespace that isn't a theorem
            if stripped and not stripped.startswith('--'):
                latex_comment_just_ended = False

    # Don't forget the last statement
    if current_stmt:
        statements.append('\n'.join(current_stmt))

    return statements


def check_coverage(input_file: str, output_file: str) -> Tuple[Dict[str, List[str]], Dict[str, List[str]], Dict[str, int]]:
    """
    Check if each theorem statement from input_file appears exactly once in output_file.

    Returns:
        - missing: dict mapping statement type to list of missing statements
        - duplicates: dict mapping statement type to list of duplicate statements
        - totals: dict mapping statement type to total count
    """
    with open(input_file, 'r', encoding='utf-8') as f:
        input_content = f.read()

    with open(output_file, 'r', encoding='utf-8') as f:
        output_content = f.read()

    statements = extract_lean_statements_simple(input_content)

    missing = defaultdict(list)
    duplicates = defaultdict(list)
    totals = defaultdict(int)

    for stmt in statements:
        stype = get_statement_type(stmt)
        name = get_statement_name(stmt)
        totals[stype] += 1

        if not name:
            # Skip unnamed statements
            continue

        # Build combined pattern: "theorem name" or "def name" followed by the rest
        # This ensures we check both the name and statement together as one string
        normalized_stmt = stmt.strip()

        # Verify the statement contains the expected "type name" pattern
        expected_prefix = f"{stype} {name}"
        if not normalized_stmt.startswith(expected_prefix):
            missing[stype].append(stmt)
            continue

        # Check if the combined name+statement appears in output
        # Use regex with \b-like boundary to avoid substring matches
        # (e.g. "def Ch1_def_1" matching inside "def Ch1_def_15")
        count = len(re.findall(re.escape(normalized_stmt) + r'(?!\w)', output_content))
        if count == 0:
            missing[stype].append(stmt)
        elif count > 1:
            duplicates[stype].append(stmt)

    return dict(missing), dict(duplicates), dict(totals)


def get_statement_preview(stmt: str, max_len: int = 80) -> str:
    """Get a short preview of a statement for display."""
    first_line = stmt.split('\n')[0]
    if len(first_line) > max_len:
        return first_line[:max_len] + "..."
    return first_line


def main():
    if len(sys.argv) != 3:
        print("Usage: python check_coverage_lean_statement.py <input_lean_file> <output_lean_file>")
        print("Example: python check_coverage_lean_statement.py input.lean output.lean")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]

    missing, duplicates, totals = check_coverage(input_file, output_file)

    # Calculate overall stats
    total_all = sum(totals.values())
    missing_all = sum(len(v) for v in missing.values())
    duplicates_all = sum(len(v) for v in duplicates.values())
    found_all = total_all - missing_all

    # Print summary
    print("=" * 60)
    print("LEAN COVERAGE CHECK RESULTS")
    print("=" * 60)
    print(f"Input file:  {input_file}")
    print(f"Output file: {output_file}")
    print("-" * 60)

    # Print breakdown by type
    print("\nBREAKDOWN BY TYPE:")
    print("-" * 60)
    print(f"{'Type':<12} {'Total':>8} {'Found':>8} {'Missing':>8} {'Duplicate':>10}")
    print("-" * 60)

    for stype in STATEMENT_TYPES:
        total = totals.get(stype, 0)
        miss = len(missing.get(stype, []))
        dup = len(duplicates.get(stype, []))
        found = total - miss
        print(f"{stype:<12} {total:>8} {found:>8} {miss:>8} {dup:>10}")

    print("-" * 60)
    print(f"{'TOTAL':<12} {total_all:>8} {found_all:>8} {missing_all:>8} {duplicates_all:>10}")
    print("-" * 60)
    print(f"Coverage: {(total_all - missing_all) / total_all * 100:.1f}%" if total_all > 0 else "Coverage: N/A")
    print("=" * 60)

    # Print missing statements grouped by type
    if missing:
        print("\nMISSING STATEMENTS:")
        print("=" * 60)
        for stype in STATEMENT_TYPES:
            if stype in missing and missing[stype]:
                print(f"\n[{stype.upper()}] ({len(missing[stype])} missing)")
                print("-" * 60)
                for i, stmt in enumerate(missing[stype], 1):
                    name = get_statement_name(stmt)
                    print(f"{i}. {name if name else '(unnamed)'}")
                    print(stmt)
                    print()
                    print("-" * 60)

    # Print duplicates grouped by type
    if duplicates:
        print("\nDUPLICATE STATEMENTS:")
        print("=" * 60)
        for stype in STATEMENT_TYPES:
            if stype in duplicates and duplicates[stype]:
                print(f"\n[{stype.upper()}] ({len(duplicates[stype])} duplicates)")
                print("-" * 60)
                for i, stmt in enumerate(duplicates[stype], 1):
                    # Count occurrences in output
                    with open(output_file, 'r', encoding='utf-8') as f:
                        count = len(re.findall(re.escape(stmt.strip()) + r'(?!\w)', f.read()))
                    name = get_statement_name(stmt)
                    print(f"{i}. {name if name else '(unnamed)'} (appears {count} times)")
                    print(stmt)
                    print()
                    print("-" * 60)

    # Exit with status code based on results
    if missing or duplicates:
        print("-" * 60)
        if missing and duplicates:
            print(f"RESULT: INCOMPLETE - {missing_all} missing, {duplicates_all} duplicates")
        elif missing:
            print(f"RESULT: INCOMPLETE - {missing_all} missing")
        else:
            print(f"RESULT: HAS DUPLICATES - {duplicates_all} duplicates")
        sys.exit(1)
    else:
        print("\nRESULT: COMPLETE - All statements found exactly once!")
        sys.exit(0)


if __name__ == '__main__':
    main()
