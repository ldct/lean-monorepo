#!/usr/bin/env python3
"""
Check coverage of theorem/definition blocks from extracted file against a target file.

Checks two things:
  1. Every LaTeX block appears exactly once in the target (no missing, no duplicates).
  2. Every LaTeX block is immediately followed by a Lean declaration (adjacency check).
     The closing -/ of the comment block must be directly followed (ignoring blank lines)
     by a theorem/def/lemma/corollary declaration — nothing else may appear in between.

Usage:
    python check_coverage_latex_quote.py <theorems_and_defs_file> <target_file>

Example:
    python check_coverage_latex_quote.py theorems_and_defs/ch3.txt ch3.lean
"""

import sys
import re
from typing import List, Tuple


def extract_theorem_blocks(content: str) -> List[str]:
    r"""
    Extract all \begin{...}...\end{...} blocks from the content.
    Matches theorem, lemma, corollary, and definition environments.
    """
    pattern = re.compile(
        r'\\begin\{(theorem|lemma|corollary|definition)\}.*?\\end\{\1\}',
        re.DOTALL
    )
    return [match.group() for match in pattern.finditer(content)]


def check_coverage(theorems_file: str, target_file: str) -> Tuple[List[str], List[str], int]:
    """
    Check if each theorem block from theorems_file appears exactly once in target_file.

    Returns:
        - missing: list of blocks that don't appear in target
        - duplicates: list of blocks that appear more than once
        - total: total number of theorem blocks
    """
    with open(theorems_file, 'r', encoding='utf-8') as f:
        theorems_content = f.read()

    with open(target_file, 'r', encoding='utf-8') as f:
        target_content = f.read()

    blocks = extract_theorem_blocks(theorems_content)

    missing = []
    duplicates = []

    for block in blocks:
        count = target_content.count(block)
        if count == 0:
            missing.append(block)
        elif count > 1:
            duplicates.append(block)

    return missing, duplicates, len(blocks)


def check_adjacency(target_file: str) -> List[dict]:
    """
    Check that every /-Exact quote ... -/ comment block is immediately followed
    (ignoring only blank lines) by a spec theorem/def/lemma/corollary declaration
    whose name matches the naming convention Ch{N}_{type}_{index}.

    Returns a list of violations, each a dict with:
        - comment_start: line number where /-Exact quote starts
        - comment_end: line number of closing -/
        - declaration_line: line number of the actual declaration (or None)
        - declaration_name: name of the declaration found (or None)
        - offending_lines: list of (line_number, text) of non-blank lines between
        - bad_name: True if declaration was found but name doesn't match convention
    """
    with open(target_file, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    DECL_KEYWORDS = {'theorem', 'def', 'lemma', 'corollary'}
    # Naming convention: Ch{N}_{type}_{index} e.g. Ch1_theorem_3, Ch2_def_5
    NAME_PATTERN = re.compile(r'^Ch\d+_(theorem|def|corollary|lemma)_\d+')
    violations = []

    i = 0
    while i < len(lines):
        line = lines[i]

        # Detect start of a LaTeX quote comment block: /- containing "Exact quote"
        if '/-' in line and 'Exact quote' in line:
            comment_start = i + 1  # 1-indexed

            # Find the closing -/
            j = i
            found_close = False
            while j < len(lines):
                if '-/' in lines[j]:
                    # Handle /- ... -/ on the same line for start line,
                    # or -/ on a later line
                    if j == i:
                        # Check if -/ appears AFTER /- on the same line
                        open_pos = lines[j].index('/-')
                        close_pos = lines[j].index('-/')
                        if close_pos > open_pos:
                            found_close = True
                            break
                    else:
                        found_close = True
                        break
                j += 1

            if not found_close:
                i += 1
                continue

            comment_end = j + 1  # 1-indexed

            # Now scan lines after the closing -/ for the declaration
            offending = []
            decl_line = None
            decl_name = None
            bad_name = False
            k = j + 1
            while k < len(lines):
                stripped = lines[k].strip()
                if not stripped:
                    # Blank line — allowed
                    k += 1
                    continue

                # Check if this line starts with a declaration keyword
                words = stripped.split()
                first_word = words[0] if words else ''
                if first_word in DECL_KEYWORDS:
                    decl_line = k + 1  # 1-indexed
                    decl_name = words[1] if len(words) > 1 else None
                    # Verify the name matches the naming convention
                    if decl_name and not NAME_PATTERN.match(decl_name):
                        bad_name = True
                    break
                else:
                    # Non-blank, non-declaration line — violation
                    offending.append((k + 1, lines[k].rstrip()))
                    k += 1
                    # Keep scanning to find the actual declaration
                    continue

            if offending or bad_name:
                violations.append({
                    'comment_start': comment_start,
                    'comment_end': comment_end,
                    'declaration_line': decl_line,
                    'declaration_name': decl_name,
                    'offending_lines': offending,
                    'bad_name': bad_name,
                })

            i = j + 1
        else:
            i += 1

    return violations


def get_block_preview(block: str, max_len: int = 80) -> str:
    """Get a short preview of a block for display."""
    # Get the first line or first max_len chars
    first_line = block.split('\n')[0]
    if len(first_line) > max_len:
        return first_line[:max_len] + "..."
    return first_line


def get_block_label(block: str) -> str:
    """Extract the label from a theorem block if present."""
    label_match = re.search(r'\\label\{([^}]+)\}', block)
    if label_match:
        return label_match.group(1)
    return None


def main():
    if len(sys.argv) != 3:
        print("Usage: python check_coverage.py <theorems_file> <target_file>")
        print("Example: python check_coverage_latex_quote.py theorems_and_defs/ch3.txt ch3.lean")
        sys.exit(1)

    theorems_file = sys.argv[1]
    target_file = sys.argv[2]

    missing, duplicates, total = check_coverage(theorems_file, target_file)

    # Print summary
    found = total - len(missing)
    print("=" * 60)
    print("COVERAGE CHECK RESULTS")
    print("=" * 60)
    print(f"Theorems file: {theorems_file}")
    print(f"Target file:   {target_file}")
    print("-" * 60)
    print(f"Total theorem blocks:  {total}")
    print(f"Found (exactly once):  {found - len(duplicates)}")
    print(f"Missing:               {len(missing)}")
    print(f"Duplicates:            {len(duplicates)}")
    print(f"Coverage:              {(total - len(missing)) / total * 100:.1f}%" if total > 0 else "N/A")
    print("=" * 60)

    # Print missing blocks
    if missing:
        print("\nMISSING STATEMENTS:")
        print("-" * 60)
        for i, block in enumerate(missing, 1):
            print(f"{i}.")
            print(block)
            print()
            print("-" * 60)

    # Print duplicates
    if duplicates:
        print("\nDUPLICATE STATEMENTS:")
        print("-" * 60)
        for i, block in enumerate(duplicates, 1):
            # Count occurrences in target
            with open(target_file, 'r', encoding='utf-8') as f:
                count = f.read().count(block)
            print(f"{i}. (appears {count} times)")
            print(block)
            print()
            print("-" * 60)

    # Adjacency check
    violations = check_adjacency(target_file)
    gap_violations = [v for v in violations if v['offending_lines']]
    name_violations = [v for v in violations if v['bad_name']]

    if violations:
        print()
        print("=" * 60)
        print("ADJACENCY VIOLATIONS")
        print("=" * 60)

        if gap_violations:
            print(f"\nFound {len(gap_violations)} comment blocks with non-blank lines")
            print("between the closing -/ and the Lean declaration.")
            print()
            print("Rule: The closing -/ of a LaTeX quote comment block must be")
            print("immediately followed by the theorem/def/lemma/corollary")
            print("declaration. Only blank lines are allowed in between.")
            print("-" * 60)
            for idx, v in enumerate(gap_violations, 1):
                print(f"\n{idx}. Comment block at lines {v['comment_start']}-{v['comment_end']}")
                if v['declaration_line']:
                    print(f"   Declaration at line {v['declaration_line']}: {v['declaration_name'] or '?'}")
                else:
                    print("   Declaration: NOT FOUND")
                print("   Offending lines between -/ and declaration:")
                for line_num, text in v['offending_lines']:
                    print(f"     Line {line_num}: {text}")

        if name_violations:
            print()
            print(f"Found {len(name_violations)} declarations with wrong naming convention.")
            print()
            print("Rule: The declaration after a LaTeX quote block must be named")
            print("Ch{N}_{type}_{index} (e.g. Ch1_theorem_3, Ch2_def_5).")
            print("-" * 60)
            for idx, v in enumerate(name_violations, 1):
                print(f"\n{idx}. Comment block at lines {v['comment_start']}-{v['comment_end']}")
                print(f"   Declaration at line {v['declaration_line']}: {v['declaration_name']}")
                print(f"   Expected name matching: Ch*_theorem_*, Ch*_def_*, Ch*_lemma_*, or Ch*_corollary_*")

        print()
        print("-" * 60)
        parts = []
        if gap_violations:
            parts.append(f"{len(gap_violations)} gap violations")
        if name_violations:
            parts.append(f"{len(name_violations)} naming violations")
        print(f"ADJACENCY: FAIL - {', '.join(parts)}")
    else:
        print()
        print("ADJACENCY: PASS - All comment blocks immediately followed by correctly named declarations")

    # Exit with status code based on results
    has_failures = bool(missing or duplicates or violations)
    if has_failures:
        print()
        print("=" * 60)
        parts = []
        if missing:
            parts.append(f"{len(missing)} missing")
        if duplicates:
            parts.append(f"{len(duplicates)} duplicates")
        if violations:
            parts.append(f"{len(violations)} adjacency violations")
        print(f"RESULT: FAIL - {', '.join(parts)}")
        sys.exit(1)
    else:
        print()
        print("RESULT: COMPLETE - All statements found exactly once, all adjacent!")
        sys.exit(0)


if __name__ == '__main__':
    main()
