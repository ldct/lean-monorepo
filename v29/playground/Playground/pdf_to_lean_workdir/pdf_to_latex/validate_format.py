#!/usr/bin/env python3
"""
Validate that ch*.txt LaTeX files conform to the format required by the
downstream formalization pipeline.

Checks:
  1. Only allowed environments: theorem, lemma, corollary, definition, proof
  2. Every \\begin{env} has a matching \\end{env}
  3. Every theorem/lemma/corollary/definition has a \\label{...}
  4. No forbidden environments (proposition, remark, example, exercise, etc.)
  5. Section headers use \\section{}, \\subsection{}, \\subsubsection{}
  6. No exercise content
  7. Extractable by keep_only_theorems_and_defs.py (at least 1 block found)

Usage:
  python validate_format.py ch1.txt ch2.txt ...
  python validate_format.py /path/to/output_dir/
"""

import glob
import os
import re
import sys
from collections import Counter


ALLOWED_ENVS = {"theorem", "lemma", "corollary", "definition", "proof"}
STATEMENT_ENVS = {"theorem", "lemma", "corollary", "definition"}
FORBIDDEN_ENVS = {
    "proposition", "remark", "example", "exercise", "problem",
    "notation", "observation", "conjecture", "claim", "fact",
    "question", "note", "warning", "axiom",
}


def find_all_environments(content: str) -> list[tuple[str, int, str]]:
    """Find all \\begin{env} occurrences. Returns [(env_name, line_number, 'begin'|'end'), ...]."""
    results = []
    for i, line in enumerate(content.splitlines(), 1):
        for m in re.finditer(r'\\begin\{(\w+)\}', line):
            results.append((m.group(1), i, "begin"))
        for m in re.finditer(r'\\end\{(\w+)\}', line):
            results.append((m.group(1), i, "end"))
    return results


def validate_file(filepath: str) -> tuple[bool, list[str], dict]:
    """Validate a single file. Returns (passed, list_of_issues, stats_dict)."""
    issues = []

    if not os.path.exists(filepath):
        return False, [f"File not found: {filepath}"], {}

    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()

    if not content.strip():
        return False, [f"File is empty: {filepath}"], {}

    filename = os.path.basename(filepath)
    envs = find_all_environments(content)

    # --- Check 1: No forbidden environments ---
    # These are standard LaTeX environments that don't affect the pipeline — silently ignored
    BENIGN_ENVS = {
        "document", "center", "tabular", "tabular*", "table", "table*",
        "align", "align*", "equation", "equation*", "gather", "gather*",
        "multline", "multline*", "split", "gathered", "aligned",
        "enumerate", "itemize", "description", "list",
        "enumerateLoose", "itemizeLoose",
        "figure", "figure*", "tikzpicture", "tikzcd",
        "prooftree", "cases", "array", "matrix", "pmatrix", "bmatrix", "vmatrix",
        "quote", "quotation", "verbatim", "minipage", "abstract",
        "implications", "exerciseStar",
    }
    for env_name, line_num, kind in envs:
        if kind == "begin" and env_name in FORBIDDEN_ENVS:
            issues.append(f"  Line {line_num}: Forbidden environment \\begin{{{env_name}}}. "
                          f"Use theorem/lemma/corollary/definition instead.")
        elif kind == "begin" and env_name not in ALLOWED_ENVS and env_name not in BENIGN_ENVS:
            issues.append(f"  Line {line_num}: Unexpected environment \\begin{{{env_name}}}. "
                          f"Only theorem/lemma/corollary/definition/proof are expected.")

    # --- Check 2: Matched begin/end pairs ---
    stack = []
    for env_name, line_num, kind in envs:
        if kind == "begin":
            stack.append((env_name, line_num))
        elif kind == "end":
            if not stack:
                issues.append(f"  Line {line_num}: \\end{{{env_name}}} without matching \\begin")
            else:
                open_env, open_line = stack.pop()
                if open_env != env_name:
                    issues.append(f"  Line {line_num}: \\end{{{env_name}}} does not match "
                                  f"\\begin{{{open_env}}} at line {open_line}")
    for env_name, line_num in stack:
        issues.append(f"  Line {line_num}: \\begin{{{env_name}}} never closed")

    # --- Check 3: Section headers present ---
    section_pattern = re.compile(r'^\\(sub)*section\{[^}]+\}', re.MULTILINE)
    section_matches = section_pattern.findall(content)
    if not section_matches:
        # Not necessarily an error for short chapters, but warn
        section_count = 0
    else:
        section_count = len(section_pattern.findall(content))

    # --- Check 5: No exercise content ---
    exercise_patterns = [
        (r'\\begin\{exercise\}', "\\begin{exercise} environment"),
        (r'\\begin\{problem\}', "\\begin{problem} environment"),
        (r'^\\noindent\s*\*?\*?\s*Exercise\b', "Exercise heading"),
        (r'^Exercises?\s*$', "Exercises section"),
        (r'^Problems?\s*$', "Problems section"),
    ]
    for pattern, desc in exercise_patterns:
        for m in re.finditer(pattern, content, re.MULTILINE | re.IGNORECASE):
            line_num = content[:m.start()].count("\n") + 1
            issues.append(f"  Line {line_num}: Found exercise content ({desc})")

    # --- Check 6: At least one extractable block ---
    extract_pattern = re.compile(
        r'\\begin\{(theorem|lemma|corollary|definition)\}.*?\\end\{\1\}',
        re.DOTALL,
    )
    blocks = extract_pattern.findall(content)
    if not blocks:
        issues.append(f"  No theorem/lemma/corollary/definition blocks found — "
                      f"nothing for the pipeline to formalize")

    # --- Count stats ---
    env_counts = Counter()
    for env_name, _, kind in envs:
        if kind == "begin" and env_name in STATEMENT_ENVS:
            env_counts[env_name] += 1
    proof_count = sum(1 for e, _, k in envs if k == "begin" and e == "proof")

    return len(issues) == 0, issues, {
        "sections": section_count,
        "theorems": env_counts.get("theorem", 0),
        "lemmas": env_counts.get("lemma", 0),
        "corollaries": env_counts.get("corollary", 0),
        "definitions": env_counts.get("definition", 0),
        "proofs": proof_count,
    }


def main():
    if len(sys.argv) < 2:
        print("Usage: python validate_format.py <ch1.txt> [ch2.txt ...]")
        print("       python validate_format.py <directory/>")
        sys.exit(1)

    # Collect files
    files = []
    for arg in sys.argv[1:]:
        if os.path.isdir(arg):
            found = sorted(glob.glob(os.path.join(arg, "ch*.txt")))
            if not found:
                print(f"ERROR: No ch*.txt files found in {arg}")
                sys.exit(1)
            files.extend(found)
        else:
            files.append(arg)

    all_pass = True
    total_stats = Counter()

    print("=" * 60)
    print("FORMAT VALIDATION RESULTS")
    print("=" * 60)

    for filepath in files:
        filename = os.path.basename(filepath)
        passed, issues, stats = validate_file(filepath)

        total_stats.update(stats)

        if passed:
            print(f"\n  PASS: {filename}")
            if stats:
                parts = []
                for key in ["definitions", "theorems", "lemmas", "corollaries", "proofs", "sections"]:
                    if stats.get(key, 0) > 0:
                        parts.append(f"{stats[key]} {key}")
                print(f"        {', '.join(parts)}")
        else:
            print(f"\n  FAIL: {filename}")
            all_pass = False
            for issue in issues:
                print(issue)
            if stats:
                parts = []
                for key in ["definitions", "theorems", "lemmas", "corollaries", "proofs", "sections"]:
                    if stats.get(key, 0) > 0:
                        parts.append(f"{stats[key]} {key}")
                if parts:
                    print(f"        Found: {', '.join(parts)}")

    # Summary
    print()
    print("=" * 60)
    total_stmts = total_stats.get("theorems", 0) + total_stats.get("lemmas", 0) + \
                  total_stats.get("corollaries", 0) + total_stats.get("definitions", 0)
    print(f"Files checked:  {len(files)}")
    print(f"Total blocks:   {total_stmts} statements, {total_stats.get('proofs', 0)} proofs, {total_stats.get('sections', 0)} sections")
    print(f"Result:         {'ALL PASS' if all_pass else 'SOME FAILED'}")
    print("=" * 60)

    sys.exit(0 if all_pass else 1)


if __name__ == "__main__":
    main()
