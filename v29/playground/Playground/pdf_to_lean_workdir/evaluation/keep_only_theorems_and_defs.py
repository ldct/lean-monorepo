#!/usr/bin/env python3
"""
Extract section headers, theorem blocks, and definition blocks from LaTeX files.

Usage:
    python keep_only_theorems_and_defs.py <input_file> <output_file>

Example:
    python keep_only_theorems_and_defs.py /path/to/ch1.txt /path/to/ch1_theorems_and_defs.txt
"""

import sys
import re


def extract_theorems_defs_and_sections(input_path: str, output_path: str) -> None:
    """
    Extract section headers, theorem blocks, and definition blocks from a LaTeX file.

    Extracts:
    - \\section{}, \\subsection{}, \\subsubsection{} lines
    - \\begin{theorem}...\\end{theorem} blocks (including content)
    - \\begin{lemma}...\\end{lemma} blocks
    - \\begin{corollary}...\\end{corollary} blocks
    - \\begin{definition}...\\end{definition} blocks
    """
    with open(input_path, 'r', encoding='utf-8') as f:
        content = f.read()

    results = []

    # Pattern for section headers (matches the entire line)
    section_pattern = re.compile(r'^\\(sub)*section\{[^}]*\}.*$', re.MULTILINE)

    # Pattern for theorem-like and definition environments
    # This captures everything from \begin{env} to \end{env}
    theorem_pattern = re.compile(
        r'\\begin\{(theorem|lemma|corollary|definition)\}.*?\\end\{\1\}',
        re.DOTALL
    )

    # Find all section headers with their positions
    section_matches = [(m.start(), m.end(), m.group(), 'section')
                       for m in section_pattern.finditer(content)]

    # Find all theorem/definition blocks with their positions
    theorem_matches = [(m.start(), m.end(), m.group(), 'theorem')
                       for m in theorem_pattern.finditer(content)]

    # Combine and sort by position
    all_matches = section_matches + theorem_matches
    all_matches.sort(key=lambda x: x[0])

    # Extract the text from each match
    for start, end, text, match_type in all_matches:
        results.append(text.strip())

    # Write output
    output_text = '\n\n'.join(results)
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(output_text)

    print(f"Extracted {len(section_matches)} section headers and {len(theorem_matches)} theorem/definition blocks")
    print(f"Output written to: {output_path}")


def main():
    if len(sys.argv) != 3:
        print("Usage: python keep_only_theorems_and_defs.py <input_file> <output_file>")
        print("Example: python keep_only_theorems_and_defs.py ch1.txt ch1_theorems_and_defs.txt")
        sys.exit(1)

    input_path = sys.argv[1]
    output_path = sys.argv[2]

    extract_theorems_defs_and_sections(input_path, output_path)


if __name__ == '__main__':
    main()
