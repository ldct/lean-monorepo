#!/usr/bin/env python3
r"""
PDF-to-LaTeX converter agent: reads a math textbook PDF and extracts
definitions, theorems, lemmas, corollaries (with proofs) into LaTeX
using the environments required by the downstream formalization pipeline.

Output format is compatible with:
  evaluation/keep_only_theorems_and_defs.py
which expects:
  \begin{theorem}...\end{theorem}
  \begin{lemma}...\end{lemma}
  \begin{corollary}...\end{corollary}
  \begin{definition}...\end{definition}
  \section{...}, \subsection{...}, \subsubsection{...}

Usage:
  python convert.py input.pdf output.txt
  python convert.py input.pdf output.txt --pages 1-50
  python convert.py input.pdf output_dir/ --split-chapters
"""

import argparse
import asyncio
import os
import sys

import yaml
from agent_framework.anthropic import ClaudeAgent


SYSTEM_PROMPT = r"""You are a mathematical LaTeX transcription expert. Your task is to read a PDF of a math textbook and produce LaTeX output containing ONLY:

1. Section/subsection headers
2. Definitions, theorems, lemmas, and corollaries with their proofs

## Output Format Rules (CRITICAL — the downstream pipeline depends on these exact formats)

### Section headers
Use standard LaTeX sectioning commands:
```
\section{Section Title}
\subsection{Subsection Title}
\subsubsection{Subsubsection Title}
```

### Definitions
```
\begin{definition}
<exact mathematical content of the definition>
\end{definition}
```

### Theorems
```
\begin{theorem}
<exact mathematical content of the theorem statement>
\end{theorem}

\begin{proof}
<the proof>
\end{proof}
```

### Lemmas
```
\begin{lemma}
<exact mathematical content of the lemma statement>
\end{lemma}

\begin{proof}
<the proof>
\end{proof}
```

### Corollaries
```
\begin{corollary}
<exact mathematical content of the corollary statement>
\end{corollary}

\begin{proof}
<the proof>
\end{proof}
```

## Critical Requirements

1. **FAITHFULNESS IS THE #1 PRIORITY — do NOT correct anything**: Your job is transcription, not editing. Reproduce the textbook content exactly as written. If the textbook has a spelling mistake, a wrong formula, an incorrect theorem statement, or a flawed proof, reproduce it exactly as-is. Do NOT fix errors, do NOT improve wording, do NOT add missing hypotheses, do NOT correct typos, do NOT rephrase. The downstream formalization pipeline needs the exact content from the textbook. Any corrections will be handled later by a separate verification agent.

2. **Use ONLY these four environments**: `theorem`, `lemma`, `corollary`, `definition`. Do NOT use `proposition`, `remark`, `example`, `exercise`, or any other environment. If the textbook has a "Proposition", wrap it in `\begin{theorem}...\end{theorem}`.

3. **Every \begin must have a matching \end**: `\begin{theorem}...\end{theorem}`, never leave one unclosed.

4. **Preserve mathematical notation faithfully**: Use proper LaTeX math notation ($...$, \[...\], etc.). Reproduce the mathematical symbols, quantifiers, set notation, etc. as accurately as possible from the PDF.

5. **Include proofs**: If a theorem/lemma/corollary has a proof in the textbook, include it in a `\begin{proof}...\end{proof}` block immediately after the statement.

6. **Preserve ALL section headers**: Include every `\section{}`, `\subsection{}`, and `\subsubsection{}` from the textbook, even if there are no theorems or definitions in that section. These headers are needed to maintain the document structure for the downstream pipeline.

7. **Skip everything else — output ONLY environments and section headers**: Every line of your output must be either:
   - Inside `\begin{theorem}...\end{theorem}`, `\begin{lemma}...\end{lemma}`, `\begin{corollary}...\end{corollary}`, or `\begin{definition}...\end{definition}`
   - Inside `\begin{proof}...\end{proof}`
   - A `\section{}`, `\subsection{}`, or `\subsubsection{}` header
   - A `\chapter{}` header
   - Blank lines between environments
   Do NOT include any prose, commentary, examples, exercises, remarks, notes, motivational text, or any other content outside these environments. If the textbook has a paragraph of explanation between two theorems, skip it entirely.

8. **EXCLUDE exercises entirely**: Do not include any exercises, problems, problem sets, homework questions, or "prove that..." prompts from end-of-section exercise blocks. These are NOT theorems — they are tasks for the reader. Even if an exercise contains a mathematical statement, do NOT include it.

9. **Order matters**: Output items in the same order they appear in the textbook.

## What to do with edge cases

- **Numbered theorems** (e.g., "Theorem 3.2.1"): Use `\begin{theorem}[Theorem 3.2.1]`
- **Named theorems** (e.g., "Deduction Theorem"): Use `\begin{theorem}[Deduction Theorem]`
- **Propositions**: Use `\begin{theorem}` environment
- **Facts/Claims**: Use `\begin{lemma}` environment
- **Axioms**: Use `\begin{definition}` environment
- **Multi-part theorems**: Keep as one environment with parts (a), (b), (c) inside
- **Proof sketches**: Include in `\begin{proof}` and note it's a sketch
- **Proofs left as exercises**: Add `\begin{proof} Left as an exercise. \end{proof}`

## CRITICAL: How to read the PDF — DO NOT SKIP THIS

**ABSOLUTE RULE: NEVER read the full PDF file directly. It WILL crash with an API error.** Each PDF page becomes an image, and the API has a hard limit of ~20 images per call. A 50+ page PDF will fail every time if read at once. There is NO workaround — you MUST split first, then read chunks.

Instead, split the PDF into small chunks and read each chunk separately:

```bash
# Step 1: Install pymupdf if not available
pip install pymupdf

# Step 2: Split PDF into per-page or small-chunk PDFs
python3 -c "
import pymupdf
doc = pymupdf.open('INPUT_PDF_PATH')
# Split into chunks of 8 pages
chunk_size = 8
for i in range(0, len(doc), chunk_size):
    chunk = pymupdf.open()
    chunk.insert_pdf(doc, from_page=i, to_page=min(i + chunk_size - 1, len(doc) - 1))
    chunk.save(f'/tmp/pdf_chunk_{i // chunk_size + 1}.pdf')
    chunk.close()
print(f'Split {len(doc)} pages into {(len(doc) + chunk_size - 1) // chunk_size} chunks')
"

# Step 3: Read each chunk PDF (small enough for the API)
# Then process its content before moving to the next chunk
```

This approach preserves mathematical notation (read as images) while staying under API limits.

## Strategy for large PDFs

1. First, split the PDF into small chunks (8-10 pages each) using the method above.
2. Read chunk 1, identify chapter/section boundaries, extract theorems/definitions for those pages, and **write to the output file immediately**.
3. Move to chunk 2, continue extracting, append to the same output file (or start a new chapter file if a new chapter begins).
4. Repeat until all chunks are processed.
5. After all chunks are done, verify the output files for completeness and correctness.

Key rules:
- NEVER read more than 10 PDF pages in a single read operation
- Write output incrementally — do not accumulate the entire book before writing
- Keep track of which chunk you're on so you don't lose your place
"""


LOG_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "log")


class ConvertLogger:
    """Real-time logging for PDF-to-LaTeX conversion."""

    def __init__(self):
        os.makedirs(LOG_DIR, exist_ok=True)
        from datetime import datetime
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.log_file = os.path.join(LOG_DIR, f"convert_{timestamp}.log")
        self.log(f"=== PDF-to-LaTeX conversion started at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} ===")

    def log(self, msg: str):
        print(msg)
        with open(self.log_file, "a") as f:
            f.write(msg + "\n")


def _format_content_for_log(content) -> str | None:
    """Format a Content object into a human-readable log line."""
    ctype = getattr(content, "type", None)
    if ctype is None:
        return None
    ctype_str = str(ctype)

    if "function_call" in ctype_str:
        name = getattr(content, "name", "") or ""
        args = getattr(content, "arguments", "") or ""
        if isinstance(args, dict):
            cmd = args.get("command", "")
            if cmd:
                return f">>> Tool: {name} - {cmd[:200]}"
            return f">>> Tool: {name}({str(args)[:150]})"
        return f">>> Tool: {name}"

    if "function_result" in ctype_str:
        exc = getattr(content, "exception", None)
        if exc:
            name = getattr(content, "name", "") or ""
            return f"<<< Result ({name}): ERROR - {str(exc)[:100]}"
        return None

    if "text" in ctype_str:
        text = getattr(content, "text", "") or ""
        if len(text) > 20:
            return text[:300] + ("..." if len(text) > 300 else "")
        return None

    return None


async def run_agent_with_logging(claude_opts: dict, instructions: str, prompt: str, logger: ConvertLogger) -> str:
    """Run ClaudeAgent with streaming output logged in real time."""
    from datetime import datetime
    start = datetime.now()
    text_buffer = ""  # Accumulate text deltas, flush on tool calls or newlines

    def flush_text_buffer():
        nonlocal text_buffer
        if text_buffer.strip():
            logger.log(text_buffer.rstrip())
        text_buffer = ""

    async with ClaudeAgent(instructions=instructions, default_options=claude_opts) as agent:
        stream = agent.run(prompt, stream=True)
        async for update in stream:
            if hasattr(update, "contents") and update.contents:
                for content in update.contents:
                    ctype_str = str(getattr(content, "type", ""))

                    # Text deltas — accumulate in buffer
                    if "text" in ctype_str:
                        delta = getattr(content, "text", "") or ""
                        text_buffer += delta
                        # Flush on newlines so log stays readable
                        while "\n" in text_buffer:
                            line, text_buffer = text_buffer.split("\n", 1)
                            if line.strip():
                                logger.log(line)
                    else:
                        # Non-text content (tool calls, results) — flush buffer first
                        flush_text_buffer()
                        line = _format_content_for_log(content)
                        if line:
                            logger.log(line)

        # Flush any remaining text
        flush_text_buffer()

        final = await stream.get_final_response()
        elapsed = (datetime.now() - start).total_seconds()
        usage = getattr(final, "usage_details", None)
        if usage:
            input_t = usage.get("input_token_count", "?") if isinstance(usage, dict) else getattr(usage, "input_token_count", "?")
            output_t = usage.get("output_token_count", "?") if isinstance(usage, dict) else getattr(usage, "output_token_count", "?")
            logger.log(f"--- Stats: {elapsed:.0f}s | input={input_t} output={output_t} ---")
        else:
            logger.log(f"--- Stats: {elapsed:.0f}s ---")

        return final.text or ""


def load_config() -> dict:
    """Load claude config from the parent config.yaml."""
    config_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "config.yaml")
    if os.path.exists(config_path):
        with open(config_path) as f:
            return yaml.safe_load(f)
    return {}


def _build_claude_opts(claude_cfg: dict, cwd: str) -> dict:
    """Build ClaudeAgent options from config. Supports subscription, bedrock, api_key."""
    provider = claude_cfg.get("provider", "subscription")
    env = {}
    if provider == "subscription":
        sub_cfg = claude_cfg.get("subscription", {})
        model = sub_cfg.get("model", "opus")
    elif provider == "api_key":
        api_cfg = claude_cfg.get("api_key", {})
        model = api_cfg.get("model", "claude-opus-4-6-20250609")
        key = api_cfg.get("key", "")
        if not key:
            raise ValueError("config.yaml: claude.api_key.key is empty. Set your Anthropic API key.")
        env["ANTHROPIC_API_KEY"] = key
    elif provider == "bedrock":
        bedrock_cfg = claude_cfg.get("bedrock", {})
        model = bedrock_cfg.get("model", "us.anthropic.claude-opus-4-6-v1[1m]")
        env["CLAUDE_CODE_USE_BEDROCK"] = "1"
        env["AWS_PROFILE"] = bedrock_cfg.get("aws_profile", "default")
    else:
        raise ValueError(f"config.yaml: unknown claude.provider '{provider}'. Use 'subscription', 'bedrock', or 'api_key'.")
    return {
        "cli_path": claude_cfg.get("cli_path", "claude"),
        "model": model,
        "permission_mode": claude_cfg.get("permission_mode", "bypassPermissions"),
        "cwd": cwd,
        "env": env,
        "max_buffer_size": 1000 * 1024 * 1024,  # 1000 MB — avoid SDK 1 MB default
    }


async def convert_pdf(pdf_path: str, output_path: str, pages: str | None = None) -> str:
    """Convert a PDF to LaTeX using ClaudeAgent."""
    config = load_config()
    claude_cfg = config.get("claude", {})
    claude_opts = _build_claude_opts(claude_cfg, os.path.dirname(os.path.abspath(pdf_path)))

    pdf_abs = os.path.abspath(pdf_path)
    output_abs = os.path.abspath(output_path)

    prompt = f"""Read the PDF file at `{pdf_abs}`.

Extract all definitions, theorems, lemmas, corollaries, and their proofs into LaTeX format.
"""
    if pages:
        prompt += f"\nOnly process pages {pages}.\n"

    prompt += f"""
Follow the output format rules from your instructions EXACTLY.

Write the complete LaTeX output to `{output_abs}`.

After writing, verify your output by checking:
1. Every `\\begin{{theorem}}` has a matching `\\end{{theorem}}` (same for lemma, corollary, definition)
2. No other environments are used (no proposition, remark, example, exercise, etc.)
3. No content outside of environments or section headers (no loose prose)
4. Section headers use `\\section{{}}`, `\\subsection{{}}`, or `\\subsubsection{{}}`
5. Mathematical notation is proper LaTeX
6. No exercises included

If any check fails, fix the output file before finishing.
"""

    logger = ConvertLogger()
    logger.log(f"Input: {pdf_abs}")
    logger.log(f"Output: {output_abs}")
    logger.log(f"Log: {logger.log_file}")

    result = await run_agent_with_logging(claude_opts, SYSTEM_PROMPT, prompt, logger)
    logger.log("=== Conversion complete ===")
    return result


async def convert_pdf_split_chapters(pdf_path: str, output_dir: str, pages: str | None = None) -> None:
    """Convert a PDF to LaTeX, splitting output into per-chapter files (ch1.txt, ch2.txt, ...)."""
    config = load_config()
    claude_cfg = config.get("claude", {})
    claude_opts = _build_claude_opts(claude_cfg, os.path.dirname(os.path.abspath(pdf_path)))

    pdf_abs = os.path.abspath(pdf_path)
    output_dir_abs = os.path.abspath(output_dir)
    os.makedirs(output_dir_abs, exist_ok=True)

    prompt = f"""Read the PDF file at `{pdf_abs}`.

Extract all definitions, theorems, lemmas, corollaries, and their proofs into LaTeX format.
"""
    if pages:
        prompt += f"\nOnly process pages {pages}.\n"

    prompt += f"""
Follow the output format rules from your instructions EXACTLY.

Split the output into per-chapter files in `{output_dir_abs}/`:
- `ch1.txt` for Chapter 1
- `ch2.txt` for Chapter 2
- etc.

Each file should start with:
```
%
% Chapter N
%

\\chapter[Short Title]{{Full Title}}
```

Then contain the sections, definitions, theorems, lemmas, corollaries for that chapter.

After writing all files, verify each output file by checking:
1. Every `\\begin{{theorem}}` has a matching `\\end{{theorem}}` (same for lemma, corollary, definition)
2. No other environments are used (no proposition, remark, example, exercise, etc.)
3. No content outside of environments or section headers (no loose prose)
4. Section headers use `\\section{{}}`, `\\subsection{{}}`, or `\\subsubsection{{}}`
5. Mathematical notation is proper LaTeX
6. No exercises included

If any check fails, fix the output files before finishing.

List all chapter files you created when done.
"""

    logger = ConvertLogger()
    logger.log(f"Input: {pdf_abs}")
    logger.log(f"Output dir: {output_dir_abs}")
    logger.log(f"Log: {logger.log_file}")

    result = await run_agent_with_logging(claude_opts, SYSTEM_PROMPT, prompt, logger)
    logger.log("=== Conversion complete ===")
    print(result)


async def main():
    parser = argparse.ArgumentParser(description="Convert math textbook PDF to LaTeX (definitions/theorems only)")
    parser.add_argument("input", help="Path to input PDF file")
    parser.add_argument("output", help="Output file path (.txt) or directory (with --split-chapters)")
    parser.add_argument("--pages", default=None, help="Page range to process (e.g., '1-50', '10-20')")
    parser.add_argument("--split-chapters", action="store_true", help="Split output into per-chapter files (ch1.txt, ch2.txt, ...)")
    args = parser.parse_args()

    if not os.path.exists(args.input):
        print(f"ERROR: Input file not found: {args.input}")
        sys.exit(1)

    if args.split_chapters:
        await convert_pdf_split_chapters(args.input, args.output, args.pages)
    else:
        result = await convert_pdf(args.input, args.output, args.pages)
        print(result)

    print("\nDone. Output files are ready for the formalization pipeline.")
    print("Next step: run the pipeline with the output as --input")


if __name__ == "__main__":
    asyncio.run(main())
