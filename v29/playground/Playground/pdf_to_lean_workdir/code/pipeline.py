#!/usr/bin/env python3
"""
Agent Framework pipeline: converts LaTeX textbook chapters into verified Lean 4 formalizations.

Replaces the original bash-based pipeline with Python-native orchestration
using ClaudeAgent from the Microsoft Agent Framework.
"""

import asyncio
import argparse
import glob
import json
import os
import re
import shutil
import subprocess
import sys
from datetime import datetime

import yaml
from agent_framework.anthropic import ClaudeAgent
from tools import loogle_search

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def discover_chapters(input_dir: str) -> list[int]:
    files = glob.glob(os.path.join(input_dir, "ch*.txt"))
    nums = []
    for f in files:
        m = re.search(r'ch(\d+)\.txt$', os.path.basename(f))
        if m:
            nums.append(int(m.group(1)))
    return sorted(nums)


def load_prompt(prompts_dir: str, name: str, **kwargs) -> str:
    """Load a prompt template and fill placeholders."""
    path = os.path.join(prompts_dir, name)
    with open(path) as f:
        template = f.read()
    return template.format(**kwargs)


def make_claude_options(claude_cfg: dict, project_root: str) -> dict:
    """Build ClaudeAgent default_options from config.

    Supports three providers:
      - "subscription": Claude Pro/Max subscription (no keys, shorthand model names)
      - "bedrock": AWS Bedrock (requires AWS credentials)
      - "api_key": Anthropic API key (requires ANTHROPIC_API_KEY)
    """
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
        "cwd": project_root,
        "env": env,
        "max_buffer_size": 1000 * 1024 * 1024,  # 1000 MB — avoid SDK 1 MB default
    }


def check_prerequisites():
    """Check that required tools are available."""
    missing = []
    for cmd in ["elan", "lake", "claude", "python3"]:
        if shutil.which(cmd) is None:
            missing.append(cmd)
    if missing:
        print(f"ERROR: Missing required tools: {', '.join(missing)}")
        print("Please install them before running the pipeline.")
        sys.exit(1)
    try:
        import yaml as _y  # noqa: F401
    except ImportError:
        missing.append("pyyaml (pip install pyyaml)")
    if missing:
        print(f"ERROR: Missing Python packages: {', '.join(missing)}")
        sys.exit(1)


# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

class PipelineLogger:
    """Persistent logging matching the bash pipeline's AUTO_RUN_STATUS.md,
    AUTO_RUN_STATUS.md.history, and AUTO_RUN_LOG.txt."""

    def __init__(self, log_dir: str, ch: int, phase: str):
        os.makedirs(log_dir, exist_ok=True)
        self.log_dir = log_dir
        self.ch = ch
        self.phase = phase
        self.status_file = os.path.join(log_dir, "AUTO_RUN_STATUS.md")
        self.history_file = os.path.join(log_dir, "AUTO_RUN_STATUS.md.history")
        self.log_file = os.path.join(log_dir, "AUTO_RUN_LOG.txt")
        self.start_time = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.pid = os.getpid()

        # Append to history (preserve previous runs on resume)
        self.append_history(f"Chapter {ch} {phase} started")

    def update_status(self, iteration: int, max_iter: int, step: str, state: str, details: str):
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        history = ""
        if os.path.exists(self.history_file):
            with open(self.history_file) as f:
                history = f.read()
        with open(self.status_file, "w") as f:
            f.write(f"# Chapter {self.ch} {self.phase} - Auto Status\n\n")
            f.write("| Field | Value |\n|-------|-------|\n")
            f.write(f"| **Status** | {state} |\n")
            f.write(f"| **Current Iteration** | {iteration} / {max_iter} |\n")
            f.write(f"| **Current Step** | {step} |\n")
            f.write(f"| **Started At** | {self.start_time} |\n")
            f.write(f"| **Last Updated** | {now} |\n")
            f.write(f"| **PID** | {self.pid} |\n\n")
            f.write(f"## Current Activity\n{details}\n\n")
            f.write(f"## Progress History\n{history}\n")

    def append_history(self, msg: str):
        now = datetime.now().strftime("%H:%M:%S")
        with open(self.history_file, "a") as f:
            f.write(f"- [{now}] {msg}\n")

    def log(self, msg: str):
        print(msg)
        with open(self.log_file, "a") as f:
            f.write(msg + "\n")

    def finalize(self, iteration: int, max_iter: int, exit_state: str, details: str):
        self.update_status(iteration, max_iter, exit_state, exit_state, details)
        self.append_history(f"Process ended: {exit_state}")


# ---------------------------------------------------------------------------
# Token usage tracking
# ---------------------------------------------------------------------------

class TokenTracker:
    """Accumulates token usage across all agent calls and persists to disk
    after every update so the user can check TOKEN_USAGE.md at any time."""

    def __init__(self, output_dir: str, model: str):
        self.output_dir = output_dir
        self.model = model
        self.calls: list[dict] = []
        self.total_input = 0
        self.total_output = 0
        self.total_elapsed = 0.0
        self.md_path = os.path.join(output_dir, "TOKEN_USAGE.md")
        self.json_path = os.path.join(output_dir, "token_usage.json")
        self.start_time = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        # Resume from existing token usage if available
        if os.path.exists(self.json_path):
            try:
                with open(self.json_path) as f:
                    data = json.load(f)
                self.calls = data.get("calls", [])
                self.total_input = data.get("total_input_tokens", 0)
                self.total_output = data.get("total_output_tokens", 0)
                self.total_elapsed = data.get("total_elapsed_s", 0.0)
                self.start_time = data.get("started", self.start_time)
            except (json.JSONDecodeError, KeyError):
                pass  # Start fresh if file is corrupted

    def record(self, call_name: str, input_tokens: int, output_tokens: int, elapsed: float):
        self.total_input += input_tokens
        self.total_output += output_tokens
        self.total_elapsed += elapsed
        self.calls.append({
            "call": len(self.calls) + 1,
            "name": call_name,
            "input_tokens": input_tokens,
            "output_tokens": output_tokens,
            "elapsed_s": round(elapsed, 1),
            "cumul_input": self.total_input,
            "cumul_output": self.total_output,
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        })
        self._save()

    def _save(self):
        """Write both TOKEN_USAGE.md and token_usage.json."""
        # --- Markdown ---
        lines = [
            "# Token Usage\n",
            f"**Model:** `{self.model}`  ",
            f"**Started:** {self.start_time}  ",
            f"**Last updated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}  \n",
            "## Summary\n",
            "| Metric | Value |",
            "|--------|-------|",
            f"| Total input tokens | {self.total_input:,} |",
            f"| Total output tokens | {self.total_output:,} |",
            f"| Total tokens | {self.total_input + self.total_output:,} |",
            f"| Total elapsed | {self.total_elapsed:.0f}s |",
            f"| Agent calls | {len(self.calls)} |\n",
            "## Per-Call Breakdown\n",
            "| # | Agent | Input | Output | Time | Cumul In | Cumul Out |",
            "|---|-------|------:|-------:|-----:|---------:|----------:|",
        ]
        for c in self.calls:
            lines.append(
                f"| {c['call']} | {c['name']} "
                f"| {c['input_tokens']:,} | {c['output_tokens']:,} "
                f"| {c['elapsed_s']}s "
                f"| {c['cumul_input']:,} | {c['cumul_output']:,} |"
            )
        lines.append("")

        with open(self.md_path, "w") as f:
            f.write("\n".join(lines))

        # --- JSON ---
        data = {
            "model": self.model,
            "started": self.start_time,
            "last_updated": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "total_input_tokens": self.total_input,
            "total_output_tokens": self.total_output,
            "total_tokens": self.total_input + self.total_output,
            "total_elapsed_s": round(self.total_elapsed, 1),
            "calls": self.calls,
        }
        with open(self.json_path, "w") as f:
            json.dump(data, f, indent=2)


# ---------------------------------------------------------------------------
# Agent runners
# ---------------------------------------------------------------------------

def _format_content_for_log(content) -> str | None:
    """Format a Content object into a human-readable log line."""
    ctype = getattr(content, "type", None)
    if ctype is None:
        return None

    ctype_str = str(ctype)

    # Tool calls (function_call, shell commands, MCP tools)
    if "function_call" in ctype_str:
        name = getattr(content, "name", "") or ""
        args = getattr(content, "arguments", "") or ""
        if isinstance(args, dict):
            # For bash commands, show the command
            cmd = args.get("command", "")
            if cmd:
                preview = cmd[:200] + ("..." if len(cmd) > 200 else "")
                return f">>> Tool: {name} - {preview}"
            args_preview = str(args)[:150]
            return f">>> Tool: {name}({args_preview})"
        return f">>> Tool: {name}"

    if "shell_tool" in ctype_str or "shell_command" in ctype_str:
        cmds = getattr(content, "commands", None) or []
        cmd_str = "; ".join(cmds)[:200] if cmds else ""
        return f">>> Shell: {cmd_str}" if cmd_str else None

    if "function_result" in ctype_str:
        name = getattr(content, "name", "") or ""
        exc = getattr(content, "exception", None)
        if exc:
            return f"<<< Result ({name}): ERROR - {str(exc)[:100]}"
        return None  # Don't log successful results (too verbose)

    # Text content — skip streaming deltas, only log substantial text
    if "text" in ctype_str:
        text = getattr(content, "text", "") or ""
        if len(text) > 20:
            return text[:300] + ("..." if len(text) > 300 else "")
        return None

    return None


async def run_agent(claude_opts: dict, prompt: str, logger: PipelineLogger | None = None, tools: list | None = None, instructions: str | None = None, tracker: TokenTracker | None = None, call_name: str = "") -> str:
    """Run a single ClaudeAgent call with streaming output logged in real time."""
    start_time = datetime.now()
    text_buffer = ""  # Accumulate text deltas, flush on newlines or tool calls

    def flush_text():
        nonlocal text_buffer
        if logger and text_buffer.strip():
            logger.log(text_buffer.rstrip())
        text_buffer = ""

    agent_kwargs = {}
    if tools:
        agent_kwargs["tools"] = tools
    if instructions:
        agent_kwargs["instructions"] = instructions

    # Import ResultMessage to capture usage from the CLI's result event
    from agent_framework_claude._agent import ResultMessage

    result_msg = None  # Will capture the ResultMessage during streaming

    async with ClaudeAgent(default_options=claude_opts, **agent_kwargs) as agent:
        # Intercept at the client level to capture ResultMessage
        if hasattr(agent, "_client") and agent._client:
            original_receive = agent._client.receive_response

            async def _patched_receive():
                nonlocal result_msg
                async for message in original_receive():
                    if isinstance(message, ResultMessage):
                        result_msg = message
                    yield message

            agent._client.receive_response = _patched_receive

        stream = agent.run(prompt, stream=True)
        async for update in stream:
            if logger and hasattr(update, "contents") and update.contents:
                for content in update.contents:
                    ctype_str = str(getattr(content, "type", ""))
                    if "text" in ctype_str:
                        delta = getattr(content, "text", "") or ""
                        text_buffer += delta
                        while "\n" in text_buffer:
                            line, text_buffer = text_buffer.split("\n", 1)
                            if line.strip():
                                logger.log(line)
                    else:
                        flush_text()
                        line = _format_content_for_log(content)
                        if line:
                            logger.log(line)

        flush_text()
        final = await stream.get_final_response()
        elapsed = (datetime.now() - start_time).total_seconds()
        final_text = final.text or ""

        # Extract token counts — try usage_details first, then captured ResultMessage
        input_tokens = 0
        output_tokens = 0
        usage = getattr(final, "usage_details", None)
        if usage:
            input_tokens = (usage.get("input_token_count", 0) if isinstance(usage, dict)
                            else getattr(usage, "input_token_count", 0)) or 0
            output_tokens = (usage.get("output_token_count", 0) if isinstance(usage, dict)
                             else getattr(usage, "output_token_count", 0)) or 0

        # Fallback: use captured ResultMessage from CLI
        if not (input_tokens or output_tokens) and result_msg and result_msg.usage:
            ru = result_msg.usage
            # input_tokens only counts non-cached input; add cache tokens for the real total
            input_tokens = (
                (ru.get("input_tokens", 0) or 0)
                + (ru.get("cache_creation_input_tokens", 0) or 0)
                + (ru.get("cache_read_input_tokens", 0) or 0)
            )
            output_tokens = ru.get("output_tokens", 0) or 0

        if tracker:
            tracker.record(call_name or "agent", input_tokens, output_tokens, elapsed)

        return final_text


async def run_agent_for_verdict(claude_opts: dict, prompt: str, logger: PipelineLogger | None = None, tools: list | None = None, tracker: TokenTracker | None = None, call_name: str = "") -> str:
    """Run agent and extract DONE/CONTINUE verdict from response."""
    text = await run_agent(claude_opts, prompt, logger, tools=tools, tracker=tracker, call_name=call_name)
    # Extract the last meaningful word — scan from bottom up
    for line in reversed(text.strip().splitlines()):
        stripped = line.strip().upper()
        if stripped == "DONE":
            return "DONE"
        if stripped == "CONTINUE":
            return "CONTINUE"
    # Fallback: substring match (less strict, like the bash version)
    # Check CONTINUE first — if both appear, prefer the conservative choice
    for line in reversed(text.strip().splitlines()):
        stripped = line.strip().upper()
        if "CONTINUE" in stripped:
            return "CONTINUE"
        if "DONE" in stripped:
            return "DONE"
    return "CONTINUE"


# ---------------------------------------------------------------------------
# Statement formalization loop
# ---------------------------------------------------------------------------

async def run_statement_loop(
    ch: int,
    project_root: str,
    claude_opts: dict,
    prompts_dir: str,
    evaluation_dir: str,
    max_iterations: int,
    tracker: TokenTracker | None = None,
) -> bool:
    """Run the statement formalization/verification loop for one chapter.
    Returns True if successful (DONE), False if max iterations reached.
    """
    raw_data_dir = os.path.join(project_root, "natural_language", "raw_data")
    theorems_dir = os.path.join(raw_data_dir, "theorems_and_defs")
    lean_file = os.path.join(project_root, "Formalization", f"ch{ch}.lean")
    lean_src_dir = os.path.join(project_root, "Formalization")
    verify_dir = os.path.join(project_root, "experiments", "auto", f"ch{ch}", "verification_fl_statement")

    logger = PipelineLogger(verify_dir, ch, "Statement Formalization")

    # Check if this phase already completed successfully in a previous run
    status_path = os.path.join(verify_dir, "AUTO_RUN_STATUS.md")
    if os.path.exists(status_path):
        with open(status_path) as f:
            status_content = f.read()
        if "FINISHED" in status_content:
            logger.log("Statement formalization already FINISHED in a previous run. Skipping.")
            return True

    # Build reuse instructions
    prior_files = glob.glob(os.path.join(lean_src_dir, "ch*.lean"))
    prior_chapters = sorted([
        int(re.search(r'ch(\d+)\.lean', os.path.basename(f)).group(1))
        for f in prior_files
        if re.search(r'ch(\d+)\.lean', os.path.basename(f))
        and int(re.search(r'ch(\d+)\.lean', os.path.basename(f)).group(1)) < ch
    ])
    if prior_chapters:
        deps = ", ".join(f"{lean_src_dir}/ch{c}.lean" for c in prior_chapters)
        reuse_instructions = f"You should reuse definitions from {deps} whenever possible!!!"
    else:
        reuse_instructions = "This is the first chapter. No prior chapter definitions to reuse."

    # Resume: find the first incomplete round (no verification result file)
    start_round = 1
    for r in range(1, max_iterations + 1):
        result = os.path.join(verify_dir, f"round_{r}", "fl_statements_verification_result.md")
        if os.path.exists(result) and os.path.getsize(result) > 0:
            start_round = r + 1
        else:
            break
    if start_round > max_iterations:
        logger.log("All statement rounds already completed (max iterations reached).")
        logger.finalize(max_iterations, max_iterations, "STOPPED", "Max iterations already reached in previous run.")
        return False
    if start_round > 1:
        logger.log(f"Resuming from round {start_round} (rounds 1-{start_round - 1} already have verification results)")

    for i in range(start_round, max_iterations + 1):
        round_dir = os.path.join(verify_dir, f"round_{i}")
        os.makedirs(round_dir, exist_ok=True)
        status_file = os.path.join(round_dir, "fl_statements_status.md")
        verify_result_file = os.path.join(round_dir, "fl_statements_verification_result.md")

        prev_verify = os.path.join(verify_dir, f"round_{i-1}", "fl_statements_verification_result.md")

        logger.log(f"\n========================================")
        logger.log(f"=== ITERATION {i} of {max_iterations} ===")
        logger.log(f"========================================")
        logger.append_history(f"Iteration {i} started (round dir: round_{i})")

        # Step 1: Statement formalization
        logger.update_status(i, max_iterations, "1/3 Statement Formalization", "RUNNING", "Running Claude statement formalization task...")
        logger.append_history(f"Iteration {i}: Statement formalization started")

        fl_prompt = load_prompt(
            prompts_dir, "statement_fl.md",
            ch_num=ch, raw_data_dir=raw_data_dir, theorems_and_defs_dir=theorems_dir,
            lean_chapter_file=lean_file, lean_src_dir=lean_src_dir,
            project_root=project_root, evaluation_dir=evaluation_dir,
            reuse_instructions=reuse_instructions, status_file=status_file,
        )
        if os.path.exists(prev_verify):
            fl_prompt += f"\n\nAlso read the PREVIOUS round's verification result from {prev_verify}, and focus on fixing any major discrepancies or coverage issues reported there."
        fl_prompt += f"\n\nThis is round {i}. Save your verification efforts and status log to {status_file}. IMPORTANT: Do NOT modify any file outside of this chapter. Ignore any errors or warnings that are not about this chapter."

        await run_agent(claude_opts, fl_prompt, logger, tools=[loogle_search],
                        tracker=tracker, call_name=f"ch{ch} Stmt FL R{i}")
        logger.append_history(f"Iteration {i}: Statement formalization completed")

        # Step 2: Statement verification
        logger.update_status(i, max_iterations, "2/3 Statement Verification", "RUNNING", "Running Claude statement verification task...")
        logger.append_history(f"Iteration {i}: Statement verification started")

        verify_prompt = load_prompt(
            prompts_dir, "statement_verify.md",
            ch_num=ch, lean_chapter_file=lean_file,
            theorems_and_defs_dir=theorems_dir,
            project_root=project_root, evaluation_dir=evaluation_dir,
            output_file=verify_result_file,
        )
        verify_prompt += f"\n\nThis is round {i}. Write results to {verify_result_file}. IMPORTANT: Do NOT modify any file outside of this chapter. Ignore any errors or warnings that are not about this chapter."

        await run_agent(claude_opts, verify_prompt, logger, tools=[loogle_search],
                        tracker=tracker, call_name=f"ch{ch} Stmt Verify R{i}")
        logger.append_history(f"Iteration {i}: Statement verification completed")

        # Step 3: Verdict
        logger.update_status(i, max_iterations, "3/3 Checking Verdict", "RUNNING", "Claude is analyzing verification results...")
        logger.append_history(f"Iteration {i}: Checking verdict")

        verdict_prompt = load_prompt(
            prompts_dir, "verdict_statement.md",
            ch_num=ch, verification_result_file=verify_result_file,
        )
        decision = await run_agent_for_verdict(claude_opts, verdict_prompt, logger,
                                               tracker=tracker, call_name=f"ch{ch} Stmt Verdict R{i}")
        logger.log(f"Iteration {i}: Decision is {decision}")
        logger.append_history(f"Iteration {i}: Decision = {decision}")

        if decision == "DONE":
            logger.finalize(i, max_iterations, "FINISHED", "All verifications passed successfully!")
            logger.append_history("SUCCESS - All verifications passed")
            return True

        await asyncio.sleep(2)  # Brief pause between iterations

    logger.finalize(max_iterations, max_iterations, "STOPPED", "Max iterations reached.")
    logger.append_history("STOPPED - Max iterations reached")
    return False


# ---------------------------------------------------------------------------
# Proof search loop
# ---------------------------------------------------------------------------

async def run_proof_loop(
    ch: int,
    project_root: str,
    claude_opts: dict,
    prompts_dir: str,
    evaluation_dir: str,
    max_iterations: int,
    check_interval: int,
    proving_skill: str = "",
    tracker: TokenTracker | None = None,
) -> bool:
    """Run the proof search/verification loop for one chapter.
    Returns True if successful (DONE), False if max iterations reached.
    """
    lean_file = os.path.join(project_root, "Formalization", f"ch{ch}.lean")
    intermediate_dir = os.path.join(project_root, "Formalization", "intermediate_files", f"ch{ch}")
    verify_dir = os.path.join(project_root, "experiments", "auto", f"ch{ch}", "verification")
    proof_info_file = os.path.join(project_root, "Formalization", "utils", f"ch{ch}_info.txt")

    logger = PipelineLogger(verify_dir, ch, "Proof Search")

    # Check if this phase already completed successfully in a previous run
    status_path = os.path.join(verify_dir, "AUTO_RUN_STATUS.md")
    if os.path.exists(status_path):
        with open(status_path) as f:
            status_content = f.read()
        if "FINISHED" in status_content:
            logger.log("Proof search already FINISHED in a previous run. Skipping.")
            return True

    # Resume: find the first incomplete round (no verification result file)
    start_round = 1
    for r in range(1, max_iterations + 1):
        result = os.path.join(verify_dir, f"round_{r}", "fl_proof_verification_result.md")
        if os.path.exists(result) and os.path.getsize(result) > 0:
            start_round = r + 1
        else:
            break
    if start_round > max_iterations:
        logger.log("All proof rounds already completed (max iterations reached).")
        logger.finalize(max_iterations, max_iterations, "STOPPED", "Max iterations already reached in previous run.")
        return False
    if start_round > 1:
        logger.log(f"Resuming from round {start_round} (rounds 1-{start_round - 1} already have verification results)")

    for i in range(start_round, max_iterations + 1):
        round_dir = os.path.join(verify_dir, f"round_{i}")
        os.makedirs(round_dir, exist_ok=True)
        proof_status_file = os.path.join(round_dir, "fl_proof_status.md")
        verify_result_file = os.path.join(round_dir, "fl_proof_verification_result.md")
        unfaithful_args_file = os.path.join(round_dir, "fl_statements_unfaithful_arguments.md")
        change_history_file = os.path.join(round_dir, "fl_statements_change_history.md")

        prev_verify = os.path.join(verify_dir, f"round_{i-1}", "fl_proof_verification_result.md")
        prev_proof_status = os.path.join(verify_dir, f"round_{i-1}", "fl_proof_status.md")

        logger.log(f"\n========================================")
        logger.log(f"=== ITERATION {i} of {max_iterations} ===")
        logger.log(f"========================================")
        logger.append_history(f"Iteration {i} started (round dir: round_{i})")

        # Build previous-round instructions
        prev_instructions = ""
        if os.path.exists(prev_verify):
            prev_instructions += f"- Read the PREVIOUS round's verification result from {prev_verify}.\n"
        if os.path.exists(prev_proof_status):
            prev_instructions += f"- Read the PREVIOUS round's proof status from {prev_proof_status}. It contains which approaches were tried and FAILED — do NOT repeat these.\n"
        if not prev_instructions:
            prev_instructions = "- This is the first round. No previous round data available.\n"

        # Step 1: Proof search
        logger.update_status(i, max_iterations, "1/3 Proof Search", "RUNNING", "Running Claude proof search task...")
        logger.append_history(f"Iteration {i}: Proof search started")

        search_prompt = load_prompt(
            prompts_dir, "proof_search.md",
            ch_num=ch, lean_chapter_file=lean_file,
            project_root=project_root, evaluation_dir=evaluation_dir,
            intermediate_dir=intermediate_dir,
            proof_info_file=proof_info_file,
            round_num=i, proof_status_file=proof_status_file,
            unfaithful_args_file=unfaithful_args_file,
            previous_round_instructions=prev_instructions,
        )
        search_prompt += f"\n\nThis is round {i}. Start proving theorems. If one approach doesn't work after much effort, try a completely different proof strategy. No sorry allowed in proofs! IMPORTANT: Do NOT modify any file outside of this chapter. Ignore any errors or warnings that are not about this chapter."

        await run_agent(claude_opts, search_prompt, logger, tools=[loogle_search], instructions=proving_skill or None,
                        tracker=tracker, call_name=f"ch{ch} Proof Search R{i}")
        logger.append_history(f"Iteration {i}: Proof search completed")

        # Step 2: Proof verification
        logger.update_status(i, max_iterations, "2/3 Verification", "RUNNING", "Running Claude verification task...")
        logger.append_history(f"Iteration {i}: Verification started")

        verify_prompt = load_prompt(
            prompts_dir, "proof_verify.md",
            ch_num=ch, lean_chapter_file=lean_file,
            project_root=project_root, evaluation_dir=evaluation_dir,
            intermediate_dir=intermediate_dir,
            output_file=verify_result_file,
        )
        verify_prompt += f"\n\nThis is round {i}. Write results to {verify_result_file}. IMPORTANT: Do NOT modify any file outside of this chapter. Ignore any errors or warnings that are not about this chapter."

        await run_agent(claude_opts, verify_prompt, logger, tools=[loogle_search],
                        tracker=tracker, call_name=f"ch{ch} Proof Verify R{i}")
        logger.append_history(f"Iteration {i}: Verification completed")

        # Step 3: Verdict
        logger.update_status(i, max_iterations, "3/3 Checking Verdict", "RUNNING", "Claude is analyzing verification results...")
        logger.append_history(f"Iteration {i}: Checking verdict")

        verdict_prompt = load_prompt(
            prompts_dir, "verdict_proof.md",
            ch_num=ch, verification_result_file=verify_result_file,
        )
        decision = await run_agent_for_verdict(claude_opts, verdict_prompt, logger,
                                               tracker=tracker, call_name=f"ch{ch} Proof Verdict R{i}")
        logger.log(f"Iteration {i}: Decision is {decision}")
        logger.append_history(f"Iteration {i}: Decision = {decision}")

        # Step 4: Check statement change (periodic) — runs regardless of verdict
        # so unfaithful arguments are always reviewed, even if proofs all pass
        statement_changed = False
        if i % check_interval == 0:
            if os.path.exists(unfaithful_args_file):
                logger.update_status(i, max_iterations, "4/4 Check Statement Change", "RUNNING", "Running Claude statement change verification...")
                logger.append_history(f"Iteration {i}: Check statement change started")

                change_prompt = load_prompt(
                    prompts_dir, "check_statement_change.md",
                    ch_num=ch, lean_chapter_file=lean_file,
                    intermediate_dir=intermediate_dir,
                    unfaithful_args_file=unfaithful_args_file,
                    change_history_file=change_history_file,
                )
                await run_agent(claude_opts, change_prompt, logger, tools=[loogle_search],
                                tracker=tracker, call_name=f"ch{ch} Stmt Change Check R{i}")
                logger.append_history(f"Iteration {i}: Check statement change completed")
                statement_changed = True

        if decision == "DONE":
            if statement_changed:
                logger.log(f"Iteration {i}: Verdict was DONE but statement changes were reviewed; continuing to re-verify.")
                logger.append_history(f"Iteration {i}: Re-verifying after statement change review")
            else:
                logger.finalize(i, max_iterations, "FINISHED", "All verifications passed successfully!")
                logger.append_history("SUCCESS - All verifications passed")
                return True

        await asyncio.sleep(2)  # Brief pause between iterations

    logger.finalize(max_iterations, max_iterations, "STOPPED", "Max iterations reached.")
    logger.append_history("STOPPED - Max iterations reached")
    return False


# ---------------------------------------------------------------------------
# Full chapter pipeline
# ---------------------------------------------------------------------------

async def run_chapter(
    ch: int,
    project_root: str,
    claude_opts: dict,
    prompts_dir: str,
    evaluation_dir: str,
    pipeline_cfg: dict,
    proving_skill: str = "",
    tracker: TokenTracker | None = None,
) -> bool:
    """Run the full pipeline for one chapter: statements → snapshot → proofs."""
    max_stmt = pipeline_cfg.get("max_statement_iterations", 9)
    max_proof = pipeline_cfg.get("max_proof_iterations", 9)
    check_interval = pipeline_cfg.get("statement_check_interval", 1)

    # Phase 1: Statement formalization
    print(f"\n--- Chapter {ch}: Statement Formalization ---")
    stmt_ok = await run_statement_loop(
        ch, project_root, claude_opts, prompts_dir, evaluation_dir, max_stmt,
        tracker=tracker,
    )

    # Phase 2: Snapshot specs (only if no snapshot exists yet — don't overwrite
    # on resume, since the proof agent may have partially modified the .lean file)
    lean_file = os.path.join(project_root, "Formalization", f"ch{ch}.lean")
    specs_dir = os.path.join(project_root, "Formalization", "intermediate_files", f"ch{ch}")
    os.makedirs(specs_dir, exist_ok=True)
    specs_file = os.path.join(specs_dir, f"ch{ch}_specs.lean")
    if os.path.exists(lean_file) and not os.path.exists(specs_file):
        shutil.copy2(lean_file, specs_file)
        print(f"  [ch{ch}] Specs snapshot saved")
    elif os.path.exists(specs_file):
        print(f"  [ch{ch}] Specs snapshot already exists, keeping it")

    # Phase 3: Proof search
    print(f"\n--- Chapter {ch}: Proof Search ---")
    proof_ok = await run_proof_loop(
        ch, project_root, claude_opts, prompts_dir, evaluation_dir,
        max_proof, check_interval, proving_skill=proving_skill,
        tracker=tracker,
    )

    return stmt_ok and proof_ok


# ---------------------------------------------------------------------------
# Main pipeline
# ---------------------------------------------------------------------------

async def main():
    parser = argparse.ArgumentParser(description="Agent Framework textbook-to-Lean pipeline")
    parser.add_argument("--input", required=True, help="Directory containing ch*.txt LaTeX chapter files")
    parser.add_argument("--output", required=True, help="Lean project root")
    parser.add_argument("--config", required=True, help="Path to config.yaml")
    parser.add_argument("--skip-chapters", default="", help="Comma-separated chapter numbers to skip in Stage 3 (e.g. '1,2')")
    args = parser.parse_args()

    skip_chapters = set()
    if args.skip_chapters:
        skip_chapters = {int(x.strip()) for x in args.skip_chapters.split(",") if x.strip()}

    # Prerequisites check
    check_prerequisites()

    with open(args.config) as f:
        config = yaml.safe_load(f)

    pipeline_cfg = config.get("pipeline", {})
    claude_cfg = config.get("claude", {})
    project_root = os.path.abspath(args.output)

    # Resolve paths relative to project root (one level up from code/)
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_base = os.path.dirname(script_dir)  # formalization_upgrade/
    prompts_dir = os.path.join(project_base, "prompts")
    evaluation_dir = os.path.join(project_base, "evaluation")
    skill_dir = os.path.join(project_base, "skill")

    # Load proof search skill (used as system prompt for proof search agent)
    proving_skill_path = os.path.join(skill_dir, "proving_skill.md")
    math_skill_path = os.path.join(skill_dir, "super_math_skill.md")
    lean_advice_path = os.path.join(skill_dir, "lean_proving_advice.md")
    proving_skill = ""
    if os.path.exists(proving_skill_path):
        with open(proving_skill_path) as f:
            proving_skill = f.read()
        # Fill in the reference file paths
        proving_skill = proving_skill.replace("{math_skill_file}", math_skill_path)
        proving_skill = proving_skill.replace("{lean_advice_file}", lean_advice_path)

    chapters = discover_chapters(args.input)
    if not chapters:
        print(f"ERROR: No ch*.txt files found in {args.input}")
        sys.exit(1)

    print(f"=== Discovered {len(chapters)} chapters: {chapters} ===")
    print(f"=== Project root: {project_root} ===")

    # Build ClaudeAgent options
    claude_opts = make_claude_options(claude_cfg, project_root)

    # Token usage tracker — writes TOKEN_USAGE.md after every agent call
    tracker = TokenTracker(project_root, claude_opts["model"])
    print(f"=== Token log: {tracker.md_path} ===")

    # -------------------------------------------------------
    # Stage 0: Scaffold
    # -------------------------------------------------------
    print("\n" + "=" * 60)
    print("STAGE 0: Scaffolding Lean project")
    print("=" * 60)
    from scaffold import scaffold
    scaffold(args.input, project_root, chapters)

    # Fetch Mathlib cache
    print("  Fetching Mathlib cache...")
    subprocess.run(["lake", "exe", "cache", "get"], cwd=project_root, check=True)

    # -------------------------------------------------------
    # Stage 1: Extract theorem blocks
    # -------------------------------------------------------
    print("\n" + "=" * 60)
    print("STAGE 1: Extracting theorem and definition blocks")
    print("=" * 60)
    theorems_dir = os.path.join(project_root, "natural_language", "raw_data", "theorems_and_defs")
    extract_script = os.path.join(evaluation_dir, "keep_only_theorems_and_defs.py")
    for ch in chapters:
        src = os.path.join(args.input, f"ch{ch}.txt")
        dst = os.path.join(theorems_dir, f"ch{ch}.txt")
        print(f"  ch{ch}: extracting theorem/definition blocks...")
        subprocess.run([sys.executable, extract_script, src, dst], check=True)

    # -------------------------------------------------------
    # Stage 2: Copy raw chapter files to utils for proof reference
    # -------------------------------------------------------
    print("\n" + "=" * 60)
    print("STAGE 2: Copying raw chapter text to utils for proof reference")
    print("=" * 60)
    utils_dir = os.path.join(project_root, "Formalization", "utils")
    os.makedirs(utils_dir, exist_ok=True)
    for ch in chapters:
        src = os.path.join(args.input, f"ch{ch}.txt")
        dst = os.path.join(utils_dir, f"ch{ch}_info.txt")
        if os.path.exists(src):
            shutil.copy2(src, dst)
            print(f"  ch{ch}: copied -> {dst}")
        else:
            print(f"  ch{ch}: WARNING: {src} not found, skipping")

    # -------------------------------------------------------
    # Stage 3: Formalization (sequential by chapter)
    # -------------------------------------------------------
    print("\n" + "=" * 60)
    print("STAGE 3: Formalization (sequential by chapter)")
    print("=" * 60)
    formalize_chapters = [ch for ch in chapters if ch not in skip_chapters]
    if skip_chapters:
        print(f"  Skipping chapters: {sorted(skip_chapters)}")
        print(f"  Processing chapters: {formalize_chapters}")

    failed_chapters = []
    for ch in formalize_chapters:
        print(f"\n{'=' * 60}")
        print(f"Chapter {ch}: statements → proofs")
        print(f"{'=' * 60}")
        try:
            ok = await run_chapter(ch, project_root, claude_opts, prompts_dir, evaluation_dir, pipeline_cfg, proving_skill=proving_skill, tracker=tracker)
            if ok:
                print(f"  Chapter {ch}: DONE")
            else:
                print(f"  Chapter {ch}: INCOMPLETE (max iterations reached)")
                failed_chapters.append(ch)
        except Exception as e:
            print(f"  Chapter {ch}: FAILED: {e}")
            failed_chapters.append(ch)

    if failed_chapters:
        print(f"\nWARNING: Chapters {failed_chapters} had issues")

    # -------------------------------------------------------
    # Stage 4: Final validation
    # -------------------------------------------------------
    print("\n" + "=" * 60)
    print("STAGE 4: Final validation")
    print("=" * 60)
    from validate import validate
    validate(project_root, chapters, evaluation_dir)

    print("\n" + "=" * 60)
    print("PIPELINE COMPLETE")
    print("=" * 60)
    print(f"Project at:    {project_root}")
    print(f"Token usage:   {tracker.md_path}")


if __name__ == "__main__":
    asyncio.run(main())
