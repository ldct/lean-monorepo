# Proof-work delegation

- Read `README.md` for current progress and known statement errors.
- Delegate token-intensive Lean proof development, tactic iteration, and
  supporting lemma searches to the local `pi` CLI using Muse Spark. Keep Codex
  focused on coordination and concise status reporting. The user explicitly
  delegated local verification to Muse Spark; do not repeat its Lean runs in
  Codex. Use Prove2me server verdicts for acceptance. Do not silently fall back to an expensive model if `pi` fails.
- The configured model is `opencode-go/muse-spark-1.3-contributor`. Check readiness
  through the interactive-shell wrapper with
  `zsh -ic 'pi auth check --provider opencode-go --model muse-spark-1.3-contributor --json'`;
  never print credentials. The user's `.zshrc` defines a `pi` function that
  supplies authentication; invoking the executable directly bypasses it.
- Run workers from `~/prove2me_workspace`. Give each worker a bounded task file
  specifying the exact theorem, allowed output files, relevant imports, and
  acceptance criteria. Invoke with explicit model selection:

  ```sh
  zsh -ic 'pi -p --provider opencode-go --model muse-spark-1.3-contributor \
    --session-dir work/pi-sessions @work/TASK.md' > work/TASK.log 2>&1
  ```

- Workers should write to uniquely named scratch files, compile using
  `lake env lean`, and return a short report with changed paths, verification
  commands, and remaining gaps. Require no `sorry`, `admit`, new axioms, weakened
  hypotheses, or modifications to shared definitions or target statements.
  Ordinary scratch-only task prompts prohibit platform submissions, commits,
  pushes, and unrelated changes. The scheduled mission worker is explicitly
  authorized to integrate and submit checked mission work; see below. These
  are workflow constraints, not a security sandbox.
- Muse Spark checks the final proof, compiler exit status, and dependencies
  before integration/submission. Compilation alone does not establish closure
  when imported targets contain axioms or placeholders. Codex does not need
  to independently verify the proof.
- Preserve existing uncommitted work. Keep worker transcripts outside this
  notes repository and summarize results concisely to limit Codex token use.

## Periodic mission work

The user explicitly wants **Astra in this existing thread** to be woken every
30 minutes, coordinate pending work, and delegate proofs to Muse Spark. Do not
replace Astra check-ins with a pi-only supervisor.

- LaunchAgent: `com.xuanji.diophantine-mission-checkin`.
- Runner: `~/prove2me_workspace/work/mission_checkins/wake_astra.py`.
- It queues a message with `codex queue --model gpt-6-astra` to thread
  `01a07a25-4033-7051-a222-3894ceca79a5`; detailed instructions are in
  `work/mission_checkins/astra_prompt.md`.
- Status is recorded in `work/mission_checkins/status.json`.
- Astra checks active workers, processes finished results, reviews statement
  and dependency correctness, submits ready work, polls server verdicts,
  updates README, and delegates the next useful task. Trust Muse Spark's local
  Lean verification; do not rerun proofs independently in Codex.
- Check for active pi work before starting another task. Avoid duplicating
  submissions and tasks if several wake-up messages were queued while busy.
- Pause future wake-ups by creating `work/mission_checkins/PAUSED` in the Lean
  workspace; remove it to resume. It does not cancel an already queued turn.
- Plist: `~/Library/LaunchAgents/com.xuanji.diophantine-mission-checkin.plist`.
  The schedule needs the Mac awake and the user logged in. Delivery is queued
  through the local Codex app-server; a busy thread handles it when available.
- The old `run.py`/`prompt.md` pi-only supervisor is inactive and superseded.
