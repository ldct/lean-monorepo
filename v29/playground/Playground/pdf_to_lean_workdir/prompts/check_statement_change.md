# Task: Verify and Apply Lean 4 Statement Changes

You are a Lean 4 expert. Your task is to verify proposed changes to theorem/definition statements and apply them if legitimate.

## Step 1: Review the Proposed Changes

Read the unfaithful arguments analysis file at `{unfaithful_args_file}`.

Read carefully! You are the only one I can count on. Make sure your judge is mathematically justified. Think carefully.

If the file is empty or does not exist, stop and exit.

## Step 2: If change is not legitimate

Skip this statement and move to the next.

## Step 3: If change is legitimate

If you think the analysis and explanation makes sense, so that the theorem statement or definition is indeed unfaithful and semantically inequivalent to the latex quote, please modify the corresponding statement in {lean_chapter_file} so that the new statement is faithful and semantically equivalent to the latex quote.

You should deal with each statement one at a time.

----------------------------------------------------------------

After all statements (theorems and definitions) are dealt with,

1. **Find the next version number**: Check the directory `{intermediate_dir}/` for existing files matching the pattern `ch{ch_num}_specs_*.lean` and determine the next version number.

2. **Rename the current specs file**: Rename:
   ```
   {intermediate_dir}/ch{ch_num}_specs.lean
   ```
   to:
   ```
   {intermediate_dir}/ch{ch_num}_specs_{{next_version}}.lean
   ```
   if only ch{ch_num}_specs.lean exists, the next_version number is 0.

3. **Copy the updated ch{ch_num}.lean**: Copy the contents of:
   ```
   {lean_chapter_file}
   ```
   to:
   ```
   {intermediate_dir}/ch{ch_num}_specs.lean
   ```

## Always log your decision into `{change_history_file}`. Don't overwrite; always append.

## Summary of Files

| Purpose | Path |
|---------|------|
| Analysis of unfaithful arguments | `{unfaithful_args_file}` |
| Decision log | `{change_history_file}` |
| Main Lean file (source of truth) | `{lean_chapter_file}` |
| Specs file to version | `{intermediate_dir}/ch{ch_num}_specs.lean` |
| Versioned specs directory | `{intermediate_dir}/` |
