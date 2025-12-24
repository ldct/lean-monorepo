To build the smallgroups project, run this command

```
lake build Playground.Geometry.SmallGroups.SmallGroups
```

the command will only run if the current directory has a lakefile.toml

## Python Scripts

Check project progress (groups per order 1-60):
```
python3 check_progress.py
```

Check that all Gap files are complete:
```
python3 check_completeness.py
```

Generate HTML table of groups (runs build and parses output):
```
python3 generate_groups_table.py
```