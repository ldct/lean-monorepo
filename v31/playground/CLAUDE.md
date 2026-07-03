Steps

The output of one step is generally needed in future steps

- generate_direct_products.py relies on group_names.tsv existing, and creates SmallGroups.lean
- generate_eval_files.py creates EvalXXX.lean
- collect_group_stats.py creates group_stats.json
- generate_groups_table_from_json.py creates the html page