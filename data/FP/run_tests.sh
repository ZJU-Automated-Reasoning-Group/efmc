#!/bin/bash

echo "=== EFMC Floating-Point Template Tests ==="

declare -a tests=(
  "Simple Interval Test|simple_interval.smt2|fp_interval"
  "Auto Template Selection|simple_interval.smt2|auto"
  "Polyhedron Test|polyhedron_test.smt2|fp_poly"
  "Unsafe Test|unsafe_test.smt2|fp_interval"
)

for i in "${!tests[@]}"; do
  IFS="|" read -r name file template <<< "${tests[$i]}"
  echo "Test $((i+1)): $name"
  echo "File: $file"
  echo "Template: $template"
  python -m efmc.cli.efmc --file "$file" --engine ef --template "$template"
  echo "---"
done

echo "=== All Tests Completed ==="
echo "Note: 'unknown' results are expected for complex floating-point reasoning."