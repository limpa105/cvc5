#!/bin/bash

# Check if at least three arguments are provided
if [ "$#" -lt 3 ]; then
    echo "Usage: $0 <path_to_cvc5> <TEST_DIR> <output_file> [cvc5_options...]"
    exit 1
fi

# Extract the arguments
CVC5=$1
TEST_DIR=$2
output_file=$3
shift 3  # Remove the first three arguments from the list

# The remaining arguments are options for cvc5
CVC5_OPTIONS="$@"
solved=0
total=0

# Create or clear the output file
if [ ! -f "$output_file" ]; then
    touch "$output_file"
else
    > "$output_file"
fi

# Find all files in the directory (including nested directories) that contain 'smt' in their names
find "$TEST_DIR" -type f -name '*smt*' | while read -r file; do
    total=$((total+1))
    echo -n "$file: " >> "$output_file"
    "$CVC5" $CVC5_OPTIONS "$file" | tail -n 1 >> "$output_file"
done 

# Analyze the results
python3 analyze.py "$output_file"

