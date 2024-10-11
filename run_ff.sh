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

# Add CSV headers
echo "Filename,Result,Global Time (ms)" > "$output_file"

# Find all files in the directory (including nested directories) that contain 'smt' in their names
find "$TEST_DIR" -type f -name '*smt*' | while read -r file; do
    total=$((total+1))
    
    echo $file

    # Run cvc5 and capture both stdout and stderr in one go
    output=$( gtimeout --signal=SIGTERM --kill-after=5s 130s  "$CVC5" --tlimit 120000 $CVC5_OPTIONS --stats  "$file" 2>&1 )

    echo "Finished cvc5"

    # Extract the last line (result) from stdout (assuming unsat/sat is in stdout)
    result=$(echo "$output" | grep -v 'global::totalTime' | tail -n 6 | head -n 1)

    echo "finished first grep"

    # Extract the global::totalTime from stderr
    global_time=$(echo "$output" | awk '/global::totalTime/ {print $NF}' || echo "timeout")

     echo "finished second grep"

    # Write filename, result, and global time to the CSV file
    echo "$file,$result,$global_time" >> "$output_file"
done 

# Analyze the results
python3 analyze.py "$output_file"
