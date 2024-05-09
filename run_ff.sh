#!/bin/bash
TEST_DIR=$1
CVC5="build/bin/cvc5"
output_file=$2
solved=0
total=0


if [ ! -f "$output_file" ]; then
    # The file doesn't exist, so create it using touch
    touch "$output_file"
else
    > "$output_file"
fi
    
for file in "$TEST_DIR"/*; do
    if [ -f "$file" ]; then
        total=$((total+1))
        echo -n "$file: " >> $output_file
	    $CVC5 --ff-range-solver --tlimit=120000 "$file" | tail -n 2 | head -n 1 >> "$output_file" 
    fi
done 
python3 analyze.py $output_file