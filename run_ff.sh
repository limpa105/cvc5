#!/bin/bash

TEST_DIR=$1
CVC5="build/bin/cvc5"
output_file=$2
solved=0
total=0

for file in "$TEST_DIR"/*; do
    if [ -f "$file" ]; then
        total=$((total+1))
        echo -n >> "$output_file"
	    timeout 120 $CVC5 --ff-range-solver "$file" 
        if [ $? -eq 0 ]; then
    # If the program did not timeout, increment the counter
            solved=$((solved+1))
        else
            echo 
        # If the program timed out, do nothing
        fi
    fi
done 
echo -n "Solved: $solved out of $total"
