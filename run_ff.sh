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
        echo  >> "$output_file"
	    timeout 120 $CVC5 --ff-range-solver "$file" 
        if [ $? -eq 0 ]; then
		echo -n "$file solved" >> $output_file
    # If the program did not timeout, increment the counter
            solved=$((solved+1))
        else
	    echo "$file failed" >> $output_file
        # If the program timed out, do nothing
        fi
    fi
done 
echo  "Solved: $solved out of $total"
